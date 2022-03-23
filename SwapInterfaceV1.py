import json
import time
import asyncio
import aiosqlite
import sqlite3
import logging
import redis
import base64
import math
import phpserialize

from typing import Any, Dict, List, Optional, Set, Tuple

from blspy import AugSchemeMPL, G2Element, PrivateKey

from chives.consensus.constants import ConsensusConstants
from chives.util.hash import std_hash
from chives.types.announcement import Announcement
from chives.types.blockchain_format.coin import Coin
from chives.types.blockchain_format.program import Program
from chives.types.blockchain_format.sized_bytes import bytes32
from chives.types.coin_spend import CoinSpend
from chives.types.condition_opcodes import ConditionOpcode
from chives.types.condition_with_args import ConditionWithArgs
from chives.types.spend_bundle import SpendBundle
from chives.util.clvm import int_from_bytes, int_to_bytes
from chives.util.condition_tools import conditions_by_opcode, conditions_for_solution, pkm_pairs_for_conditions_dict
from chives.util.ints import uint32, uint64
from chives.util.byte_types import hexstr_to_bytes
from chives.util.condition_tools import conditions_dict_for_solution, pkm_pairs_for_conditions_dict

from chives.types.blockchain_format.classgroup import ClassgroupElement
from chives.types.blockchain_format.coin import Coin
from chives.types.blockchain_format.foliage import TransactionsInfo
from chives.types.blockchain_format.program import SerializedProgram
from chives.types.blockchain_format.sized_bytes import bytes32
from chives.types.blockchain_format.slots import InfusedChallengeChainSubSlot
from chives.types.blockchain_format.vdf import VDFInfo, VDFProof
from chives.types.end_of_slot_bundle import EndOfSubSlotBundle
from chives.types.full_block import FullBlock
from chives.types.unfinished_block import UnfinishedBlock

from chives.wallet.derive_keys import master_sk_to_wallet_sk,master_sk_to_wallet_sk_unhardened
from chives.wallet.puzzles.p2_delegated_puzzle_or_hidden_puzzle import (
    DEFAULT_HIDDEN_PUZZLE_HASH,
    calculate_synthetic_secret_key,
    puzzle_for_pk,
    solution_for_conditions,
)
from chives.wallet.puzzles.puzzle_utils import (
    make_assert_aggsig_condition,
    make_assert_coin_announcement,
    make_assert_puzzle_announcement,
    make_assert_relative_height_exceeds_condition,
    make_assert_absolute_height_exceeds_condition,
    make_assert_my_coin_id_condition,
    make_assert_absolute_seconds_exceeds_condition,
    make_assert_relative_seconds_exceeds_condition,
    make_create_coin_announcement,
    make_create_puzzle_announcement,
    make_create_coin_condition,
    make_reserve_fee_condition,
    make_assert_my_parent_id,
    make_assert_my_puzzlehash,
    make_assert_my_amount,
)
from chives.util.keychain import Keychain, bytes_from_mnemonic, bytes_to_mnemonic, generate_mnemonic, mnemonic_to_seed

from chives.consensus.default_constants import DEFAULT_CONSTANTS

from chives.rpc.full_node_rpc_api import FullNodeRpcApi
from chives.rpc.full_node_rpc_client import FullNodeRpcClient
from chives.util.default_root import DEFAULT_ROOT_PATH
from chives.util.config import load_config
from chives.util.ints import uint16
from chives.util.misc import format_bytes

from chives.wallet.transaction_record import TransactionRecord

from chives.wallet.cc_wallet.cat_constants import DEFAULT_CATS
from chives.wallet.cc_wallet.cc_info import CCInfo
from chives.wallet.cc_wallet.cc_utils import (
    CC_MOD,
    SpendableCC,
    construct_cc_puzzle,
    unsigned_spend_bundle_for_spendable_ccs,
    match_cat_puzzle,
)

from chives.wallet.puzzles.p2_delegated_puzzle_or_hidden_puzzle import (
    DEFAULT_HIDDEN_PUZZLE_HASH,
    calculate_synthetic_secret_key,
    puzzle_for_pk,
    solution_for_conditions,
)
import dataclasses
from dataclasses import replace
from dataclasses import dataclass

from chives.wallet.derivation_record import DerivationRecord
from chives.wallet.lineage_proof import LineageProof
from chives.wallet.puzzles.genesis_checkers import ALL_LIMITATIONS_PROGRAMS
from chives.wallet.puzzles.p2_delegated_puzzle_or_hidden_puzzle import (
    DEFAULT_HIDDEN_PUZZLE_HASH,
    calculate_synthetic_secret_key,
)
from chives.wallet.transaction_record import TransactionRecord
from chives.wallet.util.transaction_type import TransactionType
from chives.wallet.util.wallet_types import WalletType
from chives.wallet.wallet import Wallet
from chives.wallet.wallet_coin_record import WalletCoinRecord
from chives.wallet.wallet_info import WalletInfo
from chives.util.streamable import Streamable, streamable
from chives.util.bech32m import decode_puzzle_hash, encode_puzzle_hash

# This should probably not live in this file but it's for experimental right now
@dataclasses.dataclass
class Payment:
    puzzle_hash: bytes32
    amount: uint64
    memos: Optional[List[Optional[bytes]]] = None
    
@dataclass(frozen=True)
@streamable
class CCInfo(Streamable):
    limitations_program_hash: bytes32
    my_genesis_checker: Optional[Program]  # this is the program
    lineage_proofs: List[Tuple[bytes32, Optional[LineageProof]]]  # {coin.name(): lineage_proof}


# SWAP LIB CODE
from SwapWalletAssetTokenV1 import SwapWalletAssetTokenV1
from SwapStandardCoinV1 import SwapStandardCoinV1

'''
1 用户质押流程:
    1 用户存入XCH和TOKEN,其中FEE为一个随机数,XCH找零为钱包的第二个地址,得到的找零同时也为一个随机数
    2 判断用户找零地址是否存在有对应金额的COIN,如果转账失败,则直接标记转账失败,无需再次转账;如果存在,则LP池则转移凭证．
    3 如果LP的TOKEN转移成功,则标记质押状态完成,如果转移失败,则需要重新发送.
    4 LP的TOKEN需要拆分为十条左右的记录,以扩大并发处理能力.
    5 流动性池的接收地址,可以为同一个INNER地址,但是会有不同的外部地址.
2 用户取消质押:
    1 用户转账汇入TOKEN给LP,同时需要支付转账手续费(手续费数值随机,得到一个找零地址和随机金额).如果失败,则不需要再次发送.
    2 判断用户找零地址是否存在有对应金额的COIN,如果转账失败,则直接标记转账失败,无需再次转账;如果存在,则LP池给用户转账XCH和TOKEN
    3 同时标记一个手续费地址,如果手续费地址存在,则标记为取消成功
'''

class SwapInterfaceV1:
    def __init__(self, constants: ConsensusConstants, sk: Optional[PrivateKey] = None):
        self.constants = constants
        self.current_balance = 0
        pool = redis.ConnectionPool(host='localhost', port=6379, db=0)
        self.r = redis.Redis(connection_pool=pool) 
        
    def 返回一个跟时间有关的随机数(self): 
        #时间随机数
        RandomNumber    = int(str(int(time.time()))[5:])
        if RandomNumber < 50000:
            RandomNumber = RandomNumber + 50000
        return RandomNumber
    
    def POOL交易对全局变量(self,SWAP_PAIR): 
        交易对全局变量 = {}
        '''
        #流动性池的接收地址
        交易对全局变量['Pool']                                = {}
        交易对全局变量['Pool']['CAT_ASSET_ID']                = "3e3a7614a02d9714a21927ef99c7ef9bf8270e374dc6ecc48f2619cbc70c4ddc"
        交易对全局变量['Pool']['Mnemonic']                    = ""
        交易对全局变量['Pool']['Mnemonic_Tandem']             = ""
        交易对全局变量['Pool']['ReceivedAddress']             = "xcc1j52u3e3nf3tfp6x5k2u5p9k8tndqk24ds3rnsa9cuwvh0y4kyzhqpaq8zr"
        交易对全局变量['Pool']['miner_fee_mojo']              =  self.返回一个跟时间有关的随机数()
        #流动性池所有权凭证发送TOKEN给用户
        交易对全局变量['LP']                                  = {}
        交易对全局变量['LP']['CAT_ASSET_ID']                  = "c7df7731a849c87a42cd0d3dcde0def8b5e53a4232bb31e1c7dcde6ba3325c29"
        交易对全局变量['LP']['Mnemonic']                      = ""
        交易对全局变量['LP']['Mnemonic_Tandem']               = ""
        交易对全局变量['LP']['TotalIssueAmount']              =  100000000
        交易对全局变量['LP']['miner_fee_mojo']                =  self.返回一个跟时间有关的随机数()
        '''
        TODO_ORDER = self.r.hget("CHIVES_SWAP_V1_CHIVES_PAIR",SWAP_PAIR)        
        TODO_ORDER_64 = base64.b64decode(TODO_ORDER)        
        if TODO_ORDER_64 is not None:
            交易对全局变量 = json.loads(TODO_ORDER_64)
            交易对全局变量['Pool']['miner_fee_mojo']         =  self.返回一个跟时间有关的随机数()
            交易对全局变量['LP']['miner_fee_mojo']           =  self.返回一个跟时间有关的随机数()
            交易对全局变量['SWAP_PAIR']                      =  SWAP_PAIR
            return 交易对全局变量
    
    async def connect_fullnode(self):
        self.SWAT = SwapWalletAssetTokenV1(self.constants);
        #连接主节点
        await self.SWAT.connect_fullnode()
        
    async def close_fullnode(self):
        #关闭结点连接
        await self.SWAT.close_fullnode()
    
    async def 开始处理任务(self):
        await self.connect_fullnode()
        
        TodoListDict                = self.POOL交易对全局变量("Chives-KITTY")
        await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict); 
                    
        CHIVES_SWAP_V1_CHIVES_DOING = self.r.hgetall("CHIVES_SWAP_V1_CHIVES_DOING")
        COUNTER = 0
        for ORDER_KEY,ORDER_STATUS in CHIVES_SWAP_V1_CHIVES_DOING.items():
            if(ORDER_STATUS == bytes("","ascii") ):
                TODO_ORDER = self.r.hget("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY)
                TODO_ORDER_64 = base64.b64decode(TODO_ORDER)
                if len(TODO_ORDER_64)>0:
                    print('********************************') 
                    TODO_ORDER_JSON = json.loads(TODO_ORDER_64)
                    #print(TODO_ORDER_JSON)
                    #交易_输入COIN_输出TOKEN
                    SWAP_PAIR                   = TODO_ORDER_JSON['SWAP_PAIR']
                    TodoListDict                = self.POOL交易对全局变量(SWAP_PAIR)
                    #print(SWAP_PAIR)
                    #print(TodoListDict)
                    当前PAIR状态是否锁定        = self.SWAT.当前PAIR状态是否锁定(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                    print(f"当前PAIR状态是否锁定:{当前PAIR状态是否锁定}")    
                    
                    if "SWAP_IN_COIN" in TODO_ORDER_JSON and 当前PAIR状态是否锁定 == False:
                        print(ORDER_KEY)
                        #构建处理任务清单
                        TodoListDict['SWAP_IN_COIN']    = TODO_ORDER_JSON['SWAP_IN_COIN']
                        TodoListDict['SWAP_IN_COIN']['CAT_ASSET_ID']     = TodoListDict['Pool']['CAT_ASSET_ID']
                        TodoListDict['SWAP_IN_COIN']['Mnemonic']         = TodoListDict['Pool']['Mnemonic']
                        #print(TodoListDict)
                        self.SWAT.锁定当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                        
                        if TodoListDict['SWAP_IN_COIN']['Status'] =="" :
                            await self.SWAT.交易_输入COIN_输出TOKEN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                        if TodoListDict['SWAP_IN_COIN']['Status'] =="Submitted" and TodoListDict['SWAP_IN_COIN']['ChangeAmount']>0 and TodoListDict['SWAP_IN_COIN']['ChangePuzzleHash'] != "" and TodoListDict['SWAP_IN_COIN']['ChangePuzzleHash'] is not None:
                            await self.SWAT.Check_交易_输入COIN_输出TOKEN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                        
                        if TodoListDict['SWAP_IN_COIN']['Status'] =="DONE" and len(TodoListDict['SWAP_IN_COIN']['Mnemonic']) > 15:
                            await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
                            #清除密钥
                            #print(TodoListDict['SWAP_IN_COIN'])
                            TodoListDict['SWAP_IN_COIN']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                            TodoListDict['SWAP_IN_COIN']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                            TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                            TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                            TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY,TODO_ORDER_64_TEXT)
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_DOING",ORDER_KEY,"DONE")
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",TodoListDict['SWAP_IN_COIN']['CreatorUser'],0)
                            self.SWAT.解锁当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                            
                    
                    #交易_输入TOKEN_输出COIN
                    if "SWAP_IN_TOKEN" in TODO_ORDER_JSON and 当前PAIR状态是否锁定 == False:    
                        print(ORDER_KEY)
                        #构建处理任务清单
                        TodoListDict['SWAP_IN_TOKEN']                   = TODO_ORDER_JSON['SWAP_IN_TOKEN']
                        TodoListDict['SWAP_IN_TOKEN']['CAT_ASSET_ID']     = TodoListDict['Pool']['CAT_ASSET_ID']
                        TodoListDict['SWAP_IN_TOKEN']['Mnemonic_Tandem']  = TodoListDict['Pool']['Mnemonic']
                        self.SWAT.锁定当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                        #print(TodoListDict)
                        if TodoListDict['SWAP_IN_TOKEN']['Status'] =="" :
                            await self.SWAT.交易_输入TOKEN_输出COIN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                        if TodoListDict['SWAP_IN_TOKEN']['Status'] =="Submitted" and TodoListDict['SWAP_IN_TOKEN']['ChangeAmount']>0 and TodoListDict['SWAP_IN_TOKEN']['ChangePuzzleHash'] != "" and TodoListDict['SWAP_IN_TOKEN']['ChangePuzzleHash'] is not None:
                            await self.SWAT.Check_交易_输入TOKEN_输出COIN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                        
                        if TodoListDict['SWAP_IN_TOKEN']['Status'] =="DONE" and len(TodoListDict['SWAP_IN_TOKEN']['Mnemonic']) > 15:
                            await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
                            #清除密钥
                            #print(TodoListDict['SWAP_IN_TOKEN'])
                            TodoListDict['SWAP_IN_TOKEN']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                            TodoListDict['SWAP_IN_TOKEN']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                            TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                            TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                            TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY,TODO_ORDER_64_TEXT)
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_DOING",ORDER_KEY,"DONE")
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",TodoListDict['SWAP_IN_TOKEN']['CreatorUser'],0)
                            self.SWAT.解锁当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                            

                    if "User" in TODO_ORDER_JSON and "LP" in TODO_ORDER_JSON and "USER_LPS" not in TODO_ORDER_JSON and 当前PAIR状态是否锁定 == False: 
                        print(ORDER_KEY)
                        #构建处理任务清单
                        TodoListDict['User']                            = TODO_ORDER_JSON['User']                        
                        TodoListDict['User']['CAT_ASSET_ID']            = TodoListDict['Pool']['CAT_ASSET_ID']
                        TodoListDict['User']['Coin_SendToPuzzleHash']   = str(decode_puzzle_hash(TodoListDict['Pool']['ReceivedAddress']).hex())
                        TodoListDict['User']['Token_SendToPuzzleHash']  = str(decode_puzzle_hash(TodoListDict['Pool']['ReceivedAddress']).hex())
                        
                        for key1,value1 in TODO_ORDER_JSON['LP'].items():
                            TodoListDict['LP'][key1]                    = value1;
                            
                        #print(TodoListDict['LP'])
                        #print(f"质押COIN:{TodoListDict['User']['Coin_SendToAmount']}")
                        #print(f"质押TOKEN:{TodoListDict['User']['Token_SendToAmount']}")
                        #print(f"TotalIssueAmount:{TodoListDict['LP']['TotalIssueAmount']}")
                        self.SWAT.锁定当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                        
                        if TodoListDict['User']['Status'] =="" :                
                            是否转账成功 = await self.SWAT.向某一个账户转COIN和TOKEN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict,ActionValue="User");
                            if 是否转账成功 == True:
                                #如果转账成功,就需要立即计算应该获得的LPS,然后把数值保存起来
                                计算需要增加的LPS的值VALUE = await self.SWAT.计算需要增加的LPS的值(SendAssetTokenDict=TodoListDict)
                                TodoListDict['LP']['Token_SendToAmount']  = 计算需要增加的LPS的值VALUE
                                TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                                self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY,TODO_ORDER_64_TEXT)
                                print(f"获得LPS:{TodoListDict['LP']['Token_SendToAmount']}")
                            
                        if TodoListDict['User']['Status'] =="Submitted" and TodoListDict['User']['ChangeAmount']>0 and TodoListDict['User']['ChangePuzzleHash'] != "" and TodoListDict['User']['ChangePuzzleHash'] is not None:
                            await self.SWAT.Check_向某一个账户转COIN和TOKEN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict,ActionValue="User");
                        
                        if TodoListDict['LP']['Status'] =="" and TodoListDict['User']['Status'] =="DONE":
                            await self.SWAT.LP向用户发放质押凭证(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                            TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY,TODO_ORDER_64_TEXT)
                            #print("111")
                            #print(TodoListDict['LP'])
                        
                        if TodoListDict['LP']['Status'] =="Submitted" and TodoListDict['LP']['ChangeAmount']>0 and TodoListDict['LP']['ChangePuzzleHash'] != "" and TodoListDict['LP']['ChangePuzzleHash'] is not None:
                            await self.SWAT.Check_向某一个账户转COIN和TOKEN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict,ActionValue="LP");
                            #print("222")
                            TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY,TODO_ORDER_64_TEXT)
                        
                        if TodoListDict['LP']['Status'] =="DONE" and len(TodoListDict['User']['Mnemonic']) > 15:
                            await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
                            #清除密钥
                            TodoListDict['User']['Mnemonic']              =  str(TodoListDict['User']['Mnemonic'])[0:10]
                            TodoListDict['User']['Mnemonic_Tandem']       =  str(TodoListDict['User']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                            TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                            TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                            #print(TodoListDict)
                            TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY,TODO_ORDER_64_TEXT)
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_DOING",ORDER_KEY,"DONE")
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",TodoListDict['User']['CreatorUser'],0)
                            self.SWAT.解锁当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                            
                            
                    if "USER_LPS" in TODO_ORDER_JSON and "POOL_BACK" in TODO_ORDER_JSON and 当前PAIR状态是否锁定 == False: 
                        print(ORDER_KEY)
                        #构建处理任务清单
                        TodoListDict['USER_LPS']                            = TODO_ORDER_JSON['USER_LPS']                        
                        TodoListDict['USER_LPS']['CAT_ASSET_ID']            = TodoListDict['LP']['CAT_ASSET_ID']
                        TodoListDict['USER_LPS']['Mnemonic_Tandem']         = TodoListDict['LP']['Mnemonic_Tandem'] #只用来扣除FEE
                        
                        TodoListDict['POOL_BACK']                            = TODO_ORDER_JSON['POOL_BACK']  
                        TodoListDict['POOL_BACK']['CAT_ASSET_ID']            = TodoListDict['Pool']['CAT_ASSET_ID']
                        TodoListDict['POOL_BACK']['Mnemonic']                = TodoListDict['Pool']['Mnemonic']
                        TodoListDict['POOL_BACK']['Mnemonic_Tandem']         = TodoListDict['Pool']['Mnemonic_Tandem'] #只用来扣除FEE
                        
                        self.SWAT.锁定当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)

                        if TodoListDict['USER_LPS']['Status'] =="" :
                            await self.SWAT.用户取消质押时用户退还LPS并且记录数量(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                            print("")
                        if TodoListDict['USER_LPS']['Status'] =="Submitted" and TodoListDict['USER_LPS']['ChangeAmount']>0 and TodoListDict['USER_LPS']['ChangePuzzleHash'] != "" and TodoListDict['USER_LPS']['ChangePuzzleHash'] is not None:
                            await self.SWAT.Check_用户取消质押时用户退还LPS并且记录数量(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                            print("")
                        
                        if TodoListDict['POOL_BACK']['Status'] =="" and TodoListDict['USER_LPS']['Status'] =="DONE":
                            await self.SWAT.用户取消质押时LP退还用户COIN和TOKEN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                            print("")
                        if TodoListDict['POOL_BACK']['Status'] =="Submitted" and TodoListDict['POOL_BACK']['ChangeAmount']>=0 and TodoListDict['POOL_BACK']['ChangePuzzleHash'] != "" and TodoListDict['POOL_BACK']['ChangePuzzleHash'] is not None:
                            await self.SWAT.Check_用户取消质押时LP退还用户COIN和TOKEN(TodoListKey=ORDER_KEY,SendAssetTokenDict=TodoListDict);
                            print("")
                        
                        if TodoListDict['POOL_BACK']['Status'] =="DONE" and len(TodoListDict['USER_LPS']['Mnemonic']) > 15:
                            await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
                            #清除密钥
                            TodoListDict['POOL_BACK']['Mnemonic']              =  str(TodoListDict['POOL_BACK']['Mnemonic'])[0:10]
                            TodoListDict['POOL_BACK']['Mnemonic_Tandem']       =  str(TodoListDict['POOL_BACK']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['USER_LPS']['Mnemonic']                =  str(TodoListDict['USER_LPS']['Mnemonic'])[0:10]
                            TodoListDict['USER_LPS']['Mnemonic_Tandem']         =  str(TodoListDict['USER_LPS']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                            TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                            TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                            TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                            #print(TodoListDict)
                            TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",ORDER_KEY,TODO_ORDER_64_TEXT)
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_DOING",ORDER_KEY,"DONE")
                            self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",TodoListDict['POOL_BACK']['CreatorUser'],0)
                            self.SWAT.解锁当前PAIR(CAT_ASSET_ID=TodoListDict['Pool']['CAT_ASSET_ID'],ORDER_KEY=ORDER_KEY)
                            
                                    
        #await self.用户质押COIN和TOKEN(TodoListDict)
        #await self.用户取消质押得到COIN和TOKEN(TodoListDict)
        #
        #await self.输入TOKEN_输出COIN(TodoListDict)
        await self.close_fullnode()
            
        
    async def 输入COIN_输出TOKEN(self,TodoListDict):
                
        #交易_输入COIN_输出TOKEN
        TodoListDict['SWAP_IN_COIN']                                    = {}
        TodoListDict['SWAP_IN_COIN']['CAT_ASSET_ID']                    = TodoListDict['Pool']['CAT_ASSET_ID']
        TodoListDict['SWAP_IN_COIN']['Mnemonic']                        = TodoListDict['Pool']['Mnemonic']
        TodoListDict['SWAP_IN_COIN']['Mnemonic_Tandem']                 = ""
        #需要设置用户需要输入的COIN值        
        TodoListDict['SWAP_IN_COIN']['Coin_SendToAmount']               = 20* 100000000
        TodoListDict['SWAP_IN_COIN']['Coin_SendToPuzzleHash']           = "" # POOL的COIN地址
        TodoListDict['SWAP_IN_COIN']['Coin_SendToMemos']                = ""
        #
        TodoListDict['SWAP_IN_COIN']['Token_SendToAmount']              = 0 # 提前计算POOL需要转账的TOKEN金额
        TodoListDict['SWAP_IN_COIN']['Token_SendToPuzzleHash']          = "" # 用户的TOKEN地址
        TodoListDict['SWAP_IN_COIN']['Token_SendToMemos']               = ""    
        #LP时间随机数
        TodoListDict['SWAP_IN_COIN']['miner_fee_mojo']                =  self.返回一个跟时间有关的随机数()
        TodoListDict['SWAP_IN_COIN']['Status']                        =  ""
        TodoListDict['SWAP_IN_COIN']['ChangeAmount']                  =  0
        TodoListDict['SWAP_IN_COIN']['ChangePuzzleHash']              =  ""
        
        TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
        TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
        self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
        
        #await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
        
        TODO_ORDER = self.r.hget("CHIVES_SWAP_V1_TEST","TEST_KEY")
        TODO_ORDER_64 = base64.b64decode(TODO_ORDER)
        if TODO_ORDER_64 is not None:
            TodoListDict = json.loads(TODO_ORDER_64)
            
            if TodoListDict['SWAP_IN_COIN']['Status'] =="" :
                await self.SWAT.交易_输入COIN_输出TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
            if TodoListDict['SWAP_IN_COIN']['Status'] =="Submitted" and TodoListDict['SWAP_IN_COIN']['ChangeAmount']>0 and TodoListDict['SWAP_IN_COIN']['ChangePuzzleHash'] != "" and TodoListDict['SWAP_IN_COIN']['ChangePuzzleHash'] is not None:
                await self.SWAT.Check_交易_输入COIN_输出TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
            
            if TodoListDict['SWAP_IN_COIN']['Status'] =="DONE" and len(TodoListDict['SWAP_IN_COIN']['Mnemonic']) > 15:
                #清除密钥
                print(TodoListDict['SWAP_IN_COIN'])
                TodoListDict['SWAP_IN_COIN']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                TodoListDict['SWAP_IN_COIN']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
    
    async def 输入TOKEN_输出COIN(self,TodoListDict):
        #交易_输出TOKEN_输入COIN
        TodoListDict['SWAP_IN_TOKEN']                                    = {}
        TodoListDict['SWAP_IN_TOKEN']['CAT_ASSET_ID']                    = TodoListDict['Pool']['CAT_ASSET_ID']
        TodoListDict['SWAP_IN_TOKEN']['Mnemonic']                        = ""
        TodoListDict['SWAP_IN_TOKEN']['Mnemonic_Tandem']                 = TodoListDict['Pool']['Mnemonic']
        #需要设置用户需要输入的TOKEN值        
        TodoListDict['SWAP_IN_TOKEN']['Coin_SendToAmount']               = 0 # 提前计算POOL收到的COIN金额金额
        TodoListDict['SWAP_IN_TOKEN']['Coin_SendToPuzzleHash']           = "" # POOL的COIN地址
        TodoListDict['SWAP_IN_TOKEN']['Coin_SendToMemos']                = ""
        #
        TodoListDict['SWAP_IN_TOKEN']['Token_SendToAmount']              = 60 * 1000 # 提前计算用户需要转账的TOKEN金额
        TodoListDict['SWAP_IN_TOKEN']['Token_SendToPuzzleHash']          = "" # 用户的TOKEN地址
        TodoListDict['SWAP_IN_TOKEN']['Token_SendToMemos']               = ""    
        #LP时间随机数
        TodoListDict['SWAP_IN_TOKEN']['miner_fee_mojo']                =  self.返回一个跟时间有关的随机数()
        TodoListDict['SWAP_IN_TOKEN']['Status']                        =  ""
        TodoListDict['SWAP_IN_TOKEN']['ChangeAmount']                  =  0
        TodoListDict['SWAP_IN_TOKEN']['ChangePuzzleHash']              =  ""
        
        TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
        TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
        #self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
        
        #await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
        
        TODO_ORDER = self.r.hget("CHIVES_SWAP_V1_TEST","TEST_KEY")
        TODO_ORDER_64 = base64.b64decode(TODO_ORDER)
        if TODO_ORDER_64 is not None:
            TodoListDict = json.loads(TODO_ORDER_64)
            #print(TodoListDict)
            if TodoListDict['SWAP_IN_TOKEN']['Status'] =="" :
                await self.SWAT.交易_输入TOKEN_输出COIN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
            if TodoListDict['SWAP_IN_TOKEN']['Status'] =="Submitted" and TodoListDict['SWAP_IN_TOKEN']['ChangeAmount']>0 and TodoListDict['SWAP_IN_TOKEN']['ChangePuzzleHash'] != "" and TodoListDict['SWAP_IN_TOKEN']['ChangePuzzleHash'] is not None:
                await self.SWAT.Check_交易_输入TOKEN_输出COIN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
            
            if TodoListDict['SWAP_IN_TOKEN']['Status'] =="DONE" and len(TodoListDict['SWAP_IN_TOKEN']['Mnemonic']) > 15:
                #清除密钥
                print(TodoListDict['SWAP_IN_TOKEN'])
                TodoListDict['SWAP_IN_TOKEN']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                TodoListDict['SWAP_IN_TOKEN']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
                
    async def 用户质押COIN和TOKEN(self,TodoListDict):
        初始发行价格                                        = 5
        
        #用户发送TOKEN到流动性池
        TodoListDict['User']                                = {}
        TodoListDict['User']['CAT_ASSET_ID']                = "3e3a7614a02d9714a21927ef99c7ef9bf8270e374dc6ecc48f2619cbc70c4ddc"
        TodoListDict['User']['Mnemonic']                    = ""
        TodoListDict['User']['Mnemonic_Tandem']             = ""
        #发送标准COIN 
        TodoListDict['User']['Coin_SendToAmount']           = 30*100000000
        TodoListDict['User']['Coin_SendToPuzzleHash']       = str(decode_puzzle_hash(TodoListDict['Pool']['ReceivedAddress']).hex())
        TodoListDict['User']['Coin_SendToMemos']            = ""
        #发送TOKEN
        TodoListDict['User']['Token_SendToAmount']          = int(初始发行价格 * TodoListDict['User']['Coin_SendToAmount'] * 1000 / 100000000 )
        TodoListDict['User']['Token_SendToPuzzleHash']      = str(decode_puzzle_hash(TodoListDict['Pool']['ReceivedAddress']).hex())
        TodoListDict['User']['Token_SendToMemos']           = ""        
        #时间随机数
        TodoListDict['User']['miner_fee_mojo']              =  self.返回一个跟时间有关的随机数()
        #执行结果
        TodoListDict['User']['Status']                      =  ""
        TodoListDict['User']['ChangeAmount']                =  0
        TodoListDict['User']['ChangePuzzleHash']            =  ""
        
        #流动性池所有权凭证发送TOKEN给用户
        #发送TOKEN
        TodoListDict['LP']['Token_SendToAmount']            = 0
        TodoListDict['LP']['Token_SendToPuzzleHash']        = ""
        TodoListDict['LP']['Token_SendToMemos']             = ""
        #发送标准COIN
        TodoListDict['LP']['Coin_SendToAmount']             = 0
        TodoListDict['LP']['Coin_SendToPuzzleHash']         = ""
        TodoListDict['LP']['Coin_SendToMemos']              = ""
        #时间随机数
        TodoListDict['LP']['miner_fee_mojo']                =  self.返回一个跟时间有关的随机数()
        #执行结果
        TodoListDict['LP']['Status']                        =  ""
        TodoListDict['LP']['ChangeAmount']                  =  0
        TodoListDict['LP']['ChangePuzzleHash']              =  ""
        
        TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
        TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
        self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
        #print(TodoListDict['LP'])
        #print("*****************************")
        
        TODO_ORDER = self.r.hget("CHIVES_SWAP_V1_TEST","TEST_KEY")
        TODO_ORDER_64 = base64.b64decode(TODO_ORDER)
        if TODO_ORDER_64 is not None:
            TodoListDict = json.loads(TODO_ORDER_64)
            #print(TodoListDict['User'])
            print(f"质押COIN:{TodoListDict['User']['Coin_SendToAmount']}")
            print(f"质押TOKEN:{TodoListDict['User']['Token_SendToAmount']}")
            print(f"TotalIssueAmount:{TodoListDict['LP']['TotalIssueAmount']}")
            if TodoListDict['User']['Status'] =="" :                
                await self.SWAT.向某一个账户转COIN和TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict,ActionValue="User");
                #如果转账成功,就需要立即计算应该获得的LPS,然后把数值保存起来
                计算需要增加的LPS的值VALUE = await self.SWAT.计算需要增加的LPS的值(SendAssetTokenDict=TodoListDict)
                TodoListDict['LP']['Token_SendToAmount']  = 计算需要增加的LPS的值VALUE
                TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
                print(f"获得LPS:{TodoListDict['LP']['Token_SendToAmount']}")
                
            if TodoListDict['User']['Status'] =="Submitted" and TodoListDict['User']['ChangeAmount']>0 and TodoListDict['User']['ChangePuzzleHash'] != "" and TodoListDict['User']['ChangePuzzleHash'] is not None:
                await self.SWAT.Check_向某一个账户转COIN和TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict,ActionValue="User");
            
            if TodoListDict['LP']['Status'] =="" and TodoListDict['User']['Status'] =="DONE":
                await self.SWAT.LP向用户发放质押凭证(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
            if TodoListDict['LP']['Status'] =="Submitted" and TodoListDict['LP']['ChangeAmount']>0 and TodoListDict['LP']['ChangePuzzleHash'] != "" and TodoListDict['LP']['ChangePuzzleHash'] is not None:
                await self.SWAT.Check_向某一个账户转COIN和TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict,ActionValue="LP");
            
            if TodoListDict['LP']['Status'] =="DONE" and len(TodoListDict['User']['Mnemonic']) > 15:
                #清除密钥
                TodoListDict['User']['Mnemonic']              =  str(TodoListDict['User']['Mnemonic'])[0:10]
                TodoListDict['User']['Mnemonic_Tandem']       =  str(TodoListDict['User']['Mnemonic_Tandem'])[0:10]
                TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                print(TodoListDict)
                TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
                
    async def 用户取消质押得到COIN和TOKEN(self,TodoListDict):
        
        #用户所持有的LPS
        TodoListDict['USER_LPS']                                    = {}
        TodoListDict['USER_LPS']['CAT_ASSET_ID']                    = TodoListDict['LP']['CAT_ASSET_ID']
        TodoListDict['USER_LPS']['Mnemonic']                        = ""
        TodoListDict['USER_LPS']['Mnemonic_Tandem']                 = TodoListDict['LP']['Mnemonic_Tandem'] #只用来扣除FEE
        #只用来扣除FEE        
        TodoListDict['USER_LPS']['Coin_SendToAmount']               = 0
        TodoListDict['USER_LPS']['Coin_SendToPuzzleHash']           = ""
        TodoListDict['USER_LPS']['Coin_SendToMemos']                = ""
        #返还TOKEN给LP
        TodoListDict['USER_LPS']['Token_SendToAmount']              = 0
        TodoListDict['USER_LPS']['Token_SendToPuzzleHash']          = ""
        TodoListDict['USER_LPS']['Token_SendToMemos']               = ""    
        #时间随机数
        TodoListDict['USER_LPS']['miner_fee_mojo']                =  self.返回一个跟时间有关的随机数()
        TodoListDict['USER_LPS']['Status']                        =  ""
        TodoListDict['USER_LPS']['ChangeAmount']                  =  0
        TodoListDict['USER_LPS']['ChangePuzzleHash']              =  ""
        
        #LP退还COIN和TOKEN给用户
        TodoListDict['POOL_BACK']                                    = {}
        TodoListDict['POOL_BACK']['CAT_ASSET_ID']                    = TodoListDict['Pool']['CAT_ASSET_ID']
        TodoListDict['POOL_BACK']['Mnemonic']                        = TodoListDict['Pool']['Mnemonic']
        TodoListDict['POOL_BACK']['Mnemonic_Tandem']                 = TodoListDict['Pool']['Mnemonic_Tandem'] #只用来扣除FEE
        #LP退还COIN        
        TodoListDict['POOL_BACK']['Coin_SendToAmount']               = 0
        TodoListDict['POOL_BACK']['Coin_SendToPuzzleHash']           = ""
        TodoListDict['POOL_BACK']['Coin_SendToMemos']                = ""
        #LP退还TOKEN
        TodoListDict['POOL_BACK']['Token_SendToAmount']              = 0
        TodoListDict['POOL_BACK']['Token_SendToPuzzleHash']          = ""
        TodoListDict['POOL_BACK']['Token_SendToMemos']               = ""    
        #LP时间随机数
        TodoListDict['POOL_BACK']['miner_fee_mojo']                =  self.返回一个跟时间有关的随机数()
        TodoListDict['POOL_BACK']['Status']                        =  ""
        TodoListDict['POOL_BACK']['ChangeAmount']                  =  0
        TodoListDict['POOL_BACK']['ChangePuzzleHash']              =  ""
        
        TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
        TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
        #self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
        
        #print(TodoListDict['POOL_BACK'])
        #检查余额
        #计算当前TOKEN价格V = await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
        #await self.SWAT.计算需要增加的LPS的值(SendAssetTokenDict=TodoListDict);
        #await self.SWAT.交易_输入COIN_输出TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
        #await self.SWAT.合并指定账户的COIN(SendAssetTokenDict=TodoListDict,ActionValue="Pool")
        #await self.SWAT.计算当前TOKEN价格(SendAssetTokenDict=TodoListDict);
        
        TODO_ORDER = self.r.hget("CHIVES_SWAP_V1_TEST","TEST_KEY")
        TODO_ORDER_64 = base64.b64decode(TODO_ORDER)
        if TODO_ORDER_64 is not None and 1:
            TodoListDict = json.loads(TODO_ORDER_64)
            #print(TodoListDict)
            if TodoListDict['USER_LPS']['Status'] =="" :
                await self.SWAT.用户取消质押时用户退还LPS并且记录数量(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
                print("")
            if TodoListDict['USER_LPS']['Status'] =="Submitted" and TodoListDict['USER_LPS']['ChangeAmount']>0 and TodoListDict['USER_LPS']['ChangePuzzleHash'] != "" and TodoListDict['USER_LPS']['ChangePuzzleHash'] is not None:
                await self.SWAT.Check_用户取消质押时用户退还LPS并且记录数量(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
                print("")
            
            if TodoListDict['POOL_BACK']['Status'] =="" and TodoListDict['USER_LPS']['Status'] =="DONE":
                await self.SWAT.用户取消质押时LP退还用户COIN和TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
                print("")
            if TodoListDict['POOL_BACK']['Status'] =="Submitted" and TodoListDict['POOL_BACK']['ChangeAmount']>=0 and TodoListDict['POOL_BACK']['ChangePuzzleHash'] != "" and TodoListDict['POOL_BACK']['ChangePuzzleHash'] is not None:
                await self.SWAT.Check_用户取消质押时LP退还用户COIN和TOKEN(TodoListKey="TEST_KEY",SendAssetTokenDict=TodoListDict);
                print("")
            
            if TodoListDict['POOL_BACK']['Status'] =="DONE" and len(TodoListDict['USER_LPS']['Mnemonic']) > 15:
                #清除密钥
                TodoListDict['POOL_BACK']['Mnemonic']              =  str(TodoListDict['POOL_BACK']['Mnemonic'])[0:10]
                TodoListDict['POOL_BACK']['Mnemonic_Tandem']       =  str(TodoListDict['POOL_BACK']['Mnemonic_Tandem'])[0:10]
                TodoListDict['USER_LPS']['Mnemonic']                =  str(TodoListDict['USER_LPS']['Mnemonic'])[0:10]
                TodoListDict['USER_LPS']['Mnemonic_Tandem']         =  str(TodoListDict['USER_LPS']['Mnemonic_Tandem'])[0:10]
                TodoListDict['LP']['Mnemonic']                =  str(TodoListDict['LP']['Mnemonic'])[0:10]
                TodoListDict['LP']['Mnemonic_Tandem']         =  str(TodoListDict['LP']['Mnemonic_Tandem'])[0:10]
                TodoListDict['Pool']['Mnemonic']              =  str(TodoListDict['Pool']['Mnemonic'])[0:10]
                TodoListDict['Pool']['Mnemonic_Tandem']       =  str(TodoListDict['Pool']['Mnemonic_Tandem'])[0:10]
                print(TodoListDict)
                TODO_ORDER_JSON_TEXT = json.dumps(TodoListDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_TEST","TEST_KEY",TODO_ORDER_64_TEXT)
            
if __name__ == "__main__":
    SwapInterface = SwapInterfaceV1(DEFAULT_CONSTANTS)
       
    while True:
        asyncio.run(SwapInterface.开始处理任务()) 
        print("休息30秒")
        time.sleep(10)
     
    
