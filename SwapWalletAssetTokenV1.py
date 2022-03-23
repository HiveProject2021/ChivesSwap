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
from SwapStandardCoinV1 import SwapStandardCoinV1


class SwapWalletAssetTokenV1:
    next_address = 0
    pubkey_num_lookup: Dict[bytes, uint32] = {}

    def __init__(self, constants: ConsensusConstants, sk: Optional[PrivateKey] = None):
        
        empty_bytes = bytearray(32)
        self.cc_info = CCInfo(empty_bytes, None, [])
        info_as_string = bytes(self.cc_info).hex()
        
        self.constants = constants
        self.current_balance = 0
        self.my_utxos: set = set()
        self.generator_lookups: Dict = {}
        self.puzzle_pk_cache: Dict = {}
        self.inner_puzzle_for_cc_puzhash = {}
        self.get_new_inner_hash = ""
        self.LINEAGE_PROOF_NAME_TO_DICT = {}
        self.get_keys = {}
        self.CHIVES_COIN_NAME_IS_USED_ARRAY = {}
        
        self.database_path              = "/home/ubuntu/.chives/standalone_wallet/db/blockchain_v1_mainnet.sqlite"
        
        pool = redis.ConnectionPool(host='localhost', port=6379, db=0)
        self.r = redis.Redis(connection_pool=pool)
    
    async def connect_fullnode(self):
        #连接主节点
        config = load_config(DEFAULT_ROOT_PATH, "config.yaml")
        self_hostname = config["self_hostname"]
        rpc_port = config["full_node"]["rpc_port"]
        self.client_node = await FullNodeRpcClient.create(self_hostname, uint16(rpc_port), DEFAULT_ROOT_PATH, config)
        
    async def close_fullnode(self):
        #关闭结点连接
        self.client_node.close()
        await self.client_node.await_closed()
         
    async def init_wallet(self,SendAssetTokenDict,ActionValue):
        print(f"ActionValue:{ActionValue}")
        self.mnemonic                   = SendAssetTokenDict[ActionValue]['Mnemonic']
        self.mnemonic_tandem            = SendAssetTokenDict[ActionValue]['Mnemonic_Tandem']
        self.CAT_ASSET_ID               = SendAssetTokenDict[ActionValue]['CAT_ASSET_ID']        
        self.miner_fee_mojo             = SendAssetTokenDict[ActionValue]['miner_fee_mojo']
        #print(SendAssetTokenDict[ActionValue])
        #print("---------------------------------------------")
    
    async def 得到指定钱包的COIN地址PH(self,mnemonic,AddressIndex):
        #初始化钱包
        #await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue1);
        #生成地址
        #print(f"ActionValue:{ActionValue1}")
        #print(f"mnemonic:{mnemonic}")
        #print(f"SendAssetTokenDict:{SendAssetTokenDict}")
        #print("")
        #entropy = bytes_from_mnemonic(mnemonic)
        seed = mnemonic_to_seed(mnemonic, "")
        private_key = AugSchemeMPL.key_gen(seed)
        fingerprint = private_key.get_g1().get_fingerprint()        
        
        private = master_sk_to_wallet_sk(private_key, AddressIndex)
        pubkey = private.get_g1()
        puzzle = puzzle_for_pk(bytes(pubkey))
        puzzle_hash = str(puzzle.get_tree_hash())
        
        return puzzle_hash;
    
    
    async def 合并指定账户的COIN(self,SendAssetTokenDict,ActionValue):
        得到Pool的COIN和TOKEN总和VALUE = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        目前已经质押的COIN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_COIN']
        目前已经质押的TOKEN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_TOKEN']
        fee = int(str(int(time.time()))[6:])
        if 目前已经质押的COIN的总和 > fee:
            SendToXchAmountArray = [int(目前已经质押的COIN的总和*1 - fee)] #这个值指的是实际发送的金额,不包括FEE
            POOL钱包的PH = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict[ActionValue]['Mnemonic'],AddressIndex=1)
            SendToXchPuzzleHashArray = [str(POOL钱包的PH)]
            #COIN 合并
            print(SendToXchAmountArray)
            SwapStandardCoinV1Object = SwapStandardCoinV1(DEFAULT_CONSTANTS)
            chives_tx,CHIVES_COIN_NAME_IS_USED_ARRAY,SelectedCoinList,Step1_ChangePuzzleHash,Step1_ChangeAmount = await SwapStandardCoinV1Object.get_standard_coin_signed_tx(SendToXchAmountArray, SendToXchPuzzleHashArray, fee=fee,mnemonic=SendAssetTokenDict[ActionValue]['Mnemonic'],database_path=self.database_path)
            if chives_tx is not None:
                #print(f"chives_tx:{chives_tx.name()}")
                try:
                    push_tx_cat = await self.client_node.push_tx(chives_tx)
                    print("push_tx_cat=====================================================")
                    print(push_tx_cat)
                    #{'status': 'SUCCESS', 'success': True}
                    if push_tx_cat['status']=="SUCCESS" and push_tx_cat['success']==True:
                        #作废已经花费过的COIN
                        for CHIVES_CAT_COIN_NAME_IS_USED_KEY in CHIVES_COIN_NAME_IS_USED_ARRAY:
                            self.r.hset("CHIVES_CAT_COIN_NAME_IS_USED",CHIVES_CAT_COIN_NAME_IS_USED_KEY,1)
                    #print(type(push_tx_cat))
                except Exception as e:
                    print(f"Exception {e}")
                finally:
                    print()
        else:
            print(f"目前已经质押的COIN的总和:{目前已经质押的COIN的总和} 太小")
            
    async def 交易_输入COIN_输出TOKEN(self,TodoListKey,SendAssetTokenDict):
        得到Pool的COIN和TOKEN总和VALUE = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue="Pool");
        目前已经质押的COIN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_COIN']
        目前已经质押的TOKEN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_TOKEN']
        
        POOL的TOKEN发送给用户PH = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['SWAP_IN_COIN']['Mnemonic_Tandem'],AddressIndex=1)
        SendAssetTokenDict['SWAP_IN_COIN']['Token_SendToPuzzleHash'] = POOL的TOKEN发送给用户PH
        USER的COIN发送给POOLPH  = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['Pool']['Mnemonic'],AddressIndex=1)
        SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToPuzzleHash'] = USER的COIN发送给POOLPH        
        #0.2%的COIN直接汇入SWAP账户
        #0.3%的COIN提前扣除,则会少置换0.3%的TOKEN,这些TOKEN还在POOL里面,用于提高LPS的价值
        用于计算TOKEN的COIN金额      = SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToAmount']
        print(f"用户输入的COINMOJO-未扣除:{用于计算TOKEN的COIN金额}")
        用于计算TOKEN的COIN金额      = int(用于计算TOKEN的COIN金额 * 0.998)
        用户可以收到的TOKEN数量      = 目前已经质押的TOKEN的总和 - ( 目前已经质押的COIN的总和*目前已经质押的TOKEN的总和/(用于计算TOKEN的COIN金额+目前已经质押的COIN的总和) )
        用户可以收到的TOKEN数量      = int(用户可以收到的TOKEN数量)
        print(f"用户输入的COINMOJO-已扣除0.2%:{用于计算TOKEN的COIN金额}")
        print(f"可以收到的TOKEN数量MOJO-计算:{用户可以收到的TOKEN数量}")
        当前成交的价格 = (用于计算TOKEN的COIN金额/100000000) / (用户可以收到的TOKEN数量/1000)
        print(f"当前成交的价格:{当前成交的价格}")
        
        写入PAIR状态 = {}
        写入PAIR状态['目前已经质押的COIN的总和'] = 目前已经质押的COIN的总和
        写入PAIR状态['目前已经质押的TOKEN的总和'] = 目前已经质押的TOKEN的总和
        写入PAIR状态['当前成交的价格'] = 当前成交的价格
        写入PAIR状态['更新时间'] = int(time.time())
        TODO_ORDER_JSON_TEXT = json.dumps(写入PAIR状态)
        TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
        self.r.hset("CHIVES_SWAP_PAIR_STATUS",SendAssetTokenDict['Pool']['CAT_ASSET_ID'],TODO_ORDER_64_TEXT)
        
        #扣除0.3%的POOL费用
        用户可以收到的TOKEN数量 = int(用户可以收到的TOKEN数量 * 0.997)
        #用户可以收到的TOKEN数量
        SendAssetTokenDict['SWAP_IN_COIN']['Token_SendToAmount']            = 用户可以收到的TOKEN数量        
        SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToPuzzleHash_Swap']    = str(decode_puzzle_hash("xcc15tx4trfcs6699rgzmvypy73trmpud74ra3muj899m0er7dxnrccsvly6p5").hex())
        SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToAmount_Swap']        = int(SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToAmount'] * 0.002)   
        
        SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToAmount']             = 用于计算TOKEN的COIN金额
        print(f"可以收到的COIN数量MOJO-SWAP手续费:{SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToAmount_Swap']}")
        print(f"可以收到的TOKEN数量MOJO-扣除0.3%以后:{SendAssetTokenDict['SWAP_IN_COIN']['Token_SendToAmount']}")
        
        SendAssetTokenDict['SWAP_IN_COIN']['Token_SendToAddress'] = encode_puzzle_hash(hexstr_to_bytes(SendAssetTokenDict['SWAP_IN_COIN']['Token_SendToPuzzleHash']),"xcc")
        SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToAddress'] = encode_puzzle_hash(hexstr_to_bytes(SendAssetTokenDict['SWAP_IN_COIN']['Coin_SendToPuzzleHash']),"xcc")
        
        print(SendAssetTokenDict['SWAP_IN_COIN'])        
        #向某一个账户转COIN和TOKEN
        await self.向某一个账户转COIN和TOKEN(TodoListKey=TodoListKey,SendAssetTokenDict=SendAssetTokenDict,ActionValue="SWAP_IN_COIN");
    
    async def Check_交易_输入COIN_输出TOKEN(self,TodoListKey,SendAssetTokenDict):
        ActionValue = "SWAP_IN_COIN"
        #初始化钱包
        await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        #再次在数据库里面查询,到到LINEAGE_PROOF的COIN的值.父币一定是花费过的币
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash = '"+SendAssetTokenDict[ActionValue]['ChangePuzzleHash']+"' ")
        rows = await cursor.fetchall()
        await cursor.close()
        await db_connection.close() 
        print(f"开始匹配地址和金额-{ActionValue}...... 交易_输入COIN_输出TOKEN");
        for row in rows:
            CoinAmount = uint64.from_bytes(row[7])
            if CoinAmount == uint64(SendAssetTokenDict[ActionValue]['ChangeAmount']):
                #已经匹配到指定的找零地址和指定的金额,表示汇款已经成功
                print(f"已经匹配到指定的找零地址和指定的金额,表示汇款已经成功:{CoinAmount} 交易_输入COIN_输出TOKEN");
                #标记转账进度状态 
                SendAssetTokenDict[ActionValue]['Status']              = "DONE"
                TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
        
    
    async def 交易_输入TOKEN_输出COIN(self,TodoListKey,SendAssetTokenDict):
        得到Pool的COIN和TOKEN总和VALUE = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue="Pool");
        目前已经质押的COIN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_COIN']
        目前已经质押的TOKEN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_TOKEN']
        
        USER的TOKEN发送给POOLPH = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['Pool']['Mnemonic'],AddressIndex=1)
        SendAssetTokenDict['SWAP_IN_TOKEN']['Token_SendToPuzzleHash'] = USER的TOKEN发送给POOLPH
        POOL的COIN发送给用户PH = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['SWAP_IN_TOKEN']['Mnemonic'],AddressIndex=1)
        SendAssetTokenDict['SWAP_IN_TOKEN']['Coin_SendToPuzzleHash'] = POOL的COIN发送给用户PH
        #0.3%的TOKEN提前扣除,则会少置换0.3%的COIN,这些COIN还在POOL里面,用于提高LPS的价值
        用户输入的TOKEN = SendAssetTokenDict['SWAP_IN_TOKEN']['Token_SendToAmount']
        print(f"用户输入的TOKEN-未扣除:{用户输入的TOKEN}")
        用户输入的TOKEN = int(用户输入的TOKEN * 0.997)
        用户可以收到的COIN数量 = 目前已经质押的COIN的总和 - ( 目前已经质押的COIN的总和*目前已经质押的TOKEN的总和/(用户输入的TOKEN+目前已经质押的TOKEN的总和) )
        用户可以收到的COIN数量 = int(用户可以收到的COIN数量)
        print(f"用户输入的TOKEN-扣除0.3%做为POOL的费用之后余额:{用户输入的TOKEN}")
        print(f"可以收到的COIN数量MOJO总和:{用户可以收到的COIN数量}")
        当前成交的价格 = (用户输入的TOKEN/1000) / (用户可以收到的COIN数量/100000000)
        print(f"当前成交的价格:{当前成交的价格}")
        
        写入PAIR状态 = {}
        写入PAIR状态['目前已经质押的COIN的总和'] = 目前已经质押的COIN的总和
        写入PAIR状态['目前已经质押的TOKEN的总和'] = 目前已经质押的TOKEN的总和
        写入PAIR状态['当前成交的价格'] = 1/当前成交的价格
        写入PAIR状态['更新时间'] = int(time.time())
        TODO_ORDER_JSON_TEXT = json.dumps(写入PAIR状态)
        TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
        self.r.hset("CHIVES_SWAP_PAIR_STATUS",SendAssetTokenDict['Pool']['CAT_ASSET_ID'],TODO_ORDER_64_TEXT)
        
        
        SendAssetTokenDict['SWAP_IN_TOKEN']['Coin_SendToPuzzleHash_Swap']   = str(decode_puzzle_hash("xcc15tx4trfcs6699rgzmvypy73trmpud74ra3muj899m0er7dxnrccsvly6p5").hex())
        SendAssetTokenDict['SWAP_IN_TOKEN']['Coin_SendToAmount_Swap']       = int(用户可以收到的COIN数量 * 0.002)
        
        #用户可以收到的COIN数量
        SendAssetTokenDict['SWAP_IN_TOKEN']['Coin_SendToAmount'] = int(用户可以收到的COIN数量 * 0.998)
        
        print(f"可以收到的COIN数量MOJO-SWAP:{SendAssetTokenDict['SWAP_IN_TOKEN']['Coin_SendToAmount_Swap']}")
        print(f"可以收到的COIN数量MOJO-用户:{SendAssetTokenDict['SWAP_IN_TOKEN']['Coin_SendToAmount']}")
        
        print(SendAssetTokenDict['SWAP_IN_TOKEN'])
        #交易_输入TOKEN_输出COIN
        await self.向某一个账户转COIN和TOKEN(TodoListKey=TodoListKey,SendAssetTokenDict=SendAssetTokenDict,ActionValue="SWAP_IN_TOKEN");
    
    async def Check_交易_输入TOKEN_输出COIN(self,TodoListKey,SendAssetTokenDict):
        ActionValue = "SWAP_IN_TOKEN"
        #初始化钱包
        await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        #再次在数据库里面查询,到到LINEAGE_PROOF的COIN的值.父币一定是花费过的币
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash = '"+SendAssetTokenDict[ActionValue]['ChangePuzzleHash']+"' ")
        rows = await cursor.fetchall()
        await cursor.close()
        await db_connection.close() 
        print(f"开始匹配地址和金额-{ActionValue}...... 交易_输出TOKEN_输入COIN");
        for row in rows:
            CoinAmount = uint64.from_bytes(row[7])
            if CoinAmount == uint64(SendAssetTokenDict[ActionValue]['ChangeAmount']):
                #已经匹配到指定的找零地址和指定的金额,表示汇款已经成功
                print(f"已经匹配到指定的找零地址和指定的金额,表示汇款已经成功:{CoinAmount} 交易_输出TOKEN_输入COIN");
                #标记转账进度状态 
                SendAssetTokenDict[ActionValue]['Status']              = "DONE"
                TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
    
    async def 计算当前TOKEN价格(self,SendAssetTokenDict):
        得到Pool的COIN和TOKEN总和VALUE = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue="Pool");
        目前已经质押的COIN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_COIN']
        目前已经质押的TOKEN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_TOKEN']
        if 目前已经质押的COIN的总和 > 0:
            当前成交的价格 = (目前已经质押的TOKEN的总和/1) / (目前已经质押的COIN的总和/100000)
            #print(f"NAME:{SendAssetTokenDict}")
            print(f"计算当前TOKEN价格:{SendAssetTokenDict['infor']['Pair']}")
            print(f"CAT_ASSET_ID:{SendAssetTokenDict['Pool']['CAT_ASSET_ID']}")
            print(f"当前POOL中COIN:{format(int(目前已经质押的COIN的总和/100000000),',')}")
            print(f"当前POOL中TOKEN:{format(int(目前已经质押的TOKEN的总和/1000),',')}")
            print(f"当前POOL乘积:{format(int(目前已经质押的TOKEN的总和/1) * int(目前已经质押的COIN的总和/100000),',')}")
            print(f"当前成交的价格:{当前成交的价格}")
            当前成交的价格 = (目前已经质押的COIN的总和/100000) / (目前已经质押的TOKEN的总和/1)
            print(f"当前成交的价格:{当前成交的价格}")
            
            写入PAIR状态 = {}
            写入PAIR状态['目前已经质押的COIN的总和'] = 目前已经质押的COIN的总和
            写入PAIR状态['目前已经质押的TOKEN的总和'] = 目前已经质押的TOKEN的总和
            写入PAIR状态['当前成交的价格'] = 当前成交的价格
            写入PAIR状态['更新时间'] = int(time.time())
            TODO_ORDER_JSON_TEXT = json.dumps(写入PAIR状态)
            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
            self.r.hset("CHIVES_SWAP_PAIR_STATUS",SendAssetTokenDict['Pool']['CAT_ASSET_ID'],TODO_ORDER_64_TEXT)
        else:
            写入PAIR状态 = {}
            写入PAIR状态['目前已经质押的COIN的总和'] = 0
            写入PAIR状态['目前已经质押的TOKEN的总和'] = 0
            写入PAIR状态['当前成交的价格'] = 0
            写入PAIR状态['更新时间'] = int(time.time())
            TODO_ORDER_JSON_TEXT = json.dumps(写入PAIR状态)
            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
            self.r.hset("CHIVES_SWAP_PAIR_STATUS",SendAssetTokenDict['Pool']['CAT_ASSET_ID'],TODO_ORDER_64_TEXT)
            
    def 锁定当前PAIR(self,CAT_ASSET_ID,ORDER_KEY):
        #得到当前PAIR状态V = self.r.hget("CHIVES_SWAP_PAIR_LOCK_STATUS",CAT_ASSET_ID)
        #if 得到当前PAIR状态V is not None:
        #    得到当前PAIR状态V = json.loads(得到当前PAIR状态V)
        #else:
        #    得到当前PAIR状态V = {}
        #得到当前PAIR状态V['ORDER_KEY'] = "DOING"
        #self.r.hset("CHIVES_SWAP_PAIR_LOCK_STATUS",CAT_ASSET_ID,json.dumps(写入PAIR状态).encode('ascii'))
        print(f"锁定当前PAIR:{ORDER_KEY}")
        self.r.hset("CHIVES_SWAP_PAIR_LOCK_STATUS",CAT_ASSET_ID,ORDER_KEY)
        
    def 解锁当前PAIR(self,CAT_ASSET_ID,ORDER_KEY):
        print(f"解锁当前PAIR:{ORDER_KEY}")
        self.r.hdel("CHIVES_SWAP_PAIR_LOCK_STATUS",CAT_ASSET_ID,"")
        
    def 当前PAIR状态是否锁定(self,CAT_ASSET_ID,ORDER_KEY):
        print(f"当前PAIR状态是否锁定:{ORDER_KEY}")
        得到当前PAIR状态V = self.r.hget("CHIVES_SWAP_PAIR_LOCK_STATUS",CAT_ASSET_ID)
        if 得到当前PAIR状态V is not None:
            if 得到当前PAIR状态V == ORDER_KEY:
                return False
            else:
                return True 
        else:
            return False       
            
    async def 用户取消质押时LPS转换为COIN和TOKEN(self,SendAssetTokenDict):
        得到已经发行的LPS的值VALUE = await self.得到已经发行的LPS的值(SendAssetTokenDict=SendAssetTokenDict);
        得到已经发行的LPS的值VALUE = int(得到已经发行的LPS的值VALUE)  
        
        得到用户已经持有的LPS = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue="USER_LPS");
        取消质押比例 = 1
        得到用户已经持有的LPS['CurrentAmount_TOKEN_RETURN'] = 得到用户已经持有的LPS['CurrentAmount_TOKEN'] * 取消质押比例
        
        得到Pool的COIN和TOKEN总和VALUE = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue="Pool");
        目前已经质押的COIN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_COIN']
        目前已经质押的TOKEN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_TOKEN']
        本次退还比例 = int(得到用户已经持有的LPS['CurrentAmount_TOKEN_RETURN'] * 10000 / 得到已经发行的LPS的值VALUE) / 100
        print("***************************************************************************")
        print(f"得到已经发行的LPS的值VALUE:{得到已经发行的LPS的值VALUE}")
        print(f"得到用户已经持有的LPS:{得到用户已经持有的LPS['CurrentAmount_TOKEN_RETURN']}")
        print(f"本次退还比例:{本次退还比例}%")
        print(f"取消质押比例:{取消质押比例}")
        print(f"目前已经质押的TOKEN的总和:{目前已经质押的TOKEN的总和}")
        
        COIN退还数量 = int(得到用户已经持有的LPS['CurrentAmount_TOKEN_RETURN'] / 得到已经发行的LPS的值VALUE * 目前已经质押的COIN的总和)
        TOKEN退还数量 = int(得到用户已经持有的LPS['CurrentAmount_TOKEN_RETURN']  / 得到已经发行的LPS的值VALUE * 目前已经质押的TOKEN的总和)
        print(f"COIN退还数量:{COIN退还数量}")
        print(f"TOKEN退还数量:{TOKEN退还数量}")
        
        return COIN退还数量,TOKEN退还数量,取消质押比例,得到用户已经持有的LPS;
    
    async def 用户取消质押时用户退还LPS并且记录数量(self,TodoListKey,SendAssetTokenDict):
        COIN退还数量,TOKEN退还数量,取消质押比例,得到用户已经持有的LPS = await self.用户取消质押时LPS转换为COIN和TOKEN(SendAssetTokenDict=SendAssetTokenDict);
        if COIN退还数量>0 and TOKEN退还数量>0:       
            SendAssetTokenDict['USER_LPS']['Token_SendToAmount'] = int(得到用户已经持有的LPS['CurrentAmount_TOKEN_RETURN'])
            SendAssetTokenDict['USER_LPS']['Token_SendToPuzzleHash'] = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['LP']['Mnemonic'],AddressIndex=1)
            
            USER钱包的PH = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['USER_LPS']['Mnemonic'],AddressIndex=1)
            #LP退还COIN
            SendAssetTokenDict['POOL_BACK']['Coin_SendToAmount']               = int(COIN退还数量)
            SendAssetTokenDict['POOL_BACK']['Coin_SendToPuzzleHash']           = str(USER钱包的PH)
            SendAssetTokenDict['POOL_BACK']['Coin_SendToMemos']                = ""
            #LP退还TOKEN
            SendAssetTokenDict['POOL_BACK']['Token_SendToAmount']              = int(TOKEN退还数量)
            SendAssetTokenDict['POOL_BACK']['Token_SendToPuzzleHash']          = str(USER钱包的PH)
            SendAssetTokenDict['POOL_BACK']['Token_SendToMemos']               = "" 
            #print(SendAssetTokenDict)
            #用户退还LPS并且记录数量
            await self.向某一个账户转COIN和TOKEN(TodoListKey=TodoListKey,SendAssetTokenDict=SendAssetTokenDict,ActionValue="USER_LPS");
        else:
            print(f"COIN退还数量 TOKEN退还数量 为 0")
            '''
            #用户LPS为0,作废订单
            SendAssetTokenDict['USER_LPS']['Status']                  = "FAIL"
            SendAssetTokenDict['POOL_BACK']['Status']                 = "FAIL"
            SendAssetTokenDict['POOL_BACK']['Mnemonic']               =  str(SendAssetTokenDict['POOL_BACK']['Mnemonic'])[0:10]
            SendAssetTokenDict['POOL_BACK']['Mnemonic_Tandem']        =  str(SendAssetTokenDict['POOL_BACK']['Mnemonic_Tandem'])[0:10]
            SendAssetTokenDict['USER_LPS']['Mnemonic']                =  str(SendAssetTokenDict['USER_LPS']['Mnemonic'])[0:10]
            SendAssetTokenDict['USER_LPS']['Mnemonic_Tandem']         =  str(SendAssetTokenDict['USER_LPS']['Mnemonic_Tandem'])[0:10]
            SendAssetTokenDict['LP']['Mnemonic']                =  str(SendAssetTokenDict['LP']['Mnemonic'])[0:10]
            SendAssetTokenDict['LP']['Mnemonic_Tandem']         =  str(SendAssetTokenDict['LP']['Mnemonic_Tandem'])[0:10]
            SendAssetTokenDict['Pool']['Mnemonic']              =  str(SendAssetTokenDict['Pool']['Mnemonic'])[0:10]
            SendAssetTokenDict['Pool']['Mnemonic_Tandem']       =  str(SendAssetTokenDict['Pool']['Mnemonic_Tandem'])[0:10]
            #print(SendAssetTokenDict)
            TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
            self.r.hset("CHIVES_SWAP_V1_CHIVES_DOING",TodoListKey,"DONE")
            self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",SendAssetTokenDict['POOL_BACK']['CreatorUser'],0)
            '''
            
    async def Check_用户取消质押时用户退还LPS并且记录数量(self,TodoListKey,SendAssetTokenDict):
        ActionValue = "USER_LPS"
        #初始化钱包
        await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        #再次在数据库里面查询,到到LINEAGE_PROOF的COIN的值.父币一定是花费过的币
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash = '"+SendAssetTokenDict[ActionValue]['ChangePuzzleHash']+"' ")
        rows = await cursor.fetchall()
        await cursor.close()
        await db_connection.close() 
        print(f"开始匹配地址和金额-{ActionValue}...... 用户取消质押时用户退还LPS并且记录数量:{SendAssetTokenDict[ActionValue]['Token_SendToAmount']}");
        for row in rows:
            CoinAmount = uint64.from_bytes(row[7])
            if CoinAmount == uint64(SendAssetTokenDict[ActionValue]['ChangeAmount']):
                #已经匹配到指定的找零地址和指定的金额,表示汇款已经成功
                print(f"已经匹配到指定的找零地址和指定的金额,表示汇款已经成功:{CoinAmount} 用户取消质押时用户退还LPS并且记录数量");
                #标记转账进度状态 
                SendAssetTokenDict[ActionValue]['Status']              = "DONE"
                TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
        
    async def 用户取消质押时LP退还用户COIN和TOKEN(self,TodoListKey,SendAssetTokenDict):
        #用户退还LPS并且记录数量 
        #需要扣除FEE,并且预留少部分金额,用于状态判断 同时需要找零1 Mojo
        ChangePuzzleHash = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['POOL_BACK']['Mnemonic'],AddressIndex=1)
        RandomNumberChange = int(str(int(time.time()))[6:])
        #重新设置参数
        SendAssetTokenDict['POOL_BACK']['Coin_SendToAmount'] = int(SendAssetTokenDict['POOL_BACK']['Coin_SendToAmount'] * 1) - int(SendAssetTokenDict['POOL_BACK']['miner_fee_mojo']) - int(RandomNumberChange)
        SendAssetTokenDict['POOL_BACK']['Token_SendToAmount'] = int(SendAssetTokenDict['POOL_BACK']['Token_SendToAmount'] * 1)
        SendAssetTokenDict['POOL_BACK']['ChangeAmount'] = RandomNumberChange
        SendAssetTokenDict['POOL_BACK']['ChangePuzzleHash'] = ChangePuzzleHash
        #SendAssetTokenDict['POOL_BACK']['Coin_SendToAmount'] = 5565646502 - SendAssetTokenDict['POOL_BACK']['miner_fee_mojo']
        #SendAssetTokenDict['POOL_BACK']['Token_SendToAmount'] = 1113151
        #print(SendAssetTokenDict['POOL_BACK'])
        await self.向某一个账户转COIN和TOKEN(TodoListKey=TodoListKey,SendAssetTokenDict=SendAssetTokenDict,ActionValue="POOL_BACK");

    async def Check_用户取消质押时LP退还用户COIN和TOKEN(self,TodoListKey,SendAssetTokenDict):
        ActionValue = "POOL_BACK"
        #初始化钱包
        await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        #再次在数据库里面查询,到到LINEAGE_PROOF的COIN的值.父币一定是花费过的币
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash = '"+SendAssetTokenDict[ActionValue]['ChangePuzzleHash']+"' ")
        rows = await cursor.fetchall()
        await cursor.close()
        await db_connection.close() 
        print(f"开始匹配地址和金额-{ActionValue}...... 用户取消质押时LP退还用户:{SendAssetTokenDict['POOL_BACK']['Coin_SendToAmount']} 和TOKEN:{SendAssetTokenDict['POOL_BACK']['Token_SendToAmount']}");
        for row in rows:
            CoinAmount = uint64.from_bytes(row[7])
            if CoinAmount == uint64(SendAssetTokenDict[ActionValue]['ChangeAmount']):
                #已经匹配到指定的找零地址和指定的金额,表示汇款已经成功
                print(f"已经匹配到指定的找零地址和指定的金额,表示汇款已经成功:{CoinAmount} 用户取消质押时LP退还用户COIN:{SendAssetTokenDict['POOL_BACK']['Coin_SendToAmount']} 和TOKEN:{SendAssetTokenDict['POOL_BACK']['Token_SendToAmount']}");
                #标记转账进度状态 
                SendAssetTokenDict[ActionValue]['Status']              = "DONE"
                TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
        
        
    async def 计算需要增加的LPS的值(self,SendAssetTokenDict):
        得到已经发行的LPS的值VALUE = await self.得到已经发行的LPS的值(SendAssetTokenDict=SendAssetTokenDict);
        得到已经发行的LPS的值VALUE = int(得到已经发行的LPS的值VALUE)
        print(f"得到已经发行的LPS的值VALUE:{得到已经发行的LPS的值VALUE}")
        if 得到已经发行的LPS的值VALUE == 0:        
            #math.sqrt(10000000000000/1000000*2000000000)/100000000000
            #存入10万XCC和200万的TOKEN,发行1000XCC的LP,初始占比0.01 最多存入1000万的XCC.
            #需要在初始化的时候除以6即可.可以扩大到一个亿的XCC
            #初始化流动性池,第一次存入: S0 = sqrt(X0*Y0)
            X0 = int(SendAssetTokenDict['User']['Coin_SendToAmount']);
            #X0的值是COIN的值,需要除以 1000000 ,不然LPS值太大,无法支付或是需要铸造一个超大的TOKEN,所以需要除以 1000000
            X0 = int(X0/1000000);
            Y0 = int(SendAssetTokenDict['User']['Token_SendToAmount']);
            S0 = int(math.sqrt(X0 * Y0))
            print(f"X0:{X0}")
            print(f"Y0:{Y0}")
            print(f"S0:{S0}")
            计算需要增加的LPS的值VALUE = S0
            return 计算需要增加的LPS的值VALUE;
        else:    
            得到Pool的COIN和TOKEN总和VALUE = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue="Pool");
            目前已经质押的COIN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_COIN']
            目前已经质押的TOKEN的总和 = 得到Pool的COIN和TOKEN总和VALUE['CurrentAmount_TOKEN']
            当前用户打算要质押的COIN = SendAssetTokenDict['User']['Coin_SendToAmount']
            当前用户打算要质押的TOKEN = SendAssetTokenDict['User']['Token_SendToAmount']
            print(f"目前已经质押的COIN的总和:{目前已经质押的COIN的总和}")
            print(f"目前已经质押的TOKEN的总和:{目前已经质押的TOKEN的总和}")
            print(f"当前用户打算要质押的COIN:{当前用户打算要质押的COIN}")
            print(f"当前用户打算要质押的TOKEN:{当前用户打算要质押的TOKEN}")
            if 目前已经质押的COIN的总和>0:
                print(f"COIN占比:{当前用户打算要质押的COIN/目前已经质押的COIN的总和}")
                print(f"TOKEN占比:{当前用户打算要质押的TOKEN/目前已经质押的TOKEN的总和}")
                COIN和TOKEN占比的最小值 = min(当前用户打算要质押的COIN/目前已经质押的COIN的总和,当前用户打算要质押的TOKEN/目前已经质押的TOKEN的总和)
                print(f"COIN和TOKEN占比的最小值:{COIN和TOKEN占比的最小值}")
                print(f"得到已经发行的LPS的值VALUE:{得到已经发行的LPS的值VALUE}")
                计算需要增加的LPS的值VALUE = int(得到已经发行的LPS的值VALUE * COIN和TOKEN占比的最小值)
                print(f"计算需要增加的LPS的值VALUE:{计算需要增加的LPS的值VALUE}")
                return 计算需要增加的LPS的值VALUE;
            else:   
                return 100
        
    async def 得到已经发行的LPS的值(self,SendAssetTokenDict):
        ActionValue = "LP"
        TotalIssueAmount = int(SendAssetTokenDict[ActionValue]['TotalIssueAmount'])
        #初始化钱包
        得到指定钱包账户的COIN和TOKEN总和VALUE = await self.得到指定钱包账户的COIN和TOKEN总和(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        CurrentAmount_TOKEN = 得到指定钱包账户的COIN和TOKEN总和VALUE['CurrentAmount_TOKEN']
        得到已经发行的LPS的值VALUE = TotalIssueAmount * 1000 - CurrentAmount_TOKEN;
        print(f"得到已经发行的LPS的值VALUE:{得到已经发行的LPS的值VALUE}")
        return 得到已经发行的LPS的值VALUE;
         
    async def 得到指定钱包账户的COIN和TOKEN总和(self,SendAssetTokenDict,ActionValue):
        #初始化钱包
        await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        #生成地址
        entropy = bytes_from_mnemonic(self.mnemonic)
        seed = mnemonic_to_seed(self.mnemonic, "")
        self.private_key = AugSchemeMPL.key_gen(seed)
        fingerprint = self.private_key.get_g1().get_fingerprint()        
        
        AddressNumber = 5
        #得到指定账户的地址-COIN-TOKEN
        AllPuzzleHashArrayCoin = []
        AllPuzzleHashArrayToken = []
        FirstAddressPuzzleHash1 = ""
        FirstAddressPuzzleHash2 = ""
        
        for i in range(0, AddressNumber):
            private = master_sk_to_wallet_sk(self.private_key, i)
            pubkey = private.get_g1()
            puzzle = puzzle_for_pk(bytes(pubkey))
            puzzle_hash = str(puzzle.get_tree_hash())
            AllPuzzleHashArrayCoin.append(puzzle_hash);            
            limitations_program_hash = hexstr_to_bytes(self.CAT_ASSET_ID)
            inner_puzzle = puzzle_for_pk(bytes(pubkey))
            cc_puzzle = construct_cc_puzzle(CC_MOD, limitations_program_hash, inner_puzzle)
            cc_puzzle_hash = cc_puzzle.get_tree_hash()
            AllPuzzleHashArrayToken.append(str(cc_puzzle_hash)) 
            if i ==0 :
                FirstAddressPuzzleHash1 = puzzle_hash
        
        for i in range(0, AddressNumber):
            private = master_sk_to_wallet_sk_unhardened(self.private_key, i)
            pubkey = private.get_g1()
            puzzle = puzzle_for_pk(bytes(pubkey))            
            puzzle_hash = str(puzzle.get_tree_hash())
            AllPuzzleHashArrayCoin.append(puzzle_hash);            
            limitations_program_hash = hexstr_to_bytes(self.CAT_ASSET_ID)
            inner_puzzle = puzzle_for_pk(bytes(pubkey))
            cc_puzzle = construct_cc_puzzle(CC_MOD, limitations_program_hash, inner_puzzle)
            cc_puzzle_hash = cc_puzzle.get_tree_hash()
            AllPuzzleHashArrayToken.append(str(cc_puzzle_hash))
            if i ==0 :
                FirstAddressPuzzleHash2 = puzzle_hash
            
        separator = "','"
        AllPuzzleHashArrayText = separator.join(AllPuzzleHashArrayCoin)
        AllPuzzleHashArrayText_COIN= "'"+AllPuzzleHashArrayText+"'"
        #print(f"AllPuzzleHashArrayText:{AllPuzzleHashArrayText}")
            
        separator = "','"
        AllPuzzleHashArrayText = separator.join(AllPuzzleHashArrayToken)
        AllPuzzleHashArrayText_TOKEN = "'"+AllPuzzleHashArrayText+"'"
        #print(f"AllPuzzleHashArrayText:{AllPuzzleHashArrayText}")
        
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        
        #查询未花费记录-COIN
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash in ("+AllPuzzleHashArrayText_COIN+")")
        rows = await cursor.fetchall()
        CurrentAmount_COIN = 0
        for row in rows:
            if int(row[3]) == 0:
                coin = Coin(bytes32(bytes.fromhex(row[6])), bytes32(bytes.fromhex(row[5])), uint64.from_bytes(row[7]))
                #查询该COIN是否被花费 
                if self.r.hget("CHIVES_CAT_COIN_NAME_IS_USED",str(coin.name())) is None:
                    CurrentAmount_COIN += uint64.from_bytes(row[7])
        #查询未花费记录-TOKEN
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash in ("+AllPuzzleHashArrayText_TOKEN+")")
        rows = await cursor.fetchall()
        CurrentAmount_TOKEN = 0
        for row in rows:
            if int(row[3]) == 0:
                coin = Coin(bytes32(bytes.fromhex(row[6])), bytes32(bytes.fromhex(row[5])), uint64.from_bytes(row[7]))
                #查询该COIN是否被花费 
                if self.r.hget("CHIVES_CAT_COIN_NAME_IS_USED",str(coin.name())) is None:
                    CurrentAmount_TOKEN += uint64.from_bytes(row[7])
        #关闭数据库连接        
        await cursor.close()
        await db_connection.close()
        #print(f"CurrentAmount_COIN:{float(CurrentAmount_COIN/100000000)}")
        #print(f"CurrentAmount_TOKEN:{float(CurrentAmount_TOKEN/1000)}")
        #print(f"当前TOKEN价格:{}")
        #print("当前TOKEN价格: %.4f XCC" % float(float(CurrentAmount_COIN/100000000)/float(CurrentAmount_TOKEN/1000)))
        
        #返回值
        RS = {}
        RS['CurrentAmount_COIN'] = CurrentAmount_COIN
        RS['CurrentAmount_TOKEN'] = CurrentAmount_TOKEN
        if CurrentAmount_TOKEN>0:
            RS['CurrentPrice_TOKEN'] = float(float(CurrentAmount_COIN/100000000)/float(CurrentAmount_TOKEN/1000))
        else:
            RS['CurrentPrice_TOKEN'] = 0
        RS['FirstAddressPuzzleHash1'] = FirstAddressPuzzleHash1
        RS['FirstAddressPuzzleHash2'] = FirstAddressPuzzleHash2
        return RS
    
    async def LP向用户发放质押凭证(self,TodoListKey,SendAssetTokenDict):
        #计算需要增加的LPS的值VALUE = await self.计算需要增加的LPS的值(SendAssetTokenDict=SendAssetTokenDict)
        #print(f"计算需要增加的LPS的值VALUE:{计算需要增加的LPS的值VALUE}")
        print(f"LP向用户发放质押凭证 发送TOKEN的地址 {SendAssetTokenDict['User']['Mnemonic_Tandem']}")
        得到指定钱包的COIN地址PUZZLEHASH = await self.得到指定钱包的COIN地址PH(mnemonic=SendAssetTokenDict['User']['Mnemonic_Tandem'],AddressIndex=1)
        SendAssetTokenDict['LP']['Coin_SendToPuzzleHash']   = 得到指定钱包的COIN地址PUZZLEHASH
        SendAssetTokenDict['LP']['Token_SendToPuzzleHash']  = 得到指定钱包的COIN地址PUZZLEHASH
        #SendAssetTokenDict['LP']['Token_SendToAmount']  = 计算需要增加的LPS的值VALUE
        await self.向某一个账户转COIN和TOKEN(TodoListKey=TodoListKey,SendAssetTokenDict=SendAssetTokenDict,ActionValue="LP");
        
    async def Check_向某一个账户转COIN和TOKEN(self,TodoListKey,SendAssetTokenDict,ActionValue):
        #初始化钱包
        await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        #再次在数据库里面查询,到到LINEAGE_PROOF的COIN的值.父币一定是花费过的币
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash = '"+SendAssetTokenDict[ActionValue]['ChangePuzzleHash']+"' ")
        rows = await cursor.fetchall()
        await cursor.close()
        await db_connection.close() 
        print(f"开始匹配地址和金额-{ActionValue}...... 向某一个账户转COIN:{SendAssetTokenDict[ActionValue]['Coin_SendToAmount']} 和TOKEN:{SendAssetTokenDict[ActionValue]['Token_SendToAmount']}");
        for row in rows:
            CoinAmount = uint64.from_bytes(row[7])
            if CoinAmount == uint64(SendAssetTokenDict[ActionValue]['ChangeAmount']):
                #已经匹配到指定的找零地址和指定的金额,表示汇款已经成功
                print(f"已经匹配到指定的找零地址和指定的金额,表示汇款已经成功:{CoinAmount}");
                #标记转账进度状态 
                SendAssetTokenDict[ActionValue]['Status']              = "DONE"
                TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
                TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
        
    
    async def 向某一个账户转COIN和TOKEN(self,TodoListKey,SendAssetTokenDict,ActionValue):
        #初始化钱包
        await self.init_wallet(SendAssetTokenDict=SendAssetTokenDict,ActionValue=ActionValue);
        #得到可用的COIN列表
        rows = await self.Get_Coinlist_AssetToken();
        #print(rows)
        #用户发送TOKEN到流动性池 
        SendToAmountArray = [int(SendAssetTokenDict[ActionValue]['Token_SendToAmount'])]
        SendToPuzzleHashArray = [hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Token_SendToPuzzleHash']))]
        SendToMemosArray = [str(SendAssetTokenDict[ActionValue]['Token_SendToMemos'])]
        
        fee = self.miner_fee_mojo
        
        ADDRESS_NUMBER = 0
        SEND_ADDRESS_KEY_CACHE = []
        
        fee = self.miner_fee_mojo
        SendToAmountTotal: int = sum([SendToAmountItem for SendToAmountItem in SendToAmountArray])
        
        #查询未花费记录
        # coin_name|confirmed_index|spent_index|spent|coinbase|puzzle_hash|coin_parent|amount|timestamp
        coinList = []
        CurrentCoinAmount = 0
        LINEAGE_PROOF_PARENT_PH = []
        CHIVES_CAT_COIN_NAME_IS_USED_ARRAY  = []
        for row in rows:
            if int(row[3]) == 0:
                coin = Coin(bytes32(bytes.fromhex(row[6])), bytes32(bytes.fromhex(row[5])), uint64.from_bytes(row[7]))
                #查询该COIN是否被花费 
                if self.r.hget("CHIVES_CAT_COIN_NAME_IS_USED",str(coin.name())) is None:
                    CurrentCoinAmount += uint64.from_bytes(row[7])
                    coinList.append(coin)
                    #需要缓存每一个币的父币值,去查询他们的父币信息 下一个SQL中去COIN_NAME过滤
                    LINEAGE_PROOF_PARENT_PH.append(row[6])
                    #标记该COIN已经被花费过,不能再次使用
                    CHIVES_CAT_COIN_NAME_IS_USED_ARRAY.append(str(coin.name()))
                    #Asset Token交易不需要考虑到矿工费用
                    if(CurrentCoinAmount>SendToAmountTotal):
                        break
        
        if len(coinList)==0:
            #print(f"没有任何可以使用的TOKEN记录.需要支出:{SendToAmountTotal},目前拥有:{CurrentCoinAmount}") 
            #print("")            
            #import os,sys
            #os._exit(0)
            return "FAIL","没有任何可以使用的TOKEN记录",SendToAmountTotal,CurrentCoinAmount
        if len(coinList)>500:
            print(f"错误信息: 选中ASSET的数量太多,会生成交易包体积太大,从而导致失败. 选中ASSET数量:{len(coinList)}")
            print()
            print()
            return "FAIL","没有任何可以使用的TOKEN记录",SendToAmountTotal,CurrentCoinAmount  
        print(f"选中ASSET数量:{len(coinList)}")
        
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        #再次在数据库里面查询,到到LINEAGE_PROOF的COIN的值.父币一定是花费过的币
        separator = "','"
        AllPuzzleHashArrayText = separator.join(LINEAGE_PROOF_PARENT_PH)
        AllPuzzleHashArrayText = "'"+AllPuzzleHashArrayText+"'"
        cursor = await db_connection.execute("SELECT * from coin_record WHERE coin_name in ("+AllPuzzleHashArrayText+")")
        rows = await cursor.fetchall()
        await cursor.close()
        await db_connection.close() 
        for row in rows:
            if int(row[3]) == 1:
                coin = Coin(bytes32(bytes.fromhex(row[6])), bytes32(bytes.fromhex(row[5])), uint64.from_bytes(row[7]))
                LINEAGE_SINGLE = {}
                LINEAGE_SINGLE['amount'] = uint64.from_bytes(row[7])
                temp_cat_puzzle_hash = row[5]
                if temp_cat_puzzle_hash not in self.inner_puzzle_for_cc_puzhash.keys():
                    #父币是其它人给我们发送过来的,不是属于我们自己,所以需要一个单独的写法来获得inner_puzzle
                    get_puzzle_and_solution = await self.client_node.get_puzzle_and_solution(coin.name(), height=int(row[2]))
                    matched, curried_args = match_cat_puzzle(get_puzzle_and_solution.puzzle_reveal)
                    if matched:        
                        mod_hash, genesis_coin_checker_hash, inner_puzzle = curried_args
                        ASSET_ID = str(genesis_coin_checker_hash)[2:]
                        inner_puzzle_hash = inner_puzzle.get_tree_hash()
                        #print(f"ASSET_ID: {ASSET_ID}")
                        #print(f"coin.name(): {coin.name()}")
                        #print(f"inner_puzzle_hash: {inner_puzzle_hash}")
                        #print(f"cat_puzzle_hash: {row[5]}")
                        LINEAGE_SINGLE['inner_puzzle_hash'] = inner_puzzle_hash
                    else:   
                        raise ValueError(f"coin.name(): {coin.name()} not get the inner_puzzle")
                else:
                    LINEAGE_SINGLE['inner_puzzle_hash'] = self.inner_puzzle_for_cc_puzhash[temp_cat_puzzle_hash].get_tree_hash()
                LINEAGE_SINGLE['parent_name'] = row[6]
                self.LINEAGE_PROOF_NAME_TO_DICT[str(row[0])] = LineageProof(hexstr_to_bytes(LINEAGE_SINGLE['parent_name']), LINEAGE_SINGLE['inner_puzzle_hash'], LINEAGE_SINGLE['amount'])
        #print("LINEAGE_PROOF_NAME_TO_DICT===============================")
        #print(self.LINEAGE_PROOF_NAME_TO_DICT)  
        
        
        
        #流动性池LP把用户质押的凭证发送给用户
        coinListLP = SendToAmountArrayLP     = SendToPuzzleHashArrayLP = SendToMemosArrayLP = []
        
        #用户发送XCH到流动性池    
        if "Coin_SendToAmount_Swap" in SendAssetTokenDict[ActionValue] and SendAssetTokenDict[ActionValue]['Coin_SendToAmount_Swap']>0 and "Coin_SendToPuzzleHash_Swap" in SendAssetTokenDict[ActionValue] and SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash_Swap'] is not None:
            SendToXchAmountArray         = [int(SendAssetTokenDict[ActionValue]['Coin_SendToAmount']),int(SendAssetTokenDict[ActionValue]['Coin_SendToAmount_Swap'])]
            SendToXchPuzzleHashArray     = [str(SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash']),str(SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash_Swap'])]
        else:
            SendToXchAmountArray         = [int(SendAssetTokenDict[ActionValue]['Coin_SendToAmount'])]
            SendToXchPuzzleHashArray     = [str(SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash'])]
        
        #coinList里面是一个数组,里面包含有的COIN对像. 这个函数可以传入多个COIN,可以实现多个输入,对应两个输出的结构.
        generate_signed_transaction_cat,Step1_ChangePuzzleHash,Step1_ChangeAmount = await self.generate_signed_transaction_cat(
            amounts=SendToAmountArray,
            puzzle_hashes=SendToPuzzleHashArray,
            fee=fee,
            coins=coinList,
            memos=SendToMemosArray,
            amountsLP=SendToAmountArrayLP,
            puzzle_hashesLP=SendToPuzzleHashArrayLP,
            coinsLP=coinListLP,
            memosLP=SendToMemosArrayLP,
            SendToXchAmountArray=SendToXchAmountArray,
            SendToXchPuzzleHashArray=SendToXchPuzzleHashArray,
        )
        
        #提交交易记录到区块链网络
        if generate_signed_transaction_cat is not None:
            print(f"generate_signed_transaction_cat:{generate_signed_transaction_cat.name()}")
            try:
                push_tx_cat = await self.client_node.push_tx(generate_signed_transaction_cat)
                print("push_tx_cat=====================================================")
                print(push_tx_cat)
                #{'status': 'SUCCESS', 'success': True}
                if push_tx_cat['status']=="SUCCESS" and push_tx_cat['success']==True:
                    #标记转账进度状态 
                    SendAssetTokenDict[ActionValue]['Status']              = "Submitted" #
                    SendAssetTokenDict[ActionValue]['ChangeAmount']        = int(Step1_ChangeAmount)
                    SendAssetTokenDict[ActionValue]['ChangePuzzleHash']    = str(Step1_ChangePuzzleHash)
                    TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
                    TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
                    self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
                    #print(SendAssetTokenDict[ActionValue])
                    #作废已经花费过的COIN
                    for CHIVES_CAT_COIN_NAME_IS_USED_KEY in CHIVES_CAT_COIN_NAME_IS_USED_ARRAY:
                        self.r.hset("CHIVES_CAT_COIN_NAME_IS_USED",CHIVES_CAT_COIN_NAME_IS_USED_KEY,1)
                    for CHIVES_CAT_COIN_NAME_IS_USED_KEY in self.CHIVES_COIN_NAME_IS_USED_ARRAY:
                        self.r.hset("CHIVES_CAT_COIN_NAME_IS_USED",CHIVES_CAT_COIN_NAME_IS_USED_KEY,1)
                    #操作日志    
                    
                    if ActionValue == "SWAP_IN_COIN":
                        COIN_KEY_NAME = str.upper(SendAssetTokenDict[ActionValue]['CHIVES_SWAP_PAIR_SELECTED'])
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_CHIVES"
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.loads(WalletRecords)
                            WalletRecordsLen = len(WalletRecords)
                        else:
                            WalletRecords = {}
                            WalletRecordsLen = 0
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----OUT----"+str(ActionValue)+"----"+str(SendAssetTokenDict[ActionValue]['Coin_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'],phpserialize.dumps(WalletRecords))
                        #print("-----------------------------")
                        #print(SendAssetTokenDict[ActionValue])
                        #print(WalletRecords)
                        print("COIN OUT 记录创建成功---------------------")
                        
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_"+COIN_KEY_NAME
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.dumps([])
                        WalletRecords   = phpserialize.loads(WalletRecords)
                        WalletRecordsLen = len(WalletRecords)
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----IN----"+str(ActionValue)+"----"+str(SendAssetTokenDict[ActionValue]['Token_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Token_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'],phpserialize.dumps(WalletRecords))
                        #print(WalletRecordKey)
                        print("TOKEN IN 记录创建成功---------------------")
                            
                    if ActionValue == "SWAP_IN_TOKEN":
                        COIN_KEY_NAME = str.upper(SendAssetTokenDict[ActionValue]['CHIVES_SWAP_PAIR_SELECTED'])
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_"+COIN_KEY_NAME
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.loads(WalletRecords)
                            WalletRecordsLen = len(WalletRecords)
                        else:
                            WalletRecords = {}
                            WalletRecordsLen = 0
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----OUT----"+str(ActionValue)+"----"+str(SendAssetTokenDict[ActionValue]['Token_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'],phpserialize.dumps(WalletRecords))
                        print(WalletRecordKey)
                        print("COIN OUT 记录创建成功---------------------")
                            
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_CHIVES"
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.loads(WalletRecords)
                            WalletRecordsLen = len(WalletRecords)
                        else:
                            WalletRecords = {}
                            WalletRecordsLen = 0
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----IN----"+str(ActionValue)+"----"+str(SendAssetTokenDict[ActionValue]['Coin_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Token_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'],phpserialize.dumps(WalletRecords))
                        print(WalletRecordKey)
                        print("TOKEN IN 记录创建成功---------------------")
                    
                    if ActionValue == "User":
                        COIN_KEY_NAME = str.upper(SendAssetTokenDict[ActionValue]['CHIVES_SWAP_PAIR_SELECTED'])
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_"+COIN_KEY_NAME
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.loads(WalletRecords)
                            WalletRecordsLen = len(WalletRecords)
                        else:
                            WalletRecords = {}
                            WalletRecordsLen = 0
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----OUT----AddPoolLiquidity----"+str(SendAssetTokenDict[ActionValue]['Token_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'],phpserialize.dumps(WalletRecords))
                        print(WalletRecordKey)
                        print("COIN OUT 记录创建成功---------------------")
                            
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_CHIVES"
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.loads(WalletRecords)
                            WalletRecordsLen = len(WalletRecords)
                        else:
                            WalletRecords = {}
                            WalletRecordsLen = 0
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----OUT----AddPoolLiquidity----"+str(SendAssetTokenDict[ActionValue]['Coin_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Token_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'],phpserialize.dumps(WalletRecords))
                        print(WalletRecordKey)
                        print("TOKEN OUT 记录创建成功---------------------")
                    
                    if ActionValue == "POOL_BACK":
                        COIN_KEY_NAME = str.upper(SendAssetTokenDict[ActionValue]['CHIVES_SWAP_PAIR_SELECTED'])
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_"+COIN_KEY_NAME
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.loads(WalletRecords)
                            WalletRecordsLen = len(WalletRecords)
                        else:
                            WalletRecords = {}
                            WalletRecordsLen = 0
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----IN----CancelPoolLiquidity----"+str(SendAssetTokenDict[ActionValue]['Token_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Coin_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyToken'],phpserialize.dumps(WalletRecords))
                        print(WalletRecordKey)
                        print("COIN IN 记录创建成功---------------------")
                            
                        WalletRecordKey = "CHIVES_WALLET_TX_USER_CHIVES"
                        WalletRecords   = self.r.hget(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'])
                        if WalletRecords is not None:
                            WalletRecords   = phpserialize.loads(WalletRecords)
                            WalletRecordsLen = len(WalletRecords)
                        else:
                            WalletRecords = {}
                            WalletRecordsLen = 0
                        WalletRecord    = str(TodoListKey.decode('utf-8'))+"----IN----CancelPoolLiquidity----"+str(SendAssetTokenDict[ActionValue]['Coin_SendToAmount'])+"----"+encode_puzzle_hash(hexstr_to_bytes(str(SendAssetTokenDict[ActionValue]['Token_SendToPuzzleHash'])),"xcc")+"----"+str(SendAssetTokenDict[ActionValue]['CreatorTime'])+"----"+str(generate_signed_transaction_cat.name())
                        WalletRecords[WalletRecordsLen] = WalletRecord
                        self.r.hset(WalletRecordKey,SendAssetTokenDict[ActionValue]['WalletRecordkeyCoin'],phpserialize.dumps(WalletRecords))
                        print(WalletRecordKey)
                        print("TOKEN IN 记录创建成功---------------------")                    
                    
                    return True
                    
                else:
                    print("执行失败的结果:")
                    print(push_tx_cat)
                    
            except Exception as e:
                print(f"Exception {e}")
            finally:
                print()
        
        elif ActionValue == "SWAP_IN_COIN" or ActionValue == "SWAP_IN_TOKEN" or ActionValue == "User" or ActionValue == "USER_LPS":
            #失败,需要标记为FAIL
            SendAssetTokenDict[ActionValue]['Status']                  = "FAIL"
            if "POOL_BACK" in SendAssetTokenDict and "Mnemonic" in SendAssetTokenDict['POOL_BACK']:
                SendAssetTokenDict['POOL_BACK']['Mnemonic']               =  str(SendAssetTokenDict['POOL_BACK']['Mnemonic'])[0:10]
                SendAssetTokenDict['POOL_BACK']['Mnemonic_Tandem']        =  str(SendAssetTokenDict['POOL_BACK']['Mnemonic_Tandem'])[0:10]
                self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",SendAssetTokenDict['POOL_BACK']['CreatorUser'],0)
            if "USER_LPS" in SendAssetTokenDict and "Mnemonic" in SendAssetTokenDict['USER_LPS']:
                SendAssetTokenDict['USER_LPS']['Mnemonic']                =  str(SendAssetTokenDict['USER_LPS']['Mnemonic'])[0:10]
                SendAssetTokenDict['USER_LPS']['Mnemonic_Tandem']         =  str(SendAssetTokenDict['USER_LPS']['Mnemonic_Tandem'])[0:10]
            if "LP" in SendAssetTokenDict and "Mnemonic" in SendAssetTokenDict['LP']:
                SendAssetTokenDict['LP']['Mnemonic']                =  str(SendAssetTokenDict['LP']['Mnemonic'])[0:10]
                SendAssetTokenDict['LP']['Mnemonic_Tandem']         =  str(SendAssetTokenDict['LP']['Mnemonic_Tandem'])[0:10]
            if "Pool" in SendAssetTokenDict and "Mnemonic" in SendAssetTokenDict['Pool']:
                SendAssetTokenDict['Pool']['Mnemonic']              =  str(SendAssetTokenDict['Pool']['Mnemonic'])[0:10]
                SendAssetTokenDict['Pool']['Mnemonic_Tandem']       =  str(SendAssetTokenDict['Pool']['Mnemonic_Tandem'])[0:10]
            if "User" in SendAssetTokenDict and "Mnemonic" in SendAssetTokenDict['User']:
                SendAssetTokenDict['User']['Mnemonic']              =  str(SendAssetTokenDict['Pool']['Mnemonic'])[0:10]
                SendAssetTokenDict['User']['Mnemonic_Tandem']       =  str(SendAssetTokenDict['Pool']['Mnemonic_Tandem'])[0:10]
                self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",SendAssetTokenDict['User']['CreatorUser'],0)
            if "SWAP_IN_COIN" in SendAssetTokenDict:
                self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",SendAssetTokenDict['SWAP_IN_COIN']['CreatorUser'],0)
            if "SWAP_IN_TOKEN" in SendAssetTokenDict:
                self.r.hset("CHIVES_SWAP_V1_CHIVES_USER_LOCK",SendAssetTokenDict['SWAP_IN_TOKEN']['CreatorUser'],0)
            #print(SendAssetTokenDict)
            TODO_ORDER_JSON_TEXT = json.dumps(SendAssetTokenDict)
            TODO_ORDER_64_TEXT = base64.b64encode(TODO_ORDER_JSON_TEXT.encode('ascii'))
            self.r.hset("CHIVES_SWAP_V1_CHIVES_TX",TodoListKey,TODO_ORDER_64_TEXT)
            self.r.hset("CHIVES_SWAP_V1_CHIVES_DOING",TodoListKey,"DONE")
        else:    
            print("LP发送用户TOKEN,不能做失败处理,是属于第二步操作.")
        
    async def Get_Coinlist_AssetToken(self,AddressNumber:int=5):
        print(f"self.CAT_ASSET_ID:{self.CAT_ASSET_ID}")
        self.limitations_program_hash   = hexstr_to_bytes(self.CAT_ASSET_ID)
        entropy = bytes_from_mnemonic(self.mnemonic)
        seed = mnemonic_to_seed(self.mnemonic, "")
        self.private_key = AugSchemeMPL.key_gen(seed)
        fingerprint = self.private_key.get_g1().get_fingerprint()
        
        #得到指定账户的地址.
        AllPuzzleHashArray = []
        for i in range(0, AddressNumber):
            private = master_sk_to_wallet_sk(self.private_key, i)
            pubkey = private.get_g1()
            puzzle = puzzle_for_pk(bytes(pubkey))
            puzzle_hash = str(puzzle.get_tree_hash())
            #AllPuzzleHashArray.append(puzzle_hash);            
            limitations_program_hash = hexstr_to_bytes(self.CAT_ASSET_ID)
            inner_puzzle = puzzle_for_pk(bytes(pubkey))
            cc_puzzle = construct_cc_puzzle(CC_MOD, limitations_program_hash, inner_puzzle)
            cc_puzzle_hash = cc_puzzle.get_tree_hash()
            AllPuzzleHashArray.append(str(cc_puzzle_hash))
            #把CAT_PH转换为INNER_PH
            self.inner_puzzle_for_cc_puzhash[str(cc_puzzle_hash)] = inner_puzzle
            #缓存找零地址
            if i==0:
                self.FirstAddressPuzzleHash = str(puzzle_hash)
                self.get_new_inner_hash = puzzle_hash
                self.get_new_cc_puzzle_hash = str(cc_puzzle_hash)
            #缓存公钥和私钥
            self.get_keys[puzzle_hash] = {'pubkey':pubkey,'private':private}           
        
        for i in range(0, AddressNumber):
            private = master_sk_to_wallet_sk_unhardened(self.private_key, i)
            pubkey = private.get_g1()
            puzzle = puzzle_for_pk(bytes(pubkey))            
            puzzle_hash = str(puzzle.get_tree_hash())
            #AllPuzzleHashArray.append(puzzle_hash);            
            limitations_program_hash = hexstr_to_bytes(self.CAT_ASSET_ID)
            inner_puzzle = puzzle_for_pk(bytes(pubkey))
            cc_puzzle = construct_cc_puzzle(CC_MOD, limitations_program_hash, inner_puzzle)
            cc_puzzle_hash = cc_puzzle.get_tree_hash()
            AllPuzzleHashArray.append(str(cc_puzzle_hash))
            #把CAT_PH转换为INNER_PH
            self.inner_puzzle_for_cc_puzhash[str(cc_puzzle_hash)] = inner_puzzle
            if i==0:
                self.get_new_inner_hash = puzzle_hash
                self.get_new_cc_puzzle_hash = str(cc_puzzle_hash)
            #缓存公钥和私钥
            self.get_keys[puzzle_hash] = {'pubkey':pubkey,'private':private}
            
        separator = "','"
        AllPuzzleHashArrayText = separator.join(AllPuzzleHashArray)
        AllPuzzleHashArrayText = "'"+AllPuzzleHashArrayText+"'"
        #print(f"AllPuzzleHashArrayText:{AllPuzzleHashArrayText}")
        
        #连接数据库
        root_path = DEFAULT_ROOT_PATH
        config = load_config(root_path, "config.yaml")
        selected = config["selected_network"]
        prefix = config["network_overrides"]["config"][selected]["address_prefix"]
        log = logging.Logger
        db_connection = await aiosqlite.connect(self.database_path)
        
        #返回AssetToken的所有记录
        # coin_name|confirmed_index|spent_index|spent|coinbase|puzzle_hash|coin_parent|amount|timestamp
        cursor = await db_connection.execute("SELECT * from coin_record WHERE puzzle_hash in ("+AllPuzzleHashArrayText+")")
        rows = await cursor.fetchall()
        await cursor.close()
        await db_connection.close()
        
        return rows;
    
    async def generate_signed_transaction_cat(
        self,
        amounts: List[uint64],
        puzzle_hashes: List[bytes32],
        fee: uint64 = uint64(0),
        coins: Set[Coin] = None,
        memos: Optional[List[List[bytes]]] = None,
        amountsLP: List[uint64] = None,
        puzzle_hashesLP: List[bytes32] = None,
        coinsLP: Set[Coin] = None,
        memosLP: Optional[List[List[bytes]]] = None,
        SendToXchAmountArray: List[uint64] = [0],
        SendToXchPuzzleHashArray: List[bytes32] = None,
    ) -> List[SpendBundle]:
        if memos is None:
            memos = [[] for _ in range(len(puzzle_hashes))]

        if not (len(memos) == len(puzzle_hashes) == len(amounts)):
            raise ValueError("Memos, puzzle_hashes, and amounts must have the same length")
        
        payments = []
        for amount, puzhash, memo_list in zip(amounts, puzzle_hashes, memos):
            memos_with_hint = [puzhash]
            memos_with_hint.extend(memo_list)
            payments.append(Payment(puzhash, amount, memos_with_hint))
        
        #LP
        if memosLP is None:
            memosLP = [[] for _ in range(len(puzzle_hashesLP))]

        if not (len(memosLP) == len(puzzle_hashesLP) == len(amountsLP)):
            raise ValueError("LP Memos, puzzle_hashes, and amounts must have the same length")
        
        paymentsLP = []
        for amount, puzhash, memo_list in zip(amountsLP, puzzle_hashesLP, memosLP):
            memos_with_hint = [puzhash]
            memos_with_hint.extend(memo_list)
            paymentsLP.append(Payment(puzhash, amount, memos_with_hint))
            
        unsigned_spend_bundle, chives_tx, Step1_ChangePuzzleHash, Step1_ChangeAmount = await self.generate_unsigned_spendbundle_cat(payments, fee, coins=coins, paymentsLP=paymentsLP, coinsLP=coinsLP, SendToXchAmountArray=SendToXchAmountArray, SendToXchPuzzleHashArray=SendToXchPuzzleHashArray)
        if chives_tx is None:
            return (None,None,None)
            
        #AssetToken 签名
        spend_bundle = await self.sign_tx_cat(unsigned_spend_bundle)

        return spend_bundle,Step1_ChangePuzzleHash,Step1_ChangeAmount
    
    async def create_tandem_xch_tx(
        self,
        fee: uint64,
        amount_to_claim: uint64,
        announcement_to_assert: Optional[Announcement] = None,
        SendToXchAmountArray: List[uint64] = [0],
        SendToXchPuzzleHashArray: List[bytes32] = None,
    ) -> Tuple[TransactionRecord, Optional[Announcement]]:
        """
        This function creates a non-CAT transaction to pay fees, contribute funds for issuance, and absorb melt value.
        It is meant to be called in `generate_unsigned_spendbundle` and as such should be called under the
        wallet_state_manager lock
        """
        announcement = None
        if fee > amount_to_claim:
            # 在原来TOKEN交易的基础上面,附加一个标准COIN的交易
            print("在原来TOKEN交易的基础上面,附加一个标准COIN的交易-----------------")
            SwapStandardCoinV1Object = SwapStandardCoinV1(DEFAULT_CONSTANTS)
            chives_tx,CHIVES_COIN_NAME_IS_USED_ARRAY,SelectedCoinList,Step1_ChangePuzzleHash,Step1_ChangeAmount = await SwapStandardCoinV1Object.get_standard_coin_signed_tx(SendToXchAmountArray, SendToXchPuzzleHashArray, fee=fee,mnemonic=self.mnemonic_tandem,database_path=self.database_path)     
            if chives_tx is None:
                return (None,None,None,None)
            print(f"create_tandem_xch_tx chives_tx:{chives_tx.name()} Step1_ChangePuzzleHash:{Step1_ChangePuzzleHash} Step1_ChangeAmount:{Step1_ChangeAmount}")
            self.CHIVES_COIN_NAME_IS_USED_ARRAY = CHIVES_COIN_NAME_IS_USED_ARRAY;
            #print(SelectedCoinList)
            #print("------------------------------------------------------------------")
            #继续正常流程
            origin_id = list(SelectedCoinList)[0].name()
            assert chives_tx.coin_spends is not None
            message = None
            for spend in chives_tx.coin_spends:
                if spend.coin.name() == origin_id:
                    conditions = spend.puzzle_reveal.to_program().run(spend.solution.to_program()).as_python()
                    for condition in conditions:
                        if condition[0] == ConditionOpcode.CREATE_COIN_ANNOUNCEMENT:
                            message = condition[1]

            assert message is not None
            announcement = Announcement(origin_id, message)
        else:
            # 暂时没有测试这一块代码
            '''
            chives_coins = await self.standard_wallet.select_coins(fee)
            selected_amount: int = sum([c.amount for c in chives_coins])
            chives_tx = await self.standard_wallet.generate_signed_transaction(
                uint64(selected_amount + amount_to_claim - fee),
                (await self.standard_wallet.get_new_puzzlehash()),
                coins=chives_coins,
                negative_change_allowed=True,
                announcements_to_consume=set([announcement_to_assert]) if announcement_to_assert is not None else None,
            )
            assert chives_tx.spend_bundle is not None
            '''
        return chives_tx, announcement,Step1_ChangePuzzleHash,Step1_ChangeAmount
        
    async def generate_unsigned_spendbundle_cat(
        self,
        payments: List[Payment],
        fee: uint64 = uint64(0),
        cat_discrepancy: Optional[Tuple[int, Program]] = None,  # (extra_delta, limitations_solution)
        coins: Set[Coin] = None,
        paymentsLP: List[Payment] = None,
        coinsLP: Set[Coin] = None,
        SendToXchAmountArray: List[uint64] = [0],
        SendToXchPuzzleHashArray: List[bytes32] = None,
    ) -> Tuple[SpendBundle, Optional[TransactionRecord]]:
        if cat_discrepancy is not None:
            extra_delta, limitations_solution = cat_discrepancy
        else:
            extra_delta, limitations_solution = 0, Program.to([])
        payment_amount: int = sum([p.amount for p in payments])
        starting_amount: int = payment_amount - extra_delta

        if coins is None:
            cat_coins = await self.select_coins(uint64(starting_amount))
        else:
            cat_coins = coins

        selected_cat_amount: int = sum([c.amount for c in cat_coins])
        
        if selected_cat_amount >= starting_amount:
            print(f"选中TOKEN汇出:{selected_cat_amount}")
            print(f"实际汇出TOKEN:{starting_amount}")
        if selected_cat_amount < starting_amount:
            print(f"TOKEN 余额不足 需要支付TOKEN:{starting_amount} 已经选中TOKEN:{selected_cat_amount} 首地址PZ: {self.FirstAddressPuzzleHash} self.CAT_ASSET_ID:{self.CAT_ASSET_ID}")
            print()
            print()
            return (None,None,None,None)
        
        fee = int(fee)
        # Figure out if we need to absorb/melt some XCH as part of this
        regular_chives_to_claim: int = 0
        if payment_amount > starting_amount:
            fee = uint64(fee + payment_amount - starting_amount)
        elif payment_amount < starting_amount:
            regular_chives_to_claim = payment_amount

        need_chives_transaction = False
        need_chives_transaction = (fee > 0 or regular_chives_to_claim > 0) and (fee - regular_chives_to_claim != 0)
        #print(f"need_chives_transaction:{need_chives_transaction}")
        
        # Calculate standard puzzle solutions
        change: int = selected_cat_amount - starting_amount
        primaries = []
        for payment in payments:
            primaries.append({"puzzlehash": payment.puzzle_hash, "amount": payment.amount, "memos": payment.memos})

        if change > 0:
            changepuzzlehash = hexstr_to_bytes(self.get_new_inner_hash)
            primaries.append({"puzzlehash": changepuzzlehash, "amount": change})

        limitations_program_reveal = Program.to([])
        if self.cc_info.my_genesis_checker is None:
            assert cat_discrepancy is None
        elif cat_discrepancy is not None:
            limitations_program_reveal = self.cc_info.my_genesis_checker

        # Loop through the coins we've selected and gather the information we need to spend them
        spendable_cc_list = []
        chives_tx = None
        first = True
        for coin in cat_coins:
            if first:
                first = False
                if need_chives_transaction:
                    if fee > regular_chives_to_claim:
                        announcement = Announcement(coin.name(), b"$", b"\xca")
                        chives_tx, _, Step1_ChangePuzzleHash, Step1_ChangeAmount = await self.create_tandem_xch_tx(
                            fee, uint64(regular_chives_to_claim), announcement_to_assert=announcement,SendToXchAmountArray=SendToXchAmountArray,SendToXchPuzzleHashArray=SendToXchPuzzleHashArray
                        )
                        innersol = self.make_solution_cat(
                            primaries=primaries, coin_announcements={announcement.message}
                        )
                    #elif regular_chives_to_claim > fee:
                    #    chives_tx, _ = await self.create_tandem_xch_tx(fee, uint64(regular_chives_to_claim))
                    #    innersol = self.standard_wallet.make_solution_cat(
                    #        primaries=primaries, coin_announcements_to_assert={announcement.name()}
                    #    )
                else:
                    innersol = self.make_solution_cat(primaries=primaries)
            else:
                innersol = self.make_solution_cat()
            inner_puzzle = self.inner_puzzle_for_cc_puzhash[str(coin.puzzle_hash)]
            
            if chives_tx is None:
                return (None,None,None,None)
            
            lineage_proof = None
            if str(coin.parent_coin_info) in self.LINEAGE_PROOF_NAME_TO_DICT:
                lineage_proof = self.LINEAGE_PROOF_NAME_TO_DICT[str(coin.parent_coin_info)]
            else:
                print("coin.parent_coin_in 在 self.LINEAGE_PROOF_NAME_TO_DICT 不存在，有可能是没有指定过滤的地址数量太少。")
            assert lineage_proof is not None
            '''
            print("coin===============================")
            print(coin)
            print("self.limitations_program_hash===============================")
            print(self.limitations_program_hash)
            print("inner_puzzle===============================")
            print(inner_puzzle)
            print("innersol===============================")
            print(innersol)
            print("limitations_solution===============================")
            print(limitations_solution)
            print("extra_delta===============================")
            print(extra_delta)
            print("lineage_proof===============================")
            print(lineage_proof)
            print("limitations_program_reveal===============================")
            print(limitations_program_reveal)
            '''
            new_spendable_cc = SpendableCC(
                coin,
                self.limitations_program_hash,
                inner_puzzle,
                innersol,
                limitations_solution=limitations_solution,
                extra_delta=extra_delta,
                lineage_proof=lineage_proof,
                limitations_program_reveal=limitations_program_reveal,
            )
            spendable_cc_list.append(new_spendable_cc)
            
        cat_spend_bundle = unsigned_spend_bundle_for_spendable_ccs(CC_MOD, spendable_cc_list)
        chives_spend_bundle = SpendBundle([], G2Element())
        if chives_tx is not None and chives_tx is not None:
            chives_spend_bundle = chives_tx
        
        return (
            SpendBundle.aggregate(
                [
                    cat_spend_bundle,
                    chives_spend_bundle,
                ]
            ),
            chives_tx,
            Step1_ChangePuzzleHash,
            Step1_ChangeAmount,
        )
       
    def make_solution_cat(
        self,
        primaries: Optional[List[Dict[str, Any]]] = None,
        min_time=0,
        me=None,
        coin_announcements: Optional[Set[bytes32]] = None,
        coin_announcements_to_assert: Optional[Set[bytes32]] = None,
        puzzle_announcements: Optional[Set[bytes32]] = None,
        puzzle_announcements_to_assert: Optional[Set[bytes32]] = None,
        fee=0,
    ) -> Program:
        assert fee >= 0
        condition_list = []
        if primaries:
            for primary in primaries:
                if "memos" in primary:
                    memos = primary["memos"]
                else:
                    memos = None
                condition_list.append(make_create_coin_condition(primary["puzzlehash"], primary["amount"], memos))
        if min_time > 0:
            condition_list.append(make_assert_absolute_seconds_exceeds_condition(min_time))
        if me:
            condition_list.append(make_assert_my_coin_id_condition(me["id"]))
        if fee:
            condition_list.append(make_reserve_fee_condition(fee))
        if coin_announcements:
            for announcement in coin_announcements:
                condition_list.append(make_create_coin_announcement(announcement))
        if coin_announcements_to_assert:
            for announcement_hash in coin_announcements_to_assert:
                condition_list.append(make_assert_coin_announcement(announcement_hash))
        if puzzle_announcements:
            for announcement in puzzle_announcements:
                condition_list.append(make_create_puzzle_announcement(announcement))
        if puzzle_announcements_to_assert:
            for announcement_hash in puzzle_announcements_to_assert:
                condition_list.append(make_assert_puzzle_announcement(announcement_hash))
        return solution_for_conditions(condition_list)
    
    async def sign_tx_cat(self, spend_bundle: SpendBundle) -> SpendBundle:
        sigs: List[G2Element] = []
        for spend in spend_bundle.coin_spends:
            matched, puzzle_args = match_cat_puzzle(spend.puzzle_reveal.to_program())
            if matched:
                _, _, inner_puzzle = puzzle_args
                puzzle_hash = inner_puzzle.get_tree_hash()
                pubkey = self.get_keys[str(puzzle_hash)]['pubkey']
                private = self.get_keys[str(puzzle_hash)]['private']
                #print(self.get_keys)
                #print(f"puzzle_hash:{puzzle_hash}")
                #print(f"private:{private}")
                #print(DEFAULT_HIDDEN_PUZZLE_HASH)
                synthetic_secret_key = calculate_synthetic_secret_key(private, DEFAULT_HIDDEN_PUZZLE_HASH)
                error, conditions, cost = conditions_dict_for_solution(
                    spend.puzzle_reveal.to_program(),
                    spend.solution.to_program(),
                    self.constants.MAX_BLOCK_COST_CLVM,
                )
                if conditions is not None:
                    synthetic_pk = synthetic_secret_key.get_g1()
                    for pk, msg in pkm_pairs_for_conditions_dict(
                        conditions, spend.coin.name(), self.constants.AGG_SIG_ME_ADDITIONAL_DATA
                    ):
                        try:
                            assert synthetic_pk == pk
                            sigs.append(AugSchemeMPL.sign(synthetic_secret_key, msg))
                        except AssertionError:
                            raise ValueError("This spend bundle cannot be signed by the CAT wallet")

        agg_sig = AugSchemeMPL.aggregate(sigs)
        return SpendBundle.aggregate([spend_bundle, SpendBundle([], agg_sig)])


    # ##########################################################################################    
    async def push_tx_cat(self,generate_signed_transaction_cat):
        try:
            config = load_config(DEFAULT_ROOT_PATH, "config.yaml")
            self_hostname = config["self_hostname"]
            rpc_port = config["full_node"]["rpc_port"]
            client_node = await FullNodeRpcClient.create(self_hostname, uint16(rpc_port), DEFAULT_ROOT_PATH, config)
            push_res = await client_node.push_tx_cat(generate_signed_transaction_cat)
            return push_res
        except Exception as e:
            print(f"Exception {e}")
        finally:
            client_node.close()
            await client_node.await_closed()
 