### PRF pcollapserARX-24...128
### Copyright (c) 2022 Polikarpov S.V., Prudnikov V.A., Rumyantsev K.E.
### Southern Federal University,
### Russia, Taganrog
### MIT License
### 
### this source created to use in CASCADA
### https://github.com/ranea/CASCADA (c) 2022 Adrián Ranea

import pcollapserARX_full
primitive = pcollapserARX_full
cipher = primitive.pcollapserARXcipher

############################################################################################################################################################

from cascada.smt.chsearch import PrintingMode
from cascada.linear.mask import LinearMask
from cascada.differential.difference import XorDiff, RXDiff
from cascada.smt.chsearch import ChModelAssertType, round_based_ch_search, round_based_cipher_ch_search
from cascada.smt.chsearch import ChFinder, CipherChFinder

from cascada.smt.invalidpropsearch import InvalidCipherPropFinder, get_wrapped_cipher_chmodel
from cascada.differential.chmodel import CipherChModel, ChModel
from datetime import datetime

def find_XorDiff_ch(fround=None, lround=None, initial_weight=None):
    print("\nFinding XorDiff characteristics (no validation by empirical weights)")
    print("Warning! Too many invalid characteristics")
    if(fround == None): fround = 1
    if(lround == None): lround = 4
    if(initial_weight == None): 
        initial_weight = 0    
    assert_type = ChModelAssertType.ValidityAndWeight
    iterator = round_based_ch_search(cipher, fround, lround, XorDiff, assert_type, "btor",
    extra_chfinder_args={"exclude_zero_input_prop": True, "solver_seed": 0, "printing_mode": PrintingMode.WeightsAndSrepr},
    extra_findnextchweight_args={"initial_weight": initial_weight})
    for (num_rounds, ch) in iterator:
        print(num_rounds, ":", ch.srepr())  
        if(SHOW_CH_DETAILS): 
            print(num_rounds, ":", ch)
        print()
        if(num_rounds > 1 and SHOW_CH_DETAILS):
            for i, sub_ch in enumerate(ch.split(ch.get_round_separators())):
                print(f"Round {i}: {sub_ch.srepr()}") 
                print(f"Round {i}: {sub_ch}")
                print() 


def find_Linear_ch(fround=None, lround=None, initial_weight=None):
    print("\nFinding LinearMask characteristics (no validation by empirical weights)")
    if(fround == None): fround = 1
    if(lround == None): lround = 4
    if(initial_weight == None): 
        initial_weight = 0        
    assert_type = ChModelAssertType.ValidityAndWeight
    iterator = round_based_ch_search(cipher, fround, lround, LinearMask, assert_type, "btor",
    extra_chfinder_args={"exclude_zero_input_prop": True, "solver_seed": 0, "printing_mode": PrintingMode.WeightsAndSrepr},
    #extra_chfinder_args={"exclude_zero_input_prop": True, "solver_seed": 0, "printing_mode": PrintingMode.Debug},
    extra_findnextchweight_args={"initial_weight": initial_weight})
    for (num_rounds, ch) in iterator:
        print(num_rounds, ":", ch.srepr())  
        if(SHOW_CH_DETAILS): 
            print(num_rounds, ":", ch)
        print()
        if(num_rounds > 1 and SHOW_CH_DETAILS):
            for i, sub_ch in enumerate(ch.split(ch.get_round_separators())):
                print(f"Round {i}: {sub_ch.srepr()}") 
                print(f"Round {i}: {sub_ch}")
                print()


def find_XorDiff_ch_we_extra(fround=None, lround=None, initial_weight=None):
    print("\nFinding XorDiff characteristics and validate them by using empirical weights (ew)!")
    Nsamples = 2**24
    if(fround == None): fround = 1
    if(lround == None): lround = 4
    if(initial_weight == None): 
        initial_weight = 0     
    assert_type = ChModelAssertType.ValidityAndWeight
    iterator = round_based_ch_search(cipher, fround, lround, XorDiff, assert_type, "btor",
    extra_chfinder_args={"exclude_zero_input_prop": True, "solver_seed": 0, "printing_mode": PrintingMode.WeightsAndVrepr},
    extra_findnextchweight_args={ "initial_weight": initial_weight, "empirical_weight_options":{"C_code": True, "num_parallel_processes": 8, "num_input_samples": Nsamples, "num_external_samples": 64} })
    for (num_rounds, ch) in iterator:
        print(num_rounds, ":", ch.srepr())  
        if(SHOW_CH_DETAILS): 
            print(num_rounds, ":", ch)
        print()
        if(num_rounds > 1 and SHOW_CH_DETAILS):
            for i, sub_ch in enumerate(ch.split(ch.get_round_separators())):
                print(f"Round {i}: {sub_ch.srepr()}") 
                print(f"Round {i}: {sub_ch}")
                print()


def find_Linear_ch_we_extra(fround=None, lround=None, initial_weight=None):
    print("\nFinding LinearMask characteristics and validate them by using empirical weights (ew)")
    Nsamples = 2**24
    if(fround == None): fround = 1
    if(lround == None): lround = 4
    if(initial_weight == None): 
        initial_weight = 0     
    assert_type = ChModelAssertType.ValidityAndWeight
    iterator = round_based_ch_search(cipher, fround, lround, LinearMask, assert_type, "btor",
    extra_chfinder_args={"exclude_zero_input_prop": True, "solver_seed": 0, "printing_mode": PrintingMode.WeightsAndVrepr},
    extra_findnextchweight_args={ "initial_weight": initial_weight, "empirical_weight_options":{"C_code": True, "num_parallel_processes": 4, "num_input_samples": Nsamples, "num_external_samples": 64} })
    for (num_rounds, ch) in iterator:
        print(num_rounds, ":", ch.srepr())  
        if(SHOW_CH_DETAILS): 
            print(num_rounds, ":", ch)
        print()
        if(num_rounds > 1 and SHOW_CH_DETAILS):
            for i, sub_ch in enumerate(ch.split(ch.get_round_separators())):
                print(f"Round {i}: {sub_ch.srepr()}") 
                print(f"Round {i}: {sub_ch}")
                print()


def find_RxDiff_ch(num_rounds=None, initial_weight=None):
    print("\nFinding RXDiff or Related-Key RXDiff characteristics  (no validation by empirical weights)")
    if(num_rounds == None): num_rounds = 1
    if(initial_weight == None): 
        initial_weight = 0 
    print("Current number of rounds: ", num_rounds)    
    from cascada.bitvector.core import Constant
    from cascada.differential.difference import XorDiff, RXDiff
    from cascada.differential.chmodel import CipherChModel
    from cascada.smt.chsearch import ChFinder, CipherChFinder, ChModelAssertType
    cipher.set_num_rounds(num_rounds)
    ch_model = CipherChModel(cipher, RXDiff)
    assert_type = ChModelAssertType.ValidityAndWeight
    ch_finder = CipherChFinder(ch_model, assert_type,  assert_type, "btor", solver_seed=0, printing_mode=PrintingMode.WeightsAndSrepr)
    best_ch = next(ch_finder.find_next_ch_increasing_weight(initial_weight))
    print(num_rounds, ":", best_ch.srepr())
    if(SHOW_CH_DETAILS): 
        print(num_rounds, ":", best_ch)
    print()
    if(num_rounds > 1 and SHOW_CH_DETAILS):
        for i, sub_ch in enumerate(best_ch.split(best_ch.get_round_separators())):
            print(f"Round {i}: {sub_ch.srepr()}") 
            print(f"Round {i}: {sub_ch}")
            print()        


def find_Related_XorDiff_ch(num_rounds=None, initial_weight=None):
    print("\nFinding Related-Key XorDiff characteristics (no validation by empirical weights)")
    if(primitive.SCHEDULE_NROUNDS == 0): 
        print("Warning! You need Enable key schedule for this type of analysis!")
    if(num_rounds == None): num_rounds = 1
    if(initial_weight == None): 
        initial_weight = 0 
    print("Current number of rounds: ", num_rounds)    
    cipher.set_num_rounds(num_rounds)
    ch_model = CipherChModel(cipher, XorDiff)
    assert_type = ChModelAssertType.ValidityAndWeight
    ch_finder = CipherChFinder(ch_model, assert_type,  assert_type, "btor", enc_exclude_zero_input_prop=True, ks_exclude_zero_input_prop=True, solver_seed=0, printing_mode=PrintingMode.WeightsAndSrepr)
    best_ch = next(ch_finder.find_next_ch_increasing_weight(initial_weight))
    print(num_rounds, ":", best_ch.srepr())
    if(SHOW_CH_DETAILS): 
        print(num_rounds, ":", best_ch)
    print()
    #if(num_rounds > 1 and SHOW_CH_DETAILS):
        #for i, sub_ch in enumerate(best_ch.split(best_ch.get_round_separators())):
            #print(f"Round {i}: {sub_ch.srepr()}") 
            #print(f"Round {i}: {sub_ch}")
            #print()  


def find_Impossible_XorDiff_ch(num_rounds=None, initial_weight=None):
    print("\nFinding Impossible XorDiff characteristics (no validation by empirical weights)")
    if(num_rounds == None): num_rounds = 1
    if(initial_weight == None): 
        initial_weight = 0 
    print("Current number of rounds: ", num_rounds)    
    cipher.set_num_rounds(num_rounds)
    ch_model = get_wrapped_cipher_chmodel(CipherChModel(cipher, XorDiff))
    invalid_prop_finder = InvalidCipherPropFinder(ch_model, "z3")
    uni_inv_ch = next(invalid_prop_finder.find_next_invalidprop_quantified_logic())
    print(num_rounds, ":", uni_inv_ch.srepr())
    if(SHOW_CH_DETAILS): 
        print(num_rounds, ":", uni_inv_ch)
    print()
    if(num_rounds > 1 and SHOW_CH_DETAILS):
        for i, sub_ch in enumerate(uni_inv_ch.split(uni_inv_ch.get_round_separators())):
            print(f"Round {i}: {sub_ch.srepr()}") 
            print(f"Round {i}: {sub_ch}")
            print()              


def find_Impossible_RXDiff_ch(num_rounds=None, initial_weight=None):
    print("\nFinding Impossible RXDiff characteristics (no validation by empirical weights)")
    if(num_rounds == None): num_rounds = 1
    if(initial_weight == None): 
        initial_weight = 0 
    print("Current number of rounds: ", num_rounds)    
    cipher.set_num_rounds(num_rounds)
    ch_model = get_wrapped_cipher_chmodel(CipherChModel(cipher, RXDiff))
    invalid_prop_finder = InvalidCipherPropFinder(ch_model, "z3")
    uni_inv_ch = next(invalid_prop_finder.find_next_invalidprop_quantified_logic())
    print(num_rounds, ":", uni_inv_ch.srepr())
    if(SHOW_CH_DETAILS): 
        print(num_rounds, ":", uni_inv_ch)
    print()
    if(num_rounds > 1 and SHOW_CH_DETAILS):
        for i, sub_ch in enumerate(uni_inv_ch.split(uni_inv_ch.get_round_separators())):
            print(f"Round {i}: {sub_ch.srepr()}") 
            print(f"Round {i}: {sub_ch}")
            print()  


def find_ZeroCorellation_ch(num_rounds=None, initial_weight=None):
    print("\nFinding ZeroCorellation characteristics (no validation by empirical weights)")
    if(num_rounds == None): num_rounds = 1
    if(initial_weight == None): 
        initial_weight = 0 
    print("Current number of rounds: ", num_rounds)    
    cipher.set_num_rounds(num_rounds)
    ch_model = get_wrapped_cipher_chmodel(CipherChModel(cipher, LinearMask))
    invalid_prop_finder = InvalidCipherPropFinder(ch_model, "z3")
    uni_inv_ch = next(invalid_prop_finder.find_next_invalidprop_quantified_logic())
    print(num_rounds, ":", uni_inv_ch.srepr())
    if(SHOW_CH_DETAILS): 
        print(num_rounds, ":", uni_inv_ch)
    print()
    if(num_rounds > 1 and SHOW_CH_DETAILS):
        for i, sub_ch in enumerate(uni_inv_ch.split(uni_inv_ch.get_round_separators())):
            print(f"Round {i}: {sub_ch.srepr()}") 
            print(f"Round {i}: {sub_ch}")
            print()  

#for i, ch in enumerate(invalid_prop_finder.find_next_invalidprop_quantified_logic()):
#    print(ch.srepr())
#    if i == 2: break  

########################################################################################################################

if __name__ == '__main__':
    import sys
    import warnings
    import argparse
    
    parser = argparse.ArgumentParser(description="PRF pCollapserARX testing",
                                 formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    
    #", default="SE"
    parser.add_argument("type_of_analysis", default="xordiff", type=str, help="the type of analysis (linear, xordiff, rxdiff, related-xordiff, impossible-xordiff, impossible-rxdiff, zerocorellation, verify_implementation )")
    parser.add_argument("-b", "--block-size", default=64, type=int, help="block size, bit (32, 64 or 128 - the lenght of in/out blocks)")
    parser.add_argument("-f", "--first-round", default=1, type=int, help="the number of the round from which the analysis starts")
    parser.add_argument("-l", "--last-round",  default=4, type=int, help="the number of the round at which the analysis ends")
    parser.add_argument("-w", "--starting-weight", default=0, type=int, help="starting weight")
    parser.add_argument("--ks-nrounds", default=0, type=int, help="num of the key-schedule rounds")
    parser.add_argument("--use-empirical-weights", action="store_true", help="using empirical weights calculation (only for block_size <= 24)")
    parser.add_argument("--show-debug-info", default=False, action="store_true", help="showing detailed debug info")
    parser.add_argument("--show-ch-details", default=False, action="store_true", help="showing detailed info about found Characteristic")
    
    args = parser.parse_args()
    config = vars(args)
    print("\n<><><><><> Run analysis using parameters: <><><><><>")
    print(config)
    print("<><><><><><><><><><><><><><><><><><><><><><><><><><>\n")
    
    warnings.simplefilter("ignore")
    DEBUG_OUTS = config["show_debug_info"]

    now = datetime.now()
    dt_string = now.strftime("%d/%m/%Y %H:%M:%S")
    print("Log started at : ", dt_string)        
    
    block_size = config["block_size"]
    if(block_size == 16 or block_size == 24 or block_size == 32 or block_size == 64 or block_size == 128 or block_size == 256):
        WORDSIZE = block_size >> 2
    else:
        print("Warning: no valid block-size used !!!")
        exit(1)
    
    if(block_size < 32):
        print("\nWarning: extra weak ARX-func used !!! Use only for miniversion testing !!!")
    
    fround = config["first_round"] 
    lround = config["last_round"] 
    initial_weight = config["starting_weight"] 
    type_of_analysis = config["type_of_analysis"]
    ks_nrounds = config["ks_nrounds"]
    
    USE_EW = config["use_empirical_weights"]
    SHOW_CH_DETAILS = config["show_ch_details"]
    
    primitive.DEBUG_OUTS = DEBUG_OUTS
    primitive.WORDSIZE = WORDSIZE
    primitive.SCHEDULE_NROUNDS = ks_nrounds
    
    if(type_of_analysis == "verify_implementation"):
        primitive.DEBUG_OUTS = 0
        primitive.SHOW_CAPTION = 0
        primitive.SCHEDULE_NROUNDS = 4
        primitive.verify_prf_implementation()
        print("\nVerification was successful !")
        exit(0)
    
    if(USE_EW == False):
        if(type_of_analysis ==   "xordiff"):
            find_XorDiff_ch(fround, lround, initial_weight)
        elif(type_of_analysis == "linear"):    
            find_Linear_ch(fround, lround, initial_weight)
        elif(type_of_analysis == "rxdiff"):
            #SCHEDULE_NROUNDS = 0
            for nrounds in range(fround, lround+1):
                find_RxDiff_ch(nrounds, initial_weight)   
        elif(type_of_analysis == "related-xordiff"):
            for nrounds in range(fround, lround+1):
                find_Related_XorDiff_ch(nrounds, initial_weight)
        elif(type_of_analysis == "impossible-xordiff"):
            for nrounds in range(fround, lround+1):
                find_Impossible_XorDiff_ch(nrounds, initial_weight)
        elif(type_of_analysis == "impossible-rxdiff"):
            for nrounds in range(fround, lround+1):
                find_Impossible_RXDiff_ch(nrounds, initial_weight)
        elif(type_of_analysis == "zerocorellation"):
            for nrounds in range(fround, lround+1):
                find_ZeroCorellation_ch(nrounds, initial_weight)
    elif(USE_EW == True and WORDSIZE <= 8):
        if(type_of_analysis ==   "xordiff"):
            find_XorDiff_ch_we_extra(fround, lround, initial_weight)
        elif(type_of_analysis == "linear"):    
            find_Linear_ch_we_extra(fround, lround, initial_weight)
        else:
            print("Warning: no valid type of analysis used for empirical weights calculation option !")
    elif(USE_EW == True):
        print("Warning: empirical weights calculation used only for block_size <= 32 !")
        print("Warning: use it with caution (simplified model used) !")
    
    now = datetime.now()
    dt_string = now.strftime("%d/%m/%Y %H:%M:%S")
    print("Log ended at : ", dt_string)  
