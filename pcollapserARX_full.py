### PRF pcollapserARX-16...256
### Copyright (c) 2023 Polikarpov S.V., Prudnikov V.A., Rumyantsev K.E.
### Southern Federal University,
### Russia, Taganrog
### MIT License
### 
### this source created to use in CASCADA
### https://github.com/ranea/CASCADA (c) 2022 Adrián Ranea

DEBUG_OUTS = 0

NROUNDS		= 4
NCOLUMNS	= 4   # 4
NROWS		= 4   # 4 
WORDSIZE    = 8   # 4, 6, 8, 16, 32, 64

SCHEDULE_NROUNDS = 4        # 4

USE_sboxARX_MINIMAL    = 0          # 1
EXTRA_MINI_sboxARX_MINIMAL = 0      # 1

INJECT_TO_STATE = 1
OLD_STYLE_ARX_FUNC = 0              # enable for rxdiff only
SHOW_CAPTION = 1
####################################################################################################

import sys
sys.setrecursionlimit(100000000)  

import itertools

from cascada.bitvector.core import Constant, Term, Variable, bitvectify
from cascada.bitvector.operation import BvComp, BvNot, RotateLeft, RotateRight, Concat
from cascada.bitvector.secondaryop import LutOperation, MatrixOperation

from cascada.differential.opmodel import get_wdt_model as get_differential_wdt_model
from cascada.linear.opmodel import get_wdt_model as get_linear_wdt_model

from cascada.bitvector.ssa import RoundBasedFunction
from cascada.primitives.blockcipher import Encryption, Cipher


def _hex2byte_list(state):
    """Convert the hexadecimal string to a byte list

        >>> _hex2byte_list("000102030405060708090a0b0c0d0e0f")
        [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]

    """
    byte_list = []
    for i in range(0, len(state), 2):
        my_byte = int(state[i:i + 2], base=16)
        byte_list.append(Constant(my_byte, 8))
    return byte_list

def _hex2nibble_list(state):
    """Convert the hexadecimal string to a nibble list

        >>> _hex2nibble_list("000102030405060708090a0b0c0d0e0f")
        [0x0, 0x0, 0x0, 0x1, 0x0, 0x2, 0x0, 0x3, 0x0, 0x4, 0x0, 0x5, 0x0, 0x6, 0x0, 0x7, 0x0, 0x8, 0x0, 0x9, 0x0, 0xa, 0x0, 0xb, 0x0, 0xc, 0x0, 0xd, 0x0, 0xe, 0x0, 0xf]
    """
    nibble_list = []
    for i in range(0, len(state), 1):
        my_nibble = int(state[i:i + 1], base=16)
        nibble_list.append(Constant(my_nibble, 4))
    return nibble_list

print("type of PRF: pCollapserARX_full (included key-schedule)")
print("Copyright (c) 2023 Polikarpov S.V., Prudnikov V.A., Rumyantsev K.E.")
print("Southern Federal University")
print("febrary 2023")

##################
### func_arx

def sboxARX_new(x, constant, rot_a1, rot_b1, rot_a2, rot_b2, rot_af1, rot_bf1, rot_abf2, wordsize_): 
	wordsize = wordsize_ >> 1
	
	const1 = constant[2*wordsize-1:wordsize]
	const2 = constant[wordsize-1:0]
	
    # split input word by two subwords
	a = x[wordsize-1:0]
	b = x[2*wordsize-1:wordsize]
	
	#-- 1
	at = RotateLeft(a, rot_a1) ^ b 
	bt = RotateLeft(b, rot_b1) ^ a 
	
	a = (a + at)
	b = (b + bt) 
	
	a =  RotateLeft(a, rot_af1)
	b =  RotateLeft(b, rot_bf1)
	
	a = a ^ const1
	b = b ^ const2	
	
	#-- 2	
	at = RotateLeft(a, rot_a2) ^ b 
	bt = RotateLeft(b, rot_b2) ^ a 
		
	a = (a + at) 
	b = (b + bt) 
	
	#---
	a =  RotateLeft(a, rot_abf2)
	b =  RotateLeft(b, rot_abf2)
	
	arxout = Concat( b, a )
	
	return arxout


def sboxARX_minimal_possible_new(x, constant, rot_a1, rot_a2, rot_af1, wordsize):
	
	const1 = constant[wordsize-1:0]
	a = x[wordsize-1:0]
	
	#-- 1
	at = RotateLeft(a, rot_a1) ^ const1
	a = (a + at)
	
	if(EXTRA_MINI_sboxARX_MINIMAL != 1):
		at = RotateLeft(a, rot_a2);
		a = (a + at)
		
	arxout =  RotateLeft(a, rot_af1)
	
	return arxout

####################################################################################################
### func_RotateLeft

def ROTL(x, shift, wordsize):
	if(shift == 0):
		return x;
	if(wordsize == 4):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xF;
	if(wordsize == 6):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0x3F;
	if(wordsize == 8):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xFF;
	if(wordsize == 12):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xFFF;
	if(wordsize == 16):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xFFFF;
	if(wordsize == 20):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xFFFFF;
	if(wordsize == 24):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xFFFFFF;
	if(wordsize == 28):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xFFFFFFF;
	if(wordsize == 32):
		return ((x << shift) ^ (x >> (wordsize-shift)) ) & 0xFFFFFFFF;
		
	return 0;	


##################
### func_arx

def sboxARX_old(x, constant, rot_a1, rot_b1, rot_a2, rot_b2, rot_af1, rot_bf1, rot_abf2, wordsize_): 
	wordsize = wordsize_ >> 1
	mask = 0 
	
	if(wordsize == 4):  mask = 0xF
	if(wordsize == 6):  mask = 0x3F;
	if(wordsize == 8):  mask = 0xFF;
	if(wordsize == 12): mask = 0xFFF;
	if(wordsize == 16): mask = 0xFFFF;
	if(wordsize == 20): mask = 0xFFFFF;
	if(wordsize == 24): mask = 0xFFFFFF;
	if(wordsize == 28): mask = 0xFFFFFFF;
	if(wordsize == 32): mask = 0xFFFFFFFF;
	
	const1 = (constant >> wordsize) & mask 
	const2 = constant & mask
	
	a = x & mask;				# split in word by two subwords
	b = (x >> wordsize) & mask;
	
	#-- 1
	at = ROTL(a, rot_a1, wordsize) ^ b 
	bt = ROTL(b, rot_b1, wordsize) ^ a 
	
	a = (a + at) & mask 
	b = (b + bt) & mask 
	
	a =  ROTL(a, rot_af1, wordsize)
	b =  ROTL(b, rot_bf1, wordsize)
	
	
	a = a ^ const1
	b = b ^ const2	
	
	#-- 2
	
	at = ROTL(a, rot_a2, wordsize) ^ b
	bt = ROTL(b, rot_b2, wordsize) ^ a
		
	a = (a + at) & mask 
	b = (b + bt) & mask 
	
	#---
	
	a =  ROTL(a, rot_abf2, wordsize)
	b =  ROTL(b, rot_abf2, wordsize)
	
	arxout = (a & mask) ^ ((b & mask) << wordsize) 
	
	return arxout;


def sboxARX_minimal_possible_old(x, constant, rot_a1, rot_a2, rot_af1, wordsize_):
	wordsize = wordsize_;	
	mask = 0 	
	if(wordsize == 4):  mask = 0x0F;
	if(wordsize == 6):  mask = 0x3F;
	if(wordsize == 8):  mask = 0xFF;
	if(wordsize == 12): mask = 0xFFF;
	if(wordsize == 16): mask = 0xFFFF;
	if(wordsize == 20): mask = 0xFFFFF;
	if(wordsize == 24): mask = 0xFFFFFF;
	if(wordsize == 28): mask = 0xFFFFFFF;
	if(wordsize == 32): mask = 0xFFFFFFFF;
	
	const1 = constant & mask
	
	a = x & mask				
	
	#-- 1
	at = ROTL(a, rot_a1, wordsize) ^ const1
	a = (a + at) & mask 
	
	if(EXTRA_MINI_sboxARX_MINIMAL != 1):
		at = ROTL(a, rot_a2, wordsize)
		a = (a + at) & mask; 
		
	a =  ROTL(a, rot_af1, wordsize)
	arxout = (a & mask) 
	
	return arxout;


####################################################################################################
sboxARX = sboxARX_new
sboxARX_minimal_possible = sboxARX_minimal_possible_new

if(OLD_STYLE_ARX_FUNC == 1):    # for RXDIFF only
    sboxARX = sboxARX_old
    sboxARX_minimal_possible = sboxARX_minimal_possible_old
    print("WARNING: Using OLD_STYLE_ARX_FUNC !")
####################################################################################################
    
dec_vec_16 = [
    [Constant(d_i, 4) for d_i in [0x4, 0x1, 0xE, 0x9]],
    [Constant(d_i, 4) for d_i in [0xA, 0x0, 0x7, 0x4]],
    [Constant(d_i, 4) for d_i in [0xD, 0x8, 0x3, 0x2]],
    [Constant(d_i, 4) for d_i in [0xE, 0x4, 0x1, 0x9]],
    [Constant(d_i, 4) for d_i in [0xF, 0xA, 0x8, 0xC]],
    [Constant(d_i, 4) for d_i in [0xF, 0x5, 0xC, 0x6]],
    [Constant(d_i, 4) for d_i in [0x7, 0x2, 0x6, 0xB]],
    [Constant(d_i, 4) for d_i in [0x3, 0x9, 0x3, 0xD]],
]
    
dec_vec_24 = [  # vec = 0x290FB3
    [Constant(d_i, 6) for d_i in [0x0A, 0x10, 0x3E, 0x33]],
    [Constant(d_i, 6) for d_i in [0x25, 0x08, 0x1F, 0x19]],
    [Constant(d_i, 6) for d_i in [0x32, 0x24, 0x0F, 0x2C]],
    [Constant(d_i, 6) for d_i in [0x19, 0x12, 0x07, 0x36]],
    [Constant(d_i, 6) for d_i in [0x0C, 0x29, 0x03, 0x3B]],
    [Constant(d_i, 6) for d_i in [0x26, 0x14, 0x21, 0x3D]],
    [Constant(d_i, 6) for d_i in [0x33, 0x0A, 0x10, 0x3E]],
    [Constant(d_i, 6) for d_i in [0x19, 0x25, 0x08, 0x1F]],
]
    
dec_vec_32 = [  # vec = 0x4A18EC9F
    [Constant(d_i, 8) for d_i in [0x4A, 0x18, 0xEC, 0x9F]],
    [Constant(d_i, 8) for d_i in [0xA5, 0x0C, 0x76, 0x4F]],
    [Constant(d_i, 8) for d_i in [0xD2, 0x86, 0x3B, 0x27]],
    [Constant(d_i, 8) for d_i in [0xE9, 0x43, 0x1D, 0x93]],
    [Constant(d_i, 8) for d_i in [0xF4, 0xA1, 0x8E, 0xC9]],
    [Constant(d_i, 8) for d_i in [0xFA, 0x50, 0xC7, 0x64]],
    [Constant(d_i, 8) for d_i in [0x7D, 0x28, 0x63, 0xB2]],
    [Constant(d_i, 8) for d_i in [0x3E, 0x94, 0x31, 0xD9]],
]
    
dec_vec_64 = [  # vec = 0x8ABB01487F9CCBC6
    [Constant(d_i, 16) for d_i in [0x8ABB, 0x0148, 0x7F9C, 0xCBC6]],
    [Constant(d_i, 16) for d_i in [0x455D, 0x80A4, 0x3FCE, 0x65E3]],
    [Constant(d_i, 16) for d_i in [0xA2AE, 0xC052, 0x1FE7, 0x32F1]],
    [Constant(d_i, 16) for d_i in [0xD157, 0x6029, 0x0FF3, 0x9978]],
    [Constant(d_i, 16) for d_i in [0x68AB, 0xB014, 0x87F9, 0xCCBC]],
    [Constant(d_i, 16) for d_i in [0x3455, 0xD80A, 0x43FC, 0xE65E]],
    [Constant(d_i, 16) for d_i in [0x1A2A, 0xEC05, 0x21FE, 0x732F]],
    [Constant(d_i, 16) for d_i in [0x8D15, 0x7602, 0x90FF, 0x3997]],
]
    
dec_vec_128 = [  # vec = 0x15E64A1A45C8C200FEB5DAAE8BCC979F
    [Constant(d_i, 32) for d_i in [0x15E64A1A, 0x45C8C200, 0xFEB5DAAE, 0x8BCC979F]],
    [Constant(d_i, 32) for d_i in [0x8AF3250D, 0x22E46100, 0x7F5AED57, 0x45E64BCF]],
    [Constant(d_i, 32) for d_i in [0xC5799286, 0x91723080, 0x3FAD76AB, 0xA2F325E7]],
    [Constant(d_i, 32) for d_i in [0xE2BCC943, 0x48B91840, 0x1FD6BB55, 0xD17992F3]],
    [Constant(d_i, 32) for d_i in [0xF15E64A1, 0xA45C8C20, 0x0FEB5DAA, 0xE8BCC979]],
    [Constant(d_i, 32) for d_i in [0xF8AF3250, 0xD22E4610, 0x07F5AED5, 0x745E64BC]],
    [Constant(d_i, 32) for d_i in [0x7C579928, 0x69172308, 0x03FAD76A, 0xBA2F325E]],
    [Constant(d_i, 32) for d_i in [0x3E2BCC94, 0x348B9184, 0x01FD6BB5, 0x5D17992F]],
]

dec_vec_256 = [  # vec = 0xEB57E7BC1502EDE54F15C55B9A0F3E99DACB0891617D20B8461F1209945C699F
    [Constant(d_i, 64) for d_i in [0xEB57E7BC1502EDE5, 0x4F15C55B9A0F3E99, 0xDACB0891617D20B8, 0x461F1209945C699F]],
    [Constant(d_i, 64) for d_i in [0xF5ABF3DE0A8176F2, 0xA78AE2ADCD079F4C, 0xED658448B0BE905C, 0x230F8904CA2E34CF]],
    [Constant(d_i, 64) for d_i in [0xFAD5F9EF0540BB79, 0x53C57156E683CFA6, 0x76B2C224585F482E, 0x1187C48265171A67]],
    [Constant(d_i, 64) for d_i in [0xFD6AFCF782A05DBC, 0xA9E2B8AB7341E7D3, 0x3B5961122C2FA417, 0x08C3E241328B8D33]],
    [Constant(d_i, 64) for d_i in [0xFEB57E7BC1502EDE, 0x54F15C55B9A0F3E9, 0x9DACB0891617D20B, 0x8461F1209945C699]],
    [Constant(d_i, 64) for d_i in [0xFF5ABF3DE0A8176F, 0x2A78AE2ADCD079F4, 0xCED658448B0BE905, 0xC230F8904CA2E34C]],
    [Constant(d_i, 64) for d_i in [0x7FAD5F9EF0540BB7, 0x953C57156E683CFA, 0x676B2C224585F482, 0xE1187C48265171A6]],
    [Constant(d_i, 64) for d_i in [0x3FD6AFCF782A05DB, 0xCA9E2B8AB7341E7D, 0x33B5961122C2FA41, 0x708C3E241328B8D3]],
]

###################################################################################################
def funcARX(msd, j, const):
    y_j = 0
    if(WORDSIZE == 4):  # block_size = 4*WORDSIZE = 16
        if(j == 0): y_j = sboxARX_minimal_possible(msd, const, 1, 3, 0, WORDSIZE)
        if(j == 1): y_j = sboxARX_minimal_possible(msd, const, 3, 1, 1, WORDSIZE)
        if(j == 2): y_j = sboxARX_minimal_possible(msd, const, 1, 2, 2, WORDSIZE)
        if(j == 3): y_j = sboxARX_minimal_possible(msd, const, 2, 1, 3, WORDSIZE)
    if(WORDSIZE == 6):  # block_size = 24
        if(j == 0): y_j = sboxARX_minimal_possible(msd, const, 2, 3, 0, WORDSIZE)
        if(j == 1): y_j = sboxARX_minimal_possible(msd, const, 3, 2, 2, WORDSIZE)
        if(j == 2): y_j = sboxARX_minimal_possible(msd, const, 1, 3, 3, WORDSIZE)
        if(j == 3): y_j = sboxARX_minimal_possible(msd, const, 3, 1, 4, WORDSIZE)
    if(WORDSIZE == 8):  # block_size = 32
        # sboxARX(x, const1, const2, rot_a1, rot_b1, rot_a2, rot_b2, rot_af1, rot_bf1, rot_abf2, wordsize_)
        #if(j == 0): y_j = sboxARX_minimal_possible(msd, const, 2, 6, 0, WORDSIZE)
        #if(j == 1): y_j = sboxARX_minimal_possible(msd, const, 6, 2, 2, WORDSIZE)
        #if(j == 2): y_j = sboxARX_minimal_possible(msd, const, 1, 6, 4, WORDSIZE)
        #if(j == 3): y_j = sboxARX_minimal_possible(msd, const, 6, 1, 6, WORDSIZE)        
        if(j == 0): y_j = sboxARX(msd, const, 1, 3, 1, 3, 3, 1, 0, WORDSIZE)
        if(j == 1): y_j = sboxARX(msd, const, 1, 3, 3, 1, 1, 3, 1, WORDSIZE)
        if(j == 2): y_j = sboxARX(msd, const, 3, 1, 1, 3, 1, 3, 2, WORDSIZE)
        if(j == 3): y_j = sboxARX(msd, const, 3, 1, 3, 1, 3, 1, 3, WORDSIZE)
    if(WORDSIZE == 16): # block_size = 64
        if(j == 0): y_j = sboxARX(msd, const, 2, 4, 2, 4, 4, 2, 0, WORDSIZE)
        if(j == 1): y_j = sboxARX(msd, const, 2, 4, 4, 2, 2, 4, 2, WORDSIZE)
        if(j == 2): y_j = sboxARX(msd, const, 4, 2, 2, 4, 2, 4, 4, WORDSIZE)
        if(j == 3): y_j = sboxARX(msd, const, 4, 2, 4, 2, 4, 2, 6, WORDSIZE)
        #if(j == 0): y_j = sboxARX(msd, const, 2, 6, 2, 6, 6, 2, 0, WORDSIZE)
        #if(j == 1): y_j = sboxARX(msd, const, 2, 6, 6, 2, 2, 6, 2, WORDSIZE)
        #if(j == 2): y_j = sboxARX(msd, const, 6, 2, 2, 6, 2, 6, 4, WORDSIZE)
        #if(j == 3): y_j = sboxARX(msd, const, 6, 2, 6, 2, 6, 2, 6, WORDSIZE)
    if(WORDSIZE == 32): # block_size = 128
        if(j == 0): y_j = sboxARX(msd, const, 4, 8, 4, 8, 8, 4, 0, WORDSIZE)
        if(j == 1): y_j = sboxARX(msd, const, 4, 8, 8, 4, 4, 8, 4, WORDSIZE)
        if(j == 2): y_j = sboxARX(msd, const, 8, 4, 4, 8, 4, 8, 8, WORDSIZE)
        if(j == 3): y_j = sboxARX(msd, const, 8, 4, 8, 4, 8, 4, 12, WORDSIZE)  
        #if(j == 0): y_j = sboxARX(msd, const, 4, 12, 4, 12, 12, 4, 0, WORDSIZE)
        #if(j == 1): y_j = sboxARX(msd, const, 4, 12, 12, 4, 4, 12, 4, WORDSIZE)
        #if(j == 2): y_j = sboxARX(msd, const, 12, 4, 4, 12, 4, 12, 8, WORDSIZE)
        #if(j == 3): y_j = sboxARX(msd, const, 12, 4, 12, 4, 12, 4, 12, WORDSIZE)
    if(WORDSIZE == 64): # block_size = 256
        if(j == 0): y_j = sboxARX(msd, const, 8, 16, 8, 16, 16, 8, 0, WORDSIZE)
        if(j == 1): y_j = sboxARX(msd, const, 8, 16, 16, 8, 8, 16, 8, WORDSIZE)
        if(j == 2): y_j = sboxARX(msd, const, 16, 8, 8, 16, 8, 16, 16, WORDSIZE)
        if(j == 3): y_j = sboxARX(msd, const, 16, 8, 16, 8, 16, 8, 24, WORDSIZE)
    return y_j

###################################################################################################

class pcollpaserARX_KeySchedule(RoundBasedFunction):
    """Key schedule function."""
    
    ks_num_rounds = SCHEDULE_NROUNDS   # 4
    Nrows = NROWS
    num_columns = NCOLUMNS
    
    #KEYLEN = num_columns 
    #expanded_key_size = num_columns * 2
    
    if(ks_num_rounds  < 1): 
        KEYLEN = num_columns * 2
        expanded_key_size = num_columns * 2
    if(ks_num_rounds == 1):
        KEYLEN = num_columns
        expanded_key_size = num_columns
    if(ks_num_rounds  > 1): 
        KEYLEN = num_columns
        expanded_key_size = num_columns * 2
    
    input_widths  = [WORDSIZE for _ in range(KEYLEN)]
    output_widths = [WORDSIZE for _ in range(expanded_key_size)]
    
    @classmethod
    def set_constants(cls):
        if(WORDSIZE == 4) :  cls.decollision = dec_vec_16
        if(WORDSIZE == 6) :  cls.decollision = dec_vec_24
        if(WORDSIZE == 8) :  cls.decollision = dec_vec_32
        if(WORDSIZE == 16) : cls.decollision = dec_vec_64
        if(WORDSIZE == 32) : cls.decollision = dec_vec_128
        if(WORDSIZE == 64) : cls.decollision = dec_vec_256

    @classmethod
    def reinit_params(cls):
        #cls.ks_num_rounds = SCHEDULE_NROUNDS   # 4
        #cls.KEYLEN = cls.num_columns 
        #cls.expanded_key_size = cls.num_columns * 2
        
        if(cls.ks_num_rounds  < 1): 
            cls.KEYLEN = cls.num_columns * 2
            cls.expanded_key_size = cls.num_columns * 2
        if(cls.ks_num_rounds == 1):
            cls.KEYLEN = cls.num_columns
            cls.expanded_key_size = cls.num_columns
        if(cls.ks_num_rounds  > 1): 
            cls.KEYLEN = cls.num_columns
            cls.expanded_key_size = cls.num_columns * 2
            
        cls.input_widths  = [WORDSIZE for _ in range(cls.KEYLEN)] 
        cls.output_widths = [WORDSIZE for _ in range(cls.expanded_key_size)]
    
    @classmethod
    def set_num_rounds(cls, new_num_rounds):
        cls.ks_num_rounds = SCHEDULE_NROUNDS  # 4
        if(new_num_rounds == 1):
            cls.ks_num_rounds = 1
        cls.reinit_params()
    
    @classmethod
    def pdsbox_arx(cls, i, m, s):
        if(DEBUG_OUTS): print("pdsbox_arx transform:", end = " ")
        row_state = [0 for _ in range(len(s))]
        y = 0
        decollision = cls.decollision
        
        for j in range(cls.Nrows):
            jj = (i+j) % cls.Nrows
            ms = m[i] ^ s[jj]
            msd = ms ^ decollision[i][j]
            row_state[j] = funcARX(msd, j, decollision[i+4][j])
            y ^= row_state[j]
        
        for j in range(cls.Nrows):
            row_state[j] ^= y
        
        if(DEBUG_OUTS): print("s* = ", row_state)
        
        return y, row_state
        
    @classmethod
    def transform_round(cls, m, internal_state):
        if(DEBUG_OUTS): print("*** transform_round ***")
        
        merged_state = [0 for _ in range(cls.Nrows)]
        c = [0 for _ in range(cls.num_columns)]
        
        for i in range(cls.num_columns):
            s = internal_state[i]
            c[i], internal_state[i] = cls.pdsbox_arx(i, m, s)    # PDSBOX FUNC
            for j in range(cls.Nrows):
                jj = (i+j) % cls.Nrows
                merged_state[jj] ^= internal_state[i][j]
                
        for i in range(cls.num_columns):
            for j in range(cls.Nrows):
                jj = (i+j) % cls.Nrows
                internal_state[i][j] ^= merged_state[jj]
        
        return c, internal_state
    
    @classmethod
    def eval(cls, *master_key):
        
        if(SCHEDULE_NROUNDS == 0):
            print("key schedule is disabled!")
            expanded_key = [None for _ in range(cls.expanded_key_size)]
            idx = 0
            for i in range(len(expanded_key)):
                expanded_key[i] = master_key[idx]
                idx = (idx+1) % len(master_key)
            return expanded_key
        
        cls.set_constants()
        
        if(SHOW_CAPTION == 1):
            print("<><><><><><><><><><><><><><><><><><>")
            print("key schedule: pCollapserARX_full")
            print("max NROUNDS = ", NROUNDS)
            print("NCOLUMNS = ", NCOLUMNS)
            print("NROWS = ", NROWS)
            print("WORDSIZE = ", end = " ")
            print(WORDSIZE, end = " ")
            print(", bits")
            print("Block Size = ", end = " ")
            print(NCOLUMNS*WORDSIZE, end = " ")
            print(", bits")
            print("SCHEDULE_NROUNDS = ", SCHEDULE_NROUNDS)
            print("MASTER_KEY_SIZE  = ", len(master_key)*WORDSIZE, ", bits" )
            print("<><><><><><><><><><><><><><><><><><>")
       
        expanded_key = [Constant(0, WORDSIZE) for _ in range(cls.expanded_key_size)]
        
        m = [Constant(0, WORDSIZE) for _ in range(cls.Nrows)]
        s = [Constant(0, WORDSIZE) for _ in range(cls.Nrows)]
        
        internal_state = [[Constant(0, WORDSIZE) for _ in range(cls.Nrows)] for _ in range(cls.num_columns)]
        
        for i in range(cls.num_columns):
            m[i] = master_key[i]
            s[i] = master_key[i]
        
        idx = 0
        for r in range(cls.ks_num_rounds):
            if(DEBUG_OUTS):
                print("##########")
                print("key-schedule round: ", r)

            if(r == 1 and INJECT_TO_STATE == 1):  
                for i in range(cls.num_columns):
                    for j in range(cls.Nrows):
                        internal_state[i][j] ^= s[j]    # inject additional control state    
            
            if(DEBUG_OUTS):
                print("m = ", m)
                print("s = ", s)
                print("internal_state = ", internal_state)
            
            m, internal_state = cls.transform_round(m, internal_state)      # MAIN ROUND FUNC
            
            if(r >= cls.ks_num_rounds-2):
                for i in range(cls.num_columns): 
                    expanded_key[idx] = m[i]     # take last two outs as a first and second parts of the expanded_key
                    idx = idx+1                 
            
            if(DEBUG_OUTS):
                print("c = ", end = " ")
                print(m)      
            #cls.add_round_outputs(m)
            
        #for i in range(cls.num_columns): 
        #    expanded_key[idx] = master_key[i]     # take last two outs as a first and second parts of the expanded_key
        #    idx = idx+1
                    
        if(DEBUG_OUTS): print("expanded_key maked in schedule: ", expanded_key)
        
        return expanded_key
    
    @classmethod
    def test(cls):
        """Test the key-schedule."""
        old_num_rounds = cls.num_rounds
        cls.set_num_rounds(4)
        
        test_vectors = [  # masterkey, w[i]
            [   "01234567",
                ["0123456711111111",
                 "0123456711111111",
                 "0123456711111111",
                 "0123456711111111"]
            ]
        ]
        for masterkey, list_word_keys in test_vectors:
            masterkey = _hex2nibble_list(masterkey)
            round_keys = tuple(itertools.chain.from_iterable([_hex2nibble_list(w) for w in list_word_keys]))
            print("round_keys from string", end = " ")
            print(round_keys)
            print("input masterkey", end = " ")
            print(masterkey)            
            result = cls(*masterkey)
            print("round_keys from shedule", end = " ")
            print(result)
            assert result == round_keys, f"\n{cls.get_name()}({masterkey}):\n{result}\nexpected:\n{round_keys}"
            print("end test")
        
        cls.set_num_rounds(old_num_rounds)    

####################################################################################################

class pcollapserARXencryption(Encryption, RoundBasedFunction):
    
    num_rounds = NROUNDS	# 4
    num_rows = NROWS		# 4
    num_columns = NCOLUMNS	# 4
    cell_width = WORDSIZE
    word_width = WORDSIZE
    Nrows = num_rows
    
    @classmethod
    def set_constants(cls):
        if(WORDSIZE == 4) :  cls.decollision = dec_vec_16
        if(WORDSIZE == 6) :  cls.decollision = dec_vec_24
        if(WORDSIZE == 8) :  cls.decollision = dec_vec_32
        if(WORDSIZE == 16) : cls.decollision = dec_vec_64
        if(WORDSIZE == 32) : cls.decollision = dec_vec_128
        if(WORDSIZE == 64) : cls.decollision = dec_vec_256
        
    internal_state = [[Constant(0, WORDSIZE) for _ in range(NROWS)] for _ in range(NCOLUMNS)]
    
    @classmethod
    @property
    def input_widths(cls):
        return [WORDSIZE for _ in range(cls.num_columns)]  
    
    @classmethod
    @property
    def output_widths(cls):
        return [WORDSIZE for _ in range(cls.num_columns)]
    
    @classmethod
    def set_num_rounds(cls, new_num_rounds):
        assert cls.num_rounds is not None
        cls.num_rounds = new_num_rounds
    
    @classmethod
    def pdsbox_arx(cls, i, m, s):
        if(DEBUG_OUTS): print("pdsbox_arx transform:", end = " ")
        row_state = [0 for _ in range(len(s))]
        y = 0
        decollision = cls.decollision
        
        for j in range(cls.Nrows):
            jj = (i+j) % cls.Nrows;
            ms = m[i] ^ s[jj]
            msd = ms ^ decollision[i][j]
            row_state[j] = funcARX(msd, j, decollision[i+4][j])
            y ^= row_state[j]
        
        for j in range(cls.Nrows):
            row_state[j] ^= y
        
        if(DEBUG_OUTS): print("s* = ",row_state)
        
        return y, row_state
    
    
    @classmethod
    def transform_round(cls, m, internal_state):
        if(DEBUG_OUTS): print("*** transform_round ***")
        
        merged_state = [0 for _ in range(cls.Nrows)]
        c = [0 for _ in range(cls.num_columns)]
        
        for i in range(cls.num_columns):
            s = internal_state[i]
            
            c[i], internal_state[i] = cls.pdsbox_arx(i, m, s)
            
            for j in range(cls.Nrows):
                jj = (i+j) % cls.Nrows
                merged_state[jj] ^= internal_state[i][j]
        
        for i in range(cls.num_columns):
            for j in range(cls.Nrows):
                jj = (i+j) % cls.Nrows
                internal_state[i][j]  ^= merged_state[jj]
        
        return c, internal_state
    
    @classmethod
    def eval(cls, *plaintext):
        
        cls.set_constants()     # set constants (decollision vector)
        
        if(SHOW_CAPTION == 1):
            print("<><><><><><><><><><><><><><><><><><>")
            print("type of PRF: pCollapserARX_full")
            print("max NROUNDS = ", NROUNDS)
            print("NCOLUMNS = ", NCOLUMNS)
            print("NROWS = ", NROWS)
            print("WORDSIZE = ", end = " ")
            print(WORDSIZE, end = " ")
            print(", bits")
            print("Block Size = ", end = " ")
            print(NCOLUMNS*WORDSIZE, end = " ")
            print(", bits")
            print("<><><><><><><><><><><><><><><><><><>")
        
        m = [Constant(0, WORDSIZE) for _ in range(cls.Nrows)]
        #for i in range(cls.num_columns):
        #    m[i] = plaintext[i]        
        s = [Constant(0, WORDSIZE) for _ in range(cls.Nrows)]
        internal_state = [[Constant(0, WORDSIZE) for _ in range(cls.Nrows)] for _ in range(cls.num_columns)]
        
        expanded_key = cls.round_keys
        if(DEBUG_OUTS): print("expanded_key: ", expanded_key)
        
        m[0] = plaintext[0] ^ expanded_key[0]
        m[1] = plaintext[1] ^ expanded_key[1]
        m[2] = plaintext[2] ^ expanded_key[2]
        m[3] = plaintext[3] ^ expanded_key[3]
        
        if(len(expanded_key) == 8):
            s[0] = plaintext[0] ^ expanded_key[4]
            s[1] = plaintext[1] ^ expanded_key[5]
            s[2] = plaintext[2] ^ expanded_key[6]
            s[3] = plaintext[3] ^ expanded_key[7]         
        #s[0] = m[0]
        #s[1] = m[1]
        #s[2] = m[2]
        #s[3] = m[3]        
        
        for r in range(cls.num_rounds):
            if(DEBUG_OUTS):
                print("##########")
                print("round: ", r)
            
            #if r == 1:
            #    m[0] = m[0] ^ expanded_key[4]
            #    m[1] = m[1] ^ expanded_key[5]
            #    m[2] = m[2] ^ expanded_key[6]
            #    m[3] = m[3] ^ expanded_key[7]                
            
            if(r == 1 and INJECT_TO_STATE == 1):  
                for i in range(cls.num_columns):
                    for j in range(cls.Nrows):
                        internal_state[i][j] ^= s[j]    # inject additional control state
            
            if(DEBUG_OUTS):
                print("m = ", m)
                print("s = ", s)
                print("internal_state = ", internal_state)
            
            m, internal_state = cls.transform_round(m, internal_state)
            
            if(DEBUG_OUTS): print("c = ", m)
            
            cls.add_round_outputs(m)
        return m

####################################################################################################

class pcollapserARXcipher(Cipher):
    """The block cipher pcollapserLWC."""
    key_schedule = pcollpaserARX_KeySchedule
    encryption = pcollapserARXencryption
    #word_width = WORDSIZE
    #SCHEDULE_NROUNDS = 4
    
    @classmethod
    def set_num_rounds(cls, new_num_rounds):
        cls.key_schedule.set_num_rounds(new_num_rounds)
        cls.encryption.set_num_rounds(new_num_rounds)
    
    @classmethod
    def test(cls):
        old_num_rounds = cls.num_rounds
        cls.set_num_rounds(4)
        word_width = WORDSIZE
        
        print("Block_size = ", word_width*4, ", bit")
        
        test_vectors = []
        
        if(word_width == 4):    # block_size = 16 bit 
            test_vectors = [  # key, plaintext, ciphertext
                [[0x0, 0x0, 0x0, 0x0], [0x0, 0x0, 0x0, 0x0], [0xa, 0xa, 0x8, 0xc]],
                [[0x1, 0x2, 0x3, 0x4], [0x5, 0x6, 0x7, 0x0], [0xc, 0x4, 0xf, 0x7]]
            ]
        
        if(word_width == 6):    # block_size = 24 bit 
            test_vectors = [  # key, plaintext, ciphertext
                [[0x00, 0x00, 0x00, 0x00], [0x00, 0x00, 0x00, 0x00], [0b100011, 0b010010, 0b111011, 0b000010]],
                [[0x01, 0x02, 0x03, 0x04], [0x05, 0x06, 0x07, 0x08], [0b100000, 0b100101, 0b001110, 0b000100]]
            ]
        
        if(word_width == 8):    # block_size = 32 bit 
            test_vectors = [  # key, plaintext, ciphertext
                [[0x00, 0x00, 0x00, 0x00], [0x00, 0x00, 0x00, 0x00], [0x3F, 0xDF, 0x7A, 0x16]],
                [[0x01, 0x02, 0x03, 0x04], [0x05, 0x06, 0x07, 0x08], [0x87, 0x5b, 0x29, 0x09]]
            ]
        
        if(word_width == 16):    # block_size = 64 bit 
            test_vectors = [  # key, plaintext, ciphertext
                [[0x00, 0x00, 0x00, 0x00], [0x00, 0x00, 0x00, 0x00], [0xf261, 0xae4f, 0xe729, 0x3fc1]],
                [[0x01, 0x02, 0x03, 0x04], [0x05, 0x06, 0x07, 0x08], [0xa6c2, 0x5964, 0x0cb7, 0x08a1]]
            ]
        
        if(word_width == 32):    # block_size = 128 bit 
            test_vectors = [  # key, plaintext, ciphertext
                [[0x00, 0x00, 0x00, 0x00], [0x00, 0x00, 0x00, 0x00], [0x8bd15782, 0xe5934be9, 0x46797a96, 0xc41721e0]],
                [[0x01, 0x02, 0x03, 0x04], [0x05, 0x06, 0x07, 0x08], [0xa498d44b, 0x04d90dd4, 0xbf9214c1, 0xda32a999]]
            ]
        
        if(word_width == 64):    # block_size = 256 bit 
            test_vectors = [  # key, plaintext, ciphertext
                [[0x00, 0x00, 0x00, 0x00], [0x00, 0x00, 0x00, 0x00], [0xc27af7aad5983c7c, 0xd4e76c6b43b032b7, 0x817de56e7930d172, 0xae975d330832d135]],
                [[0x01, 0x02, 0x03, 0x04], [0x05, 0x06, 0x07, 0x08], [0x5df174d6f90ab602, 0x79641011ff883c70, 0xda74ba907096dff5, 0x829616dc693a1d1f]]
            ]
        
        idx = 0
        test_vectors_hex = []
        for test_vec in test_vectors:
            test_vectors_hex.append([ [Constant(t, word_width) for t in test_vec[0]], [Constant(t, word_width) for t in test_vec[1]], [Constant(t, word_width) for t in test_vec[2]] ])
        #print("test vector:", test_vectors_hex)
        
        print("--------")
        for key, plaintext, ciphertext in test_vectors_hex:
            result = list(cls(plaintext, key))
            print("test vector: (key, plaintext, ciphertext)")
            print(key, plaintext, ciphertext)
            print("result   = ", result)
            print("expected = ", ciphertext)
            print("--------")
            assert result == ciphertext, \
                f"{cls.get_name()}({plaintext}, {key}):\n{result}\nexpected:\n{ciphertext}"
        
        cls.set_num_rounds(old_num_rounds)
        
####################################################################################################
def verify_prf_implementation():
    global WORDSIZE
    
    test_word_sizes = [4, 6, 8, 16, 32, 64]
    for ws in test_word_sizes:
        print("########### verify pCollapserARX implementation ###########")
        WORDSIZE = ws
        pcollapserARXcipher.test()
    
####################################################################################################
