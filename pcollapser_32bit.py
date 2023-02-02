### pcollapserLWC-32
### Copyright (c) 2022 Polikarpov S.V., Prudnikov V.A.
### Southern Federal University,
### Russia, Taganrog
### MIT License

DEBUG_OUTS = 0
DEBUG_OUTS2 = 0

DIFF_MODEL_TYPE   = 1		# 1 - weak model,  2 - ddt model
LINEAR_MODEL_TYPE = 1		# 1 - weak model,  2 - lat model

NROUNDS		= 4
NCOLUMNS	= 8
NROWS		= 4 
WORDSIZE    = 4

NCELLS = 1 << WORDSIZE

import sys
sys.setrecursionlimit(100000)  

import itertools
import enum
from decimal import Decimal
from math import inf
import random

from cascada.bitvector.core import Constant, Term, Variable, bitvectify
from cascada.bitvector.operation import BvComp, BvNot
from cascada.bitvector.context import Memoization
from cascada.abstractproperty.property import make_partial_propextract
from cascada.bitvector.operation import RotateLeft, RotateRight
from cascada.bitvector.operation import Concat

from cascada.abstractproperty.opmodel import log2_decimal
from cascada.differential.opmodel import get_wdt_model as get_differential_wdt_model
from cascada.linear.opmodel import get_wdt_model as get_linear_wdt_model

from cascada.bitvector.secondaryop import LutOperation, MatrixOperation
from cascada.bitvector.ssa import RoundBasedFunction
from cascada.differential.difference import XorDiff
from cascada.differential.opmodel import get_weak_model as get_differential_weak_model
from cascada.differential.opmodel import get_branch_number_model as get_differential_branch_number_model
from cascada.linear.opmodel import get_weak_model as get_linear_weak_model
from cascada.linear.opmodel import get_branch_number_model as get_linear_branch_number_model
from cascada.primitives.blockcipher import Encryption, Cipher

from datetime import datetime

now = datetime.now()
# dd/mm/YY H:M:S
dt_string = now.strftime("%d/%m/%Y %H:%M:%S")

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

    
### sboxes PI
pi = [    
[8, 2, 12, 1, 11, 9, 13, 3, 7, 14, 15, 10, 5, 6, 4, 0],
[2, 8, 10, 15, 11, 9, 4, 0, 14, 7, 1, 12, 5, 6, 13, 3],
[3, 14, 7, 13, 10, 9, 11, 15, 12, 5, 6, 1, 4, 8, 2, 0],
[5, 2, 9, 7, 12, 0, 10, 13, 11, 14, 6, 8, 15, 3, 1, 4]
]
### luts for PI

class PiLut0(LutOperation): #The 4-bit S-box of pcollapserLWC.
	lut = [Constant(x, 4) for x in pi[0]]

class PiLut1(LutOperation): #The 4-bit S-box of pcollapserLWC.
	lut = [Constant(x, 4) for x in pi[1]]

class PiLut2(LutOperation): #The 4-bit S-box of pcollapserLWC.
	lut = [Constant(x, 4) for x in pi[2]]

class PiLut3(LutOperation): #The 4-bit S-box of pcollapserLWC.
	lut = [Constant(x, 4) for x in pi[3]]

### models for PI

if(DIFF_MODEL_TYPE == 1):
	if(DEBUG_OUTS): print("### Use differential_weak_model")
	PiLut0.xor_model = get_differential_weak_model(PiLut0, XorDiff, 1)
	PiLut1.xor_model = get_differential_weak_model(PiLut1, XorDiff, 1)
	PiLut2.xor_model = get_differential_weak_model(PiLut2, XorDiff, 1)
	PiLut3.xor_model = get_differential_weak_model(PiLut3, XorDiff, 1)

if(LINEAR_MODEL_TYPE == 1):
	if(DEBUG_OUTS): print("### Use linear_weak_model")
	PiLut0.linear_model = get_linear_weak_model(PiLut0, 1)
	PiLut1.linear_model = get_linear_weak_model(PiLut1, 1)
	PiLut2.linear_model = get_linear_weak_model(PiLut2, 1)
	PiLut3.linear_model = get_linear_weak_model(PiLut3, 1)

#Differentials for component sbox N0:
ddt0 = [
	[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0],
	[0, 2, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0],
	[0, 2, 4, 2, 0, 0, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0],
	[0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4],
	[0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0],
	[0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 4, 2, 0, 0, 0, 4],
	[0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4],
	[0, 0, 0, 0, 0, 2, 4, 2, 0, 0, 0, 0, 2, 4, 2, 0],
	[0, 0, 0, 0, 0, 2, 0, 2, 4, 2, 0, 2, 0, 0, 0, 4],
	[0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0],
	[0, 2, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 2, 2, 0, 0],
	[0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0],
	[0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0]
]

ddt1 = [
	[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0],
	[0, 0, 0, 0, 0, 2, 0, 2, 4, 2, 0, 2, 0, 0, 0, 4],
	[0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0],
	[0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4],
	[0, 2, 4, 2, 0, 0, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0],
	[0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0],
	[0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4],
	[0, 0, 0, 0, 0, 2, 4, 2, 0, 0, 0, 0, 2, 4, 2, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0],
	[0, 2, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0],
	[0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0],
	[0, 2, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 2, 2, 0, 0],
	[0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 4, 2, 0, 0, 0, 4],
	[0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0]
]

ddt2 = [
	[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0],
	[0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0],
	[0, 2, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 2, 2, 0, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0],
	[0, 2, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0],
	[0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0],
	[0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4],
	[0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0],
	[0, 0, 0, 0, 0, 2, 0, 2, 4, 2, 0, 2, 0, 0, 0, 4],
	[0, 2, 4, 2, 0, 0, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 2, 4, 2, 0, 0, 0, 0, 2, 4, 2, 0],
	[0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 4, 2, 0, 0, 0, 4],
	[0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0],
	[0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4]
]

ddt3 = [
	[16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0],
	[0, 0, 0, 0, 0, 2, 4, 2, 0, 0, 0, 0, 2, 4, 2, 0],
	[0, 2, 4, 2, 0, 0, 0, 0, 2, 0, 2, 4, 0, 0, 0, 0],
	[0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0],
	[0, 2, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 2, 0],
	[0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 4, 2, 0, 0, 0, 4],
	[0, 0, 0, 0, 0, 2, 0, 2, 4, 2, 0, 2, 0, 0, 0, 4],
	[0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4],
	[0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 4],
	[0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0],
	[0, 2, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 2, 2, 0, 0],
	[0, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0],
	[0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 4, 0, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0],
	[0, 2, 0, 2, 4, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 0]
]

lat0 = [
[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
[0, -1/4, 1/4, 1/2, -1/2, 1/4, -1/4, 0, -1/4, 0, 0, -1/4, -1/4, 0, 0, -1/4],
[0, 0, -1/4, -1/4, 0, 0, 1/4, 1/4, 0, 0, -1/4, -1/4, -1/2, 1/2, -1/4, -1/4],
[0, -1/4, 0, 1/4, 1/2, 1/4, 0, 1/4, 1/4, -1/2, 1/4, 0, -1/4, 0, 1/4, 0],
[0, 1/4, -1/4, 0, 0, 1/4, 1/4, -1/2, -1/4, -1/2, 0, -1/4, 1/4, 0, 0, -1/4],
[0, 0, 0, 1/2, 0, 0, 1/2, 0, 0, 0, -1/2, 0, 0, 0, 0, 1/2],
[0, 1/4, 0, 1/4, 0, 1/4, 0, 1/4, 1/4, 0, -1/4, 1/2, 1/4, 0, -1/4, -1/2],
[0, 0, 1/4, -1/4, 0, 0, 1/4, -1/4, 0, 0, -1/4, 1/4, -1/2, -1/2, 1/4, -1/4],
[0, -1/4, 1/4, 0, 1/2, -1/4, -1/4, 0, -1/4, 0, -1/2, -1/4, 1/4, 0, 0, -1/4],
[0, 1/2, 0, 0, 0, 0, 0, 1/2, -1/2, 0, 0, 0, 0, 0, 1/2, 0],
[0, 1/4, 0, 1/4, 1/2, 1/4, 0, -1/4, -1/4, 1/2, 1/4, 0, -1/4, 0, -1/4, 0],
[0, 0, -1/4, 1/4, 0, -1/2, 1/4, 1/4, 0, 0, 1/4, -1/4, 0, -1/2, -1/4, -1/4],
[0, 1/2, 1/2, 0, 0, 0, 0, 0, 1/2, 0, 0, -1/2, 0, 0, 0, 0],
[0, 1/4, 1/4, 0, 0, -1/4, -1/4, 0, -1/4, -1/2, 0, 1/4, -1/4, 0, -1/2, 1/4],
[0, 0, -1/4, -1/4, 0, 1/2, -1/4, 1/4, 0, 0, -1/4, -1/4, 0, -1/2, -1/4, 1/4],
[0, -1/4, 1/2, -1/4, 0, 1/4, 1/2, 1/4, -1/4, 0, 1/4, 0, 1/4, 0, -1/4, 0],
]

lat1 = [
[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
[0, 0, 0, -1/2, 0, 0, -1/2, 0, 0, 0, 1/2, 0, 0, 0, 0, -1/2],
[0, 0, -1/4, -1/4, 0, 0, 1/4, 1/4, 0, 0, -1/4, -1/4, -1/2, 1/2, -1/4, -1/4],
[0, 0, -1/4, 1/4, 0, 0, -1/4, 1/4, 0, 0, 1/4, -1/4, 1/2, 1/2, -1/4, 1/4],
[0, 1/4, -1/4, 0, 0, 1/4, 1/4, -1/2, -1/4, -1/2, 0, -1/4, 1/4, 0, 0, -1/4],
[0, 1/4, -1/4, -1/2, 1/2, -1/4, 1/4, 0, 1/4, 0, 0, 1/4, 1/4, 0, 0, 1/4],
[0, 1/4, 0, 1/4, 0, 1/4, 0, 1/4, 1/4, 0, -1/4, 1/2, 1/4, 0, -1/4, -1/2],
[0, 1/4, 0, -1/4, -1/2, -1/4, 0, -1/4, -1/4, 1/2, -1/4, 0, 1/4, 0, -1/4, 0],
[0, 1/4, 0, 1/4, 1/2, 1/4, 0, -1/4, -1/4, 1/2, 1/4, 0, -1/4, 0, -1/4, 0],
[0, 1/4, -1/2, 1/4, 0, -1/4, -1/2, -1/4, 1/4, 0, -1/4, 0, -1/4, 0, 1/4, 0],
[0, -1/4, 1/4, 0, 1/2, -1/4, -1/4, 0, -1/4, 0, -1/2, -1/4, 1/4, 0, 0, -1/4],
[0, -1/4, -1/4, 0, 0, 1/4, 1/4, 0, 1/4, 1/2, 0, -1/4, 1/4, 0, 1/2, -1/4],
[0, 0, -1/4, -1/4, 0, 1/2, -1/4, 1/4, 0, 0, -1/4, -1/4, 0, -1/2, -1/4, 1/4],
[0, 0, 1/4, -1/4, 0, 1/2, -1/4, -1/4, 0, 0, -1/4, 1/4, 0, 1/2, 1/4, 1/4],
[0, 1/2, 1/2, 0, 0, 0, 0, 0, 1/2, 0, 0, -1/2, 0, 0, 0, 0],
[0, -1/2, 0, 0, 0, 0, 0, -1/2, 1/2, 0, 0, 0, 0, 0, -1/2, 0],
]

lat2 = [
[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
[0, 1/4, -1/2, 1/4, 0, -1/4, -1/2, -1/4, 1/4, 0, -1/4, 0, -1/4, 0, 1/4, 0],
[0, 1/4, 1/4, 0, 0, -1/4, -1/4, 0, -1/4, -1/2, 0, 1/4, -1/4, 0, -1/2, 1/4],
[0, 0, 1/4, 1/4, 0, 0, -1/4, -1/4, 0, 0, 1/4, 1/4, 1/2, -1/2, 1/4, 1/4],
[0, -1/4, 0, -1/4, -1/2, -1/4, 0, 1/4, 1/4, -1/2, -1/4, 0, 1/4, 0, 1/4, 0],
[0, 0, 0, 1/2, 0, 0, 1/2, 0, 0, 0, -1/2, 0, 0, 0, 0, 1/2],
[0, 0, -1/4, 1/4, 0, 0, -1/4, 1/4, 0, 0, 1/4, -1/4, 1/2, 1/2, -1/4, 1/4],
[0, -1/4, 1/4, 0, 1/2, -1/4, -1/4, 0, -1/4, 0, -1/2, -1/4, 1/4, 0, 0, -1/4],
[0, -1/2, -1/2, 0, 0, 0, 0, 0, -1/2, 0, 0, 1/2, 0, 0, 0, 0],
[0, -1/4, 0, 1/4, 1/2, 1/4, 0, 1/4, 1/4, -1/2, 1/4, 0, -1/4, 0, 1/4, 0],
[0, 1/4, -1/4, -1/2, 1/2, -1/4, 1/4, 0, 1/4, 0, 0, 1/4, 1/4, 0, 0, 1/4],
[0, 0, -1/4, -1/4, 0, 1/2, -1/4, 1/4, 0, 0, -1/4, -1/4, 0, -1/2, -1/4, 1/4],
[0, 1/4, 0, 1/4, 0, 1/4, 0, 1/4, 1/4, 0, -1/4, 1/2, 1/4, 0, -1/4, -1/2],
[0, -1/2, 0, 0, 0, 0, 0, -1/2, 1/2, 0, 0, 0, 0, 0, -1/2, 0],
[0, 0, -1/4, 1/4, 0, -1/2, 1/4, 1/4, 0, 0, 1/4, -1/4, 0, -1/2, -1/4, -1/4],
[0, -1/4, 1/4, 0, 0, -1/4, -1/4, 1/2, 1/4, 1/2, 0, 1/4, -1/4, 0, 0, 1/4],
]

lat3 = [
[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
[0, -1/4, 0, -1/4, 0, -1/4, 0, -1/4, -1/4, 0, 1/4, -1/2, -1/4, 0, 1/4, 1/2],
[0, 0, -1/4, 1/4, 0, 0, -1/4, 1/4, 0, 0, 1/4, -1/4, 1/2, 1/2, -1/4, 1/4],
[0, -1/4, 1/4, 1/2, -1/2, 1/4, -1/4, 0, -1/4, 0, 0, -1/4, -1/4, 0, 0, -1/4],
[0, 0, -1/4, -1/4, 0, 0, 1/4, 1/4, 0, 0, -1/4, -1/4, -1/2, 1/2, -1/4, -1/4],
[0, -1/4, 1/4, 0, 0, -1/4, -1/4, 1/2, 1/4, 1/2, 0, 1/4, -1/4, 0, 0, 1/4],
[0, 0, 0, -1/2, 0, 0, -1/2, 0, 0, 0, 1/2, 0, 0, 0, 0, -1/2],
[0, -1/4, 0, 1/4, 1/2, 1/4, 0, 1/4, 1/4, -1/2, 1/4, 0, -1/4, 0, 1/4, 0],
[0, 0, 1/4, -1/4, 0, 1/2, -1/4, -1/4, 0, 0, -1/4, 1/4, 0, 1/2, 1/4, 1/4],
[0, 1/4, 1/4, 0, 0, -1/4, -1/4, 0, -1/4, -1/2, 0, 1/4, -1/4, 0, -1/2, 1/4],
[0, 1/2, 1/2, 0, 0, 0, 0, 0, 1/2, 0, 0, -1/2, 0, 0, 0, 0],
[0, -1/4, 0, -1/4, -1/2, -1/4, 0, 1/4, 1/4, -1/2, -1/4, 0, 1/4, 0, 1/4, 0],
[0, -1/2, 0, 0, 0, 0, 0, -1/2, 1/2, 0, 0, 0, 0, 0, -1/2, 0],
[0, -1/4, 1/2, -1/4, 0, 1/4, 1/2, 1/4, -1/4, 0, 1/4, 0, 1/4, 0, -1/4, 0],
[0, 0, -1/4, -1/4, 0, 1/2, -1/4, 1/4, 0, 0, -1/4, -1/4, 0, -1/2, -1/4, 1/4],
[0, 1/4, -1/4, 0, -1/2, 1/4, 1/4, 0, 1/4, 0, 1/2, 1/4, -1/4, 0, 0, 1/4],
]

### weight models for PI

if(DIFF_MODEL_TYPE == 2):
	if(DEBUG_OUTS): print("### Use differential_wdt_model")
	PiLut0.xor_model = get_differential_wdt_model(
		PiLut0, XorDiff, tuple([tuple(inf if x == 0 else -log2_decimal(x / Decimal(2 ** 4)) for x in row) for row in ddt0]))
	PiLut1.xor_model = get_differential_wdt_model(
		PiLut1, XorDiff, tuple([tuple(inf if x == 0 else -log2_decimal(x / Decimal(2 ** 4)) for x in row) for row in ddt1]))
	PiLut2.xor_model = get_differential_wdt_model(
		PiLut2, XorDiff, tuple([tuple(inf if x == 0 else -log2_decimal(x / Decimal(2 ** 4)) for x in row) for row in ddt2]))
	PiLut3.xor_model = get_differential_wdt_model(
		PiLut3, XorDiff, tuple([tuple(inf if x == 0 else -log2_decimal(x / Decimal(2 ** 4)) for x in row) for row in ddt3]))


if(LINEAR_MODEL_TYPE == 2):
	if(DEBUG_OUTS): print("### Use linear_wdt_model")
	PiLut0.linear_model = get_linear_wdt_model(
		PiLut0, tuple([tuple(inf if x == 0 else -log2_decimal(Decimal(abs(x))) for x in row) for row in lat0]))
	PiLut0.linear_model.precision = 0
	PiLut1.linear_model = get_linear_wdt_model(
		PiLut1, tuple([tuple(inf if x == 0 else -log2_decimal(Decimal(abs(x))) for x in row) for row in lat1]))
	PiLut1.linear_model.precision = 0
	PiLut2.linear_model = get_linear_wdt_model(
		PiLut2, tuple([tuple(inf if x == 0 else -log2_decimal(Decimal(abs(x))) for x in row) for row in lat2]))
	PiLut2.linear_model.precision = 0
	PiLut3.linear_model = get_linear_wdt_model(
		PiLut3, tuple([tuple(inf if x == 0 else -log2_decimal(Decimal(abs(x))) for x in row) for row in lat3]))
	PiLut3.linear_model.precision = 0


class pcollpaser_KeySchedule(RoundBasedFunction):
    """Key schedule function."""
    
    num_rounds = 4
    input_widths = [WORDSIZE for _ in range(NCOLUMNS)]
    output_widths = [WORDSIZE for _ in range(num_rounds*NCOLUMNS)]
    
    @classmethod
    def set_num_rounds(cls, new_num_rounds):
        cls.num_rounds = new_num_rounds
        cls.output_widths = [WORDSIZE for _ in range(cls.num_rounds*NCOLUMNS)]
    
    @classmethod
    def eval(cls, *master_key):
        round_keys = [0 for _ in range(cls.num_rounds*NCOLUMNS)]
        for r in range(cls.num_rounds):
            for i in range(len(master_key)):
                round_keys[r*len(master_key)+i] = master_key[i]
        print("round_keys maked in shedule", end = " ")
        print(round_keys)        
        return round_keys
    
    @classmethod
    def test(cls):
        """Test the key-schedule."""
        old_num_rounds = cls.num_rounds
        cls.set_num_rounds(4)
        
        test_vectors = [  # masterkey, w[i]
            [
                "01234567",
                ["01234567",
                 "01234567",
                 "01234567",
                 "01234567"]
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


class pcollapserEncryption(Encryption, RoundBasedFunction):
    
    num_rounds = NROUNDS	
    num_rows = NROWS		
    num_columns = NCOLUMNS	
    cell_width = 4
    word_width = 4
    Nrows = num_rows
    
    pi_lut = [ PiLut0, PiLut1, PiLut2, PiLut3 ]
    
    decollision_vector = [             
        [Constant(d_i, 4) for d_i in [7, 1, 4, 11]], 
        [Constant(d_i, 4) for d_i in [5, 4, 14, 10]], 
        [Constant(d_i, 4) for d_i in [5, 2, 15, 8]], 
        [Constant(d_i, 4) for d_i in [12, 2, 7, 9]], 
        [Constant(d_i, 4) for d_i in [6, 9, 2, 14]], 
        [Constant(d_i, 4) for d_i in [5, 14, 5, 1]], 
        [Constant(d_i, 4) for d_i in [3, 7, 5, 1]], 
        [Constant(d_i, 4) for d_i in [4, 0, 7, 15]]
    ]    
    
    @classmethod
    @property
    def input_widths(cls):
        return [cls.cell_width for _ in range(cls.num_columns)]  
    
    @classmethod
    @property
    def output_widths(cls):
        return [cls.cell_width for _ in range(cls.num_columns)]
    
    @classmethod
    def set_num_rounds(cls, new_num_rounds):
        assert cls.num_rounds is not None
        cls.num_rounds = new_num_rounds        
    
    @classmethod
    def pdsbox_func(cls, i, m, s):
        if(DEBUG_OUTS): print("pdsbox_func ", end = " ")
        
        row_state = [0 for _ in range(cls.Nrows)]
        y = 0        
        
        for j in range(cls.Nrows):
            jj = (i+j) % cls.Nrows;
            ms = m[i] ^ s[jj];
            msd = ms ^ cls.decollision_vector[i][j]
            row_state[j] = cls.pi_lut[j]( msd )
            y ^= row_state[j]
        
        for j in range(cls.Nrows):
            row_state[j] ^= y
        
        if(DEBUG_OUTS): print("s* = ", end = " ")
        if(DEBUG_OUTS): print(row_state)
        
        return y, row_state
    
    
    @classmethod
    def transform_round_tinystate(cls, r, m, key, s):
        if(DEBUG_OUTS): print("*** transform_round_pcollapser ***")
        
        new_control_state = [0 for _ in range(cls.Nrows)]
        row_state = [0 for _ in range(cls.Nrows)]
        c = [0 for _ in range(cls.num_columns)]
        mmm = [0 for _ in range(cls.num_columns)]
        
        for i in range(cls.num_columns):
            mmm[i] = m[i] ^ key[i]
        
        for i in range(cls.num_columns):
            c[i], row_state = cls.pdsbox_func(i, mmm, s)
            for j in range(cls.Nrows):
                jj = (i+j) % cls.Nrows
                new_control_state[jj] ^= row_state[j]
        
        return c, new_control_state
    
    @classmethod
    def validateXorDiff(cls):
        print("Log started at : ", dt_string) 
        #2 : Ch(w=18.00, id=0 0 0 7 0 0 0 7, od=0 0 0 0 0 0 0 0)
        in_xordiff  = [Constant(d_i, 4) for d_i in [0, 0, 0, 7, 0, 0, 0, 7] ]
        #2 : Ch(w=8, id=0 0 8 8 0 0 0 0, od=0 0 0 0 0 0 0 0)    (weak_model)
        #in_xordiff  = [Constant(d_i, 4) for d_i in [0, 0, 8, 8, 0, 0, 0, 0] ]
        out_xordiff = [Constant(d_i, 4) for d_i in [0, 0, 0, 0, 0, 0, 0, 0] ]
        
        real_out_xordiff = [Constant(d_i, 4) for d_i in [0, 0, 0, 0, 0, 0, 0, 0] ]
        
        rk = [Constant(d_i, 4) for d_i in [0, 0, 0, 0, 0, 0, 0, 0] ]
        
        m0 = [Constant(d_i, 4) for d_i in [0, 0, 0, 0, 0, 0, 0, 0] ]
        s0 = [Constant(d_i, 4) for d_i in [0, 0, 0, 0] ]
        
        m1 = [Constant(d_i, 4) for d_i in [0, 0, 0, 0, 0, 0, 0, 0] ]
        s1 = [Constant(d_i, 4) for d_i in [0, 0, 0, 0] ]
        
        N = 2**22
        NR = 2
        Nwords = len(m0)
        
        #print("Nwords = ", end = "")
        #print(Nwords)
        
        print("id = ", end = "")
        print(in_xordiff)
        
        print("od = ", end = "")
        print(out_xordiff)
        
        cnt_eq = 0
        cnt_total = 0
        
        for tr in range(N):
            
            if(DEBUG_OUTS2): print(tr)
            
            for i in range(Nwords):
                rk[i] = random.randint(0x0, 0xf)
                m0[i] = random.randint(0x0, 0xf)
                m1[i] = m0[i] ^ in_xordiff[i]
                
            for i in range(len(s0)):
                s0[i] = 0
                s1[i] = 0
                
            if(DEBUG_OUTS2): 
                print(m0)
                print(m1)
                
            for r in range( NR ):
                m0, s0 = cls.transform_round_tinystate(r, m0, rk, s0)
                m1, s1 = cls.transform_round_tinystate(r, m1, rk, s1)
            
            cnt = 0
            
            for i in range(Nwords):
                real_out_xordiff[i] = m0[i] ^ m1[i]
                if(real_out_xordiff[i] == out_xordiff[i]): cnt = cnt + 1
            
            if(cnt == Nwords): 
                cnt_eq = cnt_eq + 1
                print("+", end = "")
                sys.stdout.flush()
            
            cnt_total = cnt_total + 1
            
            if(cnt_total % 4096 == 0) : 
                print(".", end = "")    # progress bar
                sys.stdout.flush()
            
            if(DEBUG_OUTS2): print(real_out_xordiff)
        print("\nout diff stats: cnt_eq / cnt_total = ", end = "")    
        print(cnt_eq, end = " / ")
        print(N)
        print("Log ended at : ", dt_string)
    
    @classmethod
    def eval(cls, *plaintext):
        
        if(DEBUG_OUTS): 
            print("Log started at : ", dt_string)        
            print("<><><><><><><><><><><><><><><><><><>")
            print("type of PRF: pCollapserLWC_32")
            print("max NROUNDS = ", end = " ")
            print(NROUNDS)
            print("NCOLUMNS = ", end = " ")
            print(NCOLUMNS)
            print("NROWS = ", end = " ")
            print(NROWS)
            print("WORDSIZE = ", end = " ")
            print(WORDSIZE, end = " ")
            print(", bits")
            print("Block Size = ", end = " ")
            print(NCOLUMNS*WORDSIZE, end = " ")
            print(", bits")
            print("<><><><><><><><><><><><><><><><><><>")
            
            print("DIFF_MODEL_TYPE =   ", end = " ")
            print(DIFF_MODEL_TYPE, end = " ")
            #if(DIFF_MODEL_TYPE == 0): print(" ('no sbox' model)") 
            if(DIFF_MODEL_TYPE == 1): print(" (weak model)") 
            if(DIFF_MODEL_TYPE == 2): print(" (wdt model)") 
            print("LINEAR_MODEL_TYPE = ", end = " ")
            print(LINEAR_MODEL_TYPE, end = " ")
            #if(LINEAR_MODEL_TYPE == 0): print(" ('no sbox' model)") 
            if(LINEAR_MODEL_TYPE == 1): print(" (weak model)") 
            if(LINEAR_MODEL_TYPE == 2): print(" (wdt model)")         
            print("<><><><><><><><><><><><><><><><><><>")        
        
        m = plaintext
        s = [Constant(0, WORDSIZE) for _ in range(cls.Nrows)]
        
        for r in range(cls.num_rounds):
            rkey = cls.round_keys[NCOLUMNS*r: NCOLUMNS*r + NCOLUMNS]
            
            if(DEBUG_OUTS): 
                print("##########")
                print("round = ", end = " ")
                print(r)
                print("rkey = ", end = " ")
                print(rkey)
                print("m = ", end = " ")
                print(m)
                print("s = ", end = " ")
                print(s)
            
            m, s = cls.transform_round_tinystate(r, m, rkey, s)
            
            if(DEBUG_OUTS):
                print("new_state = ", end = " ")
                print(s)  
                print("c = ", end = " ")
                print(m)                 
            
            cls.add_round_outputs(m) 
        return m


class pcollapserLWC_32bit(Cipher):
    """The PRF: pCollapserLWC_32"""
    key_schedule = pcollpaser_KeySchedule
    encryption   = pcollapserEncryption
    
    @classmethod
    def set_num_rounds(cls, new_num_rounds):
        cls.key_schedule.set_num_rounds(new_num_rounds)
        cls.encryption.set_num_rounds(new_num_rounds)
    
    @classmethod
    def test(cls):
        old_num_rounds = cls.num_rounds
        cls.set_num_rounds(4)
        
        test_vectors = [  # key, plaintext, ciphertext
            ["01234567", "00000000", "F42168E4"],
        ]
        
        for key, plaintext, ciphertext in test_vectors:
            key, plaintext, ciphertext = _hex2nibble_list(key), _hex2nibble_list(plaintext), tuple(_hex2nibble_list(ciphertext))
            result = cls(plaintext, key)
            assert result == ciphertext, \
                f"{cls.get_name()}({plaintext}, {key}):\n{result}\nexpected:\n{ciphertext}"
        
        cls.set_num_rounds(old_num_rounds)


from cascada.differential.difference import XorDiff, RXDiff
from cascada.smt.chsearch import ChModelAssertType, round_based_ch_search

def find_XorDiff_ch():        
    pcollapser = pcollapserLWC_32bit
    assert_type = ChModelAssertType.ValidityAndWeight
    iterator = round_based_ch_search(pcollapser, 2, 4, XorDiff, assert_type, "btor",
    extra_chfinder_args={"exclude_zero_input_prop": True, "solver_seed": 0},
    extra_findnextchweight_args={"initial_weight": 0})
    for (num_rounds, ch) in iterator:
        print(num_rounds, ":", ch.srepr())  

#from cascada.primitives import pcollapser_32bit
#pcollapser_32bit.find_XorDiff_ch()
#pcollapser_32bit.pcollapserEncryption.validateXorDiff()
