# CTCrypt2023
Scripts for research and verify encryption characteristics for the PRF pCollapserARX (with block size 32, 64, 128 and 256 bit) using SAT-solvers and framework CASCADA.
Сreated as part of a report at the CTCrypt2023 conference (https://ctcrypt.ru).

To run these scripts you need to install CASCADA framework:

    https://github.com/ranea/CASCADA

and copy files to the main CASCADA directory.    
    
Check internal help:

    python3.11 test_collapser.py --help

result:    
    
    usage: test_collapser.py [-h] [-b BLOCK_SIZE] [-f FIRST_ROUND] [-l LAST_ROUND] [-w STARTING_WEIGHT] [--ks-nrounds KS_NROUNDS] [--use-empirical-weights] [--show-debug-info]
                            [--show-ch-details]
                            type_of_analysis

    PRF pCollapserARX testing

    positional arguments:
    type_of_analysis      the type of analysis (linear, xordiff, rxdiff, related-xordiff, impossible-xordiff, impossible-rxdiff, zerocorellation, verify_implementation )

    options:
    -h, --help            show this help message and exit
    -b BLOCK_SIZE, --block-size BLOCK_SIZE
                            block size, bit (32, 64 or 128 - the lenght of in/out blocks) (default: 64)
    -f FIRST_ROUND, --first-round FIRST_ROUND
                            the number of the round from which the analysis starts (default: 1)
    -l LAST_ROUND, --last-round LAST_ROUND
                            the number of the round at which the analysis ends (default: 4)
    -w STARTING_WEIGHT, --starting-weight STARTING_WEIGHT
                            starting weight (default: 0)
    --ks-nrounds KS_NROUNDS
                            num of the key-schedule rounds (default: 0)
    --use-empirical-weights
                            using empirical weights calculation (only for block_size <= 24) (default: False)
    --show-debug-info     showing detailed debug info (default: False)
    --show-ch-details     showing detailed info about found Characteristic (default: False)

To verify implementation of the PRF pCollapserARX:

    python3.11 test_collapser.py verify_implementation
  
To find XOR-differential characteristic for rounds 1,2,3,4 using block_size 32 bit:
    
    python3.11 test_collapser xordiff -b 32 -f 1 -l 4

To find XOR-differential characteristic for rounds 1,2,3,4 using block_size 32 bit and showing detailed info about found characteristic:    
    
    python3.11 test_collapser xordiff -b 32 -f 1 -l 4 -w 0 --show-ch-details

To find XOR-differential characteristic for round 2 using block_size 32 bit and start from weight 10:
    
    python3.11 test_collapser xordiff -b 32 -f 2 -l 2 -w 10
    
WARNING: all found "xordiff" characteristic are not valid (because of properties pseudo-dynamic substitutions, used in the pCollapserARX) !!!

To find valid "xordiff" characteristic use special script "diffvalchsearch_pcollapser.py", see description in it. 

Usage:
    python3.11 diffvalchsearch_pcollapser.py
    
To change "block_size", "num_rounds" and "init_weight" - edit values in a script source (lines 52, 53 and 55).    

WARNING: this script need much more time to complete.

