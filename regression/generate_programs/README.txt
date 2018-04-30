The program generator only works for 32 bit bitvectors.

The program generator requires a dummy input file, which gives the types 
and number of function arguments:
1_arg_func.sl = 1 argument function 
2_arg_func.sl = 2 argument function etc.

The program generator enumerates through all possible programs, starting from the given index.

The commands used are:
--generate-programs = enables program generator mode
--program-index-min = minimum index to start generating programs from
--program-index-max = maximum index
--program-size = length of program to generate



fastsynth --generate-programs --program-index-min 0 --program-index-max 10
--program-size 5 1_arg_func.sl

This generates programs with 5 instructions from index 0 to index 10, with 1 input argument.

The default is to generate programs with 5 instructions from index 0 to index 9.

