The program generator only works for 32 bit bitvectors.

The program generator requires a dummy input file, which gives the types 
and number of function arguments:
1_arg_func.sl = 1 argument function 
2_arg_func.sl = 2 argument function etc.

The program generator generates programs randomly. The random number generator used is std::uniform_int_distribution.
It is seeded with std::random_device, as in the example here.
http://en.cppreference.com/w/cpp/numeric/random/uniform_int_distribution


The commands used are:
--generate-N-programs <N> = generates <N> programs randomly
--number-of-constants <N> = use <N> constants
--program-size <N> = generate programs with <N> instructions


fastsynth --generate-N-programs 10 1_arg_func.sl --program-size 3 --number-of-constants 1

This generates 10 programs with 3 instructions, with 1 input argument, and using 1 constant.



