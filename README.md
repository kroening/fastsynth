# fastsynth

## Compilation instructions
Clone the repo
~~~
git clone git@github.com:kroening/fastsynth.git
cd fastsynth
git submodule init
git submodule update

~~~
compile the CBMC submodule (in `fastsynth/lib/cbmc`) by following these instructions: http://www.cprover.org/svn/cbmc/trunk/COMPILING

Finally, to compile fastsynth run `make` from the dir `fastsynth/src`


## Usage

The fastsynth binary is located in `fastsynth/src/fastsynth`. 

### SyGuS-IF format
Fastsynth can be run on SyGuS-IF format synthesis benchmarks in bitvector logic. In theory it can also be run on
Linear Integer Arithmetic but this is less thoroughly tested. To run fastsynth the command is
~~~
fastsynth file.sl [--command-line-parameters]
~~~
A description of the available command line parameters can be obtained by running `fastsynth --help`. 

By default, with no command line parameters, fastsynth runs a basic CEGIS algorithm using a SAT solver
for both verification and synthesis.

### annotated C format
In addition to SyGuS-IF, fastsynth also accepts synthesis problems in a formated based on annotating C files. 
Examples can be found in `fastsynth/regression/fastsynth-C`. 

- Any function to be synthesised must be named with the prefix `EXPRESSION`.
- Any input to the function must be initialised with a nondet function, prefixed with `nondet`.
- The logical constraints must be given using `__CPROVER_assert`. 

Note that integers in C are not true integers but integers represented using bitvectors.

~~~
int EXPRESSION_and(int, int);
int nondet_int();

int main()
{
  int in0=nondet_int(),
      in1=nondet_int();
  __CPROVER_assert(EXPRESSION_and(in0, in1)==(in0 & in1), "");
}
~~~

To run fastsynth the command is the same as with the SyGuS-IF format, and the available command line parameters remain the same.
~~~
fastsynth file.c [--command-line-parameters]
~~~