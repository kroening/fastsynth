# fastsynth

## Compilation instructions

git clone git@github.com:polgreen/fastsynth.git

cd fastsynth

git checkout enumerative_program_generator

cd lib/cbmc

git clone https://github.com/diffblue/cbmc.git .

git checkout develop

cd src

make minisat2-download

make -j8

cd ../../../src

make -j8
