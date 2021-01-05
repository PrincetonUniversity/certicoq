#!/usr/bin/env bash

DOCLEAN=$1

clean() {
    if [ "$DOCLEAN" = "noclean" ]; then
        echo "Warning: not cleaning"
    else
        git clean -dfx
    fi
}

cd submodules

cd coq-ext-lib
echo "Rebuilding coq-ext-lib"
clean
make -j 2
make install
cd ..

cd Equations
echo "Rebuilding Equations"
clean
./configure.sh
make
make install
cd ..

cd metacoq
echo "Rebuilding MetaCoq"
clean
./configure.sh local
make -j 2 translations all
make install
