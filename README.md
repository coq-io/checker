# IO Checker
Automatic checker for lock-free concurrent programs in Coq.

## Run
Using [OPAM for Coq](http://coq-blog.clarus.me/use-opam-for-coq.html), add the repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

and install the dependencies:

    opam install -j4 -v coq:io:system

Compile the Coq code:

    ./configure.sh
    make
