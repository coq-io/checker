# IO Checker
Automatic checker for lock-free concurrent programs in Coq.

## Run
Using [OPAM for Coq](http://coq-blog.clarus.me/use-opam-for-coq.html), add the Coq's [unstable repository](https://github.com/coq/repo-unstable):

    opam repo add coq-unstable https://github.com/coq/repo-unstable.git

and install the dependencies:

    opam install -j4 coq:io:system coq:io:exception

Compile the Coq code:

    ./configure.sh
    make
