# LL
Some formalizations of linear logic in the Coq proof assistant.

## Run
Install the AAC library:

    opam repo add coq-unstable https://github.com/coq/repo-unstable.git
    opam install -j4 -v coq:contrib:aac-tactics

Compile:

    ./configure.sh
    make
