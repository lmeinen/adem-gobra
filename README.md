# ADEM Verification

This repository contains the annotated and verified code of the verification component of the [Go prototype](https://github.com/adem-wg/adem-proto) of *An Authentic Digital Emblem* (ADEM) as specified in https://adem-wg.github.io/adem-spec/.

Specifically, the packages `consts`, `ident`, `roots`, `tokens`, `util`, and `vfy` were annotated and formally verified.

## Prerequisites

All prototypes are written in the [Go programming language](https://go.dev/) and verified using the [Gobra](https://github.com/viperproject/gobra) program verifier.
To install the verifier, please follow the installation instructions as specified [here](https://github.com/viperproject/gobra#compile-and-run-gobra).

## Running the verifier

We provide a bash script to run the verifier in scripts/verify.sh. To use it, ensure a pre-compiled JAR of Gobra is available, and set the environment variable BIN to point to that JAR. The verification script can then be run as follows:
```
bash /path/to/scripts/verify.sh
```

Alternatively, we provide a Python script to run the verification multiple times, e.g. to collect verification time measurements, or to only run the verification for specific packages. The script requires Python 3.10 to run. To see a description of its options, run:
```
python /path/to/scripts/evaluate.py
```