# ADEM Verification

This repository contains the annotated and verified code of the verification component of the [Go prototype](https://github.com/adem-wg/adem-proto) of *An Authentic Digital Emblem* (ADEM) as specified in https://adem-wg.github.io/adem-spec/.
Specifically, the packages `consts`, `ident`, `roots`, `tokens`, `util`, and `vfy` were annotated and formally verified.

The project is currently in development and the specification will therefore continue to evolve.

Note that due to issues in Gobra multiple breaking changes, such as renaming the `jwt.Token` interface to `jwt.JwtToken` in the the corresponding library stub, needed to be made. Therefore, directly executing the Go code contained herein is not possible. Please refer to the [original prototype](https://github.com/adem-wg/adem-proto).

## Prerequisites

All prototypes are written in the [Go programming language](https://go.dev/) and verified using the [Gobra](https://github.com/viperproject/gobra) progam verifier.
To run the verifier, please follow the installation instructions as specified [here](https://github.com/viperproject/gobra#compile-and-run-gobra).

## Running the verifier

After following the installation instructions described above to either compile or assemble the Gobra project and changing directory to the root of this repository, the verifier can be run as follows:
```
java -jar -Xss128m /path/to/gobra.jar \
		--include ./ ./goblib ./gobstubs \
		--module github.com/adem-wg/adem-proto/ \
		--noStreamErrors \
		--parallelizeBranches \
		--z3Exe /path/to/z3 \
		--onlyFilesWithHeader \
		--projectRoot pkg \
        --recursive
```