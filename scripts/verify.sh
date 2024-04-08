#!/bin/bash

function gobra_cleanup() {
    bash $ADEM/scripts/gobra-post.sh
}

function gobra() {
    BIN="${GOBRA:-/gobra/gobra.jar}"
    ADEM=$(dirname $(
            cd $(dirname "$0")
            pwd
    ))
    
    if [[ "$*" == *"--help"* || "$*" == *"-h"* ]]
    then
        java -jar -Xss128m $BIN \
        --help
        return
    fi
    
    GMAX="${GMAX:-180s}"
    
    trap gobra_cleanup EXIT
    
    bash $ADEM/scripts/gobra-pre.sh
    
    java -jar -Xss512m $BIN \
    --gobraDirectory $ADEM/out \
    --cacheFile $ADEM/.cache \
    --include $ADEM $ADEM/gob $ADEM/tamigloo \
    --module github.com/adem-wg/adem-proto/ \
    --noStreamErrors \
    --parallelizeBranches \
    --z3Exe /usr/bin/z3 \
    --onlyFilesWithHeader \
    --packageTimeout $GMAX \
    --projectRoot $ADEM/pkg \
    --recursive \
    "${@:1}"
}

gobra "$@"