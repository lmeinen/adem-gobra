#!/bin/bash

function gobra_cleanup() {
    bash $ADEM/scripts/gobra-post.sh
}

function gobra() {
    BIN="${GOBRA:-$HOME/repos/gobra/target/scala-2.13/gobra.jar}"
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
    
    echo "$BIN"
    echo "$TIMOUT"
    
    # time out after 10 minutes: not even the vfy package should take that long
    TIMEOUT="${TIMEOUT:-600s}"
    
    trap gobra_cleanup EXIT
    
    bash $ADEM/scripts/gobra-pre.sh
    
    java -jar -Xss512m $BIN \
    --gobraDirectory $ADEM/out \
    --cacheFile $ADEM/.cache \
    --include $ADEM $ADEM/gob $ADEM/tamigloo \
    --module github.com/adem-wg/adem-proto/ \
    --noStreamErrors \
    --parallelizeBranches \
    --onlyFilesWithHeader \
    --packageTimeout $TIMEOUT \
    --projectRoot $ADEM/pkg \
    --recursive \
    "${@:1}"
}

gobra "$@"