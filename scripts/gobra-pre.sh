#!/bin/sh

dir_path=$(dirname $(
        cd $(dirname "$0")
        pwd
))
pushd "$dir_path" > /dev/null

# Gobra considers 'Token' to be a duplicate identifier - See jwt package stub for details
sed -i 's/jwt.Token/jwt.JwtToken/g' ./pkg/**/*.go
sed -i 's/merkle\/proof/merkle\/merkleProof/g' ./pkg/roots/v1.go
sed -i 's/proof\.VerifyInclusion/merkleProof\.VerifyInclusion/g' ./pkg/roots/v1.go

popd > /dev/null
