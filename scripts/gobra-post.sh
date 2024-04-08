#!/bin/sh

dir_path=$(dirname $(
        cd $(dirname "$0")
        pwd
))
pushd "$dir_path" > /dev/null

# Gobra considers 'Token' to be a duplicate identifier - See jwt package stub for details
sed -i 's/jwt.JwtToken/jwt.Token/g' pkg/**/*.go
sed -i 's/merkle\/merkleProof/merkle\/proof/g' ./pkg/roots/v1.go
sed -i 's/merkleProof\.VerifyInclusion/proof\.VerifyInclusion/g' ./pkg/roots/v1.go

popd > /dev/null
