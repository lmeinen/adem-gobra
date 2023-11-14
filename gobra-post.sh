#!/bin/sh

dir_path=$( cd "$(dirname "${BASH_SOURCE[0]}")" ; pwd -P )
pushd "$dir_path" > /dev/null

# Gobra considers 'Token' to be a duplicate identifier - See jwt package stub for details
sed -i 's/jwt.JwtToken/jwt.Token/g' pkg/**/*.go
sed -i 's/merkle\/merkleProof/merkle\/proof/g' ./pkg/roots/v1.go
sed -i 's/merkleProof\.VerifyInclusion/proof\.VerifyInclusion/g' ./pkg/roots/v1.go

popd > /dev/null
