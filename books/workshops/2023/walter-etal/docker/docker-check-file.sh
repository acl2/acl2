#!/usr/bin/env bash

PROOF_FILE_ABS=$(realpath $1)
# from https://stackoverflow.com/a/246128
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
# from https://stackoverflow.com/a/28085062
: "${DOCKER_CMD:=docker}"
: "${IMAGE_VERSION:=latest}"

#echo $PROOF_FILE_ABS
$DOCKER_CMD run --rm -it -v "$PROOF_FILE_ABS:/root/checker/proof.lisp" atwalter/proof-checker-cli:$IMAGE_VERSION proof.lisp
