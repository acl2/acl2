#!/bin/bash
#
# Just a tiny script to avoid repeating so many parameters in many `run` sections of the test.yml

# safe mode
set -euo pipefail

# verbose
set -v

DOCKER_HOME=$(realpath "$(dirname $0)/../../..")

# remove the compiled .fasl files so that cl+ssl is recompiled every time
find "$DOCKER_HOME/.cache/common-lisp/" -name 'cl+ssl' | xargs rm -rf || true

# Note, the M2_HOME below is for ABCL, see https://gitlab.common-lisp.net/cl-docker-images/cl-devel/-/issues/1

docker run -e LISP -e LIB_LOAD_MODE -e OPENSSL -e BITS \
       -e "M2_HOME=/home/cl/apache-maven-3.8.6" \
       -u "$(id -u):$(id -g)" \
       -i \
       --mount type=bind,source="$DOCKER_HOME",target=/home/cl/ \
       clfoundation/cl-devel:2022-02-09 \
       -q /home/cl/cl-plus-ssl/test/run-for-ci.sh
