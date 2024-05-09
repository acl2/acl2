#!/bin/bash
#
# Just a tiny script to avoid repeating so many parameters in many `run` sections of the test.yml

# safe mode
set -euo pipefail

# verbose
set -v

DOCKER_HOME=$(realpath "$(dirname $0)/../../..")

# remove the compiled .fasl files so that cl+ssl is recompiled every time
if [ ! -v KEEP_FASLS ]
then
    KEEP_FASLS=0
fi
if [ "$KEEP_FASLS" -eq "0" ]
then
    find "$DOCKER_HOME/.cache/common-lisp/" -name 'cl-plus-ssl' | xargs --verbose rm -rf || true
fi

# Note, the M2_HOME below is for ABCL, see https://gitlab.common-lisp.net/cl-docker-images/cl-devel/-/issues/1

docker run -e LISP -e LIB_LOAD_MODE -e OPENSSL -e BITS \
       -e "M2_HOME=/home/cl/apache-maven-3.8.6" \
       -u "$(id -u):$(id -g)" \
       -i \
       --mount type=bind,source="$DOCKER_HOME",target=/home/cl/ \
       clfoundation/cl-devel:2022-02-09 \
       -q /home/cl/cl-plus-ssl/test/run-for-ci.sh

RESULT=$?

# make sure the .fasl files are placed where we expect
if [ $(find "$DOCKER_HOME/.cache/common-lisp/" -name 'cl-plus-ssl' | wc -l) -eq "0" ]
then
   echo ".fasl files are not found where expected!";
   exit 1;
else
    find "$DOCKER_HOME/.cache/common-lisp/" -name 'cl-plus-ssl'
fi

exit $RESULT
