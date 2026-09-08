#!/bin/bash

# A script to save an executable ACL2 image containing the JSON-RPC interface
# to the Kestrel C-to-C transformations.
#
# Copyright (C) 2026 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Grant Jurgensen (grant@kestrel.edu)

################################################################################

set -e

# This script builds a saved image of ACL2 with the JSON-RPC interface to the
# C-to-C transformations built in, unless the image already exists and is
# up-to-date.

# NOTE: The book top.lisp should be certified before this script is run.

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )"
cd "${THISSCRIPTDIR}"

export ACL2_CUSTOMIZATION=NONE

BASE_NAME="acl2-with-c-transformation-jsonrpc" # Also the wrapper script name

echo "Checking whether we need to save an image for the C transformation JSON-RPC server."
if [[ ( ! -f ${BASE_NAME} ) || ( ${BASE_NAME} -ot top.cert ) || ( ${BASE_NAME} -ot struct-type-split.lisp ) || ( ${BASE_NAME} -ot top.lisp ) ]] ;then
    rm -f "${BASE_NAME}"
    rm -f "${BASE_NAME}.lx86cl64"
    rm -f "${BASE_NAME}.dx86cl64"
    rm -f "${BASE_NAME}.core"

    echo "(Saving an image for the C transformation JSON-RPC server:"
    # top.lisp provides the methods (struct-type-split) and, via
    # kestrel/jsonrpc/top, the socket server entry points (run-jsonrpc-server).
    (echo '(include-book "kestrel/utilities/exit-if-function-not-defined" :dir :system) (include-book "kestrel/jsonrpc/portcullis" :dir :system) (include-book "kestrel/c/syntax/portcullis" :dir :system) (include-book "kestrel/c/transformation/portcullis" :dir :system) (include-book "top" :ttags :all) (exit-if-function-not-defined jsonrpc::run-jsonrpc-server) (exit-if-function-not-defined jsonrpc::struct-type-split) :q (save-exec "'${BASE_NAME}'" "ACL2 after including the JSON-RPC interface to the C transformations.")' | ${ACL2})
    ls -l ${BASE_NAME}*
    echo "Done saving image.)"
else
    echo "NOTE: Not saving an image for the C transformation JSON-RPC server, as things seem to be up-to-date:"
    ls -l ${BASE_NAME}*
fi
