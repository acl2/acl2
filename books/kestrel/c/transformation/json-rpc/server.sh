#!/bin/bash

# A script to start the JSON-RPC server for the Kestrel C-to-C transformations.
#
# Copyright (C) 2026 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Grant Jurgensen (grant@kestrel.edu)

################################################################################

set -e # Exit on first error

# Usage: server.sh [PORT]
# PORT defaults to 7070.

PORT="${1:-7070}"

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )"

export ACL2_CUSTOMIZATION=NONE

# Build the saved image if necessary (fast if it already exists):
${THISSCRIPTDIR}/save-exec-for-server.sh

echo "Starting JSON-RPC server for the C transformations on localhost port ${PORT}."

# Relative file paths in requests are resolved with respect to ACL2's
# connected book directory, i.e. the directory this script is run from,
# which we print first.
# Bind to localhost only (the nil interface argument).
# Add further transformation methods to the allowed-methods list as they are
# supported.
(echo "(pprogn (princ$ \"Resolving relative file paths with respect to \" *standard-co* state) (princ$ (cbd) *standard-co* state) (newline *standard-co* state) (value :invisible)) (jsonrpc::run-jsonrpc-server ${PORT} nil '(jsonrpc::input-files jsonrpc::output-files jsonrpc::list-ensembles jsonrpc::drop-ensemble jsonrpc::add-section-attr jsonrpc::simpadd0 jsonrpc::split-fn jsonrpc::split-gso jsonrpc::struct-type-split jsonrpc::wrap-fn) state)" | ${THISSCRIPTDIR}/acl2-with-c-transformation-jsonrpc)
