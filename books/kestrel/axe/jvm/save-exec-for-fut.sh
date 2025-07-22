#!/bin/bash

# A script to save an executable ACL2 image containing the Formal Unit Tester
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2025 Kestrel Institute
# Copyright (C) 2016-2020 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

set -e # exit on any error

# This script builds a saved image of ACL2 with the Formal Unit Tester
# built in, unless the image already exists and is up-to-date.

# NOTE: The book formal-unit-tester.lisp should be certified before
# this script is run.

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.
cd "${THISSCRIPTDIR}"

export ACL2_CUSTOMIZATION=NONE # Avoid confusion, since the caller may do this

BASE_NAME="acl2-with-fut" # Also the name of the wrapper script that gets created

# We could test the actual image, but the file extension depends on Lisp+OS, so we test the wrapper script:
if [[ ( ! -f ${BASE_NAME} ) || ( ${BASE_NAME} -ot formal-unit-tester.cert ) || ( ${BASE_NAME} -ot formal-unit-tester.lisp ) ]] ;then
    rm -f "${BASE_NAME}"
    rm -f "${BASE_NAME}.lx86cl64"
    rm -f "${BASE_NAME}.dx86cl64"
    rm -f "${BASE_NAME}.core"
    echo "(Saving an image for the Formal Unit Tester:"

    # (mv-let (erp val state) (ld ...) (if erp (exit 1) (value :q)))
    (echo '(include-book "kestrel/utilities/exit-if-function-not-defined" :dir :system) (include-book "kestrel/jvm/portcullis" :dir :system) (include-book "kestrel/axe/jvm/formal-unit-tester" :dir :system :ttags :all) (exit-if-function-not-defined test-file-fn) :q (save-exec "'${BASE_NAME}'" "This copy of ACL2 has the Formal Unit Tester built in.")' | ${ACL2})
    ls -l acl2-with-fut*
    echo "Done saving image.)"
else
    echo "Not saving an image for FUT (things seem to be up-to-date)."
fi
