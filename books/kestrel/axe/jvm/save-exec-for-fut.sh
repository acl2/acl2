# A script to save an executable ACL2 image containing the Formal Unit Tester
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2020 Kestrel Institute
# Copyright (C) 2016-2020 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

#!/bin/bash

set -e

# Build a saved image of ACL2 with fut built in,
# unless it already exists and is up-to-date.  TODO: What if
# fut.cert is also out of date?

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.
cd "${THISSCRIPTDIR}"

export ACL2_CUSTOMIZATION=NONE # Avoid confusion, since the caller may do this

# # Can take some time (may not be needed since below we can include formal-unit-tester even if not certified):
# buildp # Or, we could make the axe/ dir a :pre-dir of anything that uses FUT

BASE_NAME="acl2-with-fut"

# We could test the actual image, but the file extension differs on the Mac:
if [[ ( ! -f ${BASE_NAME} ) || ( ${BASE_NAME} -ot formal-unit-tester.cert ) || ( ${BASE_NAME} -ot formal-unit-tester.lisp ) ]] ;then
    rm -f "${BASE_NAME}"
    rm -f "${BASE_NAME}.lx86cl64"
    rm -f "${BASE_NAME}.dx86cl64"
    echo "(Saving an image for the Formal Unit Tester:"

    # (mv-let (erp val state) (ld ...) (if erp (exit 1) (value :q)))
    (echo '(include-book "kestrel/utilities/exit-if-function-not-defined" :dir :system) (include-book "kestrel/jvm/portcullis" :dir :system) (include-book "kestrel/axe/jvm/formal-unit-tester" :dir :system :ttags :all) (exit-if-function-not-defined test-file-fn) :q (save-exec "'${BASE_NAME}'" "ACL2 after including fut.")' | ${ACL2})
    ls -l acl2-with-fut*
    echo "Done saving image.)"
else
    echo "Not saving an image for FUT (things seem to be up-to-date)."
fi
