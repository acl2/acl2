#!/bin/bash

# A script to save an executable ACL2 image containing the C Transformations
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2025 Kestrel Institute
# Copyright (C) 2016-2020 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

set -e

# This script builds a saved image of ACL2 with the command-line
# C-to-C transformation machinery built in, unless the image already
# exists and is up-to-date.

# NOTE: The book transform-c.lisp should be certified before
# this script is run.

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.
cd "${THISSCRIPTDIR}"

export ACL2_CUSTOMIZATION=NONE

BASE_NAME="acl2-with-transform-c" # Also the name of the wrapper script that gets created

# If the saved image does not exist, or is older than any of the key
# files, we rebuild it.  This check is not perfect (some supporting
# book may have changed such that transform-c.lisp needs to be
# recertified), but we want this to be very fast in the common case
# (everything up-to-date) and so can't afford to always do a build to
# ensure everything is up-to-date.

echo "Checking whether we need to save an image for transform-c."
# We could check the actual image, but the file extension differs on
# the Mac, so we check the wrapper script, BASE_NAME:
if [[ ( ! -f ${BASE_NAME} ) || ( ${BASE_NAME} -ot transform-c.cert ) || ( ${BASE_NAME} -ot transform-c.lisp ) || ( ${BASE_NAME} -ot wrappers.lisp ) || ( ${BASE_NAME} -ot ../../../utilities/run-json-command.lisp ) ]] ;then
    rm -f "${BASE_NAME}"
    rm -f "${BASE_NAME}.lx86cl64"
    rm -f "${BASE_NAME}.dx86cl64"
    rm -f "${BASE_NAME}.core" # TODO: What other extensions (for other Lisps) do we need to handle?

    echo "(Saving an image for transform-c:"
    # (mv-let (erp val state) (ld ...) (if erp (exit 1) (value :q)))
    (echo '(include-book "kestrel/utilities/exit-if-function-not-defined" :dir :system) (include-book "kestrel/c/syntax/portcullis" :dir :system) (include-book "kestrel/c/transformation/portcullis" :dir :system) (include-book "transform-c" :ttags :all) (exit-if-function-not-defined run-json-command-fn) :q (save-exec "'${BASE_NAME}'" "ACL2 after including transform-c.")' | ${ACL2})
    ls -l acl2-with-transform-c*
    echo "Done saving image.)"
else
    echo "NOTE: Not saving an image for transform-c, as things seem to be up-to-date:"
    ls -l acl2-with-transform-c*
fi
