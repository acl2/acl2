#!/bin/bash

# A script to call the C transformations
#
# Copyright (C) 2020-2025 Kestrel Institute
# Copyright (C) 2016-2020 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

set -e # Exit on first error

# Check the number of arguments supplied:
if [ $# -ne 1 ]
then
    echo "transform_c.sh: Error: Must be given one argument (path to a .json file)."
    exit 1
fi

JSON_FILE="$1"

echo "Running Command from ${JSON_FILE}."

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.

#echo "(ACL2 is: ${ACL2})"

export ACL2_CUSTOMIZATION=NONE

#old (no saved image, slow to do the include-book):
#acl2executable=${ACL2}
# (echo '(with-output :off :all (include-book "'${THISSCRIPTDIR}'portcullis")) (with-output :off :all (include-book "'${THISSCRIPTDIR}'/transform_c" :ttags :all)) (test-file "'${JSON_FILE}'")' | ${acl2executable})

${THISSCRIPTDIR}/save-exec-for-transform-c.sh # very fast if it already exists

(echo '(run-json-command "'${JSON_FILE}'")' | ${THISSCRIPTDIR}/acl2-with-transform-c)
