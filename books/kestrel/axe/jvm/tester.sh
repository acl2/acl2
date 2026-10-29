#!/bin/bash

# A script to call the Java Formal Unit Tester
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
    echo "tester.sh: Error: Must be given one argument (name of the class to test)."
    exit 1
fi

CLASS="$1"

echo "Running Formal Unit Tester on ${CLASS}."

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.

#echo "(ACL2 is: ${ACL2})"

export ACL2_CUSTOMIZATION=NONE

#old (no saved image, slow to do the include-book):
#acl2executable=${ACL2}
# (echo '(with-output :off :all (include-book "'${THISSCRIPTDIR}'portcullis")) (with-output :off :all (include-book "'${THISSCRIPTDIR}'/tester" :ttags :all)) (test-class "'${CLASS}'")' | ${acl2executable})

${THISSCRIPTDIR}/save-exec-for-tester.sh # very fast if it already exists

# ${THISSCRIPTDIR}/../../jvm/compile-file-if-needed.sh ${JAVA_FILE}

(echo '(test-class-and-exit "'${CLASS}'")' | ${THISSCRIPTDIR}/acl2-with-tester)
