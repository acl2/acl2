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
    echo "formal-unit-tester.sh: Error: Must be given one argument (path to a .java file)."
    exit 1
fi

JAVA_FILE="$1"

echo "Running Formal Unit Tester on ${JAVA_FILE}."

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.

#echo "(ACL2 is: ${ACL2})"

export ACL2_CUSTOMIZATION=NONE

#old (no saved image, slow to do the include-book):
#acl2executable=${ACL2}
# (echo '(with-output :off :all (include-book "'${THISSCRIPTDIR}'portcullis")) (with-output :off :all (include-book "'${THISSCRIPTDIR}'/formal-unit-tester" :ttags :all)) (test-file "'${JAVA_FILE}'")' | ${acl2executable})

${THISSCRIPTDIR}/save-exec-for-fut.sh # very fast if it already exists

${KESTREL_ACL2}/jvm/compile-file-if-needed.sh ${JAVA_FILE}

(echo '(test-file-and-exit "'${JAVA_FILE}'")' | ${THISSCRIPTDIR}/acl2-with-fut)
