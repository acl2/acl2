# A script to call the Formal Unit Tester
#
# Copyright (C) 2020-2021 Kestrel Institute
# Copyright (C) 2016-2020 Kestrel Technology, LLC
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

#!/bin/bash

#Check the number of arguments supplied:
if [ $# -ne 1 ]
then
    echo "formal-unit-tester.sh: Error: Must be given one argument (full path of .java file)."
    exit 1
fi

echo "Running Formal Unit Tester on ${1}."

# echo "Args are: $*."

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.

set -e #Exit on first error

JAVA_FILE="$1" #arg1 is a file containing paths of class files in the BASE_DIR (without the .class extensions)
#BASE_DIR="$2" # arg2 is the base directory of the hierarchy that contains the .class files, with no trailing slash
#OUTPUT_DIR="$3" # arg3 is the directory where the ACL2 books for the classs will go (each file name will be a fully qualified class name).

#echo "(ACL2 is: ${ACL2})"
acl2executable=${ACL2}

#old (no saved image, slow to do the include-book):
#(echo '(with-output :off :all (ld "'${THISSCRIPTDIR}'/fut.lsp")) (with-output :off :all (include-book "'${THISSCRIPTDIR}'/fut" :ttags :all)) (fut "'${FILE_WITH_PATHS_TO_CLASSES}'" "'${BASE_DIR}'" "'${OUTPUT_DIR}'"  "'${KESTREL_ACL2}'")' | ${acl2executable})

export ACL2_CUSTOMIZATION=NONE

#old (no saved image, slow to do the include-book):
# (echo '(with-output :off :all (include-book "'${THISSCRIPTDIR}'portcullis")) (with-output :off :all (include-book "'${THISSCRIPTDIR}'/formal-unit-tester" :ttags :all)) (test-file "'${JAVA_FILE}'")' | ${acl2executable})

#new:
${THISSCRIPTDIR}/save-exec-for-fut.sh #very fast if it already exists

${KESTREL_ACL2}/jvm/compile-file-if-needed.sh ${JAVA_FILE}

(echo '(test-file-and-exit "'${JAVA_FILE}'")' | ${THISSCRIPTDIR}/acl2-with-fut)
