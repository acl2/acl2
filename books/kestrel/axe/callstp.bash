# A script to call the STP solver
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2021 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

#!/bin/bash

# This script calls STP (with no timeout) on a file.

set -e # Exit immediately on errors

#Check the number of arguments supplied:
if [ $# -ne 3 ]
then
    echo "callstp.bash: ERROR: Arguments must be the input file, output file, and COUNTEREXAMPLE (y/n)."
    exit 1
fi

INPUT_FILE=$1  # This should be the .cvc file
OUTPUT_FILE=$2 # The caller should check whether this contains "Valid."
COUNTEREXAMPLE=$3

if [ ${COUNTEREXAMPLE} = "y" ] ; then
    COUNTEREXAMPLE_ARGS="--print-counterex --print-counterexbin"
elif [ ${COUNTEREXAMPLE} = "n" ] ; then
    COUNTEREXAMPLE_ARGS=""
else
    echo "Error in callstp.bash: COUNTEREXAMPLE should be 'y' or 'n'."
    exit 1
fi

if [ -f "${NEWSTP}" ]; then
    echo "Using NEWSTP, which is ${NEWSTP}."
    ## Call a relatively new version of STP:
    ${NEWSTP} ${COUNTEREXAMPLE_ARGS} -r ${INPUT_FILE} > ${OUTPUT_FILE}
elif [ -f "${STP}" ]; then
    # echo "STP is: [${STP}]"
    # with -r and -x, the new stp seems much slower (on, say, the aes proofs) than the 2008-jan-15 stp.  the new one routinely times out.
    #adding -r on Wed Dec 21 11:27:44 2011, since it seems to speed up aes-128-decrypt a lot...
    ${STP} ${COUNTEREXAMPLE_ARGS} -r ${INPUT_FILE} > ${OUTPUT_FILE}
else
    echo "ERROR: callstp.bash: Cannot find NEWSTP or STP"
    echo "(NEWSTP environment var = ${NEWSTP})"
    echo "(STP environment var = ${STP})"
    exit 201
fi


EXITSTATUS=$?
# echo "STP exit status: $EXITSTATUS"
exit $EXITSTATUS
