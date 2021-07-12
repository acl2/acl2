# A script to call the STP solver with a timeout
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2021 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

#!/bin/bash

# This script calls STP (with a timeout) on a file.

set -e # Exit immediately on errors

#Check the number of arguments supplied:
if [ $# -ne 4 ]
then
    echo "callstplimited.bash: ERROR: Arguments must be the input file, output file, timeout (number of conflicts), and whether to generate a counterexample (y/n)."
    exit 1
fi

INPUT_FILE=$1  # This should be the .cvc file
OUTPUT_FILE=$2 # The caller should check whether this contains "Valid."
TIMEOUT=$3 # number of conflicts
COUNTEREXAMPLE=$4

if [ ${COUNTEREXAMPLE} = "y" ] ; then
    COUNTEREXAMPLE_ARGS="--print-counterex --print-counterexbin"
elif [ ${COUNTEREXAMPLE} = "n" ] ; then
    COUNTEREXAMPLE_ARGS=""
else
    echo "Error in callstplimited.bash: COUNTEREXAMPLE should be 'y' or 'n'."
    exit 1
fi

#TODO: The STP timeout is hardly graceful.  It says "Aborted..." Try the new STP?  <-- old comment?

echo "CALLING STP"

if [ -f "${NEWSTP}" ]; then
    echo "Using NEWSTP, which is ${NEWSTP}."
    ## Call a relatively new version of STP:
    ## echo "Calling new STP: ${NEWSTP}."
    ${NEWSTP} ${COUNTEREXAMPLE_ARGS} --max_num_confl $TIMEOUT -r ${INPUT_FILE} > ${OUTPUT_FILE}
elif [ -f "${STP}" ]; then
    ## Call a relatively old version of STP:
    ${STP} ${COUNTEREXAMPLE_ARGS} -g $TIMEOUT -r ${INPUT_FILE} > ${OUTPUT_FILE}
else
    echo "ERROR: callstplimited.bash: Cannot find NEWSTP or STP"
    echo "(NEWSTP environment var = ${NEWSTP})"
    echo "(STP environment var = ${STP})"
    exit 201
fi

EXITSTATUS=$?
# echo "STP exit status: $EXITSTATUS"
exit $EXITSTATUS
