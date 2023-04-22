# A script to call the STP solver.
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2023 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

#!/bin/bash

set -e # Exit immediately on errors

# Check the number of arguments supplied:
if [ $# -ne 4 ]
then
    echo "callstplimited.bash: ERROR: Arguments must be the input file, output file, max conflicts (-1 for no max), and whether to generate a counterexample (y/n)."
    exit 1
fi

INPUT_FILE=$1  # This should be the .cvc file
OUTPUT_FILE=$2 # Where to write the output (caller can then check whether this contains "Valid.")
MAX_CONFLICTS=$3 # number of conflicts (-1 means no max)
COUNTEREXAMPLE=$4 # Whether to generate a counterexample ("y" or "n")

if [ ${COUNTEREXAMPLE} = "y" ] ; then
    COUNTEREXAMPLE_ARGS="--print-counterex --print-counterexbin"
elif [ ${COUNTEREXAMPLE} = "n" ] ; then
    COUNTEREXAMPLE_ARGS=""
else
    echo "Error in callstplimited.bash: COUNTEREXAMPLE should be 'y' or 'n'."
    exit 1
fi

# For STP versions that include:
# https://github.com/stp/stp/commit/d29b19d4b8cf42df49789cf0a3b6c493c823e559
# this can restore good behavior on abs example.
# (but this option is not available on earlier STPs):
#MULT_OPTIONS=" --bb.mult-variant 13"
MULT_OPTIONS=""

#TODO: The STP timeout is hardly graceful.  It says "Aborted..." Try the new STP?  <-- old comment?

# Use STP environment var, if set, otherwise look for 'stp' on the user's path:
STP=${STP:-stp}

# echo "CALLING ${STP}"
# Requires a relatively new STP:
${STP} ${COUNTEREXAMPLE_ARGS} --max_num_confl $MAX_CONFLICTS -r ${MULT_OPTIONS} ${INPUT_FILE} > ${OUTPUT_FILE}
## For a newer STP, this may be needed (or maybe either is ok, if the boost library is new enough):
# stp ${COUNTEREXAMPLE_ARGS} --max-num-confl $MAX_CONFLICTS -r ${INPUT_FILE} > ${OUTPUT_FILE}

# if [ -f "${NEWSTP}" ]; then
#     echo "Using NEWSTP, which is ${NEWSTP}."
#     ## Call a relatively new version of STP:
#     ## echo "Calling new STP: ${NEWSTP}."
#     ${NEWSTP} ${COUNTEREXAMPLE_ARGS} --max_num_confl $MAX_CONFLICTS -r ${INPUT_FILE} > ${OUTPUT_FILE}
# elif [ -f "${STP}" ]; then
#     ## Call a relatively old version of STP:
#     ${STP} ${COUNTEREXAMPLE_ARGS} -g $MAX_CONFLICTS -r ${INPUT_FILE} > ${OUTPUT_FILE}
# else
#     echo "ERROR: callstplimited.bash: Cannot find NEWSTP or STP"
#     echo "(NEWSTP environment var = ${NEWSTP})"
#     echo "(STP environment var = ${STP})"
#     exit 201
# fi

EXITSTATUS=$?
# echo "STP exit status: $EXITSTATUS"
exit $EXITSTATUS
