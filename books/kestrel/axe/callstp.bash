#!/bin/bash

# A script to call the STP solver.
#
# Copyright (C) 2008-2011 Eric Smith and Stanford University
# Copyright (C) 2013-2023 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

set -e # Exit immediately on errors

# Check the number of arguments supplied:
if [ $# -ne 4 ]
then
    echo "callstp.bash: ERROR: Arguments must be the input file, output file, max conflicts (-1 for no max), and whether to generate a counterexample (y/n)."
    exit 1
fi

INPUT_FILE=$1  # This should be the .cvc file
OUTPUT_FILE=$2 # Where to write the output (caller can then check whether this contains "Valid.")
MAX_CONFLICTS=$3 # number of conflicts (-1 means no max)
COUNTEREXAMPLE=$4 # Whether to generate a counterexample ("y" or "n")

# Use STP environment var, if set, otherwise look for 'stp' on the user's path:
STP=${STP:-stp}

# By default, we use the newest STP syntax, but set ACL2_STP_VARIETY
# to "0" or "1" to override that.
ACL2_STP_VARIETY=${ACL2_STP_VARIETY:-2}

if [ ${COUNTEREXAMPLE} = "y" ] ; then
    COUNTEREXAMPLE_ARGS="--print-counterex --print-counterexbin"
elif [ ${COUNTEREXAMPLE} = "n" ] ; then
    COUNTEREXAMPLE_ARGS=""
else
    echo "Error in callstp.bash: COUNTEREXAMPLE should be 'y' or 'n'."
    exit 1
fi

# For STP versions that include:
# https://github.com/stp/stp/commit/d29b19d4b8cf42df49789cf0a3b6c493c823e559
# this can restore good behavior on abs example.
# (but this option is not available on earlier STPs):
#MULT_OPTIONS=" --bb.mult-variant 13"
MULT_OPTIONS=""

#TODO: The STP timeout is hardly graceful.  It says "Aborted..." Try the new STP?  <-- old comment?

if [[ $ACL2_STP_VARIETY == "0" ]] ; then
    # Use -g for max conflicts option:
    # May be necessary for very old STP versions.
    # echo "CALLING ${STP} (variety 0)"
    ${STP} ${COUNTEREXAMPLE_ARGS} -g $MAX_CONFLICTS -r ${MULT_OPTIONS} ${INPUT_FILE} > ${OUTPUT_FILE}
elif [[ $ACL2_STP_VARIETY == "1" ]] ; then
    # Use underscores in max conflicts option:
    # May be necessary for a somewhat old STP (circa 2021 is fine).
    # echo "CALLING ${STP} (variety 1)"
    ${STP} ${COUNTEREXAMPLE_ARGS} --max_num_confl $MAX_CONFLICTS -r ${MULT_OPTIONS} ${INPUT_FILE} > ${OUTPUT_FILE}
elif [[ $ACL2_STP_VARIETY == "2" ]] ; then
    # Use dashes in max conflicts option:
    # For the latest STP, this may be needed (or maybe either dashes or underscores are ok, if the boost library is new enough):
    # echo "CALLING ${STP} (variety 2)"
    # For the obscure options here, see:
    # https://github.com/stp/stp/issues/463
    # and
    # https://github.com/stp/stp/commit/d29b19d4b8cf42df49789cf0a3b6c493c823e559
    # These seemed to be the values of the options in an older STP that worked better.  I haven't explored whether each one matters.
    ${STP} ${COUNTEREXAMPLE_ARGS} --size-reducing-fixed-point-limit 1000000 --merge-same 1 --bb.conjoin-constant 1 --bb.mult-variant 13 --max-num-confl $MAX_CONFLICTS -r ${MULT_OPTIONS} ${INPUT_FILE} > ${OUTPUT_FILE}
else
    echo "Unsupported STP variety: ${ACL2_STP_VARIETY}.  Exiting."
    exit 1
fi

EXITSTATUS=$?
# echo "STP exit status: $EXITSTATUS"
exit $EXITSTATUS
