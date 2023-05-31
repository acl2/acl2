#!/bin/bash

# Test script for STP solver
#
# Copyright (C) 2023 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

# This script should print "Valid." if STP is being called correctly.

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )" #Simpler commands can just give "." here, which seems bad.
cd ${THISSCRIPTDIR}

echo "STP=${STP}"
echo "ACL2_STP_VARIETY=${ACL2_STP_VARIETY}"

./callstp.bash teststp.cvc teststp.out -1 y
cat teststp.out
