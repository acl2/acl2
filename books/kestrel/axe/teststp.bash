# Test script for STP solver
#
# Copyright (C) 2023 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

#!/bin/bash

# Run this script while standing in the [books]/kestrel/axe/ directory.
# It should print "Valid."

./callstp.bash teststp.cvc teststp.out -1 y
cat teststp.out
