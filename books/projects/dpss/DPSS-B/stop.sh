#!/bin/bash
##
## Copyright (C) 2023, Collins Aerospace
## All rights reserved.
##
## This software may be modified and distributed under the terms
## of the 3-clause BSD license.  See the LICENSE file for details.
##

docker stop z3-notebook 2>&1 > /dev/null | true
docker rm   z3-notebook 2>&1 > /dev/null | true
echo "Done."
