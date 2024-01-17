#!/bin/bash

# A script to attempt to repair a collection of broken books
#
# Copyright (C) 2023 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

set -e

echo "repair-books.sh called."

export ACL2_CUSTOMIZATION=NONE # Just in case

(echo '(include-book "kestrel/helpers/repair-book" :dir :system) (repair-books)' | ${ACL2})
