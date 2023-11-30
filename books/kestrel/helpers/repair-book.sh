#!/bin/bash

# A script to attempt to repair a broken book
#
# Copyright (C) 2023 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

set -e

BOOK="$1"
echo "repair-book.sh called on ${BOOK}."

if [ -z "${ACL2}" ] ; then
  echo "ERROR: Please set your ACL2 environment variable (e.g., to your saved_acl2)."
  exit 1
fi

export ACL2_CUSTOMIZATION=NONE # Just in case

(echo '(include-book "kestrel/helpers/repair-book" :dir :system) (repair-book "'${BOOK}'")' | ${ACL2})
