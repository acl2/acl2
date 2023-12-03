#!/bin/bash

# A script to attempt to repair a broken book, to be called by cert.pl
#
# Copyright (C) 2023 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
# Author: Eric Smith (eric.smith@kestrel.edu)

################################################################################

set -e # Exit on first error

# NOTE: See the SETUP instructions in repair-book.lisp.

# cert.pl sets the CERT_GOALFILE and PWD environment variables according to the failed book,
# and we use them here to determine which book to repair:

BOOK_CERT="${PWD}/${CERT_GOALFILE}" # .cert extension will be removed by repair-book

echo "repair-book-from-cert-pl.sh called on ${BOOK_CERT}."

if [ -z "${ACL2}" ] ; then
  echo "ERROR: Please set your ACL2 environment variable (e.g., to your saved_acl2)."
  exit 1
fi

export ACL2_CUSTOMIZATION=NONE # Just in case

(echo '(include-book "kestrel/helpers/repair-book" :dir :system) (repair-book "'${BOOK_CERT}'")' | ${ACL2})
