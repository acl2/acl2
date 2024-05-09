#!/bin/sh

# Copyright (C) 2023, ForrestHunt, Inc.
# Written by Matt Kaufmann
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# Note: This assumes that supporting books have already been certified,
# including ../patch-book and acl2data-files-agree.

# This script uses acl2data-files-agree.lisp to check whether
# *__acl2data.out files agree modulo book name and order of entries
# that might be permuted because of random$ calls.

### Settable variables:

if [ $# = 1 ] ; then
    export par="-j $1"
elif [ $# -ne 0 ] ; then
    echo "ERROR: $0 takes 0 or 1 arguments, not $#."
    exit 1
fi

if [ "$ACL2" = "" ] ; then \
    echo "ERROR: File $0 requires ACL2 to be defined."
    exit 1
fi

if [ "$ACL2_SYSTEM_BOOKS" = "" ] ; then \
    echo "ERROR: File $0 requires ACL2_SYSTEM_BOOKS to be defined."
    exit 1
fi

if [ "${ACL2_ADVICE}" = "" ] ; then \
    export test9=test9 ;\
fi

# Create directory in which to run the tests.

rm -rf runs
mkdir runs
cp -p src/test*.lisp runs/
cp -p cert.acl2 runs/
cp -p customize-tests.lsp runs/
cd runs

# The echo command just below is mainly to ensure that we don't exit,
# so that we get to the "touch" command below it.
# Note that $par has been been seen to be useless with:
# "warning: -jN forced in submake: disabling jobserver mode."
# But I'm leaving it in, below, in case some day this issue is
# resolved; it's certainly harmless to leave it in.
(export ACL2_CUSTOMIZATION=`pwd`/customize-tests.lsp ; \
$ACL2_SYSTEM_BOOKS/build/cert.pl $par --acl2 $ACL2 test test2 test2a test2b test3 test3a test4 test5 test6 test7a test7b test8 $test9 test-empty) || echo "Failure for kestrel/acl2data/gather/tests/"

# Avoid any future certification in runs.  The directory will be
# deleted before the next attempt to run tests (see "rm -rf runs"
# above).  
touch cert_pl_exclude

# Back to tests/:
cd ..

$ACL2 < chk-all-test-files.lsp > chk-all-test-files.lsp.out
fgrep TESTS-SUCCEEDED chk-all-test-files.lsp.out > /dev/null
if [ $? -ne 0 ] ; then \
    echo 'Tests FAILED; see chk-all-test-files.lsp.out' ; \
    exit 1 ; \
else \
    echo 'Tests passed.'
fi
