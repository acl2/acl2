#!/bin/bash

# Copyright (C) 2018, Regents of the University of Texas
# Written by Matt Kaufmann
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# Run ./write-td-cands.sh to move the existing td-cands.lisp and
# td-cands.acl2 (if they exist) to td-cands.lisp.backup and
# td-cands.acl2.backup, and then create new files td-cands.lisp and
# td-cands.acl2.

# Usage (the first gets acl2 from $ACL2):
# ./write-td-cands.sh
# ./write-td-cands.sh <path_to_acl2>

if [ $# -gt 1 ] ; then \
    echo "Usage: $0 [<path_to_acl2>]" ; \
    exit 1 ; \
elif [ $# -eq 1 ] ; then \
    export ACL2=$1 ; \
elif [ "$ACL2" = "" ] ; then \
    echo 'Error: Need to define ACL2 or add an argument specifying' ; \
    echo '       a path to an ACL2 executable.' ; \
    exit 1 ; \
fi

if [ -f td-cands.lisp ] ; then \
    echo 'Moving td-cands.{lisp,acl2} to td-cands.{lisp,acl2}.backup.' ; \
    rm -f td-cands.acl2.backup ; \
    rm -f td-cands.lisp.backup ; \
    mv td-cands.acl2 td-cands.acl2.backup ; \
    mv td-cands.lisp td-cands.lisp.backup ; \
fi

echo "Starting $ACL2 to run write-td-cands.lsp."
echo "  Note that this starts by including system book doc/top-slow, which"
echo "  can take several minutes.  The rest should take only seconds."

exec $ACL2 < write-td-cands.lsp > write-td-cands.out 2>&1

if [ -f td-cands.lisp ] ; then \
    echo "Completed write-td-cands.lsp" ; \
else \
    echo "FAILED to create td-cands.lisp; see write-td-cands.out." ; \
fi
