#!/bin/sh

# Copyright (C) 2023, ForrestHunt, Inc.
# Written by Matt Kaufmann
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# Causes some 'diff' implementations to use the 'stone' algorithm
# (without this, a build failed on an M2 Mac due to diff not finding
# all the common lines):
export POSIX_PEDANTIC=true

if [ "$ACL2DATA_ACL2_DIR" != "" ]
then
    export acl2_dir="$ACL2DATA_ACL2_DIR"
elif [ "$ACL2_SYSTEM_BOOKS" != "" ]
then
    export acl2_dir=`cd $ACL2_SYSTEM_BOOKS && cd .. && pwd`
    if [ ! -d "$acl2_dir" ]
    then
	echo "ERROR in $0:"
	echo "Unable to determinate ACL2 sources directory."
	echo "Consider setting environment variable ACL2DATA_ACL2_DIR"
	echo "to that directory."
	exit 1
    fi
else
    export acl2_dir=`cd $(dirname $0) && cd ../../../../ && pwd`
    if [ ! -f "$acl2_dir/axioms.lisp" ]
    then
       echo "ERROR in $0:"
       echo "Environment variable ACL2_SYSTEM_BOOKS (or ACL2DATA_ACL2_DIR)"
       echo "must be set."
       exit 1
    fi
fi

# Files other-events, rewrite, and (part of) induct are handled
# specially further below.
files="type-set-b induct defthm history-management"

my_status=0

for file in $files
do
    echo "Checking $file..."
    tmp=`diff -w $acl2_dir/$file.lisp patch-$file.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'` ; \
    if [ "$tmp" != "" ] ; then \
	echo "  ERROR: Unexpected line(s):" ;\
	echo "$tmp" ;\
	my_status=1 ;\
    fi \
done

# Patches to ACL2 source files other-events.lisp, rewrite.lisp, and
# (part of) induct.lisp need more sophisticated checks, since
# apparently diff can't manage.

### other-events

echo "Checking other-events (may take at least several seconds)..."

lines=`wc -l $acl2_dir/other-events.lisp | awk '{print $1}'`

echo " ... Checking part 1 ..."

rm -f patch-other-events-tail-1.out

line1=`fgrep -n '(defun chk-embedded-event-form ' $acl2_dir/other-events.lisp | awk -F ':' '{print $1}'`

tail -n$((lines - line1 + 1)) $acl2_dir/other-events.lisp > patch-other-events-tail-1.out

diff -w patch-other-events-tail-1.out patch-other-events-1.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'

echo " ... Checking part 2 ..."

rm -f patch-other-events-tail-2.out

line2=`fgrep -n '(defun progn-fn1 ' $acl2_dir/other-events.lisp | awk -F ':' '{print $1}'`

tail -n$((lines - line2 + 1)) $acl2_dir/other-events.lisp > patch-other-events-tail-2.out

diff -w patch-other-events-tail-2.out patch-other-events-2.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'

echo " ... Checking part 3 ..."

rm -f patch-other-events-tail-3.out

line3=`fgrep -n '(defun chk-acceptable-certify-book ' $acl2_dir/other-events.lisp | awk -F ':' '{print $1}'`

tail -n$((lines - line3 + 1)) $acl2_dir/other-events.lisp > patch-other-events-tail-3.out

diff -w patch-other-events-tail-3.out patch-other-events-3.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'

echo " ... Checking part 4 ..."

rm -f patch-other-events-tail-4.out

line4=`fgrep -n '(defun make-event-fn2 ' $acl2_dir/other-events.lisp | awk -F ':' '{print $1}'`

tail -n$((lines - line4 + 1)) $acl2_dir/other-events.lisp > patch-other-events-tail-4.out

diff -w patch-other-events-tail-4.out patch-other-events-4.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'

### rewrite

echo "Checking rewrite (may take several seconds)..."

lines=`wc -l $acl2_dir/rewrite.lisp | awk '{print $1}'`

echo " ... Checking part 1 ..."

rm -f patch-rewrite-tail-1.out

line1=`fgrep -n '(defun rewrite ' $acl2_dir/rewrite.lisp | awk -F ':' '{print $1}'`

tail -n$((lines - line1 + 1)) $acl2_dir/rewrite.lisp > patch-rewrite-tail-1.out

diff -w patch-rewrite-tail-1.out patch-rewrite-1.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'

echo " ... Checking part 2 ..."

rm -f patch-rewrite-tail-2.out

line2=`fgrep -n '(defun rewrite-with-lemma ' $acl2_dir/rewrite.lisp | awk -F ':' '{print $1}'`

tail -n$((lines - line2 + 1)) $acl2_dir/rewrite.lisp > patch-rewrite-tail-2.out

diff -w patch-rewrite-tail-2.out patch-rewrite-2.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'

### induct

echo "Checking the rest of induct (may take several seconds)..."

lines=`wc -l $acl2_dir/induct.lisp | awk '{print $1}'`

rm -f patch-induct-tail-2.out

line2=`fgrep -n '(defun@par load-hint-settings-into-rcnst ' $acl2_dir/induct.lisp | awk -F ':' '{print $1}'`

tail -n$((lines - line2 + 1)) $acl2_dir/induct.lisp > patch-induct-tail-2.out

diff -w patch-induct-tail-2.out patch-induct-2.lsp | grep '^>' | grep -v ';patch;$' | grep -v '^> ;' | grep -v '^> #|' | grep -v '^> |#'  | grep -v '^> \w*$'

###

if [ $my_status = 0 ]
then
    echo "SUCCESS running $0."
else
    echo "FAILURE running $0; see diff(s) above."
fi

exit $my_status
