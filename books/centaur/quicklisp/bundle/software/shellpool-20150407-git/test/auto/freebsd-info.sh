#!/bin/sh

set -e

echo "FreeBSD version:"
uname -a
echo ""
echo "Lisp version information:"
echo ""
echo "CCL Version: `ccl --version`"
echo ""
echo "SBCL Version: `sbcl --version`"
echo ""
echo -n "CMUCL Version: "; cmucl -quiet -eval '(progn (format t "~a ~a~%" (lisp-implementation-type) (lisp-implementation-version)) (quit))'
echo ""
echo -n "ABCL Version: "
abcl --noinit --eval "(quit)" | head -2 | sed 'N;s/\n/; /g'
