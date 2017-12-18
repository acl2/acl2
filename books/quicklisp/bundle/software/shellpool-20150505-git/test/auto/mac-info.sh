#!/bin/sh

set -e

echo "Mac version:"
uname -a
echo ""
echo "Lisp version information:"
echo ""
echo "CCL Version: `ccl --version`"
echo ""
echo "SBCL Version: `sbcl --version`"
echo ""
/bin/echo -n "CMUCL Version: "; cmucl -quiet -eval '(progn (format t "~a ~a~%" (lisp-implementation-type) (lisp-implementation-version)) (quit))'
echo ""
/bin/echo -n "ABCL Version: "
abcl --eval "(quit)" | head -2 | sed 'N;s/\n/; /g'
