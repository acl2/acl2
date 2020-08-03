#!/bin/sh

set -e

echo "Linux version:"
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
echo -n "Allegro Version: "; alisp -e '(progn (format t "~a ~a~%" (lisp-implementation-type) (lisp-implementation-version)) (exit))' < /dev/null | grep -v "; Exiting"
echo ""
echo -n "Lispworks Version: "; lispworks -eval '(progn (format t "~a ~a~%" (lisp-implementation-type) (lisp-implementation-version)) (quit))' | tail -1
echo ""
echo -n "ABCL Version: "
abcl --eval "(quit)" | head -2 | sed 'N;s/\n/; /g'
