#!/bin/sh

set -e

cd ..

echo "Testing Shellpool with CCL."
rm -f test.ok
ccl < top.lisp
ls -l test.ok

echo "Testing Shellpool with SBCL."
rm -f test.ok
sbcl < top.lisp
ls -l test.ok

echo "Testing Shellpool with CMUCL"
rm -f test.ok
cmucl < top.lisp
ls -l test.ok

echo "Testing Shellpool with ABCL."
rm -f test.ok
abcl < top.lisp
ls -l test.ok

