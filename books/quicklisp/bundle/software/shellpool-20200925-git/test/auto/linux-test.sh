#!/bin/sh

set -e

cd ..

echo "Testing with CCL"
rm -f test.ok
ccl < top.lisp
ls -l test.ok

echo "Testing with SBCL"
rm -f test.ok
sbcl < top.lisp
ls -l test.ok

echo "Testing with CMUCL"
rm -f test.ok
cmucl < top.lisp
ls -l test.ok

echo "Testing with Allegro"
rm -f test.ok
alisp < top.lisp
ls -l test.ok

echo "Testing with Lispworks"
rm -f test.ok
lispworks < top.lisp
ls -l test.ok

echo "Testing with ABCL"
rm -f test.ok
abcl < top.lisp
ls -l test.ok

