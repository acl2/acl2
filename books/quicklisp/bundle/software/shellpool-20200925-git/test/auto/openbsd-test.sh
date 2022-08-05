#!/bin/sh

set -e

cd ..

echo "Testing with ABCL"
rm -f test.ok
abcl < top.lisp
ls -l test.ok

