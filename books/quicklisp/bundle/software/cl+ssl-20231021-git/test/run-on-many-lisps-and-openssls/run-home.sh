#!/bin/sh
cd "`dirname $0`"
~/unpacked/ccl-1.11/lx86cl64 --heap-reserve 200M --load run-home.lisp --eval "(quit)"
