#!/bin/sh
cd "`dirname $0`"
~/lisps/ccl-1.11/lx86cl --heap-reserve 200M --load run-on-server.lisp --eval "(quit)"
