#!/bin/bash
#
# Copyright (C) contributors as per cl+ssl git history
#
# See LICENSE for details.

# safe mode
set -euo pipefail

# verbose
set -v

cd "`dirname $0`"

if [ ! -v OPENSSL_RELEASES_BIN_DIR ]
then
    # assume the openssl binaries are where the build scripts place them
    export OPENSSL_RELEASES_BIN_DIR=run-on-many-lisps-and-openssls/openssl-releases/bin
fi

echo M2_HOME=$M2_HOME

MAIN='(handler-case (load "run-for-ci.lisp") (serious-condition (c) (format t "~A: ~A~%" (type-of c) c) (asdf/driver:print-backtrace :condition c :count 9999) (uiop:quit 1)))'

#~/unpacked/ccl-1.11/lx86cl64 --load run-for-ci.lisp
case $LISP in
    clisp)
        $LISP -i ~/quicklisp/setup.lisp -x "$MAIN";;
    abcl)
        $LISP --eval '(require :abcl-contrib)' --eval "$MAIN";;
    *)
        $LISP --eval "$MAIN";;
esac
