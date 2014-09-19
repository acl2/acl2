#!/bin/sh

# Shared Library Relocation Test
# Copyright (C) 2014 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# Original author: Jared Davis <jared@centtech.com>


# test.sh
#
# This script will build a simple ACL2 application that requires some Quicklisp
# libraries.  It will make sure the application works before and after running
# the quicklisp_clean Makefile target, deleting those libraries.  In other
# words, if this test works, it should be the case that the relocation
# mechanism really is working.

set -e

TESTDIR=`pwd`
echo "Starting sharedlibs relocation test in $TESTDIR"

BOOKSDIR=$TESTDIR/../../..

if [ "$ACL2" == "" ]
then
    ACL2="acl2"
    echo "Setting ACL2 to default: $ACL2"
fi

if [ "$STARTJOB" == "" ]
then
    STARTJOB="bash"
    echo "Setting STARTJOB to default: $STARTJOB"
fi

echo "Building Quicklisp if necessary..."
cd $BOOKSDIR
make USE_QUICKLISP=1 quicklisp

echo "Certifying app books if necessary..."
cd $TESTDIR
$STARTJOB -c "../../../build/cert.pl app"

echo "Making myapp-core executable..."
rm -f myapp-core* *.so
$STARTJOB -c "$ACL2 < mkapp.lsp &> mkapp.out"
ls -la myapp-core

echo "Checking to make sure some shared libraries got copied..."
ls -la *.so

echo "Running myapp to verify it works before copying Quicklisp stuff..."
$STARTJOB -c "./myapp-wrap.sh &> myapp.out"
ls -l myapp.out
echo "Checking myapp.out for regular files."
fgrep ":REGULAR-FILE" myapp.out

echo "Cleaning out Quicklisp files..."
cd $BOOKSDIR
make quicklisp_clean

cd $TESTDIR
echo "Running myapp again to verify that it still works..."
$STARTJOB -c "./myapp-wrap.sh &> myapp2.out"
ls -l myapp2.out

echo "Checking myapp2.out for regular files."
fgrep ":REGULAR-FILE" myapp2.out

echo "Test looks OK"






