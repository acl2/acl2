#!/bin/sh

# ACL2 Quicklisp Interface
# Copyright (C) 2008-2015 Centaur Technology
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

# update-libs.sh -- Updates bundled libraries to the latest versions in Quicklisp
#
# Usage:  ./update-libs.sh

set -e

if [ -z "$LISP" ]
then
    echo "Defaulting LISP to ccl"
    LISP=ccl
fi

if [ -z "$STARTJOB" ]
then
    echo "Defaulting STARTJOB to bash"
    STARTJOB=bash
fi

echo "Rebuilding Quicklisp Bundle"
BUILD_DIR=`cd ../../build; pwd`

rm -f quicklisp.lsp
rm -rf temp-quicklisp-inst

echo "Downloading Quicklisp..."
curl http://beta.quicklisp.org/quicklisp.lisp -o quicklisp.lsp
$BUILD_DIR/wait.pl quicklisp.lsp

echo "Updating Bundle..."
$STARTJOB -c "$LISP < update-libs.lsp &> update-libs.out"
cat update-libs.out

rm -rf temp-quicklisp-inst






