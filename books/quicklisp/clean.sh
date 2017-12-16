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

set -e

# Modification by Matt K.: check if we are in a github repository
# before doing git operations, and if not, then remove compiled files
# bundle.* but not bundle.lisp.

if [ "`git rev-parse --git-dir 2> /dev/null`" != "" ] ; then \
echo "Cleaning inside github repo" ;\
DIFF=`git status --porcelain bundle` ;\
if [ ! -z "$DIFF" ] ; then \
    echo "Cowardly refusing to clean because there are uncommitted changes in bundle/" ;\
    git status bundle | sed 's/^/   | /' ;\
    exit 1 ;\
fi ;\
echo "Cleaning quicklisp/bundle" ;\
git clean -f bundle ;\
else \
echo "Cleaning quicklisp/bundle (only compiled files 'bundle.*', since outside git repository)" ;\
cd bundle ;\
bundles="`ls -1 bundle.* | grep -v 'lisp$'`" || bundles="" ;\
if [ "$bundles" != "" ] ; then \
rm -f $bundles ;\
fi ;\
cd .. ;\
fi

echo "Cleaning asdf-home/cache/common-lisp"
rm -rf asdf-home/cache/common-lisp

echo "Cleaning quicklisp books"
../build/clean.pl


