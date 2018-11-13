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
#
#   -- The list of libraries to install is found in update-libs.lsp


set -e

DIFF=`git status --porcelain bundle`
if [ ! -z "$DIFF" ]
then
    echo "Cowardly refusing to update because there are changes in bundle/"
    git status bundle | sed 's/^/   | /'
    exit 1
fi

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
BUILD_DIR=`cd ../build; pwd`

rm -f quicklisp.lsp
rm -rf temp-quicklisp-inst

echo "Downloading Quicklisp..."
#curl http://beta.quicklisp.org/quicklisp.lisp -o quicklisp.lsp
wget http://beta.quicklisp.org/quicklisp.lisp -O quicklisp.lsp
$BUILD_DIR/wait.pl quicklisp.lsp

echo "Cleaning Bundle..."
./clean.sh

export XDG_CONFIG_HOME=`pwd`/asdf-home/config
export XDG_DATA_HOME=`pwd`/asdf-home/data
export XDG_CACHE_HOME=`pwd`/asdf-home/cache

echo "Updating Bundle..."
$STARTJOB -c "$LISP < update-libs.lsp &> update-libs.out"
cat update-libs.out


# Start of bordeaux-threads hack
#echo "Getting patched bordeaux-threads.  BOZO get rid of this step"
#echo "after the Lispworks patch gets into the main Quicklisp dist."
#svn export https://github.com/sionescu/bordeaux-threads/trunk bundle/local-projects/bordeaux-threads
#rm -rf bundle/software/bordeaux-threads-v0.8.4-git
# End of bordeaux-threads hack



rm -rf temp-quicklisp-inst
rm quicklisp.lsp

date > bundle/timestamp.txt
touch bundle/cert_pl_exclude

git status

echo "Done updating.  Suggested next steps:"
echo " -- Review the changes to bundle/"
echo " -- Git add any new libraries, etc."
echo " -- Make a preliminary commit"
echo " -- Do a full ACL2 regression, etc"

