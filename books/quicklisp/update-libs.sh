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
    if [ $(command -v sbcl) ]
    then
       echo "Defaulting LISP to sbcl"
       LISP=sbcl
    elif [ $(command -v ccl) ]
    then
       echo "Defaulting LISP to ccl"
       LISP=ccl
    else
       echo "Can't find LISP: set \$LISP"
       exit 1    
    fi
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
if [ $(command -v curl) ]
then
    curl http://beta.quicklisp.org/quicklisp.lisp -o quicklisp.lsp
elif [ $(command -v wget) ]
then
    wget http://beta.quicklisp.org/quicklisp.lisp -O quicklisp.lsp
else
    echo "** Error: Neither curl nor wget installed"
fi

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

echo ""
echo "-- PATCHES TO CHECK --"
echo "For each patch mentioned here:"
echo "if fixed upstream, remove the entry below;"
echo "if still a problem, reapply patch to new bundle."
echo "1. osicat make-fd-stream error on ccl"
echo "   https://github.com/acl2/acl2/pull/1517"
echo "   As of 2023-11-20,"
echo "   the new version of osicat still has this problem"
echo "   and another problem with c compilation (not recorded);"
echo "   for this reason, after updating the libs,"
echo "   the osicat version was reverted as in this commit:"
echo "   https://github.com/acl2/acl2/commit/9a3fd9cd2a3319f137bbed86c9189c67a68e12da"
echo "2. In the latest dexador (as of 2023-11-20), "
echo "   two uses of the package bt2 didn't parse because the api v2"
echo "   of bordeaux-threads didn't load (not investigated further)."
echo "   Those were changed to use the previous bt: interface"
echo "   as in this commit:"
echo "   https://github.com/acl2/acl2/commit/68a1a4efe2e9e15a7fc3e94aa0f4bbf1dafc1bcd"
