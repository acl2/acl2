#!/bin/sh

# XDOC Documentation System for ACL2
# Copyright (C) 2009-2013 Centaur Technology
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

# Usage: sh "zip.sh" "/path/to/manual/directory"

set -e

if [ "$#" -ne 1 ]
then
    echo "Usage: zip.sh [path to an xdoc manual]"
    exit 1
fi

DIR=$1
cd $DIR

# Basic sanity checking to make sure we're in the right place.

if [ ! -f "xdoc.js" ]
then
    echo "zip.sh: xdoc.js not found?"
    exit 1
fi

if [ ! -f "xindex.js" ]
then
    echo "zip.sh: xindex.js not found?"
    exit 1
fi

if [ ! -f "xdata.js" ]
then
    echo "zip.sh: xdata.js not found?"
    exit 1
fi

rm -rf download

FILES=`ls`
echo "FILES are $FILES"

mkdir -p download

mkdir download/manual
cp -R -- $FILES download/manual

echo "Creating index.html in download/ directory"
cp download-index.html download/index.html

cd download

echo "Creating manual.tar.gz"
tar cvf - manual | gzip -9 > manual.tar.gz

echo "Creating manual.tar.bz2"
tar cvf - manual | bzip2 -z -9 > manual.tar.bz2

echo "Creating manual.zip"
zip -r -9 manual.zip manual

rm -rf manual
