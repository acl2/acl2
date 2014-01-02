#!/bin/sh

# XDOC Documentation System for ACL2
# Copyright (C) 2009-2013 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software# you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation# either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY# without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program# if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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

cd download

echo "Creating manual.tar.gz"
tar cvf - manual | gzip -9 > manual.tar.gz

echo "Creating manual.tar.bz2"
tar cvf - manual | bzip2 -z -9 > manual.tar.bz2

echo "Creating manual.zip"
zip -r -9 manual.zip manual

rm -rf manual


