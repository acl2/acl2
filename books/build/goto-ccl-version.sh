# This is provided to the community by the community, with no claims
# of ownership -- it is in the public domain, as found on a pastebin
# site.

#!/bin/sh

# Usage: goto-ccl-version.sh [REVISION]
#
# Example: goto-ccl-version.sh 16345

set -e

# cd ccl-linux

REV=$1

EXTERNALS=`svn propget svn:externals . | awk '{print $2}'`
echo "Switching " `pwd` "to revision $1"
echo "Externals = $EXTERNALS"
echo "Note that all subdirectories of svn will first be updated to the most"
echo "recent revision, and then they will be updated to the specific revision."

HERE=`pwd`

svn update -r $REV
for f in $EXTERNALS
do
    echo "Switching to $REV in $HERE/$f"
    cd $HERE/$f; svn update -r $REV
done

echo "I think that's it?"
