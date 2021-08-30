#!/bin/sh

# Matt Kaufmann will use this script to pull from the remote "acl2"
# repository only after a check is done that others have committed
# only under books/.

if [ `basename $PWD` = devel ] ; then \
    echo "ERROR: Must not be in a devel directory." ; \
    exit 1 ; \
fi

# The following does a "git fetch --all", as necessary in order to
# prepare for the "git merge" below.
echo "-----"
echo "Executing `dirname $0`/purity.sh"
echo "-----"
`dirname $0`/purity.sh

if [ $? -ne 0 ] ; then \
    echo 'ERROR: Not executing git merge command.' ; \
    exit 1 ; \
fi

echo "-----"
echo "Executing git merge remotes/origin/master"
echo "-----"
git merge remotes/origin/master

