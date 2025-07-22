#!/usr/bin/env bash

################################################################################

# Build the manual and deploy to the website.
# Adapted from bin/make-fancy-manual.sh, with some segments from
# books/build/jenkins/build-single.sh as well.
#
# Author: Grant Jurgensen (grant@kestrel.edu)

################################################################################

set -e

################################################################################

echo "Starting $0"
echo " -- Running in `pwd`"
echo " -- Running on `hostname`"
echo " -- PATH is $PATH"

source $JENKINS_HOME/env.sh

################################################################################

books="$WORKSPACE/books"

destdirmain="$WORKSPACE/manuals"
destdirsub=`date +%F-%H%M%S`
destdir="${destdirmain}/$destdirsub"
if [ -d $destdir ] ; then
    echo "ERROR: Directory $destdir already exists"
    exit 1
fi

if [ ! -d $books/doc/manual ] ; then
    echo "ERROR: Directory $books/doc/manual/ does not exist."
    exit 1
fi

if [ ! -f $books/system/doc/rendered-doc-combined.lsp ] ; then
    echo "ERROR: File $books/system/doc/rendered-doc-combined.lsp does not exist."
    exit 1
fi

if [ ! -f $books/system/doc/acl2-doc-search ] ; then
    echo "ERROR: File $books/system/doc/acl2-doc-search does not exist."
    exit 1
fi

# Clear old manuals
rm -rf $destdirmain
echo "mkdir -p $destdir"
mkdir -p $destdir

# Copy from source to destination and move to destination/manual/.
echo "cp -pr $books/doc/manual $destdir/manual"
cp -pr $books/doc/manual $destdir/manual
echo "cd $destdir/manual"
cd $destdir/manual

# General databases
perl "$destdir/manual/xdata2sql.pl"
perl "$destdir/manual/xdata2sql4seo.pl"

# Copy books/system/doc/rendered-doc-combined.lsp
echo "cp -p $books/system/doc/rendered-doc-combined.lsp $destdir/"
cp -p $books/system/doc/rendered-doc-combined.lsp $destdir/

# Gzip books/system/doc/rendered-doc-combined.lsp
echo "gzip $destdir/rendered-doc-combined.lsp"
gzip $destdir/rendered-doc-combined.lsp
chmod ugo+r $destdir/rendered-doc-combined.lsp.gz

# Copy books/system/doc/acl2-doc-search
echo "cp -p $books/system/doc/acl2-doc-search $destdir/"
cp -p $books/system/doc/acl2-doc-search $destdir/

# Gzip books/system/doc/acl2-doc-search
echo "gzip $destdir/acl2-doc-search"
gzip $destdir/acl2-doc-search
chmod ugo+r $destdir/acl2-doc-search.gz

################################################################################

# Deploy manual

scp -o BatchMode=yes \
    $SSH_EXTRA_ARGS \
    -r \
    -i "$LEEROY_MANUAL_SSH_FILE" \
    "$destdir" \
    $LEEROY_MANUAL_SSH_USERNAME@$MANUAL_DESTINATION:"manuals/$destdirsub"

ssh -o BatchMode=yes \
    $SSH_EXTRA_ARGS \
    -i "$LEEROY_MANUAL_SSH_FILE" \
    $LEEROY_MANUAL_SSH_USERNAME@$MANUAL_DESTINATION "./deploy-latest.sh $destdirsub 2> deploy.log"
