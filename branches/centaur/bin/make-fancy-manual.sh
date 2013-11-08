#!/bin/bash

# Example with all arguments given:
# make-fancy-manual.sh \
#  /projects/acl2/devel/books/system/doc \
#  /u/www/users/moore/acl2/manuals \
#  2013-10-25-acl2-only

if [ $# -lt 1 ] ; then
    books=/projects/acl2/devel/books
else
    books=$1
fi

if [ $# -lt 2 ] ; then
    destdir=/u/www/users/moore/acl2/manuals
else
    destdir=$2
fi

if [ $# -lt 3 ] ; then
    destfile=`/bin/date +%F`
else
    destfile=$3
fi

dest=${destdir}/$destfile
if [ -d $dest ] ; then
    echo "ERROR: Directory $dest already exists"
    exit 1
fi
echo "mkdir $dest"
mkdir $dest

# Copy from source to destination and move to destination/manual/.
echo "cp -pr $books/centaur/manual $dest/manual"
cp -pr $books/centaur/manual $dest/manual
echo "cd $dest/manual"
cd $dest/manual

# Create file, fix its permission, and add link.
echo "perl xdata2sql.pl"
perl xdata2sql.pl
echo "chmod +x xdataget.pl"
chmod +x xdataget.pl
echo "ln -s xdataget.pl xdataget.cgi"
ln -s xdataget.pl xdataget.cgi

# Replace the last line.
mv config.js config.js.orig
sed 's/^var XDATAGET = ""/var XDATAGET = "xdataget.cgi"/g' config.js.orig > config.js

# Copy books/system/doc/rendered-doc-combined.lsp
echo "cp -p $books/system/doc/rendered-doc-combined.lsp $dest/"
cp -p $books/system/doc/rendered-doc-combined.lsp $dest/

# Gzip books/system/doc/rendered-doc-combined.lsp
echo "gzip $dest/rendered-doc-combined.lsp"
gzip $dest/rendered-doc-combined.lsp

# Run update script, if available
cd $destdir
if [ -x update.sh ] ; then \
    echo "Running ./update.sh $destfile in directory $destdir"
    ./update.sh $destfile
fi
