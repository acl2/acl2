#!/bin/bash

# This program installs a web-based acl2+books combined manual as well
# as a corresponding text-based copy of that manual, suitable for the
# ACL2-Doc Emacs browser.

# The normal usage of this program, at UT CS, is first to ensure that
# /projects/acl2/devel/books/centaur/manual/ exists and is up to date,
# say, after running (in /projects/acl2/devel/):
#   make -j 8 regression-everything USE_QUICKLISP=1 ACL2=/projects/acl2/devel/ccl-saved_acl2h
# and to ensure that
# /projects/acl2/devel/books/system/doc/rendered-doc-combined.lsp is
# up to date, for example after running (in /projects/acl2/devel/):
#   make -j 8 DOC ACL2=/projects/acl2/devel/ccl-saved_acl2h
# Then, we typically execute the following in /projects/acl2/devel/:
#   bin/make-fancy-manual.sh
# But optional arguments may be given:
#   bin/make-fancy-manual.sh [booksdir] [destdir] [destfile]
# Note: if executable file update.sh exists in destdir/destfile, then
# it is executed with destfile as the argument.

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
