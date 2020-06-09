#!/usr/bin/env bash

# This program installs a web-based acl2+books combined manual as well
# as a corresponding text-based copy of that manual, suitable for the
# ACL2-Doc Emacs browser.

# The normal usage of this program, at UT CS, is first to ensure that
# books/doc/manual/ exists and is up to date, say, after running:
#   make -j 8 regression-everything USE_QUICKLISP=1 ACL2=/projects/acl2/acl2/ccl-saved_acl2
# and to ensure that
# books/system/doc/rendered-doc-combined.lsp is
# up to date, for example after running:
#   make -j 8 DOC ACL2=/projects/acl2/acl2/ccl-saved_acl2
# Then, we typically execute the following in a directory like /projects/acl2/acl2/:
#   bin/make-fancy-manual.sh
# But optional arguments may be given:
#   bin/make-fancy-manual.sh [booksdir] [destdirmain] [destdirsub]
# Note: if executable file update.sh exists in destdirmain/destdirsub, then
# it is executed in destdirmain with destdirsub as the argument.

if [ $# -lt 1 ] ; then
    books=`pwd`/books
else
    books=$1
fi

if [ $# -lt 2 ] ; then
    destdirmain=/u/www/users/moore/acl2/manuals
else
    destdirmain=$2
fi

if [ $# -lt 3 ] ; then
    destdirsub=`/bin/date +%F`
else
    destdirsub=$3
fi

destdir=${destdirmain}/$destdirsub
if [ -d $destdir ] ; then
    echo "ERROR: Directory $destdir already exists"
    exit 1
fi
echo "mkdir $destdir"
mkdir $destdir

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

# Create version of the manual optimized for search engines
# (instructions from David Rager):
pushd $books/doc/manual
chmod +x ./xdata2sql4seo.pl
perl xdata2sql.pl
./xdata2sql4seo.pl
chmod o+r ./xdata-seo.db
chmod ugo+r xdata.db
chmod ugo+rx index-seo.php
popd

# Copy from source to destination and move to destination/manual/.
echo "cp -pr $books/doc/manual $destdir/manual"
cp -pr $books/doc/manual $destdir/manual
echo "cd $destdir/manual"
cd $destdir/manual

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

# Run update script, if available
cd $destdirmain
if [ -x update.sh ] ; then \
    echo "Running ./update.sh $destdirsub in directory $destdirmain"
    ./update.sh $destdirsub
fi
