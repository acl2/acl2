#!/bin/sh

if [ $# -lt 2 ] ; then
    echo "Usage:   make-fancy-manual source-dir target-dir [suffix]"
    echo "Example:"
    echo "$0 \\"
    echo " /projects/acl2/devel/books/centaur \\"
    echo " /u/www/users/moore/acl2 \\"
    echo " 2013-10-24b"
    exit 1
fi

source=$1
target=$2

# Make destination directory.
if [ $# -lt 3 ] ; then
    suffix=`/bin/date +%F`
else
    suffix=$3
fi
dest=${target}/acl2-xdoc-$suffix
if [ -d $dest ] ; then
    echo "ERROR: Directory $dest already exists"
    exit 1
fi
echo "mkdir $dest"
mkdir $dest

# Copy from source to destination and move to destination/manual/.
echo "cp -pr $source/manual $dest/manual"
cp -pr $source/manual $dest/manual
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

