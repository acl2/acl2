#!/bin/sh

tgtdir="$1"
srcdir="$2/$tgtdir"

# The following rather odd way to get the files of interest is constructed in
# order to avoid getting any error output.  It would be great to be taught a
# better way.  We expect $files to be free of directory names.

files="`ls -1 $srcdir | grep '[.]lisp$'`"
files="`ls -1 $srcdir | grep '[.]lsp$'` $files"
files="`ls -1 $srcdir | grep '[.]pl$'` $files"
files="`ls -1 $srcdir | grep '[.]defpkg$'` $files"
files="`ls -1 $srcdir | grep '[.]acl2$'` $files"
files="`ls -1 $srcdir | grep '[.]acl2x-source$'` $files"
files="`ls -1 $srcdir | grep '^Makefile$'` $files"
files="`ls -1 $srcdir | grep '^README$'` $files"

cd $tgtdir

echo "Entering `pwd`"

for file in $files ; do \
    if [ ! -f $file ]; then \
	cmd="ln -s $srcdir/$file ." ; \
	echo $cmd ; \
	$cmd ; \
    fi ;
done
