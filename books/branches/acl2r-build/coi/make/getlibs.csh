#!/bin/csh -f

# Syntax: getlibs subdir book

# For the given subdirectory (of a top-level directory in the Makelibs BOOKS),
# find all the directories that its build depends on.

set subdir = $1
set book   = $2

set templibs = /tmp/$user.getlibs.$$

if (-e $subdir/Makefile) then

    # Use a dummy make to extract the value of $(LIBS) in the Makefile:
    #
    # Get the value of $(LIBS) from this $dir/.../Makefile with a dummy "make"
    # on the default target.  Use "MAKE=echo" to turn off forced recursive
    # submakes, if any.
    #
    # Select the book names after the "LIBS =" (note that they have leading
    # colons)
    #
    # Temporarily save the list of names

    make -pn MAKE=echo -C $subdir \
    | expand \
    | egrep "^LIBS = " \
    | sed -e 's/LIBS = //' \
    > $templibs

    # Look up each LIBS value in the directory definitions file DIRS and
    # replace it with the directory it symbolizes.  Remove all subdirectories
    # from the resulting path: only the top level directories count.  Append
    # ".all" to get the target name for use in the Makefile that we're
    # building.
    #
    # Emit the resulting target (but suppress it if it's the same as
    # $book.all, in order to avoid Makefile cirularities).
    #
    # Note the normalization of whitespace in DIRS that makes life easier for
    # the greps and seds that follow.

    foreach lib (`cat $templibs`)

        expand DIRS \
	| sed -e 's/^  *//' \
              -e 's/  */ /g' \
	| grep "^$lib =" \
	| sed -e "s/^$lib = ..\///" \
	      -e 's/\/.*//' \
	      -e 's/$/.all/' \
	| grep -v "^$book.all"'$'

    end

endif

/bin/rm -f $templibs
