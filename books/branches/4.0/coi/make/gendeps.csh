#!/bin/csh -f

# Syntax: gendeps.csh [ book ... ]

# Extract the build dependences among the argument books (directories) from
# the $(LIB) variable values in their Makefiles.  Use these dependences to
# generate the list of books in build order.

# Note: any books specified in the argument list to this script that do not
# exist as directories will be kept as books without dependences on the
# presumption that they will be added later.

# $all_deps will be populated with dummy Makefile targets, one for each book.

set all_deps = ()

# If there's a fatal error, go to quit: (which does not erase the temporary
# files)

onintr quit

# The temporary file $Makefile_all will be populated with the interdependences
# of the books expressed in dummy targets.  A dummy "make" will be run so that
# the build order can be extracted from the output in $Makefile_out.

set Makefile_all = /tmp/$user.gendeps.$$.Makefile.all

/bin/cp /dev/null $Makefile_all

set Makefile_out = /tmp/$user.gendeps.$$.Makefile.out

# Look at each book in turn to build its dependence line in $Makefile_all

# $book_path is the path to the directory of which all the books are children.

set book_path = ""

# $Makefile_bookdeps is used for accumulating the dependences of each book,
# one at a time.

set Makefile_bookdeps = /tmp/$user.gendeps.$$.Makefile.bookdeps

if ( "` uname -s `" == "Linux") then
  setenv UNIQUE_FLAG "-f"
else
  setenv UNIQUE_FLAG ""
endif

# Remove duplicate dirs, preserving order (Linux only)
#
set $UNIQUE_FLAG dirs = ($*)

foreach dir ($dirs)

    ## echo Checking $dir > /dev/tty

    # All the books must be sibling directories referring to each
    # other by simple names.

    set book = ${dir:t}

    # All books must all have the same directory prefix, so we take just the
    # first.

    if ("$book_path" == "") then
      set book_path = ${dir:h}
      if ("$book_path" == "$book") then
	set book_path = "."
      endif
    endif

    # Generate the dummy target for this book for later use

    set all_deps = ($all_deps $book.all)

    # Start building the dummy target for this book

    echo -n  "$book.all: " >> $Makefile_all

    # Compute the dependences for this book

    cp /dev/null $Makefile_bookdeps

    if (-d $dir) then

	# Get the values of $(LIBS) for $(book) from every $dir/.../Makefile
	# and build this book's Makefile target's dependences from them below

	find $dir -type d -exec ./getlibs.csh {} $book \; >> $Makefile_bookdeps

    endif

    set book_deps = ` sort -u $Makefile_bookdeps `

    # Finish building the target line for this book

    echo $book_deps >> $Makefile_all

    # Place the dummy action after the dummy target

    /bin/echo -e '\ttouch $@' >> $Makefile_all

    echo >> $Makefile_all

end

if ($#all_deps > 1) then

    # Tie together all the books found, as dependences of the master target
    # all.all

    echo "all.all: $all_deps" >> $Makefile_all

    /bin/echo -e '\ttouch $@' >> $Makefile_all

    # Now do a dummy build of all.all to generate the list of books in build
    # order from $Makefile_all.  Output is to stdout.

    ## echo Generating BOOKS > /dev/tty

    echo -n "BOOKS ="

    make -n -f $Makefile_all all.all > $Makefile_out

    if ($status) goto quit

    # Emit the newly sorted definition for BOOKS

    grep touch $Makefile_out \
	|  grep -v 'touch.all\.all$' \
	|  sed -e "s/touch /\t$book_path\//" \
	       -e 's/[.]all$/ \\/' \
	|  sed -e '$s/ \\$//'

    echo ""

else

    # No books were specified, so emit an empty definition

    echo "BOOKS ="

endif

# As an extra, list (as comments) Makefile-style rule lines for each
# book and the books it depends on.
#
# For example, extract "#foo: bar bas" from "foo.all: bar.all bas.all"

fgrep .all: $Makefile_all \
    | grep -v "^all.all:" \
    | sed -e "s/^/\n# /" \
	  -e 's/: $/:/' \
	  -e "s/: /:\n#\t/" \
    | sed -e "s/[.]all//g" \
    | fmt -c -p "#"

/bin/rm -f $Makefile_all $Makefile_bookdeps $Makefile_out

quit:

exit
