#!/bin/sh
#
# File:
#
#   make/Makefile.bash
#
# Synopsis:
#
#   Makefile.bash deps
#   Makefile.bash all
#   Makefile.bash [target...]
#
# Environment variables read:
#
#   JOBS
#   ACL2
#   ACL2_SYSTEM_BOOKS
#   BOOKS
#   DEBUG
#   LDFILES
#   LIB_ROOT
#   LIBS
#   MAKEDIR
#   MAKELEVEL
#   RETAIN_ACL2_LIBRARY_LINKS
#   SILENT
#
# Description:
#
#   Computes the dependencies for this build and then invokes a real Makefile
#   (Makefile.aux) in order to build the targets.
#
# Author: Jared Davis

# Modified by Doug Harper

# [ ] CDH: Support a failsoft option for DIRS so that the examples directory
# tangle can be unsnarled.

# Identification -------------------------------------------------------------

# CDH: Protect against funny paths containing symbolic links: stand at
# the real path of the current directory.

cd ` pwd -P `

# echo MAKEFLAGS = '"'$MAKEFLAGS'"'
echo 'RAMS['$MAKELEVEL']: Entering directory' '`'`pwd`"'"

# Configuration --------------------------------------------------------------

# Number of parallel jobs for make
if [ -n "$JOBS" ]
then
  MAKE_JOBS="-j${JOBS}"
else
  MAKE_JOBS=""
fi

# What file should we write the dependencies to?
DEPS_FILE=`pwd -P`/"Makefile.deps"

# What file should we write the add-include-book-dirs lines to?
ACL2_OUT_FILE=`pwd -P`/"Makefile.acl2"

# What file should we write the ACL2_FOO_BOOKS lines to?
MAKE_OUT_FILE=`pwd -P`/"Makefile.dirs"

if [ $OSTYPE == "msys" ]
  then
    OS_PLATFORM=`uname -s`
  else
    OS_PLATFORM=`uname -o`
fi

#|==========================================================================|#
#|                                                                          |#
#|                                Functions                                 |#
#|                                                                          |#
#|==========================================================================|#

function Debug () {
    if [ -n "$DEBUG" ]
    then
	echo "[Makefile.bash]: $1"
    fi
}

function DebugNewline () {
    if [ -n "$DEBUG" ]
    then
	echo ""
    fi
}

# IncludeBookDependencies Function
#
# This function looks through a file (given as its first argument, $1) and
# tries to find any instances of (include-book ...).  It then adds a dependency
# onto its second argument, $2, that says that $2 depends on all of the things
# found in $1.

# CDH: Every possible case variant for "include-book"

Include_Book="[iI][nN][cC][lL][uU][dD][eE]-[Bb][oO][oO][kK]"

function IncludeBookDependencies ()
{

Debug "IncludeBookDependencies($1, $2) invoked"

# Find all the include-book lines in our argument ($1).

INCLUDES=`egrep --mmap -i '^[^;"]*\([ \t]*include-book[ \t]*\".*\"' $1 \
		| egrep -v ';[ \t]*RAMS.EXEMPT'`

# We will loop through them one by one.  To do this, we need to first
# set up our for-loop separator to be a newline.  (See the ProcessDirsLine
# function for a discussion of this).

IFS="
"

# Now process each include-book line in turn.

for line in $INCLUDES
do

    Debug "Found $line"

    # We handle up to one include-book command per line.  It might be wrapped
    # in local, it might have a :dir, it might not start on the first
    # character, and so forth.  We first try to extract the name of the book,
    # by eliminating everything up until the first quote in the include-book
    # command, and then eliminating everything after the next quote.

    # apparently "i" is not a standard flag to sed, replacing this at rkrug's
    # suggestion...
    #FILENAME=`echo $line \
    #          | sed "s/.*(include-book[        ]*\"//i" \
    #          | sed "s/\".*//"`

    # CDH expanding tabs to blanks and using a simpler sed pattern

    FILENAME=`echo $line \
	| tr '\t' ' ' \
	| sed "s/.*( *${Include_Book} *\"//" \
	| sed "s/\".*//"`

    # We now check to see if :dir occurs in the include-book command, and if so,
    # we extract the part that comes after it (i.e., if the line is :dir :bags,
    # we extract :bags), and then convert it into ACL2_BAGS_BOOKS.

    DIR=""
    if [ `echo $line | grep -i ":dir"` ]
    then

	# replacing "i" flag to sed with uglier but more standard expression
	#DIR=`echo $line \
	#     | sed "s/.*(include-book[^:]*:dir[        ]*://i" \
	#     | sed "s/[        ]*).*//"`

	# CDH Expanding tabs to blanks, folding to upper case, and using
        # simpler sed patterns

	DIR=`echo $line \
		| tr '\t' ' ' \
                | tr '[:lower:]' '[:upper:]' \
		| sed "s/.*( *INCLUDE-BOOK[^:]*//" \
		| sed "s/ *:TTAGS *([^)]*)//" \
		| sed "s/ *:DIR *://" \
		| sed "s/ *).*//"`
	DIR="ACL2_`echo $DIR`_BOOKS"
	echo "$2: \$($DIR)/$FILENAME.cert" >> $TEMP
	Debug "DEP[1]: $2: \$($DIR)/$FILENAME.cert"
    else
	echo "$2: $FILENAME.cert" >> $TEMP
	Debug "DEP[2]: $2: $FILENAME.cert"
    fi

done

}

function LDDependencies ()
{

Debug "LDDependencies($1) invoked"

# Find all the ld lines in our argument ($1)

LDS=`egrep --mmap -i '^[^;]*\([ \t]*ld[ \t]*\".*\"' $1 \
		| egrep -v ';[ \t]*RAMS.EXEMPT'`

IFS="
"

for line in $LDS
do

  Debug "Found $line"

  # CDH Expanding tabs to blanks and using a simpler sed pattern

  FILENAME=`echo $line \
		| tr '\t' ' ' \
		| sed "s/^[^;]*( *ld *\"//" \
		| sed "s/\".*//"`

# I am attempting to make this handle :dir on lds but don't understand
# this code all that well. -ews
  DIR=""
  if [ `echo $line | grep -i ":dir"` ]
      then
	# replacing "i" flag to sed with uglier but more standard expression
	#DIR=`echo $line \
	#     | sed "s/.*(include-book[^:]*:dir[        ]*://i" \
	#     | sed "s/[        ]*).*//"`

	# CDH Expanding tabs to blanks, folding to upper case, and using
        # simpler sed patterns

      DIR=`echo $line \
	   | tr '\t' ' ' \
           | tr '[:lower:]' '[:upper:]' \
	   | sed "s/.*(LD[^:]*:DIR *://" \
	   | sed "s/ *).*//"`
      DIR="ACL2_`echo $DIR`_BOOKS"
      echo "$2: \$($DIR)/$FILENAME" >> $TEMP
      Debug "DEP: $2: \$($DIR)/$FILENAME"
  else
      echo "$2: $FILENAME" >> $TEMP
      Debug "DEP: $2: $FILENAME"
  fi

done

}

#|==========================================================================|#
#|                                                                          |#
#|                           Start of Processing                            |#
#|                                                                          |#
#|==========================================================================|#

Debug "Using DEPS_FILE=$DEPS_FILE"
Debug "Using ACL2_OUT_FILE=$ACL2_OUT_FILE"
Debug "Using MAKE_OUT_FILE=$MAKE_OUT_FILE"
Debug "Using LIBS=$LIBS"

# Internal Variables ---------------------------------------------------------

CRUX_OLD_FILE=/tmp/Makefile.bash.$USER.$$.old
CRUX_NEW_FILE=/tmp/Makefile.bash.$USER.$$.new

EOL_PENDING=0

# Library Path Computation ---------------------------------------------------

echo -n "Setting up library paths ... "
EOL_PENDING=1
DebugNewline

Debug "OS Platform: $OS_PLATFORM"

# First accumulate and sort all DIRS keyword entries, removing any duplicates,
# and standardizing them into lower case.  The results are left in $ENTRIES,
# separated by newlines.

if [ -x /bin/mktemp ]
  then
    TEMP=`mktemp /tmp/rams.XXXXXX` || exit 1
  else
    TEMP=/tmp/rams_libpaths.`echo $PWD | sed -e yc/c_c`
fi
Debug "Libpaths temp file is $TEMP"
echo -n "" > $TEMP

if [ -e $MAKEDIR/DIRS ]
then
    if [ -e DIRS ]
    then
	LINES=`grep "^:" $MAKEDIR/DIRS && grep "^:" DIRS`
    else
	LINES=`grep "^:" $MAKEDIR/DIRS`
    fi
else
    LINES=""
fi

IFS="
"

# NOTE: some sed versions do not support '\t', so type TAB instead.
# CDH: No, expanding tabs to blanks and using a simpler sed pattern.
for line in $LINES
do
    COLON_PART=`echo $line \
	| tr '\t' ' ' \
	| sed "s/ *=[^=]*//" \
	| tr '[:upper:]' '[:lower:]'`
    echo $COLON_PART >> $TEMP
done

# Note: don't use sort --unique, it's not supported on all systems.  -u does
# the same thing and seems to be more common.

ENTRIES=`sort -u $TEMP`

Debug "Entries are $ENTRIES"

# Now check to make sure that each library keyword in LIBS has a corresponding
# entry in DIRS, signalling an error and quitting if this isn't the case.  Note
# that the keywords in $ENTRIES need not be in lower case, hence the "grep -i".

IFS=" "
for lib in $LIBS
do
    # CDH New safeguard
    if [ "$lib" == ":system" ]
    then
	if (( $EOL_PENDING ))
	then
	  echo ""
	  EOL_PENDING=0
	fi
	echo ""
	echo "Error: You may not assign to :system in DIRS."
	echo "  Set ACL2_SYSTEM_BOOKS instead."
	echo ""
        rm $TEMP
	exit 1
    elif [ -n "`echo $ENTRIES | grep -i ^$lib'$'`" ]
    then
	Debug "  $lib checks out ok."
    else
	if (( $EOL_PENDING ))
	then
	  echo ""
	  EOL_PENDING=0
	fi
	echo ""
	echo "Error: $lib not found in DIRS or $MAKEDIR/DIRS."
	echo ""
	echo "  The Makefile indicates that $lib is a necessary external" \
	     " library,"
	echo "  but $lib is never mentioned in DIRS or $MAKEDIR/DIRS."
	echo ""
	rm $TEMP
	exit 1
    fi
done

# Now go through each entry we had found, figure out what the "real" path of it
# is (i.e., the "final" line of the mythical MAKEDIR/DIRS + DIRS combination
# file), and resolve this path, storing it into a temporary file.

if [ -x /bin/mktemp ]
  then
    TEMP_ACL2OUT=`mktemp /tmp/rams.XXXXXX` || exit 1
    TEMP_MAKEOUT=`mktemp /tmp/rams.XXXXXX` || exit 1
  else
    TEMP_ACL2OUT=/tmp/rams_acl2out.`echo $PWD | sed -e yc/c_c`
    TEMP_MAKEOUT=/tmp/rams_makeout.`echo $PWD | sed -e yc/c_c`
fi

# CDH More readable

cat <<INLINE_INPUT_BOUNDARY > $TEMP_ACL2OUT
;; $ACL2_OUT_FILE
;;
;; This file is automatically generated.  Do not hand edit!
;;
;; If you need to add events of the form
;;
;;   (add-include-book-dir :keyword "pathname")
;;
;; instead edit the file ./DIRS, adding lines of this form:
;;
;;   :keyword = pathname
;;
;; Use "make help" for more information.

INLINE_INPUT_BOUNDARY

# CDH More readable

cat <<INLINE_INPUT_BOUNDARY > $TEMP_MAKEOUT
# $MAKE_OUT_FILE
#
# This file is automatically generated.  Do not hand edit!
#
# If you need to add
#
#   :keyword = pathname
#
# lines in order to generate "add-include-book-dir" events to inform the
# ":dir" option of "include-book", write them in the file ./DIRS instead!
#
# Use "make help" for more information.

INLINE_INPUT_BOUNDARY

IFS="
"

# CDH Avoid spurious matches such as ":cutpoints" on ":cutpoints-compositional"
# by forcing a blank after $LIBS and looking for a blank to terminate $entry.
#
# Note that since $entry has a leading colon, it won't match "SENTINEL".

for entry in $ENTRIES
do
    WHICH_DIRS="none yet"
    if [ -n "`echo $LIBS SENTINEL | grep -i \"$entry \"`" ]
    then
	Debug "Processing $entry"

	# Figure out where this entry should come from and set $LAST to be
	# the line, e.g., :bags = ../bags, and set $BASE_PATH to be the path
	# to the DIRS file that $LAST comes from.

	if [ -e DIRS ]
	then
	    echo -n "" > $TEMP
	    #
	    # CDH avoid spurious matches such as ":foo" on ":foo-bar"
	    # by looking for the terminating blank or equal sign.  The
	    # use of tr '\t' ' ' means we don't have to look for tabs.
	    #
	    cat DIRS | tr '\t' ' ' | grep -i "^$entry *="  >> $TEMP
	    LAST=`tail -n 1 $TEMP`
	else
	    LAST=""
	fi

	# Hope that only Cygwin uses '/cygdrive/c'.
	if [ -n "$LAST" ]
	then
	    Debug "LAST=$LAST comes from DIRS"
	    BASE_PATH=`pwd | sed -e "s/\/cygdrive\/c/c:/"`
	    WHICH_DIRS="local"
	else
	    if [ -e $MAKEDIR/DIRS ]
	    then
		echo -n "" > $TEMP
		#
		# CDH avoid spurious matches such as ":foo" on ":foo-bar"
		# by looking for the terminating blank or equal sign.  The
		# use of tr '\t' ' ' means we don't have to look for tabs.
		#
		cat $MAKEDIR/DIRS | tr '\t' ' ' | grep -i "^$entry *=" >> $TEMP
		LAST=`tail -n 1 $TEMP`
		Debug "LAST=$LAST comes from $MAKEDIR/DIRS"
		BASE_PATH=$MAKEDIR
		WHICH_DIRS="master"
	    fi
	fi

	# CDH If $LIB_ROOT is set, it overrides $BASE_PATH for $MAKEDIR/DIRS

	if [[ "$WHICH_DIRS" == "master" \
	      && "$LIB_ROOT" != "" \
	      && "$LIB_ROOT" != "$MAKEDIR/.." ]]
	then
	    BASE_PATH=$LIB_ROOT/make
	fi

	if [ ! "$LAST" ]
	then
	    if (( $EOL_PENDING ))
	    then
	      echo ""
	      EOL_PENDING=0
	    fi
	    echo ""
	    echo "Fatal Internal error in RAMS Makefile system."
	    echo "Entry $entry has not been found in DIRS or $MAKEDIR/DIRS."
	    echo "This should never happen."
	    echo ""
	    rm -f $TEMP $TEMP_ACL2OUT $TEMP_MAKEOUT
	    exit 1
	fi

	# Split $LAST into a colon part (e.g., :bags) and a path part, (e.g.,
	# ../bags), and then check to make sure that the path exists.

	# CDH Expanding tabs to blanks and using simpler sed patterns

	COLON_PART=`echo $LAST | tr '\t' ' ' | sed "s/ *=[^=]*//"`
	PATH_PART=`echo  $LAST | tr '\t' ' ' | sed "s/[^=]*= *//"`

	# Is this an absolute path?

	if echo $PATH_PART | grep '^/' 2>&1 > /dev/null
	then
	    BASE_PATH=
            PATH_PART=`echo $PATH_PART | sed "s/^\///"`
# 	    echo ""
# 	    echo 'Error: You may not use absolute paths in DIRS files.'
# 	    echo "File:  $BASE_PATH/DIRS"
# 	    echo "Line:  $LAST"
# 	    echo ""
# 	    rm -f $TEMP $TEMP_ACL2OUT $TEMP_MAKEOUT
# 	    exit 1
	fi

	# Is this a local path based on LIB_ROOT?

	if echo $PATH_PART \
	   | egrep '^[$][\{\(]?LIB_ROOT[\)\}]?[/]' 2>&1 > /dev/null
	then
	    if [[ "$WHICH_DIRS" == "local" ]]
	    then
		PATH_PART=`echo $PATH_PART | sed 's/\$[{(]*LIB_ROOT[)}]*.//'`
		BASE_PATH=$LIB_ROOT
	    else
		echo ""
		echo 'Error: You may not use $LIB_ROOT in the master DIRS file'
	        echo "File:  $BASE_PATH/DIRS"
	        echo "Line:  $LAST"
		echo ""
		rm -f $TEMP $TEMP_ACL2OUT $TEMP_MAKEOUT
		exit 1
	    fi
	fi

	if [ ! -d $BASE_PATH/$PATH_PART ]
	then
	    if (( $EOL_PENDING ))
	    then
	      echo ""
	      EOL_PENDING=0
	    fi
	    echo ""
	    echo "Error: $BASE_PATH/$PATH_PART is not a directory."
	    echo "  According to the DIRS files, this is the location of the "
	    echo "  $COLON_PART library, which the Makefile indicates" \
		 "is necessary."
	    echo "  Perhaps you have not checked out the $COLON_PART module" \
		 "from CVS?"
	    echo ""
	    rm -f $TEMP $TEMP_ACL2OUT $TEMP_MAKEOUT
	    exit 1
	fi

	# We now resolve the path: we remove all indirection and eliminate
	# symlinks in order to get the real location of this directory.
	#
	# Continuing our example where line is ":bags = ../bags",
	# The path part is ../bags, so if we are in, say, /home/jared/foo,
	# then the RESOLVED_PATH should be /home/jared/bags.

	if [ $RETAIN_ACL2_LIBRARY_LINKS ]
	then
	    RESOLVED_PATH="`cd $BASE_PATH/$PATH_PART; pwd \
				| sed -e \"s/\/cygdrive\/c/c:/\"`"
	else
	    RESOLVED_PATH="`cd $BASE_PATH/$PATH_PART; pwd -P \
				| sed -e \"s/\/cygdrive\/c/c:/\"`"
	fi

	# We now compute the book name as it will appear in Makefiles.  We
	# just drop the colon from the COLON_PART and replace it with its
	# upper-case counterpart, e.g., "BAGS" in our example.

	BOOK_NAME="ACL2_`echo $COLON_PART \
			 | sed -e "s/://" \
			 | tr '[:lower:]' '[:upper:]'`_BOOKS"

	# Write the line to our temporary ACL2 and MAKE files.

	# Note: it's important that this path ends in a slash, so we manually
	# insert one.  Otherwise, ACL2 will be upset when it processes the
	# add-include-book-dir commands.

	# For working on MINGW (with or without ACL2s) the ACL2 image
        # wants absolute paths starting with the MS-DOS style drive
        # letter (e.g. C:) and forward slashes as separators in the
        # remainder of the path.  This mangling should be done for the
        # ACL2_OUT_FILE as it is what ACL2/ACL2s reads.  The paths in the
        # MAKE_OUT_FILE should no be mangled as that is what RAMS uses.

	if [ $OSTYPE == "msys" ]
        then
          MANGLED_RESOLVED_PATH=`echo $RESOLVED_PATH \
                                 | sed -e "s%/\([A-Za-z]\)/%\1:/%"`
        else
          MANGLED_RESOLVED_PATH=$RESOLVED_PATH
        fi

	echo "(add-include-book-dir $COLON_PART \"$MANGLED_RESOLVED_PATH/\")" \
	    >> $TEMP_ACL2OUT

	# Also echo the line into what will become a Makefile.dirs file, but
	# omit the trailing slash.

	echo "$BOOK_NAME ?= $RESOLVED_PATH" >> $TEMP_MAKEOUT

	Debug "Added $BOOK_NAME --> $RESOLVED_PATH"

    else
	Debug "Ignoring '$entry' since it is not in LIBS."
    fi
done

rm -f $TEMP

# We can now compare our temporary file to the real ACL2_OUT_FILE and see if
# any changes are necessary.  If so, we will install our new temporary file.

# CDH Ignore inessential changes.

if [ -e $ACL2_OUT_FILE ]
then
    Debug "Comparing temp file with existing $ACL2_OUT_FILE"

    sed -e 's/;.*//' $ACL2_OUT_FILE \
    | grep -v '^[ \t]$' \
    > $CRUX_OLD_FILE

    sed -e 's/;.*//' $TEMP_ACL2OUT \
    | grep -v '^[ \t]$' \
    > $CRUX_NEW_FILE

    FILES_DIFFER=`diff -w $CRUX_OLD_FILE $CRUX_NEW_FILE 2>&1 > /dev/null ; \
		  echo $?`

    rm -f $CRUX_OLD_FILE $CRUX_NEW_FILE

    if (( $FILES_DIFFER ))
    then
	# mv $TEMP_ACL2OUT $ACL2_OUT_FILE
	# mv $TEMP_MAKEOUT $MAKE_OUT_FILE
	cp $TEMP_ACL2OUT $ACL2_OUT_FILE
	cp $TEMP_MAKEOUT $MAKE_OUT_FILE
        rm -f $TEMP_ACL2OUT $TEMP_MAKEOUT
	touch $ACL2_OUT_FILE $MAKE_OUT_FILE
	chmod a+rw $ACL2_OUT_FILE $MAKE_OUT_FILE
	echo "Done (Some locations have changed)."
    else
	rm -f $TEMP_ACL2OUT $TEMP_MAKEOUT
	echo "Done (No changes)."
    fi
else
    Debug "Installing temp file since no pre-existing $ACL2_OUT_FILE"
    # mv $TEMP_ACL2OUT $ACL2_OUT_FILE
    # mv $TEMP_MAKEOUT $MAKE_OUT_FILE
    cp $TEMP_ACL2OUT $ACL2_OUT_FILE
    cp $TEMP_MAKEOUT $MAKE_OUT_FILE
    rm -f $TEMP_ACL2OUT $TEMP_MAKEOUT
    touch $ACL2_OUT_FILE $MAKE_OUT_FILE
    chmod a+rw $ACL2_OUT_FILE $MAKE_OUT_FILE
    echo "Done (First make)."
fi

rm -rf temp.contents

# Dependency Computation -----------------------------------------------------

echo -n "Computing dependencies ... "
EOL_PENDING=1
DebugNewline

if [ -x /bin/mktemp ]
  then
    TEMP=`mktemp /tmp/rams.XXXXXX` || exit 1
  else
    TEMP=/tmp/rams_deps.`echo $PWD | sed -e yc/c_c`
fi

# CDH More readable

cat <<INLINE_INPUT_BOUNDARY > $TEMP
# $DEPS_FILE
#
# This file was atutomatically generated.  Do not hand edit!
#
# NOTE: If you need to add more dependencies than appear in ./Makefile, you
# can create the file ./MOREDEPS and add your Make commands there.  The
# ./MOREDEPS file will be cat'd onto this very ./Makefile.deps each time that
# it is rebuilt (via explicit or induced "make deps").  Thus the current
# contents of ./MOREDEPS will be included into ./Makefile during every "make".
#
# Use "make help" for more information.

INLINE_INPUT_BOUNDARY

Debug "Fresh DEPS_FILE created: $TEMP"

echo "" >> $TEMP
echo "" >> $TEMP
echo "# Deps for BOOKS and any corresponding .acl2 files go here:" >> $TEMP

IFS=" "
for book in $BOOKS
do
  Debug "-- BOOK $book -------------------------"

    if [ ! -e $book.lisp ]
    then
	if (( $EOL_PENDING ))
	then
	    echo ""
	    EOL_PENDING=0
	fi
	echo "Warning: $book.lisp does not exist."
	echo "  Perhaps it will be generated later, but if so, you will" \
	     "need to manually"
	echo "  list its dependencies in the file MOREDEPS."
	if [ -f $book.acl2 ]
	then
            echo "Processing $book.acl2"
	    Debug "$book.acl2 file found (overrides cert.acl2, if any)"
	    echo "$book.cert: $book.acl2" >> $TEMP
	    echo "" >> $TEMP
	    #old: IncludeBookDependencies $book.acl2 $book.cert -ews
	    IncludeBookDependencies $book.acl2 $book.acl2
	    #old: LDDependencies $book.acl2 $book.cert -ews
	    LDDependencies $book.acl2 $book.acl2
	    echo "$book.acl2: ; touch $book.acl2" \
		>> $TEMP
	elif [ -f cert.acl2 ]
	then
	    Debug "cert.acl2 file found (becomes default portcullis)"

	    # We now put the dependencies for cert.acl2 on cert.acl2 itself
	    # instead of on the .cert files for each book without that uses
	    # cert.acl2. -ews

	    #IncludeBookDependencies cert.acl2 $book.cert
	    #LDDependencies cert.acl2 $book.cert
	    echo "$book.cert: cert.acl2" >> $TEMP
	else
	    Debug "No $book.acl2 or cert.acl2 found."
	fi
    else
	Debug "DEP: $book.cert: $book.lisp"
	echo "" >> $TEMP
	echo "$book.cert: $book.lisp" >> $TEMP

#Note that we don't call LDDependencies, since certified books can't include
#LDs.
	IncludeBookDependencies $book.lisp $book.cert

# BZO.  Perhaps we can simplify things by treating .acl2 files as LDFILES
# (see below for info on LDFILES).  Currently if foo.lisp and foo.acl2 exist,
# and if foo.acl2 includes bar, then foo.cert has a dependency of bar.  We
# could change things to make foo.cert have a dependency of foo.acl2 and
# foo.acl2 have a dependency of bar.  The big win comes when dealing with
# cert.acl2, whose dependencies are currently being copied into the dependency
# list for each book that uses cert.acl2 -- that is, for all books in the
# directory that don't have their own .acl2 files. The change might also
# simplify the code just below this comment.  One issue to consider is whether
# .acl2 files need to be listed on the "LDFILES =" line of the Makefile.
# Maybe this isn't so bad, but maybe it's confusing, since there is already a
# "BOOKS =" line.  So we could automatically treat as LDFILES all .acl2 files
# for books on the "BOOKS =" line (if they exist), plus cert.acl2 (if it
# exists). -ews  # I am attempting to make said changes... -ews

	if [ -f $book.acl2 ]
	then
	    Debug "$book.acl2 file found (overrides cert.acl2, if any)"
	    echo "$book.cert: $book.acl2" >> $TEMP
	    echo "" >> $TEMP
	    #old: IncludeBookDependencies $book.acl2 $book.cert -ews
	    IncludeBookDependencies $book.acl2 $book.acl2
	    #old: LDDependencies $book.acl2 $book.cert -ews
	    LDDependencies $book.acl2 $book.acl2
	    echo "$book.acl2: ; touch $book.acl2" \
		>> $TEMP
	elif [ -f cert.acl2 ]
	then
	    Debug "cert.acl2 file found (becomes default portcullis)"

	    # We now put the dependencies for cert.acl2 on cert.acl2 itself
	    # instead of on the .cert files for each book without that uses
	    # cert.acl2. -ews

	    #IncludeBookDependencies cert.acl2 $book.cert
	    #LDDependencies cert.acl2 $book.cert
	    echo "$book.cert: cert.acl2" >> $TEMP
	else
	    Debug "No $book.acl2 or cert.acl2 found."
	fi
    fi

done

echo "" >> $TEMP
echo "# Deps for cert.acl2 (if any) go here:" >> $TEMP

#Added by Eric
if [ -f cert.acl2 ]
then
    echo "" >> $TEMP
    IncludeBookDependencies cert.acl2 cert.acl2
    LDDependencies cert.acl2 cert.acl2
    echo "cert.acl2: ; touch cert.acl2" >> $TEMP
    echo "" >> $TEMP
else
    echo "cert.acl2: ; touch cert.acl2" >> $TEMP
fi

# I am adding this in an attempt to generate dependencies for files other than
# books, e.g., files that contain defpkg stuff and that are just LDed, not
# certified as books.  Such files will be listed in a "LDFILES =" line similar
# to the "BOOKS =" line. -ews

echo "# Deps for LDFILES (if any) go here:" >> $TEMP

echo "" >> $TEMP
echo "all: $LDFILES" >> $TEMP

IFS=" "
for ldfile in $LDFILES
do
  Debug "-- LDFILE $ldfile -------------------------"

    if [ ! -e $ldfile ]
    then
	if (( $EOL_PENDING ))
	then
	    echo ""
	    EOL_PENDING=0
	fi
	echo "Warning: $ldfile does not exist."
	echo "  Perhaps it will be generated later, but if so, you will need" \
	     "to manually"
	echo "  list its dependencies in the file MOREDEPS."
    else
#       Debug "DEP: $ldfile.cert: $ldfile.lisp"
	Debug "deps for: $ldfile"
	echo "" >> $TEMP
#       echo "$ldfile.cert: $ldfile.lisp" >> $TEMP
	IncludeBookDependencies $ldfile $ldfile
	LDDependencies $ldfile $ldfile
	echo "$ldfile: ; touch $ldfile" >> $TEMP
    fi

done

echo "" >> $TEMP
echo "# Deps from the MOREDEPS file (if any) go here:" >> $TEMP

if [ -f MOREDEPS ]
then
    echo "" >> $TEMP
    echo "# Additional dependencies loaded from MOREDEPS:" >> $TEMP
    echo "" >> $TEMP
    cat MOREDEPS >> $TEMP
else
    Debug "No MOREDEPS file found, done with dependencies"
fi

# DAG : There is an issue with fat32 filesystems where all caps
# filenames are not preserved.  The following hack allows the user to
# change MOREDEPS to Moredeps and get the desired behavior.

if [ -f Moredeps ]
then
    echo "" >> $TEMP
    echo "# Additional dependencies loaded from Moredeps:" >> $TEMP
    echo "" >> $TEMP
    cat Moredeps >> $TEMP
fi

# Install the new Makefile.deps if there have been changes.

# CDH [ ] Ignore inessential changes

if [ -e $DEPS_FILE ]
then
    Debug "Comparing temp file with existing $DEPS_FILE"

    sed -e 's/#.*//' $DEPS_FILE \
    | grep -v '^[ \t]$' \
    > $CRUX_OLD_FILE

    sed -e 's/#.*//' $TEMP \
    | grep -v '^[ \t]$' \
    > $CRUX_NEW_FILE

    FILES_DIFFER=`diff -w $CRUX_OLD_FILE $CRUX_NEW_FILE 2>&1 > /dev/null ; \
		  echo $?`

    rm -f $CRUX_OLD_FILE $CRUX_NEW_FILE

    if (( $FILES_DIFFER ))
    then
	# mv $TEMP $DEPS_FILE
	cp $TEMP $DEPS_FILE
        rm -f $TMP
	chmod a+rw $DEPS_FILE
	touch -r Makefile $DEPS_FILE
	echo "Done (Some dependencies have changed)."
    else
	rm -f $TEMP
	touch -r Makefile $DEPS_FILE
	echo "Done (No changes)."
    fi
else
    Debug "Installing temp file since no pre-existing $DEPS_FILE"
    # mv $TEMP $DEPS_FILE
    cp $TEMP $DEPS_FILE
    rm -f $TEMP
    chmod a+rw $DEPS_FILE
    touch -r Makefile $DEPS_FILE
    echo "Done (First make)."
fi

# Book Certification ---------------------------------------------------------

# We have now set up the library paths and written all of the dependency
# information.  It's time to certify the books.  We hand control over to
# $MAKEDIR/Makefile.aux to do the rest.
#
# As a special convenience, if the user typed "make deps", we don't invoke
# the other Makefile, and simply exit here.

if [[ "$@" == "deps" ]]
then
    Debug "Done with work since target was 'deps'."

# CDH Without this firestop RAMS would loop if $BOOKS were the empty list.

elif [ -z "$BOOKS" ]
then
    Debug "Done with work since BOOKS was an empty list."

else
    Debug "Passing off control to Makefile.aux to build $@"
    if [ -n "$DEBUG" ]
    then
      export SILENT=""
    else
      export SILENT="-s"
    fi

    # CDH sorted variable setting lines for consistency with Makefile.top

    make ${MAKE_JOBS} $SILENT -f $MAKEDIR/Makefile.aux \
	BOOKS="$BOOKS" \
	DEBUG="$DEBUG" \
	LIB_ROOT="$LIB_ROOT" \
	MAKEDIR="$MAKEDIR" \
	$@ \
	2>&1
	exit $?

fi

## Trying without these arguments ..
## ACL2="$ACL2" \
## ACL2_SYSTEM_BOOKS="$ACL2_SYSTEM_BOOKS" \

echo 'RAMS['$MAKELEVEL']: Leaving directory' '`'`pwd`"'"
