#!/bin/sh
#
# File: make/Makefile-deps.bash 
#
# RAMS Dependency Computation - sets up the dependencies files (Makefile.deps)
# for Make to include.
#
# Author: Jared Davis 

readonly SCRIPT="Makefile-deps.bash"
source $MAKEDIR/Makefile-checks.bash


# -----------------------------------------------------------------------------
#        PRELIMINARIES TO UNDERSTANDING THE DEPENDENCY COMPUTATION 
# -----------------------------------------------------------------------------


# ASSUMPTIONS
#
# In this script, we make the following assumptions about the organization of
# our projects.
#
#  1. Our universe (the set of files that influence the dependencies of our
#  books) is composed of "proper lisp files" (.lisp) and "improper files" (such
#  as .lsp or .acl2 files) which do not become certified books.
#
#  2. A proper file is never loaded with "ld" by any file.  (Instead,
#  include-book is always used.)
#
#  3. An improper file is never loaded with "include-book" by any file.
#  (Instead, ld must always be used.)
#
#  4. Every proper file, foo.lisp, is certified using the following scheme:
#
#    - If foo.acl2 exists, foo.acl2 is first ld'd into the certification world,
#    and foo.acl2 contains the necessary certify-book command necessary.
#
#    - ElseIf cert.acl2 exists, cert.acl2 is first ld'd into the certification
#    world, but cert.acl2 has no certify-book command, and instead a generic
#    (certify-book "foo") is executed after ld'ing cert.acl2.
#
#    - Else, no packages are needed, and foo.lisp can be certified by simply
#    executing (certify-book "foo") in the ground zero world.



# Definition: CDEPS
#
# We define CDEPS(file) for every file in our universe (i.e., for every .lisp,
# .acl2, or .lsp file, but not for .cert files themselves) as the set of all
# files that you would need to depend on, if you wanted to certify some other
# file that depends on file.
#
# Regardless of the properness of the file foo, the following three rules
# always apply.
#
#  1. CDEPS(foo) must include foo, since in order to certify any book that
#  depends on foo, we certainly need to have a current foo.
#
#  2. CDEPS(foo) must include every member of CDEPS(bar) for every improper
#  file bar which is "ld'd" into foo.  (Of course, proper files will have no
#  such dependencies.)
#
#  3. CDEPS(foo) must include bar.cert (the corresponding cert file) for every
#  proper file bar.lisp which is include-book'd in foo.  (Note that we do not
#  have to include the entire CDEPS of bar.cert, because bar.cert itself could
#  only be current if all of those files are also current.)
#
# Furthermore, if foo is actually proper file, say foo.lisp, we add the
# following rule in order to capture the dependencies of the portcullis of
# foo.cert.
#
#  4. If foo.acl2 exists, CDEPS(foo.lisp) must include every member of
#  CDEPS(foo.acl2). Else, if cert.acl2 exists, CDEPS(foo.lisp) must include
#  every member of CDEPS(cert.acl2).
#
# We believe the above rules are sufficient to completely define CDEPS(foo).
# In other words, no other files need be considered in order to know if the
# certificate for foo.cert is up to date.



# Definition: PCDEPS
#
# We define PCDEPS(file) for every file in our universe (i.e., for every .lisp,
# .acl2, or .lsp file, but not for .pcert files) as the set of all files that
# you would need depend on, if you wanted to "probably certify" some file that
# depends on file.
#
# The first two rules are similar to CDEPS, and apply to every file regardless
# of its properness.
#
#  1. PCDEPS(foo) must include foo, since in order to certify any book that
#  depends on foo, we certainly need to have a current foo.
#
#  2. PCDEPS(foo) must include every member of PCDEPS(bar) for every improper
#  file bar which is "ld'd" into foo.  (of course, proper files will have no
#  such dependencies)
#
# The third rule also applies to every file regardless of properness.  This
# rule is the major difference between PCDEPS and CDEPS:
#
#  3. PCDEPS(foo) must include every member of PCDEPS(bar.lisp) for every
#  proper file bar.lisp which is include-book'd in foo.  (The difference here
#  is that in CDEPS, we only include bar.cert instead of all of these
#  dependencies.  By "bypassing" bar.cert, we remove the order dependency that
#  requires us to certify bar before foo when we use certify-book.  Instead, we
#  want to depend on all of bar.cert's dependencies directly, because if any of
#  them have changed, the old pcert is no longer current.)
#
# Finally, just like PCDEPS we have an additional rule for proper files, in
# order to capture the dependencies of the portcullis files.
#
#  4. If foo.acl2 exists, PCDEPS(foo.lisp) must include every member of
#  PCDEPS(foo.acl2). Else, if cert.acl2 exists, PCDEPS(foo.lisp) must include
#  every member of PCDEPS(cert.acl2).
#
# Again, we believe the above rules are sufficient to completely define
# PCDEPS(foo).  In other words, no other files need be considered in order to
# know if foo.pcert is valid.




# -----------------------------------------------------------------------------
#                HOW WE IMPLEMENT THE DEPENDENCY COMPUTATION
# -----------------------------------------------------------------------------

# The above definitions of CDEPS and PCDEPS are fairly easy to implement as an
# algorithm.  An important part of how our implementation works depends upon
# the way that Makefile variable expansion occurs.  For example, the following
# Makefile will print 3 when invoked, because $(FOO) is expanded to $(BAR)
# which is expanded to 3.
#
# FOO = $(BAR)
# BAR = 3
#
# all:
# 	echo "$(FOO)"
#
# So, simply create variables for CDEPS_[Filename] and PCDEPS_[Filename] for
# each file we encounter, and set the values of these variables to be the
# "symbolic" representations of the above ideas.  For example, if foo.lisp
# include-book's bar.lisp, and has a portcullis file of foo.acl2, we would add
# the following lines.
#
#  CDEPS_FOO_DOT_LISP = foo.lisp bar.cert $(CDEPS_FOO_DOT_ACL2)
#  PCDEPS_FOO_DOT_LISP = foo.lisp $(PCDEPS_BAR_DOT_LISP) $(PCDEPS_FOO_DOT_ACL2)
#
# By doing this for all of our files, we know that these variables like 
# $(PCDEPS_BAR_DOT_LISP) and $(CDEPS_FOO_DOT_ACL2) will end up being 
# defined somewhere, and so everything just works out.
#
# Note that if our files ever have a circular dependency, Make will complain
# that a variable has been defined recursively, which is easy to understand
# when debugging, and is actually a useful check.
#
# After we create all of these variables, our last task is to hook them up 
# to the appropriate .cert and .pcert files.  All we need to do for this is,
# for each file, basically write the following:
#
# foo.cert: $(CDEPS_FOO_DOT_LISP)
# foo.pcert: $(PCDEPS_FOO_DOT_LISP)




# -----------------------------------------------------------------------------
#                             IMPLEMENTATION
# -----------------------------------------------------------------------------

readonly DEPS_FILE=`pwd`/"Makefile.deps"
readonly LOCAL_DEPS_FILE=`pwd`/"Makefile.ldeps"
Debug "DEPS_FILE = $DEPS_FILE"
Debug "LOCAL_DEPS_FILE = $LOCAL_DEPS_FILE"

if [[ "$QUIET" != "1" ]]
then
    echo -n "Computing dependencies... "
    DebugNewline
fi



# We create fresh temporary files, which we will use as our "candidates" for 
# Makefile.deps and Makefile.ldeps

readonly CANDIDATE=`mktemp /tmp/rams.XXXXXX` || exit 1
readonly LOCALCANDIDATE=`mktemp /tmp/rams.XXXXXX` || exit 1
Debug "CANDIDATE = $CANDIDATE"
Debug "LOCALCANDIDATE = $LOCALCANDIDATE"


echo "# $DEPS_FILE
#
# This file is automatically generated. Do not hand edit!
# Use \"make help\" for more information.
#
# NOTE: if you need to add additional dependencies, you can create 
# a file named MOREDEPS in this directory, and add your Make commands 
# there.  The MOREDEPS file will be cat'd onto this file each time that 
# it is regenerated, and thus will be included into your Makefile.
" > $CANDIDATE

Debug "Fresh DEPS_FILE created: $TEMP"


echo "# $LOCAL_DEPS_FILE
#
# This file is automatically generated. Do not hand edit!
# Use \"make help\" for more information.
" > $LOCALCANDIDATE




# Our first step is to load in the external Makefile.deps from each library 
# listed in LIBS.  This is a little tricky, because these files might not 
# exist and our Makefile should not complain -- e.g., what if we are doing
# a "make clean" and they don't exist.  So, we do a stupid trick with the
# Wildcard function in Make in order to test if they exist before we go to
# include them.

# You might ask, isn't this dangerous?  I mean, couldn't we get into a
# situation where we don't have the appropriate dependencies loaded?  That is
# particularly concerning for our .pcert files.  My answer is this: we always
# re-run the Makefile.bash before a build of any file, and since the
# Makefile.bash recursively computes the dependencies in all LIBS now, we will
# just rely on that to save us.  It's probably not perfect, but it's pretty
# good.

IFS=" "
for lib in $LIBS
do
    ParseLib $lib
    echo "
ifneq \"\$(wildcard \$($LIB_BOOKS)/Makefile.deps)\" \"\"
include \$($LIB_BOOKS)/Makefile.deps
endif" >> $CANDIDATE
done





# BZO BZO BZO - add a work stack so that deps get added in if they are
# locally included?



# The ComputeDepsSets function, below, does the brunt of the work.  We give
# this function a single argument, the name of the file to process.  The
# function will compute the PCDEPS and CDEPS for the file, and then write them
# to CANDIDATE.  We expect that the file $1 exists before this function is
# called.

function ComputeDepsSets () {

# We will accumulated the CDEPS and PCDEPS into the "accumulator" variables
# CDEPSACC and PCDEPSACC.  These variables are just strings.

# STEP 1: To begin, in accordance with Rules (1) for computing PCDEPS and
# CDEPS, the file depends upon itself.  Well, this sure is an easy step!

CDEPSACC="\$($NAME_BOOKS)/$1"
PCDEPSACC="\$($NAME_BOOKS)/$1"


# STEP 2: Now, in accordance with Rules (2), we process all of the "ld"
# commands in the file.  Of course, our ability to accurately detect ld
# commands is somewhat limited since, e.g., the user could use macros or split
# them across lines or otherwise try to confuse our grep commands.

# We make an effort to find any ld commands that are "sensible" in that they
# are on a single line and do not appear to be commented out.

LDS="`egrep -i '^[^;]*\([ \t]*ld[ \t]*\".*\"' $1`"

# BZO - remove from here down after v293
BOZO_LDS=`egrep -i '^[^;]*\([ \t]*bozo-ld[ \t]*\".*\"' $1 | sed "s/(bozo-ld/(ld/i"`
if [ -n "$BOZO_LDS" ]
then
    LDS="$LDS
$BOZO_LDS"
fi
# BZO - stop removing here

IFS="
"
for line in $LDS
do
  STRIP_LD=`echo $line | sed "s/.*(ld[ \t]*\"//i"`
  FILENAME=`echo $STRIP_LD | sed "s/\".*//i"`
  MangleFile $FILENAME

  if [ "`echo $STRIP_LD | grep ":dir"`" ]
      then
      DIR=`echo $STRIP_LD | sed "s/.*:dir[ \t]*:/:/i" | sed "s/[ \t]*).*//i"`
      CheckLib $DIR
      ParseLib $DIR
  else
      LIB_UPPER=$NAME_UPPER
      LIB_BOOKS=$NAME_BOOKS
  fi

  # Figure out the new deps
  CDEPS="\$(CDEPS_`echo $LIB_UPPER`_`echo $MANGLEFILE`)"
  PCDEPS="\$(PCDEPS_`echo $LIB_UPPER`_`echo $MANGLEFILE`)"

  # Add our CDEPS and PCDEPS to the accumulators.
  CDEPSACC="$CDEPSACC \\
        $CDEPS"
  PCDEPSACC="$PCDEPSACC \\
        $PCDEPS"
done



# STEP 3: Now, in accordance with Rules (3), we process all of the "include-book"
# commands in the file.  This is really very similar to our processing of lds.

INCLUDES=`egrep -i '^[^;]*\([ \t]*include-book[ \t]*\".*\"' $1`

IFS="
"
for line in $INCLUDES
do
    STRIP_IB=`echo $line | sed "s/.*(include-book[ \t]*\"//i"`
    FILENAME=`echo $STRIP_IB | sed "s/\".*//i"`

    if [ "`echo $STRIP_IB | grep -i ":dir"`" ]
	then
	DIR=`echo $STRIP_IB | sed "s/.*:dir[ \t]*:/:/i" | sed "s/[ \t]*).*//i"`
	CheckLib $DIR
	ParseLib $DIR
    else
	CheckBook $FILENAME
	LIB_UPPER=$NAME_UPPER
	LIB_BOOKS=$NAME_BOOKS
    fi

    # Compute the new CDEPS and PCDEPS
    MangleFile "$FILENAME.lisp"
    CDEPS="\$($LIB_BOOKS)/$FILENAME.cert"
    PCDEPS="\$(PCDEPS_`echo $LIB_UPPER`_`echo $MANGLEFILE`)"
    
    # Add our CDEPS and PCDEPS to the accumulators.
    CDEPSACC="$CDEPSACC \\
        $CDEPS"
    PCDEPSACC="$PCDEPSACC \\
        $PCDEPS"
done



# STEP 4:  Finally, if this is a proper lisp file, we need to go ahead and 
# add its portcullis's dependencies, if they exist.

 if [ "`echo $1 | grep -i "\.lisp$"`" ] 
 then
     BOOKNAME=`echo $1 | sed "s/.lisp$//i"`

     if [ -f "$BOOKNAME.acl2" ]
     then
 	MangleFile "$BOOKNAME.acl2"
  	CDEPS="\$(CDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)"
  	PCDEPS="\$(PCDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)"
  	CDEPSACC="$CDEPSACC \
        $CDEPS"
 	PCDEPSACC="$PCDEPSACC \
        $PCDEPS"
     elif [ -f "cert.acl2" ]
     then
 	MangleFile "cert.acl2"
  	CDEPS="\$(CDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)"
  	PCDEPS="\$(PCDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)"
  	CDEPSACC="$CDEPSACC \\
        $CDEPS"
  	PCDEPSACC="$PCDEPSACC \\
        $PCDEPS"
     fi
fi


# And that's it.  Time to write these into our candidate file.

MangleFile $1

echo "CDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE` = \\
        $CDEPSACC" >> $CANDIDATE
echo "" >> $CANDIDATE
echo "PCDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE` = \\
        $PCDEPSACC" >> $CANDIDATE
echo "" >> $CANDIDATE

}







# -----------------------------------------------------------------------------
#                             DRIVER SCRIPT
# -----------------------------------------------------------------------------


# We start by adding in cert.acl2's dependencies, if any exist.

if [ -f cert.acl2 ]
    then
    ComputeDepsSets cert.acl2
fi

IFS=" "
for book in $BOOKS
do
  Debug "Book $book"
  if [ ! -e $book.lisp ]
  then
      echo ""
      echo "Warning: $book.lisp does not exist."
      echo "Perhaps it will be generated later, but if so, you will need to "
      echo "manually list its dependencies in the file MOREDEPS."
      echo ""
  else
      ComputeDepsSets $book.lisp

      if [ -f "$book.acl2" ] 
	  then
	  ComputeDepsSets $book.acl2  
      fi

      MangleFile "$book.lisp"
      echo "\$($NAME_BOOKS)/$book.cert:  \$(CDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)" >> $CANDIDATE
      echo "\$($NAME_BOOKS)/$book.pcert: \$(PCDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)" >> $CANDIDATE
      echo "\$($NAME_BOOKS)/$book.o: \$(PCDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)" >> $CANDIDATE
      echo "" >> $CANDIDATE

      # the localdeps file provides abbreviated versions of the dependencies
      # so that "make foo.cert" works.
      echo "$book.cert:  \$(CDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)" >> $LOCALCANDIDATE
      echo "$book.pcert: \$(PCDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)" >> $LOCALCANDIDATE
      echo "$book.o: \$(PCDEPS_`echo $NAME_UPPER`_`echo $MANGLEFILE`)" >> $LOCALCANDIDATE
      echo "" >> $LOCALCANDIDATE
  fi
done



if [ -f MOREDEPS ] 
then
    echo "" >> $CANDIDATE
    echo "# Additional dependencies loaded from MOREDEPS:" >> $CANDIDATE
    echo "" >> $CANDIDATE
    cat MOREDEPS >> $CANDIDATE
else
    Debug "No MOREDEPS file found, done with dependencies"
fi


if [ -f MOREDEPS-LOCAL ] 
then
    echo "" >> $LOCALCANDIDATE
    echo "# Additional dependencies loaded from MOREDEPS-LOCAL:" >> $LOCALCANDIDATE
    echo "" >> $LOCALCANDIDATE
    cat MOREDEPS-LOCAL >> $LOCALCANDIDATE
else
    Debug "No MOREDEPS-LOCAL file found, done with dependencies"
fi



# Install the new Makefile.deps if there have been changes.

if [ -e $DEPS_FILE ]
then
    Debug "Comparing temp file with existing $DEPS_FILE"

    if [ "`diff $DEPS_FILE $CANDIDATE`" ]
    then
	mv $CANDIDATE $DEPS_FILE

	if [[ "$QUIET" != "1" ]]
	then
	    echo " (Dependencies have changed)."
	else
	    echo ""
	    echo -n "   Note: Updated dependencies links for $NAME"
	fi
    else
	rm -f $CANDIDATE

	if [[ "$QUIET" != "1" ]]
	then
	    echo " Done (No changes.)"
	fi
    fi
else
    Debug "Installing temp file since no pre-existing $DEPS_FILE"
    mv $CANDIDATE $DEPS_FILE

    if [[ "$QUIET" != "1" ]]
    then
	echo " Done (First make)."
    else
	echo ""
	echo -n "   Note: Created initial dependencies for $NAME"
    fi
fi




# Install the new Makefile.ldeps if there have been changes.

if [ -e $LOCAL_DEPS_FILE ]
then
    Debug "Comparing temp file with existing $LOCAL_DEPS_FILE"

    if [ "`diff $LOCAL_DEPS_FILE $LOCALCANDIDATE`" ]
    then
	mv $LOCALCANDIDATE $LOCAL_DEPS_FILE

	if [[ "$QUIET" != "1" ]]
	then
	    echo " (Local dependencies have changed)."
	else
	    echo ""
	    echo -n "   Note: Updated local dependencies for $NAME"
	fi
    else
	rm -f $LOCALCANDIDATE
    fi
else
    Debug "Installing temp file since no pre-existing $LOCAL_DEPS_FILE"
    mv $LOCALCANDIDATE $LOCAL_DEPS_FILE

    if [[ "$QUIET" == "1" ]]
    then
	echo ""
	echo -n "   Note: Created initial local dependencies for $NAME"
    fi
fi



