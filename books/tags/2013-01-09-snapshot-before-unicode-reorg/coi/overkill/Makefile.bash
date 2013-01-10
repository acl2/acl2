#!/bin/sh
#
# File: make/Makefile.bash 
#
# Invokes the Makefile-libs.bash and Makefile-deps.bash scripts to compute
# library paths and dependencies, then invokes the Makefile.aux in order to
# complete the build tasks.
#
# Author: Jared Davis 


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

Debug "Using LIBS=$LIBS"
Debug "Using BOOKS=$BOOKS"
Debug "Using SKIPDEPS=$SKIPDEPS"
Debug "Using NORECUR=$NORECUR"

if [ -z "$SKIPDEPS" ]
then
    # First we perform the library path computation.
    export MAKEDIR=$MAKEDIR \
	DEBUG=$DEBUG \
	BOOKS=$BOOKS \
	LIBS=$LIBS \
	NAME=$NAME \
	NORECUR=$NORECUR \
	QUIET=$QUIET \
	; sh $MAKEDIR/Makefile-libs.bash || exit $?

    # Then we perform the dependency computation.
    export MAKEDIR=$MAKEDIR \
	DEBUG=$DEBUG \
	BOOKS=$BOOKS \
	LIBS=$LIBS \
	NAME=$NAME \
	NORECUR=$NORECUR \
	QUIET=$QUIET \
	; sh $MAKEDIR/Makefile-deps.bash || exit $?
else
    echo "Warning: skipping dependency computation"
fi



# We have now set up the library paths and written all of the dependency
# information.  It's time to certify the books.  We hand control over to
# $MAKEDIR/Makefile.aux to do the rest.
#
# As a special convenience, if the user typed "make deps", we don't invoke
# the other Makefile, and simply exit here.

if [[ "$@" != "deps" ]]
then
    Debug "Passing off control to Makefile.aux to build $@"
    make -sf $MAKEDIR/Makefile.aux \
	MAKEDIR="$MAKEDIR" \
	DEBUG="$DEBUG" \
	BOOKS="$BOOKS" \
	SKIPDEPS="$SKIPDEPS" \
	LIBS="$LIBS" \
	ACL2="$ACL2" \
	ACL2_ROOT="$ACL2_ROOT" \
	$@ \
	2>&1 #| egrep -v --line-buffered "(\*\*\* Warning: File .Makefile\.(dirs|deps)' has modification time in the future|warning:  Clock skew detected\.  Your build may be incomplete\.)"
	exit $?
else
    Debug "Done with work since target was 'deps'."
fi


