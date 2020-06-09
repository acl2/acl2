#!/usr/bin/env bash

# Final Proof Checking - Jared Davis (jared@cs.utexas.edu)

# This script attempts to perform the final checks on the proofs in your Proofs/
# directory.  This is done by building a number of Lisp images, one for each
# subdirectory of Proofs.  It must be run from the Sources directory.

# The script is sort of like a Makefile in that it will only build Lisp images
# that do not already exist.  So, if you change the contents of the Proofs/
# directory, you should erase all of the Lisp images in the Sources directory.

set -e

if [ "$#" -ne "2" ]
then
    echo "Usage: final-checks.sh <LISPNAME> <IMAGE-EXTENSION>"
    echo "Where <LISPNAME> is the name of the Lisp to use, e.g., 'acl', 'ccl', etc."
    echo "Where <IMAGE-EXTENSION> is the extension for the Milawa image"
    echo ""
    exit 1
fi

LISPNAME=$1
EXT=$2

print_generic_help ()
{
    echo "If the reason for this failure is not obvious, please see the instructions"
    echo "either online at"
    echo "  - http://www.cs.utexas.edu/users/jared/milawa/Web/checking.html"
    echo "or, if you installed from Subversion, in the directory"
    echo "  - Milawa/Web/checking.html"
    echo ""
}

if [ ! -e "base.$EXT" ]
then
    echo "Error: base.$EXT does not exist."
    echo ""
    echo "Possible causes:"
    echo "  - This is not the right extension for the image you made?"
    echo "  - You have not yet run (load \"milawa.lsp\") in $LISPNAME?"
    echo "  - You are not running final-checks.sh from the 'Sources' directory?"
    echo ""
    print_generic_help
    exit 1
fi

if [ ! -e "milawa-$LISPNAME" ]
then
    echo "Error: milawa-$LISPNAME does not exist."
    echo ""
    echo "Possible causes:"
    echo "  - You did not download the milawa-$LISPNAME script yet?"
    echo "  - You downloaded milawa-$LISPNAME, but it is not in the 'Sources' directory?"
    echo "  - You are not running final-checks.sh from the 'Sources' directory?"
    echo ""
    print_generic_help
    exit 1
fi

if [ ! -x "milawa-$LISPNAME" ]
then
    echo "Note: making milawa-$LISPNAME executable."
    chmod +x "milawa-$LISPNAME"
fi

run_milawa ()
{
    CURR=$1   # Current level which is built
    NEXT=$2   # Next level which is about to be built

    if [ ! -e "$CURR.$EXT" ]
    then
	echo "Error: $CURR.$EXT does not exist."
	echo ""
	echo "Possible causes:"
	echo "  - Has someone deleted the file?"
        echo "  - Has an interrupt been sent, killing the Lisp but not final-checks.sh?"
	echo "  - Is there a programming error in final-checks.sh?"
	echo ""
	exit 1
    fi

    if [ -e "$NEXT.$EXT" ]
    then
       echo "Skipping $NEXT.$EXT since it already exists."
       return 0
    fi

    if [ ! -e "Proofs/$NEXT.events" ]
    then
	echo "Error: Proofs/$NEXT.events does not exist."
	echo ""
	echo "Possible causes:"
	echo "  - You have not generated/downloaded the proofs for $NEXT yet?"
	echo "  - The proofs for $NEXT are not in the Sources/Proofs/ directory?"
	echo ""
	pring_generic_help
	exit 1
    fi

    # Otherwise, everything looks to be set up.
    echo "Processing $NEXT"
    { time nice ./milawa-$LISPNAME "$CURR.$EXT" < "Proofs/$NEXT.events"; } \
       2>&1 | tee $NEXT.$EXT.out
    echo ""
}

run_milawa base utilities
run_milawa utilities logic
run_milawa logic level2
run_milawa level2 level3
run_milawa level3 level4
run_milawa level4 level5
run_milawa level5 level6
run_milawa level6 level7
run_milawa level7 level8
run_milawa level8 level9
run_milawa level9 level10
run_milawa level10 level11
run_milawa level11 user

