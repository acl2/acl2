#!/bin/bash

# cert.pl build system
# Copyright (C) 2008-2011 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
#
# Original authors: Sol Swords <sswords@centtech.com>
#                   Jared Davis <jared@centtech.com>
#
# NOTE: This file is not part of the standard ACL2 books build process; it is
# part of an experimental build system.  The ACL2 developers do not maintain
# this file.


# make_cert_help.sh -- this is a companion file that is used by "make_cert".
# It is the core script responsible for certifying a single ACL2 book.

# NOTE: DO NOT RENAME THIS FILE TO "make_cert.sh".  If you do that, then for
# some reason that I can't find documented anywhere, Make will overwrite the
# make_cert Makefile script with this shell script!  #@!$&*

# The code here is largely similar to the %.cert: %.lisp rule from
# Makefile-generic, but with several extensions.  For instance,
#
#   - We try to gracefully NFS lag, and
#   - We can certify certain books with other save-images, using .image files
#   - We support .acl2x files and two-pass certification,
#   - We support running commands to prepare for certification, using .prep files
#   - We support running ACL2 via an external queuing mechanism.
#
# We only expect to invoke this through make_cert, so it is not especially
# user-friendly.  We rely on several environment variables that are given to us
# by make_cert.  See make_cert for the defaults and meanings of ACL2,
# COMPILE_FLG, and other variables used in this script.

set -e

# Usage: make_cert.sh TARGET TARGETEXT PASSES
#   - TARGET is like "foo" for "foo.lisp"
#   - TARGETEXT is "cert" or "acl2x"
#   - PASSES is 1 or 2

TARGET=$1
TARGETEXT=$2
PASSES=$3

DIR=`dirname $TARGET`
FILE=`basename $TARGET`
GOAL="$FILE.$TARGETEXT"

echo "Making $GOAL on `date`"
rm -f "$GOAL"

# Figure out what ACL2 points to before we switch directories
ACL2=`which $ACL2 2> /dev/null`

cd $DIR

# Override ACL2 per foo.image or cert.image as appropriate
if [ -f "$FILE.image" ]
then
    IM=`cat $FILE.image`
    if [ "$IM" != "" ]
    then
	ACL2=$IM
    fi
elif [ -f "cert.image" ]
then
    IM=`cat cert.image`
    if [ "$IM" != "" ]
    then
	ACL2=$IM
    fi
fi


if [ "$TARGETEXT" == "acl2x" ]
then
    TIMEFILE=$FILE.acl2x.time
    OUTFILE=$FILE.acl2x.out
else
    TIMEFILE=$FILE.time
    OUTFILE=$FILE.out
fi

rm -f $TIMEFILE $OUTFILE

# File header for things like auto-revert mode.
echo $OUTFILE_HEADER > $OUTFILE



# ------------ TEMPORARY LISP FILE FOR ACL2 INSTRUCTIONS ----------------------

TMPBASE="workxxx.$GOAL.$RANDOM"
LISPTMP="$TMPBASE.LISP"

# I think this strange :q/lp dance is needed for lispworks or something?
echo '(acl2::value :q)' > $LISPTMP
echo '(in-package "ACL2")' >> $LISPTMP
echo '(acl2::lp)' >> $LISPTMP

if [ "$TARGETEXT" == "acl2x" ]
then
    echo '(set-write-acl2x t state)' >> $LISPTMP
fi

echo "$INHIBIT" >> $LISPTMP

if [ "$PASSES" == "2" ]
then
   FLAGS="$COMPILE_FLG_TWOPASS"
else
   FLAGS="$COMPILE_FLG"
fi

# Get the certification instructions from foo.acl2 or cert.acl2, if either
# exists, or make a generic certify-book command.
if [ -f "$FILE.acl2" ]
then
    cat "$FILE.acl2" >> $LISPTMP
elif [ -f "cert.acl2" ]
then
    cat cert.acl2 >> $LISPTMP
    echo "" >> $LISPTMP
    echo "(time$ #!ACL2 (certify-book \"$FILE\" ? $FLAGS))" >> $LISPTMP
else
    echo "" >> $LISPTMP
    echo "(time$ #!ACL2 (certify-book \"$FILE\" ? $FLAGS))" >> $LISPTMP
fi

echo "" >> $LISPTMP

# Special hack so that ACL2 exits with 43 on success, or 0 on failure, so we
# can avoid looking at the file system in case of NFS lag.  See make_cert.lsp
# for details.  BOZO right now we're not doing any exit code magic for .acl2x
# files.  It'd be nice to fix that.

if [ $TARGETEXT != acl2x ]
then
    echo "(acl2::ld \"make_cert.lsp\" :dir :system)" >> $LISPTMP
    echo "(acl2::horrible-include-book-exit \"$FILE\" acl2::state)" >> $LISPTMP
fi

if [ -n "$ACL2_BOOKS_DEBUG" ]
then
    echo "[make_cert.sh]: certify book commands for $GOAL:"
    echo ""
    cat $LISPTMP
    echo ""
fi



# ------------ TEMPORARY SHELL SCRIPT FOR RUNNING ACL2 ------------------------

SHTMP="$TMPBASE.SH"

echo "#!/bin/sh" > $SHTMP

# Insert the contents of file.prep or cert.prep, if appropriate.  Or, put in
# our default memory/walltime limitations for PBS.  For non-Centaur folks who
# haven't set up a STARTJOB, the STARTJOB command is just going to invoke the
# shell, and we're just inserting comments.

if [ -f "$FILE.prep" ]
then
    PREPFILE="$FILE.prep"
elif [ -f "cert.prep" ]
then
    PREPFILE="cert.prep"
fi

if [ -n "$PREPFILE" ]
then
    cat $PREPFILE >> $SHTMP
    echo "" >> $SHTMP
else
    echo "#PBS -l pmem=6gb" >> $SHTMP
    echo "#PBS -l walltime=5:00:00" >> $SHTMP
fi

if [ "$TIME_CERT" != "" ]
then
    echo "(time (($ACL2 < $LISPTMP 2>&1) >> $OUTFILE)) 2> $TIMEFILE" >> $SHTMP
else
    echo "($ACL2 < $LISPTMP 2>&1) >> $OUTFILE" >> $SHTMP
fi


# Run it!  ------------------------------------------------

set +e
$STARTJOB $SHTMP
STATUS=$?
set -e

rm -f $LISPTMP $SHTMP



# Success or Failure Detection -------------------------------

wait_for_nfs() {
    for ((i=0;i <= $MAX_NFS_LAG; i++))
    do
	echo "NFS Lag?  Waited $i seconds for $GOAL..."
	sleep 1
	if [ -f "$GOAL" ]
	then
	    return 1;
	fi
    done
    return 0
}

if [ -f "$GOAL" ]
then
    SUCCESS=1;
elif [[ "$TARGETEXT" != "acl2x" && "$STATUS" == "43" ]]
then
    # The exit code indicates that the file certified successfully, so why
    # doesn't it exist?  Maybe there's NFS lag.  Let's try waiting to see if
    # the file will show up.
    SUCCESS=wait_for_nfs
else
    SUCCESS=0
fi


if [ $SUCCESS == "0" ]
then

    if [[ $TARGETEXT == "acl2x" ]]
    then
	TASKNAME="ACL2X GENERATION"
    else
	TASKNAME="CERTIFICATION"
    fi

    echo "**$TASKNAME FAILED** for $DIR/$FILE.lisp"
    echo ""
    echo "$OUTFILE:"
    tail -300 $OUTFILE | sed 's/^/   | /'
    echo ""
    echo ""

    if [ "$ON_FAILURE_CMD" != "" ]
    then
	$ON_FAILURE_CMD
    fi
    echo "**CERTIFICATION FAILED** for $DIR/$FILE.lisp"
    exit 1
fi


# Else, we made it!
ls -l $GOAL
exit 0
