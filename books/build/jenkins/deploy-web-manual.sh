#!/usr/bin/env bash

################################################################################

# Build the manual and deploy to the website.
# Adapted from books/build/jenkins/build-single.sh and bin/make-fancy-manual.sh
#
# Author: Grant Jurgensen (grant@kestrel.edu)

################################################################################

set -e

################################################################################

echo "Starting $0"
echo " -- Running in `pwd`"
echo " -- Running on `hostname`"
echo " -- PATH is $PATH"

# Print some vars that should be set for retried builds:
echo "NAGINATOR_COUNT is $NAGINATOR_COUNT" # How many times the build was rescheduled.
echo "NAGINATOR_MAXCOUNT is $NAGINATOR_MAXCOUNT" # How many times the build can be rescheduled. This can be 0 if manually rescheduled.
echo "NAGINATOR_BUILD_NUMBER is $NAGINATOR_BUILD_NUMBER" # The build number of the failed build causing the reschedule.

source $JENKINS_HOME/env.sh

TARGET="regression-everything doc"

ACL2DIR=`pwd`

if [ -z "$STARTJOB" ]; then
  echo "Setting STARTJOB to bash";
  STARTJOB='bash';
fi

if [ -z "$TARGET" ]; then
  echo "Setting TARGET automatically";
  TARGET='manual';
fi

if [ -z "$BOOK_PARALLELISM_LEVEL" ]; then
  echo "Setting BOOK_PARALLELISM_LEVEL to 1";
  BOOK_PARALLELISM_LEVEL='1';
fi

LISP=`which ccl`
echo "Using LISP = $LISP"
echo "Making TARGET = $TARGET"
echo "Using STARTJOB = $STARTJOB"
echo "Using MAKEOPTS = $MAKEOPTS"

echo "Making ACL2"
$STARTJOB -c "nice make acl2 -f books/build/jenkins/Makefile LISP=$LISP"


echo "Building the manual."
cd books


# See https://serverfault.com/questions/786981/adjust-oom-score-at-process-launch
# for OOM Killer discussion, which includes:
# Because it's in parentheses, it launches a subshell, sets the OOM score for
# the shell (in this case to 1000, to make it extremely likely to get killed in
# an OOM situation), and then the exec replaces the subshell with the intended
# program while leaving the new OOM score intact. It also won't affect the OOM
# score of the parent process/shell, as everything is happening inside the
# subshell.
NICENESS=13
OOM_KILLER_ADJUSTMENT=500 # medium value for the build-single case
# We don't use --keep-going here, so that emails about failures get sent ASAP:
CMD="nice -n $NICENESS make $TARGET ACL2=$WORKSPACE/saved_acl2 -j $BOOK_PARALLELISM_LEVEL -l $BOOK_PARALLELISM_LEVEL $MAKEOPTS USE_QUICKLISP=1"
CMD_WITH_OOM_KILLER_ADJUSTMENT="(echo ${OOM_KILLER_ADJUSTMENT} > /proc/self/oom_score_adj && exec ${CMD})"
$STARTJOB -c "${CMD_WITH_OOM_KILLER_ADJUSTMENT}"


echo "Build was successful."

################################################################################

books="$WORKSPACE/books"

destdirmain="$WORKSPACE/manuals"
destdirsub=`date +%F-%H%M%S`
destdir="${destdirmain}/$destdirsub"
if [ -d $destdir ] ; then
    echo "ERROR: Directory $destdir already exists"
    exit 1
fi

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

# Clear old manuals
rm -rf $destdirmain
echo "mkdir -p $destdir"
mkdir -p $destdir

# Copy from source to destination and move to destination/manual/.
echo "cp -pr $books/doc/manual $destdir/manual"
cp -pr $books/doc/manual $destdir/manual
echo "cd $destdir/manual"
cd $destdir/manual

perl "$destdir/manual/xdata2sql.pl"
perl "$destdir/manual/xdata2sql4seo.pl"

# Configure the XDATAGET parameter.
printf "var XDATAGET = \"/cgi-bin/manuals/$destdirsub/xdataget.pl\";\nvar XDOCTITLE = \"XDOC\";\n" > "$destdir/manual/config.js"

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

################################################################################

scp -o BatchMode=yes \
    $SSH_EXTRA_ARGS \
    -r \
    -i "$LEEROY_MANUAL_SSH_FILE" \
    "$destdir" \
    $LEEROY_MANUAL_SSH_USERNAME@$MANUAL_DESTINATION:"manuals/$destdirsub"

ssh -o BatchMode=yes \
    $SSH_EXTRA_ARGS \
    -i "$LEEROY_MANUAL_SSH_FILE" \
    $LEEROY_MANUAL_SSH_USERNAME@$MANUAL_DESTINATION "./deploy-latest.sh $destdirsub 2> deploy.log"
