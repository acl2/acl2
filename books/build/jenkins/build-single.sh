#!/usr/bin/env bash

# Cause the script to exit immediately upon failure
set -e
echo "acl2dir is $ACL2DIR"
echo "Starting build-single.sh"
echo " -- Running in `pwd`"
echo " -- Running on `hostname`"
echo " -- PATH is $PATH"

source $JENKINS_HOME/env.sh

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

echo "Making ACL2"
$STARTJOB -c "nice make acl2 -f books/build/jenkins/Makefile LISP=$LISP &> make.log" \
  --name "J_CCL_ACL2" \
  --limits "pmem=4gb,nodes=1:ppn=1,walltime=10:00"

echo "Building the books."
cd books

# See https://serverfault.com/questions/786981/adjust-oom-score-at-process-launch for OOM Killer discussion
NICENESS=13
OOM_KILLER_ADJUSTMENT=500 # medium value for the build-single case
CMD="nice -n $NICENESS make $TARGET ACL2=$WORKSPACE/saved_acl2 -j $BOOK_PARALLELISM_LEVEL $MAKEOPTS USE_QUICKLISP=1"
CMD_WITH_OOM_KILLER_ADJUSTMENT="(echo 500 > /proc/self/oom_score_adj && exec ${CMD})"
echo "Executing command \"${CMD_WITH_OOM_KILLER_ADJUSTMENT}\""
$STARTJOB -c ${CMD_WITH_OOM_KILLER_ADJUSTMENT}

echo "Build was successful."

exit 0
