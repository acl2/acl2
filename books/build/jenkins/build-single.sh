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
$STARTJOB -c "nice make acl2 -f books/build/jenkins/Makefile LISP=$LISP"
# Outdated (as of 2020) but maybe relevant comment: If your startjob
# is just a wrapper for bash, you'll want to use $* to pass in the
# arguments to startjob
# As an example of setting a name and establishing a limit to memory and
# duration for a cluster management system, we leave the old version of this
# call below:
# $STARTJOB -c "nice make acl2 -f books/build/jenkins/Makefile LISP=$LISP" \
#   --name "J_CCL_ACL2" \
#   --limits "pmem=4gb,nodes=1:ppn=1,walltime=10:00"


echo "Building the books."
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
CMD="nice -n $NICENESS make $TARGET ACL2=$WORKSPACE/saved_acl2 -j $BOOK_PARALLELISM_LEVEL $MAKEOPTS USE_QUICKLISP=1"
CMD_WITH_OOM_KILLER_ADJUSTMENT="(echo ${OOM_KILLER_ADJUSTMENT} > /proc/self/oom_score_adj && exec ${CMD})"
$STARTJOB -c "${CMD_WITH_OOM_KILLER_ADJUSTMENT}"

echo "Build was successful."

echo "Pinging github.com to measure latency likely incurred during possible subsequent git push"
ping github.com -c 20

exit 0
