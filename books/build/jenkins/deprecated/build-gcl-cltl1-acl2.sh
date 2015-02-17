#!/bin/sh

set -e

echo "Starting build-gcl-cltl1-acl2.sh"
echo " -- Running in `pwd`"
echo " -- Running on `hostname`"
echo " -- PATH is $PATH"

source $JENKINS_HOME/env.sh

ACL2DIR=`pwd`

LISP=`which gcl-cltl1`
echo "Using LISP = $LISP"
echo "Using STARTJOB = `which startjob`"

echo "Making ACL2"
startjob -c "make acl2 LISP=$LISP &> make.log" \
  --name "J_GCL_CLTL1_ACL2" \
  --limits "pmem=4gb,nodes=1:ppn=1,walltime=40:00"

echo "Building the books."
cd acl2-devel/books
make ACL2=$ACL2DIR/acl2-devel/saved_acl2c all $MAKEOPTS

echo "Build was successful."

exit 0
