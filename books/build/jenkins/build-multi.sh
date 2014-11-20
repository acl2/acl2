#!/bin/bash

# A parameterizable script for use with Jenkins "multi" build feature.
# The parameters are predictable, but here are some sample
# invocations:
#
# build-multi.sh LISP=sbcl ACL2_HONS=t ACL2_PAR="" ACL2_REAL=t TARGET=std
# build-multi.sh LISP=ccl ACL2_HONS=t ACL2_PAR=t ACL2_REAL="" TARGET=manual

# TODO: make it work with startjob, where startjob is a wrapper for
# bash (really, the challenge in this is getting the definition of
# startjob correct... it seems like aliases are disregarded).

# Cause the script to exit immediately upon failure
set -e
echo "acl2dir is $ACL2DIR"
echo "Starting build-ccl-acl2h.sh"
echo " -- Running in `pwd`"
echo " -- Running on `hostname`"
echo " -- PATH is $PATH"

source $JENKINS_HOME/env.sh

ACL2DIR=`pwd`
#alias startjob='bash'

if [ -z "$TARGET" ]; then
  echo "Setting TARGET automatically";
  TARGET='manual';
fi

if [ -z "$BOOK_PARALLELISM_LEVEL" ]; then
  echo "Setting BOOK_PARALLELISM_LEVEL to 1";
  BOOK_PARALLELISM_LEVEL='1';
fi

LISP=`which $LISP`
echo "Using LISP = $LISP"
echo "Using STARTJOB = `which startjob`"
echo "Using ACL2_HONS = $ACL2_HONS"
echo "Using ACL2_PAR  = $ACL2_PAR"
echo "Using ACL2_REAL    = $ACL2_REAL"
echo "Making TARGET   = $TARGET"

if [ "${LISP:0:3}" == "gcl" ]; then
  USE_QUICKLISP="";
else
  USE_QUICKLISP="t";
fi

set ACL2_SUFFIX=""
if [ "$ACL2_HONS" != "" ]; then
    ACL2_SUFFIX="${ACL2_SUFFIX}h"
fi

if [ "$ACL2_PAR" != "" ]; then
    ACL2_SUFFIX="${ACL2_SUFFIX}p"
fi

if [ "$ACL2_REAL" != "" ]; then
    ACL2_SUFFIX="${ACL2_SUFFIX}r"
fi

echo "Using ACL2_SUFFIX = $ACL2_SUFFIX"


echo "Making ACL2(${ACL2_SUFFIX})"
# need to use single-quote to prevent interpolation of the double
# quotes in the calling shell.  If your startjob is just a wrapper for
# bash, you'll want to use $* to pass in the arguments to startjob
startjob -c "make acl2${ACL2_SUFFIX} -f books/build/jenkins/Makefile LISP=$LISP &> make.log" \
  --name "J_${LISP}_ACL2${ACL2_SUFFIX}" \
  --limits "pmem=4gb,nodes=1:ppn=1,walltime=10:00"

echo "Building the books."
cd books
 # inherit USE_QUICKLISP for the following make call
startjob -c "nice -n 19 time make $TARGET ACL2=$WORKSPACE/saved_acl2$ACL2_SUFFIX -j $BOOK_PARALLELISM_LEVEL $MAKEOPTS"

echo "Build was successful."

exit 0
