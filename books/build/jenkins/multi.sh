#!/bin/bash

# A parameterizable script for use with Jenkins "multi" build feature.
# The parameters are predictable, but here are some sample
# invocations:
#
# multi.sh LISP=sbcl ACL2_HONS=t ACL2_PAR="" NONSTD=t
# multi.sh LISP=ccl ACL2_HONS=t ACL2_PAR=t NONSTD=""

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

LISP=`which $LISP`
echo "Using LISP = $LISP"
#echo "Using STARTJOB = `which startjob`"
echo "Using ACL2_HONS = $ACL2_HONS"
echo "Using ACL2_PAR  = $ACL2_PAR"
echo "Using NONSTD    = $NONSTD"
echo "Making TARGET   = $TARGET"

set ACL2_SUFFIX=""
if [ "$ACL2_HONS" != "" ]; then
    ACL2_SUFFIX="${ACL2_SUFFIX}h"
fi

if [ "$ACL2_PAR" != "" ]; then
    ACL2_SUFFIX="${ACL2_SUFFIX}p"
fi

if [ "$NONSTD" != "" ]; then
    ACL2_SUFFIX="${ACL2_SUFFIX}r"
fi

echo "Using ACL2_SUFFIX = $ACL2_SUFFIX"


echo "Making ACL2(${ACL2_SUFFIX})"
# need to use single-quote to prevent interpolation of the double
# quotes in the calling shell.  If your startjob is just a wrapper for
# bash, you'll want to use $* to pass in the arguments to startjob
make acl2${ACL2_SUFFIX} -f books/build/jenkins/Makefile LISP=$LISP &> make.log #\
#  --name "J_CCL_ACL2H" \
#  --limits "pmem=4gb,nodes=1:ppn=1,walltime=10:00"
#make LISP=$LISP &> make.log 

echo "Building the books."
cd books
nice time make $TARGET ACL2=$WORKSPACE/saved_acl2$ACL2_SUFFIX -j3 $MAKEOPTS USE_QUICKLISP=1

#cd acl2-devel/books
#make ACL2=$ACL2DIR/acl2-devel/saved_acl2h all $MAKEOPTS USE_QUICKLISP=1

echo "Build was successful."

exit 0


