#!/bin/bash

# A parameterizable script for use with Jenkins "multi" build feature.
# The parameters are predictable, but here are some sample
# invocations:
#
# LISP=sbcl ACL2_HONS=h ACL2_PAR=no_p ACL2_REAL=r TARGET=std build-multi.sh
# LISP=ccl ACL2_HONS=h ACL2_PAR=p ACL2_REAL=no_r TARGET=manual build-multi.sh

# TODO: make it work with startjob, where startjob is a wrapper for
# bash (really, the challenge in this is getting the definition of
# startjob correct... it seems like aliases are disregarded).

# Cause the script to exit immediately upon failure
set -e
echo "acl2dir is $ACL2DIR"
echo "Starting build-multi.sh"
echo " -- Running in `pwd`"
echo " -- Running on `hostname`"
echo " -- PATH is $PATH"

source $JENKINS_HOME/env.sh

ACL2DIR=`pwd`

if [ -z "$TARGET" ]; then
  echo "Setting TARGET automatically";
  TARGET='manual';
fi

if [ -z "$BOOK_PARALLELISM_LEVEL" ]; then
  echo "Setting BOOK_PARALLELISM_LEVEL to 1";
  BOOK_PARALLELISM_LEVEL='1';
fi

if [ "${LISP:0:4}" == "sbcl" ]; then
  # horrible hack to set sbcl-home for leeroy.defthm.com
  export SBCL_HOME=/usr/local/lib/sbcl;
fi

LISP=`which $LISP`
echo "Using LISP = $LISP"
echo "Using STARTJOB = $STARTJOB"
#echo "Using ACL2_HONS = $ACL2_HONS"
echo "Using ACL2_PAR  = $ACL2_PAR"
echo "Using ACL2_REAL    = $ACL2_REAL"
echo "Making TARGET   = $TARGET"

if [ "${LISP:0:3}" == "gcl" ]; then
  USE_QUICKLISP="";
else
  USE_QUICKLISP="1";
fi

set ACL2_SUFFIX=""
#case "$ACL2_HONS" in
#  ""|no_h|no-h|none|NONE)
#    ACL2_SUFFIX="${ACL2_SUFFIX}c"
#    ;;
#  *)
#    ;;
#esac

case "$ACL2_PAR" in
  ""|no_p|no-p|none|NONE)
    ;;
  *)
    ACL2_SUFFIX="${ACL2_SUFFIX}p"
    ;;
esac

case "$ACL2_REAL" in
  ""|no_r|no-r|none|NONE)
    ACL2_REAL=""
    ;;
  *)
    ACL2_SUFFIX="${ACL2_SUFFIX}r"
    ;;
esac


echo "Using ACL2_SUFFIX = $ACL2_SUFFIX"

echo "Making ACL2(${ACL2_SUFFIX})"
# need to use single-quote to prevent interpolation of the double
# quotes in the calling shell.  If your startjob is just a wrapper for
# bash, you'll want to use $* to pass in the arguments to startjob
$STARTJOB -c "make acl2${ACL2_SUFFIX} -f books/build/jenkins/Makefile LISP=$LISP &> make.log" \
  --name "J_${LISP}_ACL2${ACL2_SUFFIX}" \
  --limits "pmem=4gb,nodes=1:ppn=1,walltime=10:00"

echo "Building the books."
cd books
 # inherit USE_QUICKLISP for the following make call
$STARTJOB -c "nice -n 19 time make $TARGET ACL2=$WORKSPACE/saved_acl2$ACL2_SUFFIX -j $BOOK_PARALLELISM_LEVEL $MAKEOPTS"

echo "Build was successful."

exit 0
