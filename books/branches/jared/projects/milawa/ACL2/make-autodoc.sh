#!/bin/sh

set -e

HERE=`pwd`

echo "Make sure autodoc is up to date."
omake .PHONY/build/all .PHONY/clauses/all .PHONY/tactics/all .PHONY/rewrite/all -j 64

echo "Remove old autodoc archives"

rm -f $HERE/build-autodoc.tar.gz
rm -f $HERE/clauses-autodoc.tar.gz
rm -f $HERE/lift-autodoc.tar.gz
rm -f $HERE/traces-autodoc.tar.gz
rm -f $HERE/assms-autodoc.tar.gz
rm -f $HERE/rewrite-autodoc.tar.gz
rm -f $HERE/tactic-autodoc.tar.gz
rm -f $HERE/diss-autodoc.tar.gz

echo "Build new autodoc archives"

cd $HERE/build; tar cvfz $HERE/build-autodoc.tar.gz autodoc
cd $HERE/clauses; tar cvfz $HERE/clauses-autodoc.tar.gz autodoc
cd $HERE/clauses/if-lifting; tar cvfz $HERE/lift-autodoc.tar.gz autodoc
cd $HERE/rewrite/assms; tar cvfz $HERE/assms-autodoc.tar.gz autodoc
cd $HERE/rewrite/traces; tar cvfz $HERE/traces-autodoc.tar.gz autodoc
cd $HERE/rewrite; tar cvfz $HERE/rewrite-autodoc.tar.gz autodoc
cd $HERE/tactics; tar cvfz $HERE/tactic-autodoc.tar.gz autodoc


echo "Build consolidated autodoc archive."

cd $HERE

tar cvfz \
    diss-autodoc.tar.gz \
    build-autodoc.tar.gz \
    clauses-autodoc.tar.gz \
    lift-autodoc.tar.gz \
    traces-autodoc.tar.gz \
    assms-autodoc.tar.gz \
    rewrite-autodoc.tar.gz \
    tactic-autodoc.tar.gz

echo "Clean up intermediate archives"

rm -f $HERE/build-autodoc.tar.gz
rm -f $HERE/clauses-autodoc.tar.gz
rm -f $HERE/lift-autodoc.tar.gz
rm -f $HERE/traces-autodoc.tar.gz
rm -f $HERE/assms-autodoc.tar.gz
rm -f $HERE/rewrite-autodoc.tar.gz
rm -f $HERE/tactic-autodoc.tar.gz


echo "All done"