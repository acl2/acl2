#!/bin/sh

# Note: Assumes that $workfile is empty or suitably initialized
# and that $ACL2 is defined.

if [ $# != 1 ] ; then
    echo "Usage: run-test.sh outfile"
    exit 1
fi

outfile=$1
workfile=workxxx.$1

echo '(include-book "run")' >> $workfile
echo '(time$ (run-timing* 10000 st$))' >> $workfile
echo '(time$ (run-init* 10000 st$))' >> $workfile
echo '(time$ (run-timing* 10000 st$))' >> $workfile
echo '(time$ (run-init* 10000 st$))' >> $workfile
echo 'Preparing to run the following commands:'
echo '----------'
cat $workfile
echo 'Running the above commands and then displaying timing'
echo 'results from running 350000 instructions: first the total,'
echo 'then just running the corresponding initializations.'
echo '(So ips is 350000 divided by their difference.)'
echo '----------'
echo '(ld "'$workfile'" :ld-pre-eval-print t)' | $ACL2 > $outfile
tail -13 $outfile
