#!/bin/sh
# Overkill System for ACL2 Testing
# Written by Jared Davis 

# display.sh -- this script shows you what is happening

# Example Invocation:
# ./display.sh RESULTS HOSTS BOOKS

RESULTS=$1
HOSTS=$2
BOOKS=$3

# while [ 1 ]
# do

SUCC=`mktemp /tmp/okill.XXXXXX` || exit 1
FAIL=`mktemp /tmp/okill.XXXXXX` || exit 1
grep "Failure: " $RESULTS > $FAIL
grep "Success: " $RESULTS > $SUCC

NUMHOST=`cat $HOSTS | wc -l`
NUMSUCC=`cat $SUCC | wc -l`
NUMFAIL=`cat $FAIL | wc -l`
NUMTOTAL=`cat $BOOKS | wc -l`


echo "$NUMHOST hosts   $NUMTOTAL books   $NUMSUCC successes   $NUMFAIL failures"

echo ""
NUMLEFT=$((`cat $BOOKS | wc -l` - $NUMSUCC - $NUMFAIL))
echo "Current Workload ($NUMLEFT files queued)"
IFS="
"
for host in `cat $HOSTS`
do
    echo "  `egrep "(Pending|Goodbye).*($host)" $RESULTS | tail -1`"
done

echo ""
echo "Failed Books"
cat $FAIL | sed "s/Failure: /  /" | sed "s/(.*)//"

echo ""
echo "Successful Books"
cat $SUCC | sed "s/Success: /  /" | sed "s/(.*)//"
           
rm -f $SUCC $FAIL

# sleep 5
# clear 
# done