#!/usr/bin/env bash

if [ "$#" -ne 2 ]
then
    echo "Usage: ./badsleepN.sh SECS PROCS"
    exit 1
fi

SECS=$1
PROCS=$2

for((n=0; n < PROCS; n++))
do
    echo "Launching badsleep.pl process $n"
    ./badsleep.pl $SECS &
done

echo "Waiting for badsleep.pl processes to finish."
wait

echo "Finished waiting for badsleep.pl processes."
exit 0

