#!/usr/bin/env bash

if [ "$#" -ne 2 ]
then
    echo "Usage: ./sleepN.sh SECS PROCS"
    exit 1
fi

SECS=$1
PROCS=$2

for((n=0; n < PROCS; n++))
do
    echo "Launching sleep.pl process $n"
    ./sleep.pl $SECS &
done

echo "Waiting for sleep.pl processes to finish."
wait

echo "Finished waiting for sleep.pl processes."
exit 0

