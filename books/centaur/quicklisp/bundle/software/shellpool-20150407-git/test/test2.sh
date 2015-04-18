#!/usr/bin/env bash

echo "stdout line 1"
sleep 1
echo "stdout line 2"
sleep 1
echo "stderr line 1" 1>&2
sleep 1
echo "stderr line 2" 1>&2
sleep 1
echo "stdout line 3"
sleep 1

exit 2
