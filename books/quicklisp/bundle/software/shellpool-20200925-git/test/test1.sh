#!/usr/bin/env bash

echo "stdout line 1"
echo "stdout line 2"
echo "stderr line 1" 1>&2
echo "stderr line 2" 1>&2
echo "stdout line 3"
exit 0
