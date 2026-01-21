#!/bin/env bash

ANY_FAIL=0
cd examples
for i in *.lisp; do
    [ -f "$i" ] || break
    echo "Running $i"
    if sbcl --script $i; then
        echo "$i succeeded."
    else
        echo "$i failed."
        ANY_FAIL=1
    fi
done

if [[ $ANY_FAIL -eq 0 ]]; then
    echo "All examples ran successfully."
    exit 0
else
    echo "At least one example failed."
    exit 1
fi
