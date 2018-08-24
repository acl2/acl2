#!/bin/sh

set -e

rm -f test-link

ln -s makelink.sh test-link

ln -s ./does/not/exist test-broken-link
