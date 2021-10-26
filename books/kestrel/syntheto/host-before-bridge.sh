#!/bin/bash

# This file will need to be copied to the parent directory of "syntheto/"

echo "Cerifying syntheto books prior to starting ACL2 Bridge"

cd /root/shared/syntheto
# If you get errors due to different :BOOK-WRITE-DATE,
# you can try uncommenting this:
# find . -name '*.cert' -exec rm {} \;
cert.pl -j 8 top
