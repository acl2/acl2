#!/bin/sh

# Change to ACL2_DIR/bin/
cd `dirname $0`
# Change to ACL2_DIR/
cd ..

etags -o TAGS-acl2-doc -- *.lisp
find books -name '*.lisp' -print | (time xargs etags -o TAGS-acl2-doc --append --)
