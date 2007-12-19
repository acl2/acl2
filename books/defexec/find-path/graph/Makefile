# The following variable should represent the ACL2 source directory.
# It is the only variable in this Makefile that may need to be edited.
ACL2_SRC = ../../../..
ACL2_SYSTEM_BOOKS ?= ../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 ?= $(ACL2_SRC)/saved_acl2

# Override default setting since solutions.lisp is not intended to be certified.
BOOKS = find-path1 find-path2 find-path3 helpers linear-find-path

# Dependencies:

find-path1.cert: find-path1.lisp
# find-path1.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# find-path1.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

find-path2.cert: find-path2.lisp
find-path2.cert: helpers.cert
# find-path2.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# find-path2.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

find-path3.cert: find-path3.lisp
find-path3.cert: helpers.cert
# find-path3.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top.cert
# find-path3.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/e0-ordinal.cert

helpers.cert: helpers.lisp

linear-find-path.cert: linear-find-path.lisp
linear-find-path.cert: find-path3.cert

solutions.cert: solutions.lisp
solutions.cert: find-path3.cert
solutions.cert: linear-find-path.cert
