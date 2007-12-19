
ACL2_SYSTEM_BOOKS ?= ../../../..

include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

ACL2 ?= $(ACL2_SYSTEM_BOOKS)/../saved_acl2

BOOKS = mark defrecord

# Dependencies:

mark.cert: mark.lisp
mark.cert: defrecord.cert

defrecord.cert: defrecord.lisp
