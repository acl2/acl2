ACL2 ?= ../../../../../saved_acl2
include ../../../../Makefile-generic

# Don't alphabetize this list!
BOOKS = float-extra float
 
# Dependencies:


float-extra.cert: float-extra.lisp
float-extra.cert: ../lib1/top.cert

float.cert: float.lisp
float.cert: ../lib1/log.cert
float.cert: ../lib1.delta1/float.cert
float.cert: float-extra.cert
