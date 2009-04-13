ROOT_DIR = ../../../../..
BOOKS_DIR = ../../../..

# change these as necessary

include $(BOOKS_DIR)/Makefile-generic
ACL2 = $(ROOT_DIR)/saved_acl2
BOOKS = mylet error-analysis-tool3

# dependencies 

mylet.cert: mylet.lisp

error-analysis-tool3.cert: error-analysis-tool3.lisp
error-analysis-tool3.cert: mylet.cert
# error-analysis-tool3.cert: $(ACL2_SYSTEM_BOOKS)/rtl/rel7/arithmetic/top.cert
