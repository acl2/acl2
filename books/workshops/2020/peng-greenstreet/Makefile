# Copyright (C) 2019, University of British Columbia
# Written by Yan Peng (Feb 20 2020)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with ACL2
#

.PHONY: all clean

ACL2 ?= ../../../../saved_acl2
ACL2_SYSTEM_BOOKS ?= ../../..
ACL2_BUILD_DIR := ../../../build

JOBS ?= 8

all: top

top:
	$(ACL2_BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) -b $(ACL2_SYSTEM_BOOKS) top.lisp

clean:
	$(ACL2_BUILD_DIR)/clean.pl
