# Cuong Chau

# Usage:

# make JOBS=4 \
#      ACL2=<Path of the ACL2 image>

# To remove certificate files, etc., execute the following:
#
# make clean ACL2=<Path of the ACL2 image>

#======================================================================
.PHONY: all clean
#======================================================================

ifndef ACL2
 $(error Variable ACL2 is undefined.)
endif

BUILD_DIR := $(dir $(ACL2))books/build
JOBS ?= 4

#======================================================================

all:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) *.lisp

clean:
	$(BUILD_DIR)/clean.pl

