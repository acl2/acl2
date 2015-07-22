# Cuong Chau

# Usage:

# make JOBS=2 \
#      ACL2r=<Path of the ACL2r image>

# To remove certificate files, etc., execute the following:
# 
# make clean ACL2r=<Path of the ACL2r image>

#======================================================================
.PHONY: all clean
#======================================================================

ifndef ACL2r
 $(error Variable ACL2r is undefined.)
endif

BUILD_DIR := $(dir $(ACL2r))books/build
JOBS ?= 2

#======================================================================

all:
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2r) fourier-sums int-infinite-sum-1 int-infinite-sum-2

clean:
	$(BUILD_DIR)/clean.pl

