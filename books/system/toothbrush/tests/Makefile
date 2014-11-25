# Copyright (C) 2014, ForrestHunt, Inc.
# Written by Matt Kaufmann, November, 2014
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# When des and aes are added to the community book, they should be
# added below.
TEST_DIRS := test1 test2 test-par dag-unification

.PHONY: all
all: $(TEST_DIRS)

.PHONY: $(TEST_DIRS)
$(TEST_DIRS):
	@(cd $@ ; echo "Testing in `pwd`" ; $(MAKE) TEST_DIR=$@)

clean:
	@for d in $(TEST_DIRS) ;\
	do \
	(cd $$d ; $(MAKE) clean) ;\
	done
