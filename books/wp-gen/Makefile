# Edit the next line to specify your ACL2 command, using either := (which
# will override your ACL2 environment variable, if you have one) or ?=.
# For example:
# ACL2 := /Users/smith/acl2/v4-2/acl2-sources

wp-gen-top: top all
all: top

DIRS = mutrec

# Edit the next lines according to your own ACL2 books path.
include ../Makefile-subdirs
include ../Makefile-generic

-include Makefile-deps
