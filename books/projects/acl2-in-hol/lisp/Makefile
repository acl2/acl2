include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
-include Makefile-deps

# Target clean-workxxx removes workxxx*.lisp files, which should not
# be certified (they are not books).

all: clean-workxxx

.PHONY: clean-workxxx
clean-workxxx:
	rm -rf workxxx*
