# Yan Peng
#
# Usage:
#  make ACL2=... PYTHON=... SAVE_PY_TO=.../nil JOBS=??
#  make clean ACL2=...

.PHONY: all clean

ifndef ACL2
 $(error Variable ACL2 is undefined.)
endif
BUILD_DIR := $(dir $(ACL2))books/build
JOBS ?= 2

all:
	if [ -z "$$PYTHON" ]; then echo "Variable PYTHON is undefined"; exit 1; fi
	if [ -z "$$SAVE_PY_TO" ]; then echo "Variable SAVE_PY_TO is undefined"; exit 1; fi
	$(PYTHON) gen_ACL22SMT.py ./z3_interface/ACL2_to_Z3.py ACL22SMT.lisp
	$(PYTHON) gen_config.py -i config-template.lisp \
                          -o config.lisp \
                          -p $(PYTHON) \
                          -z $(SAVE_PY_TO) \
                          -e nil
	$(BUILD_DIR)/cert.pl -j $(JOBS) -a $(ACL2) top


clean:
	$(BUILD_DIR)/clean.pl
