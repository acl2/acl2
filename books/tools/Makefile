# Avoid circular dependency:
# In books/tools/lint.lisp:
#   (include-book "system/origin" :dir :system)
# In books/system/too-many-ifs.lisp
#   (include-book "tools/flag" :dir :system)
BOOKS := $(filter-out lint, $(patsubst %.lisp, %, $(wildcard *.lisp)))

include ../Makefile-generic
-include Makefile-deps

# Extra dependencies:

time-dollar-with-gc.cert: time-dollar-with-gc-raw.lsp
