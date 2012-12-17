include ../../../../Makefile-generic
-include Makefile-deps
# Avoid popcount-demo.lisp, which is more or less subsumed by
# popcount.lisp and might otherwise be done in parallel with it
# (depending on how `make' is invoked), resulting in memory usage that
# stresses a machine with 8GB of RAM.
BOOKS = popcount
