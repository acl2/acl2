# Avoid provisional certification since it fails, probably because of
# the unusual use of ACL2_COMPILE_FLG below.  Also, since this
# directory exercises ACL2(p)-level parallelism, perhaps it's just as
# well not to chance increasing make-level parallelism with
# provisional certification.
override ACL2_PCERT =

# It can be useful to extend the :all target for use in ACL2(p)
# regressions, as shown just below.  However, we have seen the first
# theorem in proofs/ideal-speedup.lisp, ideal-4-way, take over 9 hours
# using ACL2(h) built on CCL with safety 3, on a fast 2012-vintage
# Linux machine.  So we avoid adding certification of that book to the
# default regression.
#
# all: proofs/ideal-speedup.cert

matrix-multiplication-parallel.cert: matrix-multiplication-serial.cert
fibonacci.cert: matrix-multiplication-parallel.cert

DIRS = proofs

include ../Makefile-subdirs
include ../Makefile-generic
-include Makefile-deps

# This is really gross and taken from the xdoc directory for lack of knowing of
# something better.
ACL2_COMPILE_FLG := t :ttags :all

# Additional dependencies to force serialization when set-compile-fns is set
# (causes a problem for GCL 2.6.*).


