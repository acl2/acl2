# Avoid provisional certification since it fails, probably because of
# the unusual use of ACL2_COMPILE_FLG below.  Also, since this
# directory exercises ACL2(p)-level parallelism, perhaps it's just as
# well not to chance increasing make-level parallelism with
# provisional certification.
override ACL2_PCERT =

all: proofs/ideal-speedup.cert
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


