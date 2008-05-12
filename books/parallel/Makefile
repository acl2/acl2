# This Makefile is really a stub, to avoid certifying books that use
# parallelism primitives not defined until after ACL2 Version 3.3.  If you are
# seeing this line in a later ACL2 version, please contact the ACL2
# implementors, as this Makefile needs to be updated.

include ../Makefile-generic

BOOKS := matrix-multiplication-setup

# Dependencies:

fibonacci.cert: fibonacci.lisp
# fibonacci.cert: $(ACL2_SYSTEM_BOOKS)/make-event/assert.cert

matrix-multiplication-parallel.cert: matrix-multiplication-parallel.lisp
matrix-multiplication-parallel.cert: matrix-multiplication-setup.cert
# matrix-multiplication-parallel.cert: $(ACL2_SYSTEM_BOOKS)/make-event/assert.cert
# matrix-multiplication-parallel.cert: $(ACL2_SYSTEM_BOOKS)/make-event/embeddable-event-forms.cert

matrix-multiplication-serial.cert: matrix-multiplication-serial.lisp
matrix-multiplication-serial.cert: matrix-multiplication-setup.cert
# matrix-multiplication-serial.cert: $(ACL2_SYSTEM_BOOKS)/make-event/assert.cert
# matrix-multiplication-serial.cert: $(ACL2_SYSTEM_BOOKS)/make-event/embeddable-event-forms.cert

matrix-multiplication-setup.cert: matrix-multiplication-setup.lisp

syntax-tests.cert: syntax-tests.lisp
# syntax-tests.cert: $(ACL2_SYSTEM_BOOKS)/make-event/assert.cert
# syntax-tests.cert: $(ACL2_SYSTEM_BOOKS)/make-event/eval.cert
