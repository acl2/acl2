include ../Makefile-generic

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
