# The following variable should represent the ACL2 source directory.
# It is the only variable in this Makefile that may need to be edited.
ACL2_SRC = ../../..

ACL2_SYSTEM_BOOKS = $(ACL2_SRC)/books
include $(ACL2_SYSTEM_BOOKS)/Makefile-generic
ACL2 = $(ACL2_SRC)/saved_acl2

# The generic theorems:

# partial-correctness
# total-correctness
# assertions.cert
# measures.cert
# defsimulate

# The demos:

# tiny-fib-correct
# factorial-jvm-correct

assertions.cert: assertions.lisp
assertions.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert
assertions.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert

defsimulate.cert: defsimulate.lisp
defsimulate.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals-without-arithmetic.cert
defsimulate.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
# At least some of the following are needed, because of tests in defsimulate.lisp.
defsimulate.cert: assertions.cert
defsimulate.cert: partial-correctness.cert
defsimulate.cert: assertions.cert
defsimulate.cert: measures.cert
defsimulate.cert: total-correctness.cert

factorial-jvm-correct.cert: factorial-jvm-correct.lisp
factorial-jvm-correct.cert: ../m5/demo.cert
factorial-jvm-correct.cert: defsimulate.cert
factorial-jvm-correct.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert
factorial-jvm-correct.cert: factorial-jvm-correct.acl2
factorial-jvm-correct.cert: ../m5/utilities.cert

measures.cert: measures.lisp
measures.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
measures.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert
measures.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic-2/meta/top.cert

partial-correctness.cert: partial-correctness.lisp
partial-correctness.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
partial-correctness.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert

tiny-fib-correct.cert: tiny-fib-correct.lisp
tiny-fib-correct.cert: ../tiny-fib/tiny-rewrites.cert
tiny-fib-correct.cert: ../tiny-fib/fib-def.cert
tiny-fib-correct.cert: defsimulate.cert
tiny-fib-correct.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals.cert

total-correctness.cert: total-correctness.lisp
total-correctness.cert: $(ACL2_SYSTEM_BOOKS)/misc/defpun.cert
total-correctness.cert: $(ACL2_SYSTEM_BOOKS)/ordinals/ordinals-without-arithmetic.cert
total-correctness.cert: $(ACL2_SYSTEM_BOOKS)/arithmetic/top-with-meta.cert
