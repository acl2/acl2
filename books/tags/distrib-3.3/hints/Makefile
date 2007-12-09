include ../Makefile-generic
ACL2 = ../../saved_acl2

# Dependencies:

basic-tests.cert: basic-tests.lisp
# basic-tests.cert: $(ACL2_SYSTEM_BOOKS)/make-event/eval.cert
basic-tests.cert: basic-tests.acl2

consider-hint-tests.cert: consider-hint-tests.lisp
consider-hint-tests.cert: consider-hint.cert
# consider-hint-tests.cert: $(ACL2_SYSTEM_BOOKS)/make-event/eval.cert

consider-hint.cert: consider-hint.lisp
consider-hint.cert: huet-lang-algorithm.cert
consider-hint.cert: merge-hint.cert

huet-lang-algorithm-tests.cert: huet-lang-algorithm-tests.lisp
huet-lang-algorithm-tests.cert: huet-lang-algorithm.cert
# huet-lang-algorithm-tests.cert: $(ACL2_SYSTEM_BOOKS)/make-event/eval.cert

huet-lang-algorithm.cert: huet-lang-algorithm.lisp

merge-hint.cert: merge-hint.lisp
# merge-hint.cert: $(ACL2_SYSTEM_BOOKS)/make-event/eval.cert
