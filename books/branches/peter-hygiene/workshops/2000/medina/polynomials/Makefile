include ../../../../Makefile-generic

ACL2 = ../../../../../saved_acl2

# Dependencies:

addition.cert: addition.lisp
addition.cert: normal-form.cert
addition.cert: addition.acl2
addition.cert: certification.acl2

congruences-1.cert: congruences-1.lisp
congruences-1.cert: negation.cert
congruences-1.cert: congruences-1.acl2
congruences-1.cert: certification.acl2

congruences-2.cert: congruences-2.lisp
congruences-2.cert: multiplication.cert
congruences-2.cert: congruences-2.acl2
congruences-2.cert: certification.acl2

examples.cert: examples.lisp
examples.cert: congruences-2.cert
examples.cert: examples.acl2
examples.cert: certification.acl2

lexicographical-ordering.cert: lexicographical-ordering.lisp
lexicographical-ordering.cert: term.cert
lexicographical-ordering.cert: ../../../../ordinals/ordinals-without-arithmetic.cert
lexicographical-ordering.cert: lexicographical-ordering.acl2
lexicographical-ordering.cert: certification.acl2

monomial.cert: monomial.lisp
monomial.cert: term.cert
monomial.cert: monomial.acl2
monomial.cert: certification.acl2

multiplication.cert: multiplication.lisp
multiplication.cert: congruences-1.cert
multiplication.cert: multiplication.acl2
multiplication.cert: certification.acl2

negation.cert: negation.lisp
negation.cert: addition.cert
negation.cert: negation.acl2
negation.cert: certification.acl2

normal-form.cert: normal-form.lisp
normal-form.cert: polynomial.cert
normal-form.cert: lexicographical-ordering.cert
normal-form.cert: normal-form.acl2
normal-form.cert: certification.acl2

polynomial.cert: polynomial.lisp
polynomial.cert: monomial.cert
polynomial.cert: polynomial.acl2
polynomial.cert: certification.acl2

term.cert: term.lisp
term.cert: term.acl2
term.cert: certification.acl2
