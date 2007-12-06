include ../Makefile-generic

# Dependencies:

# From other directories:

ihs-init.cert: ../data-structures/utilities.cert
math-lemmas.cert: ../arithmetic/top.cert

# From make -s dependencies:

@logops.cert: @logops.lisp
@logops.cert: ihs-definitions.cert
@logops.cert: ihs-lemmas.cert

ihs-definitions.cert: ihs-definitions.lisp
ihs-definitions.cert: ihs-init.cert
ihs-definitions.cert: ihs-theories.cert
ihs-definitions.cert: logops-definitions.cert

ihs-init.cert: ihs-init.lisp
ihs-init.cert: ../data-structures/utilities.cert
ihs-init.cert: ihs-init.acl2
ihs-init.acl2: ../data-structures/define-u-package.lisp

ihs-lemmas.cert: ihs-lemmas.lisp
ihs-lemmas.cert: math-lemmas.cert
ihs-lemmas.cert: quotient-remainder-lemmas.cert
ihs-lemmas.cert: logops-lemmas.cert

ihs-theories.cert: ihs-theories.lisp
ihs-theories.cert: ihs-init.cert

logops-definitions.cert: logops-definitions.lisp
logops-definitions.cert: ihs-init.cert
logops-definitions.cert: ihs-theories.cert
logops-definitions.cert: math-lemmas.cert
logops-definitions.cert: quotient-remainder-lemmas.cert

logops-lemmas.cert: logops-lemmas.lisp
logops-lemmas.cert: ihs-init.cert
logops-lemmas.cert: ihs-theories.cert
logops-lemmas.cert: math-lemmas.cert
logops-lemmas.cert: quotient-remainder-lemmas.cert
logops-lemmas.cert: logops-definitions.cert

math-lemmas.cert: math-lemmas.lisp
math-lemmas.cert: ../arithmetic/top.cert
math-lemmas.cert: ihs-init.cert

quotient-remainder-lemmas.cert: quotient-remainder-lemmas.lisp
quotient-remainder-lemmas.cert: ihs-init.cert
quotient-remainder-lemmas.cert: ihs-theories.cert
quotient-remainder-lemmas.cert: math-lemmas.cert
