include ../Makefile-generic

# Dependencies:

meta-plus-equal.cert: meta-plus-equal.lisp
meta-plus-equal.cert: term-defuns.cert
meta-plus-equal.cert: term-lemmas.cert

meta-plus-lessp.cert: meta-plus-lessp.lisp
meta-plus-lessp.cert: term-defuns.cert
meta-plus-lessp.cert: term-lemmas.cert

meta-times-equal.cert: meta-times-equal.lisp
meta-times-equal.cert: term-defuns.cert
meta-times-equal.cert: term-lemmas.cert
meta-times-equal.cert: ../arithmetic/equalities.cert

meta.cert: meta.lisp
meta.cert: meta-plus-equal.cert
meta.cert: meta-plus-lessp.cert
meta.cert: meta-times-equal.cert

pseudo-termp-lemmas.cert: pseudo-termp-lemmas.lisp
pseudo-termp-lemmas.cert: term-lemmas.cert

term-defuns.cert: term-defuns.lisp

term-lemmas.cert: term-lemmas.lisp
term-lemmas.cert: term-defuns.cert
