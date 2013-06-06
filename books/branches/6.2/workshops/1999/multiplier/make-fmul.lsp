; Added by Jared, Feb 2013, for simpler Makefile
(value :q)
(lp)
(include-book "compiler")
(compile-pipeline "fmul" z)
(value :q)
(exit-lisp)