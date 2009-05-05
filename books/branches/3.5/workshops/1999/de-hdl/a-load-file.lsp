
;;;  The DE Language                  Warren A. Hunt, Jr.

;;;  Commands to admit the DE interpreter definition.

;;;  Use:  (ld "a-load-file.lisp")

(LD '((CERTIFY-BOOK "help-defuns" 0))) :ubt! 1
(LD '((CERTIFY-BOOK "measure"     0))) :ubt! 1
(LD '((CERTIFY-BOOK "primitives"  0))) :ubt! 1
(LD '((CERTIFY-BOOK "syntax"      0))) :ubt! 1
(LD '((CERTIFY-BOOK "arity"       0))) :ubt! 1
(LD '((CERTIFY-BOOK "sts-okp"     0))) :ubt! 1
(LD '((CERTIFY-BOOK "de4"         0))) :ubt! 1

(include-book "de4")

(ld "examples.lisp")
(ld "thm-example.lisp")
