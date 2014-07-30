(ubt! 1) ; optional
(set-ld-skip-proofsp t state)

(ld "doc/top.acl2" :dir :system)
(ld "centaur/vl/portcullis.lisp" :dir :system) ; for defining vl::case
(ld "centaur/aignet/portcullis.acl2" :dir :system) ; needed for "SATLINK" pkg
(ld "projects/milawa/doc.acl2" :dir :system) ; for "MILAWA" package
(ld "cgen/cert.acl2" :dir :system) ; for "DEFDATA" package
(ld "centaur/defrstobj/portcullis.acl2" :dir :system) ; for "RSTOBJ" package
; To eliminate this:
;;; ACL2 Error in ( DEFUN GL-SYM::|COMMON-LISP::EQUAL| ...):  The symbol
;;; EQUAL-OF-NUMBERS (in package "GL") has neither a function nor macro
;;; definition in ACL2.  Please define it.  Note:  this error occurred
;;; in the context (EQUAL-OF-NUMBERS A B HYP).
(ld "centaur/gl/g-equal.lisp" :dir :system)
(time$ (ld "render-doc-combined.lisp"))
