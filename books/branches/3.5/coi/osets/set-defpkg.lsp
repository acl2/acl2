#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

; (ld "Makefile.acl2")

(ld "../lists/list-defpkg.lsp")
(ld "computed-hints-defpkg.lsp")

(defpkg "SET"
  (set-difference-equal 
;;   (remove-duplicates-eql   ;no longer necessary due to change in ACL2
    `(lexorder << a b c d e f g h i j k l m n o p
               q r s u v w x y z
               COMPUTED-HINTS::rewriting-goal-lit
               COMPUTED-HINTS::rewriting-conc-lit
               ,@*acl2-exports*
               ,@*common-lisp-symbols-from-main-lisp-package*)
    ;)
    '(union delete find map)))

