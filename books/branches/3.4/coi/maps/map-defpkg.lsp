#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

;(include-book "sets-pkg" :dir :osets)
(ld "set-defpkg.lsp" :dir :osets)

;(include-book "adviser-pkg" :dir :adviser)
(ld "adviser-defpkg.lsp" :dir :adviser)

(defpkg "MAP" (set-difference-eq 
;               (remove-duplicates-eql ;no longer necessary
                `(,@ACL2::*acl2-exports*
                  ,@ACL2::*common-lisp-symbols-from-main-lisp-package*
		  a b c d e f g h i j k l m n o p q r s u v w x y z
		  ADVISER::defadvice)
                ;)
               '(get set default optimize fix)))
