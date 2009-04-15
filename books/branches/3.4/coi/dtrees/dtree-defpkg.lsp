#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(ld "Makefile.acl2")

;(include-book "list-exports" :dir :lists)
(ld "list-exports.lsp" :dir :lists)

;(include-book "map-pkg" :dir :maps)
(ld "map-exports.lsp" :dir :maps)

(defpkg "DTREE" (set-difference-eq
                 ;(remove-duplicates-eql ;no longer necessary
                  `(,@ACL2::*acl2-exports*
                    ,@ACL2::*common-lisp-symbols-from-main-lisp-package*
                    ,@MAP::*exports*
                    ADVISER::defadvice
                    a b c d e f g h i j k l m n o p q r s u v w x y z
                    )
                  ;)
                  '(remove get set fix count)))
