#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(defpkg "LIST" 
  (set-difference-eq
;;   (remove-duplicates-eql ;no longer necessary due to change in ACL2
    `(,@*acl2-exports*
      ,@*common-lisp-symbols-from-main-lisp-package*
             
      a b c d e f g h i j k l m n o p q r s u v w x y z

      ;; Leave this here, becuase we want our version of firstn to be
      ;; the same one as used in some of the books, e.g.,
      ;; data-structures.
      firstn
             
      ;; bzo - this was originally in the ACL2 package and some code
      ;; may still rely on that.  But, we should remove this eventually.
      repeat           
             
      ;; bzo - remove me eventually if Matt adds me to *acl2-exports*
      update-nth-array 
      )
    ;)
    '(fix)))
