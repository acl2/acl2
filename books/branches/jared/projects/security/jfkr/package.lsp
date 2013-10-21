(defpkg "CRYPTO" 
  (union-eq '()
    (union-eq *acl2-exports*
  	      *common-lisp-symbols-from-main-lisp-package*)))

(defpkg "JFKR" 
  (set-difference-eq
   (union-eq '()
             (union-eq (union-eq *acl2-exports* '(assert$))
                       *common-lisp-symbols-from-main-lisp-package*))

   '(er)))
