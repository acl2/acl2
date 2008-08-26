(defpkg "FLAG" 
	(union-eq
         '(getprop access def-body justification current-acl2-world 
                   formals recursivep def-bodies
                   )
         (union-eq *acl2-exports*
                   *common-lisp-symbols-from-main-lisp-package*)))
