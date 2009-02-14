(defpkg "FLAG" 
  (set-difference-eq
   (union-eq
    '(getprop access def-body justification current-acl2-world 
              formals recursivep def-bodies
              make-flag flag-present flag-fn-name flag-alist
              flag-defthm-macro
              flag-equivs-name expand-calls-computed-hint
              find-calls-of-fns-term
              find-calls-of-fns-list
              )
    (union-eq *acl2-exports*
              *common-lisp-symbols-from-main-lisp-package*))
   '(defmacro defthm defun verify-guards defconst mutual-recursion)))
