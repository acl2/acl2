(include-book "std/portcullis" :dir :system) ; define std:: symbols below

(defpkg "FLAG" 
  (set-difference-eq
   (union-eq
    '(getprop access def-body justification current-acl2-world 
              formals recursivep def-bodies
              make-flag flag-present flag-fn-name flag-alist
              flag-defthm-macro
              flag-equivs-name
              std::expand-calls-computed-hint
              std::find-calls-of-fns-term
              std::find-calls-of-fns-list
              defxdoc defsection
              )
    (union-eq *acl2-exports*
              *common-lisp-symbols-from-main-lisp-package*))
   '(id)))
