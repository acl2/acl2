;; Defining a PROOF-CHECKER-ARRAY package
;; Wanted to use symbols 'subsetp and 'variablep and 'union

(defpkg "PROOF-CHECKER-ARRAY"
  (set-difference-eq
   (union-eq '(
               b*
               defxdoc
               defsection
               )
             *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(subsetp
     variablep
     union)))
