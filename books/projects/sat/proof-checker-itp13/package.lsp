;; Defining a PROOF-CHECKER-ITP13 package
;; Wanted to use symbols 'subsetp and 'variablep and 'union.

(defpkg "PROOF-CHECKER-ITP13"
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
