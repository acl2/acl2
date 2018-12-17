;; Defining a PROOF-CHECKER-ARRAY package
;; Wanted to use symbols 'subsetp and 'variablep and 'union

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

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
