;; Defining a PROOF-CHECKER-ITP13 package
;; Wanted to use symbols 'subsetp and 'variablep and 'union.

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

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
