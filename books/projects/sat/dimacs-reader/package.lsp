;; DEFPKG for DIMACS-READER
;; Includes the usual stuff plus b*

(defpkg "DIMACS-READER"
  (union-eq
   '(
     define
     defsection
     defxdoc
     b*
     implode
     explode
     rev
     )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))
