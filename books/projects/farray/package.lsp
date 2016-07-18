;; DEFPKG for farrays
;; Includes the usual stuff plus b*

(defpkg "FARRAY"
  (union-eq
   '(
     define
     defsection
     defxdoc
     b*
     )
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)))
