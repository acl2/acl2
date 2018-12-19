(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defconst *import-symbols*
  (set-difference-eq
     (union-eq (union-eq *acl2-exports*
			 '(defequiv defcong zp len make-ord))
	       *common-lisp-symbols-from-main-lisp-package*)
     '(null + * - < =
       termp ; added by Matt K., 5/26/2014
       commutativity-of-+ commutativity-of-*
       associativity-of-+ associativity-of-*
       distributivity)))

(defpkg "TER" *import-symbols*)

(defpkg "MON"
  (union-eq *import-symbols*
	    '(TER::termp)))

(defpkg "POL"
  (union-eq *import-symbols*
	    '(TER::naturalp TER::termp MON::monomial MON::coefficient
	      MON::term MON::monomialp)))

(set-verify-guards-eagerness 2)
