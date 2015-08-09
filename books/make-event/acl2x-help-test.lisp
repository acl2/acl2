
(in-package "ACL2")

;; Yes, this include-book may be local even though we'll use macros defined in
;; it, in an apparently nonlocal manner.
(local (include-book "acl2x-help"))

;; If the acl2x-expansion-alist-replacement attachment necessary for the
;; functioning of acl2x-replace has been removed, this replaces it.
;; (use-acl2x-replace)

(acl2x-replace
 ;; this is only run during pass 1 of certification
 (skip-proofs (defthm pass1-only (equal t nil) :rule-classes nil))
 ;; this is run except during pass 1.
 (defthm pass2-and-otherwise
   (equal x x) :rule-classes nil))
