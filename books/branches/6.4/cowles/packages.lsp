; Written by John Cowles
; Copyright/License: See the LICENSE file in this directory.

(defpkg 
  "ACL2-CRG"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))
(defpkg 
  "ACL2-AGP"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))
(defpkg 
  "ACL2-ASG"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))
