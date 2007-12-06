(in-package "ACL2")

;(set-cbd "<???>books/cowles/")

; In each case, we include the necessary books (presumably because at
; least something needs to be included in order to provide the
; necessary packages), then we certify a book, then we undo back to
; the start, avoiding all queries by using :u.

(ubt! 1)

(defpkg 
  "ACL2-ASG"
  (set-difference-equal
   (union-eq *acl2-exports*
             *common-lisp-symbols-from-main-lisp-package*)
   '(zero)))

(certify-book 
  "acl2-asg"
  1
  nil)

:u :u

(defpkg 
  "ACL2-ASG"
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

(certify-book
  "acl2-agp"
  2
  nil)

:u :u :u

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

(certify-book "acl2-crg" 2 nil)

:u :u :u
