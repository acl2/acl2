; This is a modification of rhs1.lisp, but where instead of equiv1 we use iff.
; This illustrates that there is value in creating a double-rewrite warning for
; the right-hand side even if

(in-package "ACL2")

(skip-proofs
 (progn
   (defstub c (x) t)
   (defstub e (x) t)
   (defstub f (x) t)
   (defstub g (x) t)
   (defstub h (x) t)
   (defstub i (x) t)
   (defthm rule1 (iff (e x) x)) ; Double-rewrite warning for x on rhs
   (defthm rule2 (iff (f x) (g x)))
   (defcong iff equal (h x) 1)
   (defthm rule3 (implies (h (double-rewrite x)) (c x)))
   (defthm rule4 (h (g a)))))

; Fails.
; (defthm test
;   (c (e (f a))))
