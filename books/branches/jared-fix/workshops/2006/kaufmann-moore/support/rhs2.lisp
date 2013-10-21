; Here is another example of a double-rewrite warning from the right-hand side
; of a rewrite rule (see also rhs1.lisp).

(in-package "ACL2")

; The following explanation is given in a bit more detail in the associated
; paper.

; The problem illustrated below is that when we are relieving hyps, we have
; just one rewrite to make everything work.  So we cannot rely on the second
; pass.

; In more detail, we need to relieve (h (e (f a))).  H admits equiv1 as a
; congruence.  We use rule1 to rewrite (h (e (f a))) to (h (f a)).  Then we'd
; like to use rule2 to rewrite (h (f a)) to (h (g a)) so we can finish by
; appealing to rule4.  But without a double-rewrite on the right-hand side of
; rule1 it won't work.

; The above is not absolutely correct.  There is a way to make it work without
; putting a double-rewrite on the right-hand side of rule1.  The way is to put
; TWO double-rewrites in rule3, i.e., turn it into

; (defthm rule3 (implies (h (double-rewrite (double-rewrite x))) (c x)))

; But we don't like that because you can't predict how many nested
; double-rewrites you'll need.  The "fault" lies with rule1.

(skip-proofs
 (progn
   (defstub equiv1 (x y) t)
   (defequiv equiv1)

   (defstub c (x) t)
   (defstub e (x) t)
   (defstub f (x) t)
   (defstub g (x) t)
   (defstub h (x) t)
   (defstub i (x) t)
   (defthm rule1 (equiv1 (e x) x)) ; Double-rewrite warning for x on rhs
   (defthm rule2 (equiv1 (f x) (g x)))
   (defcong equiv1 equal (h x) 1)
   (defthm rule3 (implies (h (double-rewrite (double-rewrite x))) (c x)))
   (defthm rule4 (h (g a)))))

(defthm test
  (c (e (f a))))
