; A double-rewrite example based on events from Dave Greve.

(in-package "ACL2")

(defun equiv (x y)
  (equal x y))

(defequiv equiv)

(encapsulate
 ((foo (x) t)
  (pred (x) t)
  (goo (x) t)
  (hoo (x) t))

 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)
 (local (defun foo (x) t))
 (local (defun pred (x) t))
 (local (defun goo (x) t))
 (local (defun hoo (x) t))

 (defthm pred-hoo
   (pred (hoo x)))
 (defthm goo-to-hoo
   (equiv (goo x) (hoo x)))
 (defcong equiv iff (pred x) 1)
 (defthm pred-implies-foo
   (implies
    (pred (double-rewrite x)) ; warning eliminated by double-rewrite call
    (foo x))))

(defthm foo-of-goo-equiv-enabled
  (foo (goo x))
  :rule-classes nil)

; Let's keep equiv in the mix for experiments below.
(in-theory (disable equiv))

(defthm foo-of-goo
  (foo (goo x))
  :rule-classes nil)

(defthm foo-of-goo-again
  (foo (goo x))
  :rule-classes nil)

(defthm pred-implies-foo-again
  (implies
   (and (equiv y (double-rewrite x))
        (pred y))
   (foo x)))

(in-theory (disable pred-implies-foo))

(defthm foo-of-goo-yet-again
  (foo (goo x))
  :rule-classes nil)

; The following modification of pred-implies-foo-again (above) generates a
; double-rewrite warning, because without the double-rewrite call, the equiv
; hypothesis does not bind y.
(defthm pred-implies-foo-again-with-warning
  (implies (and (equiv y x)
                (pred y))
           (foo x)))

; Fails, as the above-mentioned warning suggests could happen:
; (thm (foo (goo x))
;      :hints (("Goal" :in-theory (disable pred-implies-foo-again))))
