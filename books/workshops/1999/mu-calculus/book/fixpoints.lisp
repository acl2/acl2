(in-package "SETS")
(include-book "sets")

(encapsulate
 ((f (X) t)
  (S () t))

 (local (defun f (X)
          (declare (ignore X))
          nil))

 (local (defun S ()
          nil))

 (defthm f-is-monotonic
   (implies (=< X Y)
            (=< (f X) (f Y))))

 (defthm S-is-top
   (=< (f X) (set-union X (S)))))

; applyf is constrained, so we don't care about its guards.
(defun applyf (X n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      X
    (if (== X (f X))
        X
      (applyf (f X) (1- n)))))

(defabbrev lfpf ()
  (applyf nil (cardinality (S))))

(defabbrev gfpf ()
  (applyf (S) (cardinality (S))))
