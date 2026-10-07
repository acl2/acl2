; Book A.  R (equal lengths) is a genuine refinement of S (equal consp-ness),
; and G has an S-congruence.  So a goal (equal (G x) (G y)) can be closed from an
; R hypothesis ONLY via the refinement R -> S.
(in-package "ACL2")
(defun r (x y) (declare (xargs :guard t)) (equal (len x) (len y)))
(defun s (x y) (declare (xargs :guard t)) (equal (consp x) (consp y)))
(defun g (x) (declare (xargs :guard t)) (if (consp x) 1 0))
(defequiv r)
(defequiv s)
(defrefinement r s)
(defcong s equal (g x) 1)
