; Book B.  Same R, a SECOND :EQUIVALENCE rule for it under a different name.
; B never mentions S and does not include A.
(in-package "ACL2")
(defun r (x y) (declare (xargs :guard t)) (equal (len x) (len y)))
(defthm r-equiv-2
  (and (booleanp (r x y))
       (r x x)
       (implies (r x y) (r y x))
       (implies (and (r x y) (r y z)) (r x z)))
  :rule-classes ((:equivalence)))
