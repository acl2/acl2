(in-package "ACL2")

;Did we say we'd keep log= enabled?  Will this cause lots of splitting on ifs?

(defund log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

;or did we say we'd keep log= disabled?
(defthm log=-same
  (equal (log= x x) 1)
  :hints (("Goal" :in-theory (enable log=))))