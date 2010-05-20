#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "compiler")

(in-theory (disable zp))

(defund nz () 0)
(in-theory (disable (nz) (:type-prescription nz)))

(def::un zero-fn (n)
  (if (zp n) (nz)
    (zero-fn (zero-fn (1- n)))))

(defthm zero-fn_reduction
  (implies
   (zero-fn_terminates n)
   (equal (zero-fn n) 0))
  :hints (("Goal" :in-theory (enable nz))))

(defthm open-zero-fn_terminates-closed
  (equal (zero-fn_terminates-closed n)
	 (zero-fn_terminates n))
  :hints (("Goal" :in-theory (enable 
			      ZERO-FN-5_TERMINATES-CALL
			      zero-fn_terminates-closed
			      zero-fn_terminates
			      ))))

(defun mag (n)
  (if (zp n) 0
    (mag (1- n))))

(defthm zero-fn_terminates-proof
  (zero-fn_terminates n)
  :hints (("Goal" :induct (mag n)
	   :expand (zero-fn_terminates n))))


(include-book "ordinals/lexicographic-ordering" :dir :system)

(defun m1 (x y z)
  (declare (ignore z))
  (if (<= x y) 0 1))

(defun m2 (x y z)
  (- (max (max x y) z) (min (min x y) z)))

(defun m3 (x y z)
  (- x (min (min x y) z)))

(defun tarai-measure (x y z)
  (acl2::llist (m1 x y z) (m2 x y z) (m3 x y z)))

(defun tarai-open (x y z)
  (if (<= x y) y
    (if (<= y z) z
      x)))

(defun tarai-induction (x y z)
  (declare (xargs :measure (tarai-measure x y z)
		  :well-founded-relation acl2::l<))
  (cond
   ((and (integerp x) (integerp y) (integerp z) (> x y))
    (list
     (tarai-induction (tarai-open (1- x) y z)
		      (tarai-open (1- y) z x)
		      (tarai-open (1- z) x y))
     (tarai-induction (1- x) y z)
     (tarai-induction (1- y) z x)
     (tarai-induction (1- z) x y)))
   (t y)))

(defthm open-tarai_terminates_closed
  (equal (tarai_terminates-closed x y z)
	 (tarai_terminates x y z))
  :hints (("Goal" :in-theory (enable
			      tarai_terminates-closed
			      tarai_terminates
			      TARAI-5_TERMINATES-CALL
			      ))))

(defthm tarai_terminates_proof
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp z))
   (tarai_terminates x y z))
  :hints (("Goal" :induct (tarai-induction x y z)
	   :expand (tarai_terminates x y z))))
