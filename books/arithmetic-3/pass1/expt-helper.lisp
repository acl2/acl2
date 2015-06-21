; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;
;; expt-helper.lisp
;;

(in-package "ACL2")


(local (include-book "basic-arithmetic"))

(local (include-book "inequalities"))

(local (include-book "prefer-times"))

(defmacro fc (x)
  x)

(defthm expt-crock
    (equal (expt x 1)
           (fix x))
  :hints (("Goal" :expand (expt x 1))))

(encapsulate
 ()

 (local
  (defun
    Math-induction-start-at-k (k n)
    (declare (xargs :measure (if (and (integerp k)
                                      (integerp n)
                                      (< k n))
                                 (- n k)
                               0)))
    (if (and (integerp k)
             (integerp n)
             (< k n))
        (Math-induction-start-at-k k (+ -1 n))
      t)))

 (local
  (defthm justify-induction
    (implies (and (integerp i)
		  (< 1 r)
		  (rationalp r))
	     (< (expt r i) (expt r (+ 1 i))))
    :hints (("Goal" :in-theory (enable prefer-*-to-/)))))

 (defthm expt-is-increasing-for-base>1
   (implies (and (< 1 r)
                 (< i j)
                 (rationalp r)
                 (integerp i)
                 (integerp j))
            (< (expt r i)
               (expt r j)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal"
	    :do-not '(generalize)
            :induct (Math-induction-start-at-k i j)
	    :in-theory (enable prefer-*-to-/))
	   ("Subgoal *1/1" :use (:instance justify-induction
					   (i (+ -1 J))))))
)

;; The following four theorems need to be proved in the order
;; given.  However, I want them to be in a different order so
;; I prove them here, and then include them in expt.lisp in the
;; right order.

(defthm exponents-add-for-nonpos-exponents
  (implies (and (<= i 0)
		(<= j 0)
		(fc (integerp i))
		(fc (integerp j)))
	   (equal (expt r (+ i j))
		  (* (expt r i)
		     (expt r j)))))

(defthm exponents-add-for-nonneg-exponents
  (implies (and (<= 0 i)
		(<= 0 j)
		(fc (integerp i))
		(fc (integerp j)))
	   (equal (expt r (+ i j))
		  (* (expt r i)
		     (expt r j)))))

(defthm exponents-add-2
  (implies (and (not (equal 0 r))
		(fc (acl2-numberp r))
		(fc (integerp i))
		(fc (integerp j)))
	   (equal (expt r (+ i j))
		  (* (expt r i)
		     (expt r j))))
  :hints (("Goal" :expand (expt r (+ i j)))))

(defthm exponents-add-1
  (implies (and (fc (integerp i))
		(fc (integerp j)))
	   (equal (expt r (+ i j))
		  (if (equal (+ i j) 0)
		      1
		      (* (expt r i)
			 (expt r j)))))
  :hints (("Goal" :do-not '(generalize))))
