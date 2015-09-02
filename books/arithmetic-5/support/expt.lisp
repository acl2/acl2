; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;
;; expt.lisp
;;

(in-package "ACL2")


(local (include-book "basic-arithmetic"))
(local (include-book "inequalities"))
(local (include-book "prefer-times"))
(local (include-book "expt-helper"))

(defmacro fc (x)
x)

; Much of this is adapted from John Cowles's acl2-exp.lisp book.
; There are various modifications, however.
; (Note from Matt Kaufmann: While this appears to be fair use,
; John Cowles has granted explicit permission for this in an
; email to me on 8/5/2013.)

(defthm expt-type-prescription-rationalp
  (implies (real/rationalp r)
           (real/rationalp (expt r i)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-positive-1
  (implies (and (< 0 r)
                (real/rationalp r))
           (< 0 (expt r i)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-positive-2
  (implies (and (<= 0 r)
                (real/rationalp r))
           (<= 0 (expt r i)))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-nonzero
  (implies (and (fc (acl2-numberp r))
                (not (equal r 0)))
           (not (equal 0 (expt r i))))
  :rule-classes (:type-prescription :generalize))

(defthm expt-type-prescription-integerp
  (implies (and (<= 0 i)
                (integerp r))
           (integerp (expt r i)))
  :rule-classes (:type-prescription :generalize))

(defthm equal-expt-0
  (equal (equal (expt x i) 0)
	 (and (equal (fix x) 0)
	      (not (equal (ifix i) 0)))))

(defthm expt-0
 (and (equal (expt x 0)
	     1)
      (equal (expt 0 i)
	     (if (zip i)
		 1
	         0))))

(defthm expt-1
  (and (equal (expt x 1)
	      (fix x))
       (equal (expt 1 i)
	      1)))

(local
 (defthm expt-minus
   (equal (expt r (- i))
	  (/ (expt r i)))))

(local
 (defthm expt-minus-redux
   (equal (expt r (* -1 i))
	  (/ (expt r i)))
   :hints (("Goal" :use ((:theorem (equal (* -1 i)
                                          (- i))))))))

(defthm exponents-add-1
  (implies (and (fc (integerp i))
		(fc (integerp j)))
	   (equal (expt r (+ i j))
		  (if (equal (+ i j) 0)
		      1
		      (* (expt r i)
			 (expt r j))))))

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
		     (expt r j)))))

(defthm distributivity-of-expt-over-*
  (equal (expt (* a b) i)
         (* (expt a i)
            (expt b i))))

(defthm functional-commutativity-of-expt-/-base
  (equal (expt (/ r) i)
         (/ (expt r i))))

(defthm Exponents-multiply
  (implies (and (fc (integerp i))
                (fc (integerp j)))
           (equal (expt (expt r i) j)
                  (expt r (* i j))))
  :hints (("Subgoal *1/4'" :in-theory (enable prefer-*-to-/))))

(defthm expt-is-increasing-for-base>1
  (implies (and (< 1 r)
		(< i j)
		(fc (real/rationalp r))
		(fc (integerp i))
		(fc (integerp j)))
	   (< (expt r i)
	      (expt r j)))
  :rule-classes (:rewrite :linear))

(defthm Expt-is-decreasing-for-pos-base<1
  (implies (and (< 0 r)
                (< r 1)
                (< i j)
                (fc (real/rationalp r))
                (fc (integerp i))
                (fc (integerp j)))
           (< (expt r j)
              (expt r i)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use
           ((:instance
             expt-is-increasing-for-base>1
             (r (/ r))))
	   :in-theory (enable prefer-*-to-/))))

;; Should the two following rules be linear rules?

(defthm Expt-is-weakly-increasing-for-base>1
  (implies (and (<= 1 r)
                (<= i j)
                (fc (real/rationalp r))
                (fc (integerp i))
                (fc (integerp j)))
           (<= (expt r i)
               (expt r j)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use expt-is-increasing-for-base>1
           :in-theory (disable  expt-is-increasing-for-base>1))))

(defthm Expt-is-weakly-decreasing-for-pos-base<1
  (implies (and (< 0 r)
                (<= r 1)
                (<= i j)
                (fc (real/rationalp r))
                (fc (integerp i))
                (fc (integerp j)))
           (<= (expt r j)
               (expt r i)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use expt-is-decreasing-for-pos-base<1
           :in-theory (disable expt-is-decreasing-for-pos-base<1))))

;; Should these be rewrite rules also? Probably not.

(local
 (defthm stupid-hack
   (implies (and (real/rationalp x)
		 (not (equal x 0)))
	    (equal (* x (/ x) (expt a b))
		   (expt a b)))))

(local
 (in-arithmetic-theory '((:REWRITE COMMUTATIVITY-OF-*)
			(:REWRITE COMMUTATIVITY-2-OF-*)
			(:REWRITE STUPID-HACK)
                        (:REWRITE EXPT-1)
                        (:REWRITE EXPT-0))))

(defthm expt->-1-1
  (implies (and (< 1 r)
		(< 0 i)
		(fc (real/rationalp r))
		(fc (integerp i)))
	   (< 1 (expt r i)))
  :rule-classes :linear)

(defthm expt->-1-2
  (implies (and (< 0 r)
		(< r 1)
		(< i 0)
		(fc (real/rationalp r))
		(fc (integerp i)))
	   (< 1 (expt r i)))
  :rule-classes :linear)

(defthm expt-<-1-1
  (implies (and (< 0 r)
		(< r 1)
		(< 0 i)
		(fc (real/rationalp r))
		(fc (integerp i)))
	   (< (expt r i) 1))
  :rule-classes :linear)

(defthm expt-<-1-2
  (implies (and (< 1 r)
		(< i 0)
		(fc (real/rationalp r))
		(fc (integerp i)))
	   (< (expt r i) 1))
  :hints (("Goal" :in-theory (enable prefer-*-to-/)))
  :rule-classes :linear)
