(in-package "ACL2")

(local (include-book "../lib3/top"))

(include-book "arithmetic-5/top" :dir :system)

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

;; From bits.lisp:

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

;; We define a macro, CAT, that takes a list of a list X of alternating data values
;; and sizes.  CAT-SIZE returns the formal sum of the sizes.  X must contain at
;; least 1 data/size pair, but we do not need to specify this in the guard, and
;; leaving it out of the guard simplifies the guard proof.

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))


;;;**********************************************************************
;;;			Radix-4 Booth Encoding
;;;**********************************************************************

(defun theta (i y)
  (+ (bitn y (1- (* 2 i)))
     (bitn y (* 2 i))
     (* -2 (bitn y (1+ (* 2 i))))))

(defun sum-theta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta (1- m) y))
	(sum-theta (1- m) y))))

(defthm sum-theta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 2 m))))
	     (equal y (sum-theta m y)))
  :rule-classes ())

(defun bmux4 (zeta x n)
  (case zeta
    (1  x)
    (-1 (bits (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits (lognot (* 2 x)) (1- n) 0))
    (0  0)))

(defun neg (x) (if (< x 0) 1 0))

(defun pp4-theta (i x y n)
   (if (zerop i)
       (cat 1 1
	    (bitn (lognot (neg (theta i y))) 0) 1
	    (bmux4 (theta i y) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (theta i y))) 0) 1
	  (bmux4 (theta i y) x n) n
	  0 1
	  (neg (theta (1- i) y)) 1
	  0 (* 2 (1- i)))))

(defun sum-pp4-theta (x y m n)
  (if (zp m)
      0
    (+ (pp4-theta (1- m) x y n)
       (sum-pp4-theta x y (1- m) n))))

(defun pp4p-theta (i x y n)
   (if (zerop i)
       (cat (bitn (lognot (neg (theta i y))) 0) 1
            (neg (theta i y)) 1
            (neg (theta i y)) 1
	    (bmux4 (theta i y) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (theta i y))) 0) 1
	  (bmux4 (theta i y) x n) n
	  0 1
	  (neg (theta (1- i) y)) 1
	  0 (* 2 (1- i)))))

(defthm pp4p-theta-1
  (implies (not (zp k))
           (equal (pp4p-theta k x y n)
                  (pp4-theta k x y n))))

(defthm pp4p-theta-2
  (implies (natp n)
           (and (bvecp (pp4-theta 0 x y n) (+ n 3))
                (bvecp (pp4p-theta 0 x y n) (+ n 3))
                (= (bits (pp4p-theta 0 x y n) (1- n) 0)
                   (bits (pp4-theta 0 x y n) (1- n) 0))
                (= (bits (pp4p-theta 0 x y n) (+ n 2) n)
                   (1+ (bits (pp4-theta 0 x y n) (+ n 2) n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-cat bitn-cat)
                  :use ((:instance bitn-plus-bits (x (pp4-theta 0 x y n)) (n (+ n 2)) (m n))
                        (:instance bitn-plus-bits (x (pp4-theta 0 x y n)) (n (+ n 1)) (m n))
                        (:instance bitn-plus-bits (x (pp4p-theta 0 x y n)) (n (+ n 2)) (m n))
                        (:instance bitn-plus-bits (x (pp4p-theta 0 x y n)) (n (+ n 1)) (m n))))))

(in-theory (disable pp4-theta pp4p-theta))

(defthm pp4p-theta-3
  (implies (natp n)
           (equal (pp4p-theta 0 x y n)
                  (+ (pp4-theta 0 x y n) (expt 2 n))))
  :hints (("Goal" :use (pp4p-theta-2
                        (:instance bits-plus-bits (x (pp4-theta 0 x y n)) (n (+ n 2)) (p n) (m 0))
                        (:instance bits-plus-bits (x (pp4p-theta 0 x y n)) (n (+ n 2)) (p n) (m 0))))))

(defun sum-pp4p-theta (x y m n)
  (if (zp m)
      0
    (+ (pp4p-theta (1- m) x y n)
       (sum-pp4p-theta x y (1- m) n))))

(defthm pp4p-theta-4
  (implies (and (natp n)
                (not (zp m)))
           (equal (sum-pp4p-theta x y m n)
                  (+ (expt 2 n) (sum-pp4-theta x y m n))))
  :hints (("Subgoal *1/2" :cases ((= m 1)))))

(defthm pp4p-theta-5
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (equal (sum-pp4p-theta x y m n)
	            (+ (expt 2 (+ n (* 2 m)))
 	               (* x y))))
  :hints (("Goal" :use (booth4-corollary))))

(defthm expt-hack
  (implies (and (natp x)
                (natp n)
                (natp m)
                (> n m)
                (>= x (expt 2 n)))
           (>= x (expt 2 m)))
  :rule-classes ())

(defthm booth4-corollary-2
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (bits (sum-pp4p-theta x y m n) (1- (+ n (* 2 m))) 0)
                (* x y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bvecp) (acl2::|(* (expt c m) (expt d n))| acl2::|(< (expt x n) (expt x m))| acl2::expt-is-increasing-for-base->-1 bits-tail))
                  :use ((:instance bits-tail (x (* x y)) (i (1- (+ n (* 2 m)))))
                        (:instance expt-hack (x (* x y)) (n (+ n (* 2 m))) (m (+ -2 n (* 2 m))))
                        (:instance bvecp-product (m (1- n)) (n (1- (* 2 m))))
                        (:instance bits-plus-mult-2
                                   (n (1- (+ n (* 2 m)))) (m 0) (k (+ n (* 2 m))) (x (* x y)) (y 1))))))

(in-theory (disable pp4p-theta-1 pp4p-theta-3 pp4p-theta-4 pp4p-theta-5))

(in-theory (enable pp4p-theta))

(defthm booth4-corollary-1
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (+ (expt 2 n)
		   (sum-pp4-theta x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :rule-classes ()
  :hints (("Goal" :use (booth4-corollary))))
