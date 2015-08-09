(in-package "ACL2")

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))


(local (include-book "../arithmetic/top"))
(local (include-book "bvecp"))
(include-book "cat-def")
(local (include-book "bits"))
(local (include-book "bitn"))
(local (include-book "cat"))

(defund mulcat (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))
                  :verify-guards nil))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond
               ((eql n 1)
                (bits x (1- l) 0))
               ((and (integerp n) (> n 0))
                (cat (mulcat l (1- n) x)
                     (* l (1- n))
                     x
                     l))
               (t 0))))

;(defthm rationalp-mulcat
;  (and (rationalp (mulcat l n x))
;       (<= 0 (mulcat l n x)))
;  :rule-classes :type-prescription)

;(verify-guards mulcat)

(local (in-theory (disable a15)))

(defthm mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :hints (("Goal" :in-theory (enable mulcat)))
  :rule-classes (:type-prescription))

;this rule is no better than mulcat-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription mulcat)))

(defthm mulcat-1
    (implies (natp l)
	     (equal (mulcat l 1 x)
		    (bits x (1- l) 0)))
  :hints (("Goal" :in-theory (enable mulcat bits-tail)
		  :expand ((mulcat l 1 x)))))

(defthm mulcat-bvecp-simple
  (implies (and (= p (* l n))
                (case-split (natp l)))
           (bvecp (mulcat l n x) p))
  :hints (("Goal" :in-theory (enable mulcat)))
  :rule-classes ())

(defthm mulcat-bvecp
  (implies (and (>= p (* l n))
                (case-split (integerp p))
                (case-split (natp l)))
           (bvecp (mulcat l n x) p))
  :hints (("Goal" :in-theory (disable bvecp-longer)
           :use ((:instance mulcat-bvecp-simple (p (* l n)))
                 (:instance bvecp-longer (x (mulcat l n x)) (k2 p) (k1 (* l n)))))))

(defthm mulcat-0
  (equal (mulcat l n 0) 0)
  :hints (("Goal" :in-theory (enable mulcat))))

(defthm mulcat-0-two
  (equal (mulcat l 0 x) 0)
  :hints (("Goal" :in-theory (enable mulcat))))

(defthm bvecp-mulcat-1
    (implies (natp n)
	     (bvecp (mulcat 1 n 1) n))
  :rule-classes ())



(local (defthm mulcat-n-1-1
    (implies (and (natp n)
		  (> n 0))
	     (equal (mulcat 1 n 1)
		    (1+ (* 2 (mulcat 1 (1- n) 1)))))
    :hints (("Goal" :in-theory (enable mulcat cat bits-tail)))))

(defthm mulcat-n-1
    (implies (case-split (<= 0 n))
	     (equal (mulcat 1 n 1)
		    (1- (expt 2 n))))
  :hints (("Goal" :in-theory (enable mulcat expt-split))))

(defun mulcat-induct (n n2)
  (IF (AND (INTEGERP N) (> N 0) (INTEGERP N2) (> N2 0))
      (mulcat-induct (1- n) (1- n2))
      0))

(local (include-book "merge"))  ;yuck

;BOZO prove a bits-mulcat? could be used to prove-bitn-mulcat

;BOZO generalize to bits of mulcat when x is larger than 1?
;not general (note the 1 for the l parameter)
;and to when (<= n m)
;add to lib/ ?
(defthm bitn-mulcat-1
  (implies (and (< m n)
                (case-split (bvecp x 1))
                (case-split (natp m))
                (case-split (integerp n)) ;(case-split (natp n))
                )
           (equal (bitn (mulcat 1 n x) m)
                  x))
  :hints (("Goal" :induct (mulcat-induct n m)
		  :do-not '(generalize)
		  :expand ((mulcat 1 n x))
		  :in-theory (enable mulcat))))

(defthm bitn-mulcat-2
  (implies (and (<= (* l n) n2)
                (natp n)
                (natp l)
                (natp n2)
                (case-split (bvecp x l))
                )
           (equal (bitn (mulcat l n x) n2)
                  0))
  :hints (("Goal" :use ((:instance bvecp-bitn-0 (x (mulcat l n x)) (n n2))))))
