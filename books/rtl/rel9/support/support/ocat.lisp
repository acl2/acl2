; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

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

(local (include-book "../../arithmetic/expt"))
(local (include-book "../../arithmetic/expo"))
(local (include-book "../../arithmetic/arith2"))
(local (include-book "../../arithmetic/fp2"))
(local (include-book "../../arithmetic/integerp"))

(local (in-theory (enable expt-minus)))

(defund ocat (x y n)
  (declare (xargs :guard t))
  (+ (* (expt 2 (nfix n)) (nfix x)) (nfix y)))


(defthm ocat-nonnegative-integer-type
  (and (integerp (OCAT X Y N))
       (<= 0 (OCAT X Y N)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than ocat-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription ocat)))

;just a rewrite rule
(defthm ocat-natp
  (natp (ocat x y n)))

;became less general when we made ocat nfix its args
(defthm ocat-0
    (implies (and (case-split (<= 0 y))
                  (case-split (integerp y)))
	     (equal (ocat 0 y n) y))
    :hints (("Goal" :in-theory (enable ocat))))

;became less general when we made ocat nfix its args
(defthm ocat-x-0-0
  (implies (and (case-split (<= 0 x))
                (case-split (integerp x)))
           (equal (ocat x 0 0)
                  x))
  :hints (("Goal" :in-theory (enable ocat))))


#|
;old form:
(defthm ocat-upper-bound
  (implies (and (integerp x)
                (bvecp y n) ;expensive?
                (integerp n))
           (< (ocat x y n)
              (+ (* (expt 2 n) x) (expt 2 n))))
  :hints (("Goal" :in-theory (enable ocat bvecp)))
  :rule-classes (:rewrite (:linear :trigger-terms ((ocat x y n))))
  )

|#

;this can be really expensive
;old form:
(defthm ocat-upper-bound
  (implies (and (< y (expt 2 n))
                (<= 0 x)
                (integerp x)
                (<= 0 y)
                (integerp n)
                (<= 0 n)
                )
           (< (ocat x y n)
              (+ (* (expt 2 n) x) (expt 2 n))))
  :hints (("Goal" :in-theory (enable ocat )))
  :rule-classes (:rewrite (:linear :trigger-terms ((ocat x y n))))
  )






(encapsulate
 ()
 (local (defthm ocat-bvecp-rewrite-fw
          (implies (and (integerp n)
                        (<= 0 n)
                        (integerp k)
                        (<= 0 k)
                        (integerp x)
                        (<= 0 x)
                        (>= k n) ;drop?
                        (force (bvecp y n))
                        )
                   (implies (bvecp (ocat x y n) k)
                            (bvecp x (- k n))))
          :rule-classes nil
          :hints (("goal" :in-theory (enable bvecp expt-split ocat)))
          ))

 (local (defthm hack-hack
          (implies (and (integerp x)
                        (integerp y)
                        (integerp m)
                        (<= 0 m)
                        (integerp n)
                        (<= 0 n)
                        (< x (expt 2 m))
                        (< y (expt 2 n))
                        )
                   (< (+ (/ y (expt 2 n)) x)
                      (expt 2 m)))
          :hints (("goal" :in-theory (set-difference-theories
                                      (enable expt-split)
                                      '())))))

 (local (defthm hack-ocat
          (implies (and (integerp x)
                        (integerp y)
                        (integerp m)
                        (<= 0 m)
                        (integerp n)
                        (<= 0 n)

                        (< x (expt 2 m))
                        (< y (expt 2 n))
                        )
                   (< (+ y (* x (expt 2 n)))
                      (expt 2 (+ m n))))
          :hints (("goal" :in-theory (set-difference-theories
                                      (enable expt-split)
                                      '( hack-hack))
                   :use (hack-hack
                         (:instance  mult-both-sides-of-<-by-positive (a (+ x (* y (/ (expt 2 n)))))
                                     (b (expt 2 m))
                                     (c (expt 2 n))))))))

 (local (in-theory (enable bvecp)))

 (local (defthm ocat-bvecp-rewrite-bk
          (implies (and (integerp n)
                        (<= 0 n)
                        (integerp k)
                        (<= 0 k)
                        (integerp x)
                        (<= 0 x)
                        (>= k n) ;drop?
                        (force (bvecp y n))
                        )
                   (implies
                    (bvecp x (- k n))
                    (bvecp (ocat x y n) k)))
          :rule-classes nil
          :hints (("goal" :in-theory (set-difference-theories
                                      (enable ocat)
                                      '(hack-ocat))
                   :use (:instance hack-ocat (n n) (m (- k n)))))))

 (defthm ocat-bvecp-rewrite
   (implies (and (>= k n) ;handle the other case?
                 (case-split (integerp x))
                 (case-split (<= 0 x))
                 (case-split (bvecp y n))
                 (case-split (natp n))
                 (case-split (natp k))
                 )
            (equal (bvecp (ocat x y n) k)
                   (bvecp x (- k n))))
   :hints (("goal"
            :use (ocat-bvecp-rewrite-fw ocat-bvecp-rewrite-bk))
           ))

 (local (defthm hack-4
          (implies (and (integerp x)
                        (<= 0 x)
                        (not (equal x 0)))
                   (>= x 1))))

;expensive? handle this better somehow?
 (local (defthm hack-3
          (implies (and (integerp x)
                        (<= 0 x)
                        (not (equal x 0))
                        (rationalp a)
                        (<= 0 a)
                        )
                   (>= (* x a) a))
          :rule-classes :linear
          :hints (("goal" :in-theory (disable
                                      hack-4
;                                      cancel-in-prods-<
 ;                                     cancel-times-<-eric-1
                                      )
                   :use (hack-4
                         (:instance mult-both-sides-of-<-by-positive
                                    (b a) (a (* a x)) (c (/ a))))))))


;better names?
 (defthm ocat-bvecp-other-case
   (implies (and (< p n)
                 (integerp n)
                 (<= 0 n)
                 (integerp p)
                 (<= 0 p)
                 (integerp x)
                 (<= 0 x)
                 (integerp y)
                 (<= 0 y)
                 )
            (equal (bvecp (ocat x y n) p)
                   (and (bvecp y p)
                        (equal 0 x)))
            )
   :hints (("goal" :in-theory (set-difference-theories
                               (enable power2p ocat)
                               '(expt-compare
                                 ))
            :use (:instance expt-compare (lhs (expt 2 p)) (rhs (expt 2 n)))))
   :otf-flg t
   )
 )


#|
;make more general
;also make ncat ver
(defthm highbits-ocat
  (implies (and (integerp x)
                (<= 0 x)
                (force (bvecp y n))
                (integerp n)
                (<= 0 n)
                )
           (equal (highbits (OCAT x y n) n)
                  x))
  :hints (("Goal" :in-theory (enable expt-split
                                     ocat
                                     highbits))))
|#

(local (defthm hack-10
    (implies (and (integerp x)
		  (integerp y)
		  (< x y))
	     (<= x (1- y)))
  :rule-classes ()))

(local (defthm ocat-bvecp-simple
    (implies (and (natp n)
		  (natp k)
		  (bvecp x m)
		  (natp m)
		  (bvecp y n)
		  (>= k (+ m n)))
	     (bvecp (ocat x y n) k))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable natp bvecp ocat)
                              '(expt-compare EXPT-COMPARE-EQUAL))
		  :use ((:instance expt-split (i m) (j n) (r 2))
			(:instance hack-10 (y (expt 2 m)))
			(:instance expt-weak-monotone (m p))
			(:instance expt-weak-monotone (m k) (n (+ m n))))))))

(defthm ocat-bvecp
    (implies (and (>= k n) ;handle other case?
                  (bvecp x (- k n))
                  (case-split (natp n))
		  (case-split (natp k))
		  (case-split (bvecp y n))
                  )
	     (bvecp (ocat x y n) k))
  :hints (("Goal" :in-theory (enable natp bvecp)
		  :use ((:instance ocat-bvecp-simple (m (- k n)))))))

(defthm ocat-0-rewrite
    (implies (and (case-split (integerp x))
		  (case-split (<= 0 x)))
	     (equal (ocat 0 x n) x))
    :hints (("Goal" :in-theory (enable ocat))))

(defthm ocat-with-x-not-a-natural
  (implies (or (not (integerp x))
               (< x 0))
           (equal (ocat x y n)
                  (nfix y)))
  :hints (("Goal" :in-theory (enable ocat))))

(defthm ocat-with-y-not-a-natural
  (implies (or (not (integerp y))
               (< y 0))
           (equal (ocat x y n)
                  (* (nfix x) (expt 2 (nfix n)))))
  :hints (("Goal" :in-theory (enable ocat))))

(defthm ocat-with-n-not-a-natural
  (implies (or (not (integerp n))
               (< n 0))
           (equal (ocat x y n)
                  (+ (nfix x) (nfix y))))
  :hints (("Goal" :in-theory (enable ocat))))



;might be able to generalize this more
;this look like it will fire as often as we'd like
(defthm ocat-upper-bound-2
  (implies (and (< x (expt 2 k)) ; k is a free var. huh?
                (case-split (< y (expt 2 n)))
                (case-split (integerp k))
                (case-split (<= 0 k))
                (case-split (integerp n))
                (case-split (<= 0 n))
                )
           (< (ocat x y n)
              (expt 2 (+ n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bvecp expt-split)
                              '(OCAT-BVECP-REWRITE OCAT-BVECP ))
           :use ((:instance <-TRANSITIVE (a y) (b (expt 2 n)) (c (* (EXPT 2 K) (EXPT 2 N))))
                 (:instance ocat-bvecp (k (+ n k)))))))

(defthm ocat-associative
  (implies (and (case-split (<= 0 m)) ;new now that ocat fixes its args
                (case-split (<= 0 n)) ;new now that ocat fixes its args
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (ocat (ocat x y m) z n)
                  (ocat x (ocat y z n) (+ m n))))
  :hints (("Goal" :in-theory (enable ocat))))

(defthm ocat-equal-0
  (implies  (and (case-split (<= 0 x))
                 (case-split (<= 0 y))
                 (case-split (integerp x))
                 (case-split (integerp y))
                 )
            (equal (equal (ocat x y n) 0)
                   (and (equal x 0)
                        (equal y 0))))
  :hints (("Goal" :in-theory (enable ocat)))
  )

(defthm ocat-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)
                              (quotep n)
                              (quotep m)))
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (<= m n))
                (case-split (integerp m))
                (case-split (integerp n)))
           (equal (ocat x (ocat y z m) n)
                  (ocat (ocat x y (- n m)) z m)))
  :otf-flg t
  :hints
  (("goal" :in-theory (enable ocat))))

