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

(in-package "RTL")

;make some of these local?
(include-book "ground-zero")
(include-book "../../arithmetic/fl")
(include-book "../../arithmetic/induct")
(local (include-book "lognot"))
(local (include-book "../../arithmetic/top"))

;(in-theory (disable acl2::binary-logand))

(defthm logand-with-zero
  (equal (logand 0 j) 0)
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-with-non-integer-arg
  (implies (or (not (integerp i))
               (not (integerp j)))
           (equal (logand i j)
                  0))
  :hints (("Goal" :in-theory (enable logand))))



;Normalize logand terms


(defthm logand-commutative
  (equal (logand j i)
         (logand i j))
  :hints (("Goal" :in-theory (enable logand))))

(encapsulate
 ()
 (local (defthm logand-associative-helper
          (implies (and (case-split (integerp i))
                        (case-split (integerp j))
                        (case-split (integerp k))
                        )
                   (equal (logand (logand i j) k)
                          (logand i (logand j k))))
          :hints (("Goal" :in-theory (enable logand evenp)
                   :induct (logand-three-args-induct i j k)))))

 (defthm logand-associative
   (equal (logand (logand i j) k)
          (logand i (logand j k)))))

(defthm logand-commutative-2
  (equal (logand j i k)
         (logand i j k))
  :hints (("Goal" :in-theory (disable LOGAND-ASSOCIATIVE
                                      logand-commutative)
           :use (LOGAND-ASSOCIATIVE
                 logand-commutative
                 (:instance LOGAND-ASSOCIATIVE (j i) (i j))))))

(defthm logand-combine-constants
  (implies (syntaxp (and (quotep i)
                         (quotep j)))
           (equal (logand i j k)
                  (logand (logand i j) k))))


(defthm logand-with-minus-one
   (implies (case-split (integerp i))
            (equal (logand -1 i) i))
  :hints (("Goal" :in-theory (enable logand))))

;Didn't make this a rewrite rule to avoid backchaining on (integerp (logand i j)) -- should never happen, but
;just in case.
(defthm logand-non-negative-integer-type-prescription
  (implies (or (<= 0 i)
               (<= 0 j))
           (and (<= 0 (logand i j))
                (integerp (logand i j))))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-negative-integer-type-prescription
  (implies (and (< i 0)
                (< j 0)
                (case-split (integerp i))
                (case-split (integerp j)))
           (and (< (logand i j) 0)
                (integerp (logand i j))))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logand))))

; rewrites (<= 0 (logand i j)) and (< (logand i j) 0)
;could this perhaps not fire (say, during backchaining) because of case-splitting of the conclusion, causing
;us to wish we had a simple rule that the rhs implies the lhs?
;BOZO consider combining with logand-non-negative
(defthm logand-negative-rewrite
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (< (logand i j) 0)
                  (and (< i 0)
                       (< j 0))))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-non-negative
  (implies (or (<= 0 x)
               (<= 0 y)
               )
           (<= 0 (logand x y))))

;This one is a loner.
;There's no nice logand-positive rule.  Nor is there a clear rewrite for (< 0 (logand i j))
;For logand to be positive, the arguments must have bits that overlap, and there's no way to state this.
(defthm logand-non-positive-integer-type-prescription
    (implies (and (<= i 0)
                  (<= j 0))
	     (and (<= (logand i j) 0)
		  (integerp (logand i j))))
  :hints (("Goal" :in-theory (enable logand)))
  :rule-classes (:type-prescription))

(defthm logand-non-positive-rewrite
    (implies (and (<= i 0)
                  (<= j 0))
	     (<= (logand i j) 0))
  :hints (("Goal" :in-theory (enable logand))))

#| do we want this?
(defthm logand-negative
  (implies (and (< i 0)
                (< j 0)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logand i j))
                (< (logand i j) 0)))
  :hints (("Goal" :in-theory (enable logand)))
  :rule-classes (:rewrite (:type-prescription)))
|#

;think about logand when the args differ in sign

(defthm logand-self
  (implies (case-split (integerp i))
           (equal (logand i i) i))
    :hints (("Goal" :in-theory (enable logand evenp))))

(defthm logand-equal-minus-one
  (equal (equal (logand i j) -1)
         (and (equal i -1) (equal j -1)))
  :hints (("goal" :in-theory (enable logand evenp))))

(defthm logand-even
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (integerp (* 1/2 (logand i j)))
                  (or (integerp (* 1/2 i))
                      (integerp (* 1/2 j)))))
  :hints (("goal" :in-theory (enable logand evenp))))

(local (in-theory (enable evenp)))

(defthm logand-0-when-one-arg-is-odd
   (implies (and (not (integerp (* 1/2 j)))
                 (case-split (integerp j))
                 (case-split (integerp i))
                 )
            (and (equal (equal (logand i j) 0)
                        (and (integerp (* 1/2 i))
                             (equal (logand (fl (* 1/2 i)) (fl (* 1/2 j))) 0)))
                 (equal (equal (logand j i) 0)
                        (and (integerp (* 1/2 i))
                             (equal (logand (fl (* 1/2 i)) (fl (* 1/2 j))) 0)))))
   :hints (("goal" :in-theory (enable logand))))

(defthm logand-simp-1
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (LOGAND (+ 1 (* 2 i))
                          (+ 1 (* 2 j)))
                  (+ 1 (* 2 (logand i j)))))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-less-than-minus-one
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< (logand i j) -1)
                  (or (and (<= i -1) (< j -1))
                      (and (<= j -1) (< i -1))))))

;simplify the conclusion?
(defthm logand-negative-5
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< -1 (logand i j))
                  (and (or (< -1 i)
                           (< -1 j)
                           (and (<= -1 j)
                                (<= -1 i))
                           )
                       (or (not (equal i -1))
                           (not (equal j -1))))))
  :hints (("Goal" :cases ((equal j -1) (equal i -1))
           :in-theory (enable logand))))



;add to this
;linear?
;another rule for j?
(defthm logand-upper-bound-1
  (implies (<= 0 i)
           (<= (logand i j) i))
  :hints (("Goal" :in-theory (enable logand)
           :induct ( LOG-INDUCT i j))))


;phrase in terms of low bit being 0 or 1?
;try disabled...
(defthm LOGAND-with-1
  (implies (case-split (integerp i))
           (and (equal (logand 1 i)
                       (if (evenp i)
                           0
                         1))
                ))
  :hints (("Goal" :in-theory (enable logand))))

;move
(defthm mod-x-2-rewrite
  (implies (case-split (integerp x))
           (equal (mod x 2)
                  (if (INTEGERP (* 1/2 X))
                      0
                    1)))
  :hints (("Goal" :in-theory (enable mod))))

(defthmd logand-def
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logand i j)
              (+ (* 2 (logand (fl (* 1/2 i)) (fl (* 1/2 j))))
                 (logand (mod i 2) (mod j 2)))))
  :rule-classes  ((:definition :controller-alist ((acl2::binary-logand t t))))
  :hints (("goal" :in-theory (enable logand))))

(defthm fl-logand-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (fl (* 1/2 (logand i j)))
                  (logand (fl (* 1/2 i)) (fl (* 1/2 j)))))
  :hints (("goal" :in-theory (disable logand fl)
           :use ((:instance logand-def)))))

(defthm floor-logand-by-2
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (floor (logand i j) 2)
                    (logand (floor i 2) (floor j 2)))))


(defthm mod-logand-by-2
  (equal (mod (logand i j) 2)
         (logand (mod i 2) (mod j 2)))
  :hints (("Goal" :in-theory (enable logand mod))))

(defthm logand-i-lognot-i
  (implies (case-split (integerp i))
           (equal (LOGAND i (LOGNOT i))
                  0))
  :hints (("Goal" :in-theory (enable logand)
           :induct (LOG-INDUCT i (LOGNOT i)))))



(defthm logand-special-value
  (implies (case-split (integerp j))
           (EQUAL (equal (LOGAND 1 j) j)
                  (or (equal j 0) (equal j 1))))
  :hints (("Goal" :in-theory (enable logand)))
)

(defun or-dist-induct (y n)
  (if (and (integerp n) (>= n 0))
      (if (= n 0)
	  y
	(or-dist-induct (fl (/ y 2)) (1- n)))
    ()))


(encapsulate
 ()
 (local (defthm logand-2**n-1-aux
  (implies (and (< i (expt 2 n))
                (integerp n) ;drop this one
                (<= 0 i)
                (case-split (integerp i))
                )
           (equal (logand i (+ -1 (expt 2 n)))
                  i))
  :hints (("Goal" :in-theory (enable logand expt)
           :induct (or-dist-induct i n)))))

 (defthmd logand-ones
  (implies (and (< i (expt 2 n)) ;bozo drop and wrap bits around i? (will have to put that proof elsewhere?)
                (<= 0 i)
                (case-split (integerp i))
                )
           (equal (logand i (+ -1 (expt 2 n)))
                  i))
   :hints (("Goal" :cases ((integerp n)))))
)


(encapsulate
 ()
 (local
  (defthm and-dist-b-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (logand (* (expt 2 n) x) y)
		(* 2 (logand (* (expt 2 (1- n)) x)
			     (fl (/ y 2))))))
    :rule-classes ()
    :hints (("Goal" :in-theory (set-difference-theories (enable expt-split)
                                                        '())
             :use ((:instance logand-def (j y) (i (* (expt 2 n) x)))
;			(:instance rem-2*i (i (* (expt 2 (1- n)) x)))
                   )))))

 (local
  (defthm and-dist-b-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (= (logand (* (expt 2 (1- n)) x) (fl (/ y 2)))
		     (* (expt 2 (1- n)) (logand x (fl (/ (fl (/ y 2)) (expt 2 (1- n))))))))
	     (= (logand (* (expt 2 n) x) y)
		(* 2
		   (* (expt 2 (1- n))
		      (logand x
			      (fl (/ (fl (/ y 2)) (expt 2 (1- n)))))))))
    :rule-classes ()
    :hints (("Goal" :use ((:instance and-dist-b-1))))))

 (local
  (defthm and-dist-b-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0)
		  (= (logand (* (expt 2 (1- n)) x) (fl (/ y 2)))
		     (* (expt 2 (1- n)) (logand x (fl (/ (fl (/ y 2)) (expt 2 (1- n))))))))
	     (= (logand (* (expt 2 n) x) y)
		(* 2
		   (* (expt 2 (1- n))
		      (logand x
			      (fl (/ y (expt 2 n))))))))
    :rule-classes ()
    :hints (("Goal"  :in-theory (set-difference-theories (enable expt-split)
                                                         '())
             :use ((:instance and-dist-b-2)
                   (:instance fl/int-rewrite (x (/ y 2)) (n (expt 2 (1- n)))))))))

 (defthm AND-DIST-B
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (>= n 0))
            (= (logand (* (expt 2 n) x) y)
               (* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
   :rule-classes ()
   :hints (("Goal" :induct (or-dist-induct y n))
           ("Subgoal *1/2" :use ((:instance and-dist-b-3))))))



#|

(local
(defthm and-dist-c-1
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0))
	     (= x (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
			  (mod x (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-fl-2 (x x) (y (expt 2 n)))
			(:instance or-dist-b (x (fl (/ x (expt 2 n)))) (y (mod x (expt 2 n))))
			(:instance mod<n (m x) (n (expt 2 n)))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
                        )))))

(local
(defthm and-dist-c-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand x y)
		(logior (logand (* (expt 2 n) (fl (/ x (expt 2 n))))
				y)
			(logand (mod x (expt 2 n))
				y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-1)
;			(:instance mod>=0 (m x) (n (expt 2 n)))
			(:instance bit-basic-h
				   (x y)
				   (y (* (expt 2 n) (fl (/ x (expt 2 n)))))
				   (z (mod x (expt 2 n))))
			(:instance bit-basic-c (x (* (expt 2 n) (fl (/ x (expt 2 n))))))
			(:instance bit-basic-c (x (mod x (expt 2 n))))
			(:instance bit-basic-c
				   (x (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
					      (mod x (expt 2 n))))))))))

(local
 (defthm and-dist-c-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand x y)
		(logior (* (expt 2 n)
			   (logand (fl (/ x (expt 2 n)))
				   (fl (/ y (expt 2 n)))))
			(logand (mod x (expt 2 n))
				y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-2)
			(:instance and-dist-b (x (fl (/ x (expt 2 n))))))))))

(local
(defthm and-dist-c-4
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand x y)
		(+ (* (expt 2 n)
		      (logand (fl (/ x (expt 2 n)))
			      (fl (/ y (expt 2 n)))))
		   (logand (mod x (expt 2 n))
			   y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-3)
			(:instance or-dist-b
				   (x (logand (fl (/ x (expt 2 n)))
					      (fl (/ y (expt 2 n)))))
				   (y (logand (mod x (expt 2 n))
					      y)))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
			(:instance mod-bnd-1 (m x) (n (expt 2 n)))
			(:instance and-dist-a (x (mod x (expt 2 n)))))))))

(defthm AND-DIST-C
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (mod (logand x y) (expt 2 n))
		(logand (mod x (expt 2 n)) y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance and-dist-c-4)
;			(:instance mod+-thm
	;			   (m (logand (mod x (expt 2 n)) y))
		;		   (n (expt 2 n))
			;	   (a (logand (fl (/ x (expt 2 n))) (fl (/ y (expt 2 n))))))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
			(:instance mod-bnd-1 (m x) (n (expt 2 n)))
			(:instance and-dist-a (x (mod x (expt 2 n))))
			(:instance mod-does-nothing (m (logand (mod x (expt 2 n)) y))
                                   (n (expt 2 n)))))))


(defthm logand-def
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (logand i j)
                  (+ (* 2 (logand (fl (* 1/2 i)) (fl (* 1/2 j))))
                     (logand (mod i 2) (mod j 2)))))
  :rule-classes nil :hints
  (("goal" :in-theory (enable logand))))

(defun op-dist-induct-2 (i j n)
  (if (and (integerp n) (>= n 0))
      (if  (= n 0)
	  (list i j)
	(op-dist-induct (floor i 2) (floor j 2) (1- n)))
    ()))

(DEFTHM LOGAND-DEF-hack
  (IMPLIES (AND (syntaxp (equal i 'x))
                (CASE-SPLIT (INTEGERP I))
                (CASE-SPLIT (INTEGERP J)))
           (EQUAL (LOGAND I J)
                  (+ (* 2
                        (LOGAND (FL (* 1/2 I)) (FL (* 1/2 J))))
                     (LOGAND (MOD I 2) (MOD J 2)))))

)


(DEFTHM LOGAND-DEF-hack-2
  (IMPLIES (AND (syntaxp (equal i 'y))
                (CASE-SPLIT (INTEGERP I))
                (CASE-SPLIT (INTEGERP J)))
           (EQUAL (LOGAND I J)
                  (+ (* 2
                        (LOGAND (FL (* 1/2 I)) (FL (* 1/2 J))))
                     (LOGAND (MOD I 2) (MOD J 2)))))

)


(defthm AND-DIST-C
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
;                  (< x (expt 2 n))
)
	     (= (mod (logand x y) (expt 2 n))
		(logand (mod x (expt 2 n)) y)))
  :rule-classes ()
  :hints (
          ("goal" :in-theory (enable logand-def expt-split)
           :induct (op-dist-induct x y n))))

  :hints (("Goal" :use ((:instance and-dist-c-4)
;			(:instance mod+-thm
	;			   (m (logand (mod x (expt 2 n)) y))
		;		   (n (expt 2 n))
			;	   (a (logand (fl (/ x (expt 2 n))) (fl (/ y (expt 2 n))))))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
			(:instance mod-bnd-1 (m x) (n (expt 2 n)))
			(:instance and-dist-a (x (mod x (expt 2 n))))
			(:instance mod-does-nothing (m (logand (mod x (expt 2 n)) y))
                                   (n (expt 2 n)))))))


;(local (include-book "bitn"))


;change name and param names eventually
(defthm AND-BITS-A
  (implies (and (integerp x); (>= x 0)
                (integerp k); (>= k 0)
                )
           (equal (logand x (expt 2 k))
                  (* (expt 2 k) (bitn x k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories (enable expt-split bitn bits logand)
                                                      '())
           :induct (or-dist-induct x k))))

(defthm LOGAND-def
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logand i j)
                  (+ (* 2 (logand (fl (* 1/2 i)) (fl (* 1/2 j))))
                     (logand (mod i 2) (mod j 2)))))
  :hints (("Goal" :in-theory (enable logand))))
|#

(defthm logand-0
  (equal (logand 0 j) 0)
  :hints (("goal" :in-theory (enable logand)))
  )

(defthm logand-even-2
  (implies (and (integerp i)
                (integerp j))
           (equal (or (= (mod i 2) 0)
                      (= (mod j 2) 0))
                  (= (mod (logand i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mod-by-2))))



#|


;BOZO try!

(defun op-dist-induct-special (i j n)
  (if (and (integerp n) (>= n 0))
      (if  (= n 0)
	  (list i j)
	(op-dist-induct-special (fl (/ i 2)) j n))
    ()))

(defun induct-fun (i)
  (if (zp i)
      nil
    (induct-fun (fl (/ i 2)))))

(defun op-dist-induct-negative (i j n)
  (if (and (integerp n) (<= n 0))
      (if (= n 0)
	  (list i j)
	(op-dist-induct-negative (fl (/ i 2)) (fl (/ j 2)) (1+ n)))
    ()))

(defthm mod-logand-aux
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (mod (logand x y) (expt 2 n))
		(logand (mod x (expt 2 n)) y)))
    :otf-flg t
  :rule-classes ()
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize)
           :induct ( op-dist-induct x y n)
           :expand (LOGAND Y (MOD X (EXPT 2 N)))
           :in-theory (e/d (logand zip expt-split) (evenp)))))
  )


|#

(defthm integer-tighten-bound
  (implies (integerp x)
           (equal (< -1 x)
                  (<= 0 x))))

;BOZO dup?
(defthmd logand-rewrite
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                )
           (equal (logand x y)
                  (+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
                     (logand (mod x 2) (mod y 2)))))
  :hints (("Goal" :in-theory (enable LOGAND-DEF)))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logand t t)))))


(defthm logand-bnd
   (implies (<= 0 x)
            (<= (logand x y) x))
   :rule-classes :linear
   )

(defthm logand-integer-type-prescription
  (integerp (logand i j))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logand))))
