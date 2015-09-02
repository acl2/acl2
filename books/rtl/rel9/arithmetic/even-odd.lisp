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

(local (include-book "integerp"))
(local (include-book "predicate"))
(local (include-book "fp2"))

;a funny little rule:
;can be expensive!
;perhaps should export disabled
;make a forward-chaining rule?
(defthmd even-int-implies-int
  (implies (and (integerp (* 1/2 x))
                (rationalp x) ;gen?
                )
           (integerp x))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil)))
  :hints (("Goal" :in-theory (disable integerp-prod)
           :use (:instance integerp-prod (x (* 1/2 x)) (y 2)))))

;this book is currently a mess.

;normal forms: leave evenp and oddp enabled

;from basic
(defun INDUCT-NAT (x)
  (if (and (integerp x)
	   (> x 0))
      (induct-nat (1- x))
    ()))


(local
 (defthm x-or-x/2-4
   (implies (and (integerp x) (>= x 0))
            (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
   :rule-classes ()
   :hints (("Goal" :induct (induct-nat x)))))

;is this sort of thing elsewhere? integerp.lisp?
(defthm integerp-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (+ x y))))

(defthm x-or-x/2
  (implies (integerp x)
           (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-+)
           :use ((:instance integerp-+ (x (+ 1/2 (* -1/2 X))) (y x))
                 (:instance x-or-x/2-4)
                 (:instance x-or-x/2-4 (x (- x)))))))



;end stuff from basic

(encapsulate
 ()
 (local (defthm hack-int
          (implies (and (integerp x)
                        (integerp y))
                   (integerp (+ x y)))))

 (defthm integerp-sum-of-odds-over-2
   (implies (and (rationalp x)
                 (rationalp y)
                 (integerp (* 2 x)) ;these two hyps say x is of the form (odd)/2
                 (not (integerp x)) ;
                 )
            (equal (integerp (+ x y))
                   (and (integerp (* 2 y))
                        (not (integerp y)) ; (oddp (* 2 y)) ;rephrase the oddp hyps?
                        )))
   :hints (("Goal" :in-theory (disable even-int-implies-int)
            :use ( (:instance even-int-implies-int (x (+ (* 2 x) (* 2 y))))
                   (:instance hack-int (x (+ 1/2 X)) (y (+ 1/2 y)))
                   (:instance x-or-x/2 (x (* 2 x)))
                   (:instance x-or-x/2 (x (* 2 y)))))))
 )

;derive the results below from the above (or eliminate them)

(in-theory (disable integerp-sum-of-odds-over-2))

;make this a rewrite?
;special case
(defthm integerp-sum-of-odds-over-2-leading-constant
  (implies (and (syntaxp (and (quotep x)
                              (integerp (* 2 x)) ;;these two hyps say x is of the form (odd)/2
                              (not (integerp x)) ;;
                              ))
                (rationalp x)
                (rationalp y)
                (integerp (* 2 x)) ;;these two hyps say x is of the form (odd)/2
                (not (integerp x)) ;;
                (integerp (* 2 y))
                (not (integerp y)) ; (oddp (* 2 y)) ;rephrase the oddp hyps?
                )
           (integerp (+ x y)))
  :hints (("Goal" :use integerp-sum-of-odds-over-2)))

;do we need all this stuff?

;(defthm even-or-odd
 ; (implies (integerp x)
  ;         (or (evenp x) (oddp x)))
  ;:rule-classes nil)

;should be a rewrite? - general rewrites for evenp/oddp of sum/diff?
;(defthm odd-+-1
 ; (implies (and (integerp x)
  ;              (oddp x))
   ;        (evenp (+ 1 x)))
  ;:hints (("Goal" :use (:instance x-or-x/2 ))))

;(defthm odd/2-plus-1/2
 ; (implies (and (integerp x)
  ;              (oddp x))
   ;        (integerp (+ 1/2 (/ x 2))))
  ;:hints (("Goal" :use (:instance odd-+-1))))

;hack, don't leave enabled ;rewrite?
;(defthm integerp-next
 ; (implies (and (rationalp x)
  ;              (integerp (+ x 1)))
   ;        (integerp x)))

;(defthm odd/2-minus-1/2
 ; (implies (and (integerp x)
  ;              (oddp x))
   ;        (integerp (+ -1/2 (/ x 2))))
  ;:hints (("Goal" :use (:instance odd/2-plus-1/2))))

;(in-theory (disable integerp-next))

;(defthm odd/2-minus-1/2-alt
 ; (implies (and (integerp x)
  ;              (oddp x))
   ;        (integerp (+ -1/2 (* 1/2 x))))
 ; :hints (("Goal" :in-theory (disable  odd/2-minus-1/2)
  ;         :use (:instance  odd/2-minus-1/2))))

;floor of odd/2 is odd/2 -1/2


 ;; :hints (("Goal" :use ( (:instance  fl-unique
   ;                                  (x (* 1/2 x))
    ;                                 (n (- (* 1/2 x) 1/2)))))))


;needed?

(defthm even-and-odd-alternate-eric
  (implies (and (rationalp x)
                (integerp (* 2 x)))
           (equal (integerp (+ 1/2 x))
                  (not (integerp x)))))


;should this go in type.lisp?
;needed? ;lets change any leading constant of -1/2 to 1/2 and elim this rule
(defthm even-and-odd-alternate-3
  (implies (and (integerp x))
           (equal (integerp (+ -1/2 (* -1/2 x)))
                  (not (integerp (* 1/2 x)))))
  :hints (("Goal" :in-theory (disable integerp-minus)
           :use (:instance integerp-minus (x (+ -1/2 (* -1/2 x)))))))

#| never finished this
(defthm integerp-+-odd-over-2-reduce
  (implies (and (rationalp x)
                (integerp (* 2 x)) ;these two hyps say x is of the form (odd)/2
                (not (integerp x))
                (rationalp y))
           (implies (integerp (+ x y))
                    (and (integerp (* 2 y)) ;these two hyps say x is of the form (odd)/2
                         (not (integerp y))))) ;
  :otf-flg t
  :hints (("Goal" :use  integerp-sum-of-odds-over-2)))
|#




(defthm even-and-odd-alternate-eric-2-bk
  (implies (rationalp x)
           (implies (and (integerp (* 2 x))
                         (not (integerp x)))
                    (integerp (+ 1/2 x)))))

;if s is even, then s-1 is odd
(defthm even-odd-5
  (implies (and (rationalp x)
                (integerp (* 1/2 x)))
           (and (integerp (- x 1))
                (not (integerp (* 1/2 (- x 1))))))
  :hints (("Goal" :in-theory (enable even-int-implies-int)))
)


(defthm even-and-odd-alternate-eric-2-fw
  (implies (rationalp x)
           (implies (integerp (+ 1/2 x))
                  (and (integerp (* 2 x))
                       (not (integerp x)))))
  :hints (("Goal"
           :in-theory (disable even-odd-5)
           :use (:instance even-odd-5 (x (+ 1 (* 2 x)))))))


;replace the 1/2 rules above and similarly generalize the rules at the top to be equal rules
(defthm even-and-odd-alternate-eric-2
  (implies (rationalp x)
           (equal (integerp (+ 1/2 x))
                  (and (integerp (* 2 x))
                       (not (integerp x))))))

(in-theory (disable  even-and-odd-alternate-eric-2-fw even-and-odd-alternate-eric-2-bk))


