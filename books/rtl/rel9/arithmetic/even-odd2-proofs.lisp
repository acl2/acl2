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

;This is different from the book even-odd.  (We define new functions here.)

;I could take pains to define functions that agree with evenp and oddp for all inputs (complex-rationalps are
;a little weird).  But for now, I'll just focus on the integers.

;more stuff like this is in x-2xx.lisp

;a recursive version of even

(local (include-book "integerp"))
(local (include-book "arith"))
(local (include-book "arith2"))
(local (include-book "fp2")) ;ugh

(in-theory (disable evenp))

;x should be a non-negative integer
(defund even-aux (x)
  (if (zp x)
      t
    (if (eql 1 x)
        nil
      (even-aux (+ -2 x)))))

(defthm even-aux-reduce-1
  (implies (case-split (not (zp x)))
           (equal (even-aux (+ -1 x))
                  (not (even-aux x))))
  :hints (("goal" :in-theory (enable even-aux)))
  )

;this loops with defn even-aux?
(defthmd even-aux-reduce-2
  (implies (and (integerp x)
                (< 1 x))
           (equal (even-aux (+ -2 x))
                  (even-aux x)))
  :hints (("goal" :in-theory (enable even-aux)))
  )

(defthm even-aux-reduce-3
  (implies (case-split (not (zp x)))
           (equal (even-aux (+ 1 x))
                  (not (even-aux x))))
  :hints (("goal" :expand (EVEN-AUX (+ 1 X))
           :in-theory (enable even-aux-reduce-2)))
  )

(defthm even-plus-even-pos-aux
  (implies (and (even-aux x)
                (even-aux y)
                (integerp x)
                (<= 0 x)
                (<= 0 y)
                )
           (even-aux (+ x y)))
  :hints (("Goal" :in-theory (enable even-aux zp))))

(defthm even-minus-even-pos-aux
  (implies (and (even-aux x)
                (even-aux y)
                (integerp x)
                (integerp y)
                (<= 0 x)
                (<= 0 y)
                )
           (even-aux (- x y)))
  :hints (("Subgoal *1/6" :cases ((equal y x) (equal y (+ -1 x)))
           :in-theory (set-difference-theories
                       (enable even-aux-reduce-2)
                       '(even-aux)))
          ("Goal" :cases (<= y x)
           :in-theory (enable even-aux))))

;note that even is not the same as the built in function evenp
;handle complex numbers?
(defund even (x)
  (if (not (integerp x))
      nil
    (if (< x 0)
        (even-aux (- x))
      (even-aux x))))

;keep disabled?
(defthmd even-is-evenp-pos
  (implies (and (integerp x)
                (<= 0 x))
           (equal (even-aux x) (evenp x)))
  :hints (("Goal" :in-theory (enable even-aux evenp))))

(defthmd even-is-evenp
  (implies (integerp x)
           (equal (even x) (evenp x)))
  :hints (("Goal" :in-theory (enable even evenp ;or prove evenp-minus
                                     even-is-evenp-pos
                                      ))))

(defthm even-aux-negative
  (implies (<= x 0)
           (even-aux x))
  :hints (("Goal" :in-theory (enable even-aux)))
  )

(defthm even-minus
  (implies (case-split (acl2-numberp x))
           (equal (EVEN (* -1 X))
                  (even x)))
  :hints (("Goal" :in-theory (enable even)))
  )

(defthm even-means-integerp
  (implies (even x)
           (integerp x))
  :hints (("Goal" :in-theory (enable even)))
  :rule-classes (;:compound-recognizer
                 :forward-chaining))

;export
(defthm even-plus-even
  (implies (and (even x)
                (even y)
                )
           (even (+ x y)))
  :otf-flg t
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable EVEN)
                              '( even-minus-even-pos-aux EVEN-PLUS-EVEN-POS-aux))
           :use( (:instance even-plus-even-pos-aux (x x) (y y))
                 (:instance even-plus-even-pos-aux (x (- x)) (y (- y)))
                 (:instance even-minus-even-pos-aux (x x) (y (- y)))
                 (:instance even-minus-even-pos-aux (x (- x)) (y y))
                 (:instance even-minus-even-pos-aux (x (- y)) (y x))
                 (:instance even-minus-even-pos-aux (x y) (y (- x)))))))

;export
;we don't disable even-plus-even, despite the use hint
(defthm even-sum-rewrite-1
  (implies (and (even x)
                (case-split (acl2-numberp y))
                )
           (and (equal (even (+ x y))
                       (even y))
                (equal (even (+ y x))
                       (even y))))
  :hints (("Goal" :use (:instance even-plus-even (x (* -1 x)) (y (+ x y))))))

(defund odd (x)
  (and (integerp x)
       (not (even x))))

(defthm odd-means-integerp
  (implies (odd x)
           (integerp x))
  :hints (("Goal" :in-theory (enable odd)))
  :rule-classes (;:compound-recognizer
                 :forward-chaining))

(defthm odd-plus-even
  (implies (and (odd x)
                (even y))
           (and (odd (+ x y))
                (odd (+ y x))))
  :hints (("Goal" :in-theory (enable odd))))


(defthm odd-sum-rewrite-1
  (implies (even x)
           (and (equal (odd (+ x y))
                       (odd y))
                (equal (odd (+ y x))
                       (odd y))))
  :hints (("Goal" :in-theory (enable odd) )))

#|

there are plenty more nice even-odd theorems

(defthm even-sum-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (even (+ x y))
                  (or (and (even x) (even y))
                      (and (odd x) (odd y)))))
  :hints (("Goal" :in-theory (enable odd))))

plus rules to rewrite oddp and evenp

(defthm oddp-sum
  (implies (and (integerp x)
                (integerp y))
           (equal (oddp (+ x y))
                  (or (and (oddp x) (evenp y))
                      (and (evenp x) (oddp y))))))
|#




;yuck.  generalize?
;does this loop with the defn of even?
(defthm even-reduce
  (implies (case-split (integerp n))
           (equal (EVEN (+ -1 N))
                  (not (even n))))
  :hints (("Goal" :in-theory (enable even)))
)


(defthm odd-reduce
  (implies (case-split (integerp n))
           (equal (ODD (+ -1 N))
                  (not (odd n))))
  :hints (("Goal" :in-theory (enable odd))))


(defthm odd-plus-odd
  (implies (and (odd x)
                (odd y))
           (even (+ x y)))
  :hints (("Goal"
           :use ((:instance odd-reduce (n (+ x y 1)))
                 (:instance odd-reduce (n (+ x 1)))
                 (:instance even-plus-even (x (+ 1 X Y)) (y (- (+ 1 x))))
                 )
           :in-theory (set-difference-theories
                       (enable odd)
                       '(odd-reduce)))))

(defthm odd-sum-rewrite-2
  (implies (and (odd x)
                (case-split (acl2-numberp y))
                )
           (and (equal (odd (+ x y))
                       (even y))
                (equal (odd (+ y x))
                       (even y))))
  :hints (("Goal" :in-theory (enable odd) )))

(defun induct-scheme (n)
  (if (zp n)
      t
    (cons 'a (induct-scheme (+ -1 n)))))

(defthm even-double-pos
  (implies (and (integerp x)
                (<= 0 x))
           (even (* 2 x)))
  :hints (("Goal" :induct (induct-scheme x)
           :in-theory (enable even even-aux))))

(defthm even-double
  (implies (integerp x)
           (even (* 2 x)))
  :hints (("Goal" :use ((:instance even-double-pos)
                        (:instance even-minus (x (* 2 x))); or improve even-minus with negative-syntaxp?
                        (:instance even-double-pos (x (- x))))
           :in-theory (disable even-minus even-double-pos))))

(defthm odd-double
  (implies (integerp x)
           (not (odd (* 2 x))))
  :hints (("Goal" :in-theory (enable odd))))


(defthm even-sum-rewrite-2
  (implies (odd x)
           (and (equal (even (+ x y))
                       (odd y))
                (equal (even (+ y x))
                       (odd y))))
  :hints (("Goal" :cases ((acl2-numberp y))
           :in-theory (enable odd))))

(defthm even-means-half-is-integer
  (implies (even x)
           (integerp (* 1/2 x)))
  :hints (("goal" :use even-is-evenp
           :in-theory (enable evenp))))
