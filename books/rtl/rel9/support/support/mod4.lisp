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

;perhaps this book should be in arithmetic/



;just a helper function
(defund even-aux (x)
  (if (zp x)
      t
    (if (eql 1 x)
        nil
      (even-aux (+ -2 x)))))

;A recursive recognizer for even integers.
;Note that EVEN is not the same as the built in function EVENP
(defund even (x)
  (if (not (integerp x))
      nil
    (if (< x 0)
        (even-aux (- x))
      (even-aux x))))

;A recognizer for odd integers.
(defund odd (x)
  (and (integerp x)
       (not (even x))))

(local (include-book "../../arithmetic/top"))

;or maybe we do want mod4 to agree with (mod n 4) on weird values??
;no, we want a nice t-p rule?
(defund mod4 (n)
  (if (not (integerp n))
      0
    (mod n 4)))



(defthm mod4-values
  (or (equal 0 (mod4 n))
      (equal 1 (mod4 n))
      (equal 2 (mod4 n))
      (equal 3 (mod4 n)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (mod4))))
  )

(defthm mod4-type-prescription
  (and (integerp (mod4 n))
       (<= 0 (mod4 n)))
  :hints (("Goal" :use mod4-values))
  :rule-classes ((:type-prescription :typed-term (mod4 n))))

;The syntaxp hyps prevent looping.
(defthm mod4-sum-move-safe
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (case-split (<= 0 k1))
                (case-split (< k1 4))
                (rationalp n)
                (rationalp k1)
                (integerp n)
                (integerp k1)
                (integerp k2)
                )
           (equal (equal k1 (mod4 (+ k2 n)))
                  (equal (mod4 (+ k1 (- k2))) (mod4 n))))
  :hints (("Goal" :in-theory (enable mod4)
           :use (:instance mod-sum-move (x n) (y 4)))))

;orient the other way?
(defthmd even-to-mod
  (implies (integerp n)
           (equal (even n)
                  (equal 0 (mod n 2))))
  :hints (("Goal" :in-theory (enable even-is-evenp evenp mod-by-2-rewrite-to-even)))
  )


;should these next 4 be rewrite rules?
;do we need to forward from facts about even/odd to facts about mod?
(defthm mod4-is-0-fw-to-even
  (implies (and (equal 0 (mod4 n))
                (case-split (integerp n))
                )
           (even n))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (mod4 even-to-mod mod-equal-0) (integerp-prod))
           :use (:instance integerp-prod (x (* 1/4 N)) (y 2)))))

;We forward-chain to (not (even n)) instead of to (odd n) because we intend to keep ODD enabled.
(defthm mod4-is-1-fw-to-not-even
  (implies (and (equal 1 (mod4 n))
                (case-split (integerp n))
                )
           (not (even n)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (odd) (MOD4-IS-0-FW-TO-EVEN))
           :use (:instance  mod4-is-0-fw-to-even (n (+ -1 n))))))

(defthm mod4-is-2-fw-to-even
  (implies (and (equal 2 (mod4 n))
                (case-split (integerp n))
                )
           (even n))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (odd) (MOD4-IS-0-FW-TO-EVEN))
           :use (:instance  mod4-is-0-fw-to-even (n (+ -2 n))))))

;We forward-chain to (not (even n)) instead of to (odd n) because we intend to keep ODD enabled.
(defthm mod4-is-3-fw-to-not-even
  (implies (and (equal 3 (mod4 n))
                (case-split (integerp n))
                )
           (not (even n)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d (odd) (MOD4-IS-0-FW-TO-EVEN))
           :use (:instance  mod4-is-0-fw-to-even (n (+ -3 n))))))




#|
;gen -4 to any multiple of 4?
;gen to normalize the constant -4??
(defthmd mod4-reduce-by-4
  (implies (case-split (integerp n))
           (equal (mod4 (+ -4 n))
                  (mod4 n)))
  :hints (("goal" :cases ((= n 1) (= n 2))
           :in-theory (enable  mod4  mod4-neg-reduce-by-4  mod4-pos-reduce-by-4)))
  )
|#

