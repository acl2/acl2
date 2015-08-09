(in-package "ACL2")

;make an integerp-proofs book?

(include-book "negative-syntaxp")
(local (include-book "predicate"))
(local (include-book "fp2")) ;gross?

(local (in-theory (disable a2)))

(encapsulate
 ()
 (local (defthm no-room-for-an-integerp-between-0-and-1
          (implies (and (< x 1)
                        (< 0 x))
                   (not (integerp x)))))

 (defthm quotient-not-integerp
   (implies (and (< i j)
                 (<= 0 i)
                 (<= 0 j)
                 (case-split (< 0 i)) ;if we can show (<= 0 i) but not (< 0 i), split cases
                 (case-split (< 0 j))
                 (case-split (rationalp j)) ;gen?
                 )
            (not (integerp (/ i j))))
   ))


;integerp-minus-aux
(encapsulate
 ()
 (local (defthm minus-1-rewrite
          (equal (* -1 x)
                 (- x))))

 (defthm integerp-minus-aux
   (implies (acl2-numberp x) ;can't gen?
            (equal (integerp (* -1 x))
                   (integerp x)))))


(defthm integerp-minus
  (implies (and (syntaxp (negative-syntaxp x)) ;the negative-syntaxp test makes this rule quite general
                (case-split (acl2-numberp x))
                )
           (equal (integerp x)
                  (integerp (* -1 x)))))

(in-theory (disable integerp-minus-aux))



#|

 simplify integerp of a sum. see robert krug's meta rules on this subject

|#

(defthm integerp-sum-take-out-known-integer
   (implies (integerp n)
            (and (equal (integerp (+ n x))
                        (integerp (fix x)))
                 (equal (integerp (+ x n))
                        (integerp (fix x))))))

(defthm integerp-sum-take-out-known-integer-3
  (implies (integerp n)
           (and ;(equal (integerp (+ n x y))      ;this case not needed?
                 ;      (integerp (fix (+ x y))))
                (equal (integerp (+ x n y))
                       (integerp (fix (+ x y))))
                (equal (integerp (+ x y n))
                       (integerp (fix (+ x y))))))
  :hints (("Goal" :in-theory (disable integerp-sum-take-out-known-integer)
           :use (:instance  integerp-sum-take-out-known-integer (x (+ x y))))))


#|

 simplify integerp of a product. see robert krug's meta rules on this subject

|#

(defthm integerp-prod
  (implies (and (integerp x)
                (integerp y))
           (integerp (* x y)))
  :rule-classes (:rewrite :type-prescription))

;are these expensive?
(defthm integerp-prod-of-3-last-two
  (implies (and (integerp (* b c))
                (integerp a))
           (integerp (* a b c))))

(defthm integerp-prod-of-3-first-and-last
  (implies (and (integerp (* a c))
                (integerp b))
           (integerp (* a b c)))
  :hints (("Goal" :in-theory (disable integerp-prod-of-3-last-two)
           :use (:instance integerp-prod-of-3-last-two (a b) (b a)))))

(defthm integerp-prod-of-3-first-two
  (implies (and (integerp (* a b))
                (integerp c))
           (integerp (* a b c)))
  :hints (("Goal" :in-theory (disable integerp-prod-of-3-last-two
                                      integerp-prod-of-3-first-and-last)
           :use (:instance integerp-prod-of-3-last-two (a c) (c a)))))


;forces the constant to be in the range [0,1)  (and for 0, will be simplified further)
(defthm integerp-+-reduce-leading-constant
  (implies (syntaxp (and (quotep k)
                         (or (>= (cadr k) 1) (< (cadr k) 0))))
           (equal (integerp (+ k x))
                  (integerp (+ (+ k (- (floor k 1))) x))))) ;use mod?