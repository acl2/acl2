(in-package "ACL2")

#|
This book contains a hodgepodge of useful arithmetic rules.
It's still kind of a mess.  But it's better now that we have the rules in common-factor.lisp.

|#

(include-book "fp2")
(include-book "predicate")
(include-book "product")
(include-book "meta/meta-times-equal" :dir :system)
(include-book "meta/meta-plus-equal" :dir :system)
(include-book "meta/meta-plus-lessp" :dir :system)


;get more rules from arithmetic-2 ?




;;=================================================================================
;; Collect leading constants in comparisons.
;; This section is complete.  [what about products??]
;;===================================================================================

(defthm collect-constants-in-equal-of-sums
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (case-split (acl2-numberp c1))
                )
           (and (equal (equal (+ c2 x) c1)
                       (equal (fix x) (- c1 c2)))
                (equal (equal c1 (+ c2 x))
                       (equal (fix x) (- c1 c2))))))

(defthm collect-constants-in-equal-of-sums-2
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (and (equal (equal (+ c2 x) (+ c1 y))
                       (equal (fix x) (+ (- c1 c2) y))))))

(defthm collect-constants-in-<-of-sums
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (and (equal (< (+ c2 x) c1)
                       (< x (- c1 c2)))
                (equal (< c1 (+ c2 x))
                       (< (- c1 c2) x)))))

(defthm collect-constants-in-<-of-sums-2
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (< (+ c2 x) (+ c1 y))
                  (< x (+ (- c1 c2) y)))))


;this book includes (how many?) main types of lemmas

;there's stuff in inverted-factor too


;collecting constants
; equal with sums
; < with sums
; < with products
; equal with products

;rearranging negative coeffs
;getting rid of fractional coeffs

;cancelling factors in comparisons of sums (these sums may each have only 1 addend)

;misc lemmas (comparing products to 0)

;see equal-constant-+ in equalities.lisp

;see also see MULT-BOTH-SIDES-OF-EQUAL
(defthmd mult-both-sides-of-<-by-positive
  (implies (and (<= 0 c)
                (rationalp c)
                (case-split (< 0 c))
                )
           (equal (< (* c a) (* c b))
                  (< a b))))


(include-book "meta/meta-times-equal" :dir :system)
(include-book "meta/meta-plus-equal" :dir :system)
(include-book "meta/meta-plus-lessp" :dir :system)


(defthm mult-both-sides-of-equal
  (implies (and (case-split (acl2-numberp a))
                (case-split (acl2-numberp b))
                (case-split (acl2-numberp c))
                )
           (equal (equal (* a c) (* b c))
                  (if (equal c 0)
                      t
                    (equal a b))))
  :rule-classes nil)



#|

;instead of these, we should just cancel common factors from the constants

;open question: how to handle (equal (* 2 x) (* 3 y)) -- should we collect the constants or not?
;maybe so, since doing so would let us substitue for one of the vars (x or y).

;don't yet handle negative constants
;prefers that quotient of the constants be > 1  -perhaps we want the quotient to be < 1???
;maybe the constant should be by itself?
(defthm collect-constants-in-product-<-1-of-2-with-1-of-2
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (rationalp c1)
                (rationalp c2)
                (< 0 c1) ;gen
                (< 0 c2) ;gen
                (rationalp a)
                (rationalp b))
           (equal (< (* c1 a) (* c2 b))
                  (if (> c1 c2)
                      (< (* (/ c1 c2) a) b)
                    (< a (* (/ c2 c1) b)))))
  :hints (("Goal" :use ((:instance mult-both-sides-of-<-by-positive
                                   (a (* c1 a))
                                   (b (* c2 b))
                                   (c (/ c1)))
                        (:instance mult-both-sides-of-<-by-positive
                                   (a (* c1 a))
                                   (b (* c2 b))
                                   (c (/ c2)))))))

(defthm collect-constants-in-product-<-1-of-1-with-1-of-2
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (rationalp c1)
                (rationalp c2)
                (< 0 c1) ;gen
                (< 0 c2) ;gen
                (rationalp b))
           (equal (< c1 (* c2 b))
                  (< (/ c1 c2) b)))
  :hints (("Goal" :use ((:instance mult-both-sides-of-<-by-positive
                                   (a c1)
                                   (b (* c2 b))
                                   (c (/ c2)))))))

(defthm collect-constants-in-product-<-1-of-2-with-1-of-1
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (rationalp c1)
                (rationalp c2)
                (< 0 c1) ;gen
                (< 0 c2) ;gen
                (rationalp b))
           (equal (< (* c2 b) c1)
                  (< b (/ c1 c2))))
  :hints (("Goal" :use ((:instance mult-both-sides-of-<-by-positive
                                   (b c1)
                                   (a (* c2 b))
                                   (c (/ c2)))))))


|#



;generalize to acl2-numberp whenever possible
;make more like these!

;BOZO generalize this hack
;drop?
;is this like rearrange-negative coeffs?
(defthm rearr-neg-eric
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp d))
           (equal (EQUAL (+ a (* -1 b) c)
                         d)
                  (equal (+ a c) (+ b d)))))

;add "equal" to the name?
;more like this?
;BOZO bad name...
(defthm collect-constants-with-division
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (rationalp c2)
                (acl2-numberp c1)
                (not (equal c2 0))
                (rationalp x))
           (equal (equal c1 (* c2 x))
                  (equal (/ c1 c2) x))))


;; ==================================================================================================
;;
;;;comparing a product to 0

;; may cause case splits (which, for my purposes, is acceptable)

;; ==================================================================================================



#|
;BOZO I have more rules about this in product.lisp !!!

;case split on the sign of A
(defthm prod->-0-cancel-pos
  (implies (and (< 0 a)
                (rationalp x)
                (rationalp a)
                )
           (equal (< 0 (* a x))
                  (< 0 x))))

(defthm prod-<-0-cancel-pos
  (implies (and (< 0 a)
                (rationalp x)
                (rationalp a)
                )
           (equal (< (* a x) 0)
                  (< x 0))))


(defthm prod-<-0-cancel-neg
  (implies (and (< a 0)
                (rationalp x)
                (rationalp a)
                )
           (equal (< (* a x) 0)
                  (< 0 x))))

(defthm prod->-0-cancel-neg
  (implies (and (< a 0)
                (rationalp x)
                (rationalp a)
                )
           (equal (< 0 (* a x))
                  (< x 0))))


;reorder to make the most likely case of the if first?
(defthm prod->-0-cancel
  (implies (and (rationalp x)
                (rationalp a))
           (equal (< 0 (* a x))
                  (if (< 0 a)
                      (< 0 x)
                    (if (equal 0 a)
                        nil
                      (< x 0))))))


(defthm prod-<-0-cancel
  (implies (and (rationalp x)
                (rationalp a))
           (equal (< (* a x) 0)
                  (if (equal a 0)
                      nil
                    (if (< a 0)
                        (< 0 x)
                      (< x 0))))))


(in-theory (disable prod-<-0-cancel-neg
                    prod-<-0-cancel-pos
                    prod->-0-cancel-neg
                    prod->-0-cancel-pos))


|#


(defthmd cancel-in-prods-<-case-x->-0
  (implies (and (rationalp x)
                (< 0 x)
                (rationalp a)
                (rationalp b))
           (equal  (< (* x a) (* x b))
                   (< a b)))
  )

(defthmd cancel-in-prods-<-case-x-<-0
  (implies (and (rationalp x)
                (> 0 x)
                (rationalp a)
                (rationalp b))
           (equal  (< (* x a) (* x b))
                   (> a b)))
  )

;changed the var names 'cause "x" was too heavy
;disabled, since we have a bind-free rule to cancel
(defthmd cancel-in-prods-<
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c))
           (equal (< (* a b) (* a c))
                  (if (equal 0 a)
                      nil
                    (if (> a 0)
                        (< b c)
                      (> b c)))))
  :hints (("Goal" :in-theory (enable  cancel-in-prods-<-case-x-<-0
                                      cancel-in-prods-<-case-x->-0)))
  )



;it shouldn't be too hard to write a bind-free function for cancelling common factors; that rule could replace
;many of the cancelling rules below


;use negative-syntaxp? (or a version of it that operates on single addends only (i.e., has no '+ case)
;do we need this?
(defthmd move-a-negative-coeff
  (equal (< (+ a (* -1 b)) c)
         (< a (+ b c))))

;can simplify the *-1 term to have only one var
;do we need this?
(defthm rearr-negative-coeffs-<-sums-blah
  (equal (< (+ A e (* -1 C)) B)
         (< (+ A e) (+ (* C) B)))
  :hints (("Goal" :use (:instance
                        move-a-negative-coeff (a (+ a e)) (b (* c)) (c b)))))

(defthm collect-constant-mults-<-1-of-2-with-1-of-2-term-len-2
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (rationalp c1)
                (rationalp c2)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp d))
           (equal (< (+ (* c1 c d) a) (+ (* c2 c d) b))
                  (< (+ (* (- c1 c2) c d) a) b))))


(include-book "inverted-factor")


;events in :rule-classes nil which can be :used in hacks

(defthm <-transitive
  (implies (and (< a b)
                (< b c)
                )
           (< a c)
           )
  :rule-classes nil
  )

(defthm <=-transitive
  (implies (and (<= a b)
                (<= b c)
                )
           (<= a c)
           )
  :rule-classes nil
  )

;a<b and b<=c together imply a<c
(defthm <-and-<=-transitivity
  (implies (and (< a b)
                (<= b c)
                )
           (< a c)
           )
  :rule-classes nil
  )

;a<=b and b<c together imply a<c
(defthm <=-and-<-transitivity
  (implies (and (< a b)
                (<= b c)
                )
           (< a c)
           )
  :rule-classes nil
  )


;used only as a hack:


(defthm equal-transitive
  (implies (and (equal a b)
                (equal b c))
           (equal a c))
  :rule-classes nil)

;there's a conflict in my arithmetic normal forms:
; do we prefer (< (* 2 x) 1) or (< x 1/2) ?


(defthm collect-again
  (implies (and (syntaxp (quotep k))
                (rationalp x)
                (rationalp y))
           (equal (< (+ x y) (* k x))
                  (< y (* (- k 1) x)))))



;natp is defined here to try to make sure its always enabled

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(in-theory (enable natp))

;an odd rule
(defthm two-natps-add-to-1
  (implies (and (natp n)
                (natp x))
           (equal (equal 1 (+ x n))
                  (or (and (equal x 1) (equal n 0))
                      (and (equal x 0) (equal n 1))))))

;backchain-limit?
;why needed?
(defthm nonneg-+
  (implies (and (<= 0 x)
                (<= 0 y))
           (not (< (+ x y) 0))))

;improve this? make the conclusion more type-like?
(defthm nonneg-+-type
  (implies (and (<= 0 x)
                (<= 0 y))
           (not (< (+ x y) 0)))
  :rule-classes (:type-prescription))

(defthm move-negative-constant-1
  (implies (and (syntaxp (and (quotep k) (< (cadr k) 0)))
                (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal x (+ k y))
                  (equal (+ x (- k)) y))))
;move?
(defthm rationalp-sum
  (implies (rationalp k)
           (and (equal (rationalp (+ k x))
                       (not (complex-rationalp x)))
                (equal (rationalp (+ x k))
                       (not (complex-rationalp x))))))

;move?
;make rationalp-sum like this?
(defthm rationalp-prod
  (implies (and (rationalp k)
                (case-split (not (equal k 0)))
                )
           (and (equal (rationalp (* k x))
                       (not (complex-rationalp x)))
                (equal (rationalp (* x k))
                       (not (complex-rationalp x))))))
;move?
(defthm complex-rationalp-prod
  (implies (and (rationalp k)
                (case-split (not (equal k 0)))
                )
           (and (equal (complex-rationalp (* k x))
                       (complex-rationalp x))
                (equal (complex-rationalp (* x k))
                       (complex-rationalp x)))))



(defthm collect-1
  (implies (and (syntaxp (and (quotep k) (quotep j)))
                (rationalp k)
                (rationalp j)
                (rationalp x)
                (rationalp y)
                )
           (equal (< (+ y (* k x)) (* j x))
                  (< (+ (* (- k j) x) y) 0))))

(defthm collect-2
  (implies (and (syntaxp (and (quotep k) (quotep j)))
                (rationalp k)
                (rationalp j)
                (rationalp x)
                (rationalp y)
                )
           (equal (< (+ (* k x) y) (* j x))
                  (< (+ (* (- k j) x) y) 0))))

(defthm collect-another
  (implies (and (syntaxp (and (quotep k) (quotep j)))
                (rationalp k)
                (rationalp j)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (+ (* k x) y) (+ (* j x) z))
                  (< (+ (* (- k j) x) y) z))))


;simplify this
(defthm collect-in-<-of-sums-2
  (implies (syntaxp (and (quotep k) (quotep j)))
           (equal (< (+ a (* k x) d) (+ b e (* j       x) f))
                  (< (+ a         d) (+ b e (* (- j k) x) f)))))

(defthm collect-in-<-of-sums-1
  (implies (syntaxp (and (quotep k) (quotep j)))
           (equal (< (+ a d (* k x) y) (+ b e f z (* j       x) g))
                  (< (+ a d         y) (+ b e f z (* (- j k) x) g)))))


(defthm cancel-in-sum-equal-zero-1
  (implies (and (rationalp y)
                (case-split (not (equal 0 y)))
                (rationalp x1)
                (rationalp x2)
                (rationalp x3)
                (rationalp x4)
                (rationalp x5)
                (rationalp x6))
           (equal (EQUAL 0 (+ (* Y x1)
                              (* x2 Y x3)
                              (* Y x4)
                              (* x5 Y x6)))
                  (equal 0 (+ x1 (* x2 x3) x4 (* x5 x6)))))
  :hints (("Goal" :in-theory (disable product-equal-zero)
           :use (:instance product-equal-zero (x y) (y (+ x1 (* x2 x3) x4 (* x5 x6))))))

  )

;expensive?
(defthm integerp-implies-not-complex-rationalp
  (implies (integerp x)
           (not (complex-rationalp x))))

;don't need this if we have frac-coeff rules?
;move to unary-/ ?
(defthm <-of-two-inverses
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y)
                (< 0 x)
                )
           (equal (< (/ x) (/ y))
                  (< y x))))


#|
;move up?
(defthm pos*
  (implies (and (rationalp x)
                (rationalp y)
                (> x 0)
                (> y 0))
           (> (* x y) 0))
  :rule-classes ())

;bad name
;find a way to make this a rewrite rule wihtout looping?
(defthm tighten-integer-bound
  (implies (and (< x (expt 2 i))
                (integerp x)
                (case-split (natp i))
                )
           (<= x (+ -1 (expt 2 i))))
  :rule-classes :linear
  )

|#
