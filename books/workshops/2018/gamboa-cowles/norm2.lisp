(in-package "ACL2")
  
; cert_param: (uses-acl2r)


(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nonstd/nsa/nsa" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; We start by defining the traditional norm and then proving some
;; important properties about it.

(defun norm2 (x)
  (acl2-sqrt (+ (* (realpart x) (realpart x))
                (* (imagpart x) (imagpart x)))))

(in-theory (disable (:executable-counterpart norm2)))

;; Here is the first property, norm(x) is real and norm(x)>=0.

(defthm norm2-non-negative-real
  (and (realp (norm2 x))
       (<= 0 (norm2 x)))
  :rule-classes (:rewrite :type-prescription))

;; To prove that norm(x)=0 only when x=0, we have to establish this
;; simple lemma first, which lets us decide when a term of the form
;; a+bi is equal to zero -- namely a=0 and b=0:

(local
 (defthm equal-complex-0
   (iff (equal (complex r s) 0)
        (and (equal (realfix r) 0)
             (equal (realfix s) 0)))))

;; So now, we establish the second key property of norm-ness, namely
;; that norm(x)=0 if and only if x=0.

(defthm norm2-zero-for-zero-only
  (and (equal (norm2 0) 0)
       (iff (equal (norm2 x) 0)
            (equal (fix x) 0))))

(defthmd norm2-abs
  (implies (real/rationalp x)
           (equal (norm2 x)
                  (abs x))))

;; The following sequence of theorems indicate how poor ACL2 is in
;; reasoning about the complex numbers.  This first one simply says
;; how to add complex numbers.

(local
 (defthm +-complex
   (implies (and (realp i) (realp j) (realp r) (realp s))
            (equal (+ (complex i j) (complex r s))
                   (complex (+ i r) (+ j s))))
   :hints (("Goal"
            :use ((:instance complex-definition (x i) (y j))
                  (:instance complex-definition (x r) (y s))
                  (:instance complex-definition (x (+ i r)) (y (+ j s))))))))

;; Next, we'll look at multiplying complex numbers.  Here's the first
;; step in multiplying (a+bi) * (r+si)....

(local
 (defthm *-complex-lemma-1
   (implies (and (realp a) (realp b) (realp r) (realp s))
            (equal (* (complex a b) (complex r s))
                   (* (+ a (* #C(0 1) b)) (+ R (* #C(0 1) S)))))
   :hints (("Goal"
            :use ((:instance complex-definition (x a) (y b))
                  (:instance complex-definition (x r) (y s)))))))

;; ...the next step is to factor everything out, remembering that
;; i^2=-1....

(local
 (defthm *-complex-lemma-2
   (implies (and (realp a) (realp b) (realp r) (realp s))
            (equal (complex (- (* a r) (* b s))
                            (+ (* a s) (* b r)))
                   (+ (+ (* a R) (- (* b S)))
                      (* #C(0 1) (+ (* a S) (* b R))))))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x (- (* a r) (* b s)))
                             (y (+ (* a s) (* b r)))))))))

;; And so now we can get a formula for the product of two complex
;; numbers.

(local
 (defthm *-complex
   (implies (and (realp i) (realp j) (realp r) (realp s))
            (equal (* (complex i j) (complex r s))
                   (complex (- (* i r) (* j s))
                            (+ (* i s) (* j r)))))))

(local
 (in-theory (disable *-complex-lemma-1 *-complex-lemma-2)))

;; Here's a simple theorem.  if a+bi is real, then b is zero and a is
;; equal to a+bi.

(local
 (defthm realpart-imagpart-reals
   (implies (realp x)
            (and (equal (realpart x) x)
                 (equal (imagpart x) 0)))))

;; This simplification let's us get the realpart/imagpart of the sum
;; of two complex numbers.

(local
 (defthm realpart-imagpart-+
   (and
    (equal (realpart (+ x y))
           (+ (realpart x) (realpart y)))
    (equal (imagpart (+ x y))
           (+ (imagpart x) (imagpart y))))))

;; This is a similar rule for the product of two complex numbers.

(local
 (defthm realpart-imagpart-*
   (and
    (equal (realpart (* x y))
           (- (* (realpart x) (realpart y))
              (* (imagpart x) (imagpart y))))
    (equal (imagpart (* x y))
           (+ (* (realpart x) (imagpart y))
              (* (imagpart x) (realpart y)))))))

;; Now, we can move more quickly.  We prove that norm is an
;; idempotent function; i.e., norm(norm(x)) = norm(x).

(defthm norm2-norm2
  (equal (norm2 (norm2 x))
         (norm2 x)))

;; Moreover, norm is monotonic over the reals.

(defthm norm2-preserves-<=-for-reals
  (implies (and (realp x)
                (realp y)
                (<= 0 x)
                (<= x y))
           (<= (norm2 x) (norm2 y))))

;; And finally, we can establish that norm(x*y) = norm(x)*norm(y).

(defthm norm2-product
  (equal (norm2 (* a b))
         (* (norm2 a) (norm2 b)))
  :instructions
  ((:DV 1)
   (:= (ACL2-SQRT (+ (* (REALPART (* A B))
                        (REALPART (* A B)))
                     (* (IMAGPART (* A B))
                        (IMAGPART (* A B))))))
   :NX :UP (:REWRITE SQRT-=-Y)
   :S))

;; Next on the agenda are terms of the form norm(ax+bx) where a and b
;; are reals.

(defthm norm2-distributivity
  (implies (and (realp a)
                (<= 0 a)
                (realp b)
                (<= 0 b))
           (equal (norm2 (+ (* a x) (* b x)))
                  (+ (* (norm2 a) (norm2 x))
                     (* (norm2 b) (norm2 x))))))

;; The term abs(norm(x)) can be simplified to norm(x) since norm is a
;; non-negative real.

(local
 (defthm abs-norm2
   (equal (abs (norm2 x))
          (norm2 x))
   :hints (("Goal" :in-theory (enable abs)))))

;; Another silly theorem showing how to get the realpart/imagpart of
;; the negative of a number.

(local
 (defthm realpart-imagpart-uminus
   (and (equal (realpart (- x)) (- (realpart x)))
        (equal (imagpart (- x)) (- (imagpart x))))
   :hints (("Goal" :use ((:instance realpart-imagpart-* (x -1) (y x)))
            :in-theory (disable realpart-imagpart-*)))))

;; That shows that norm(-x) is the same as norm(x).....

(defthm norm2-uminus
  (equal (norm2 (- x)) (norm2 x)))

;; And now, we get an important lemma.  The norm(a+bi) cannot be smaller
;; than either a or b.  What this will mean later is that if a+bi
;; isn't small, then norm(a+bi) can't be small, since one of a or b
;; is not small, and norm(a+bi) is at least that large.

(local
 (defthm realpart-imagpart-<=-norm
   (and (<= (realpart x) (norm2 x))
        (<= (imagpart x) (norm2 x)))
   :hints (("Subgoal 2'"
            :use ((:instance sqrt-<-y
                             (x (+ (* (imagpart x) (imagpart x))
                                   (* (realpart x) (realpart x))))
                             (y (realpart x))))
            :in-theory (disable sqrt-<-y))
           ("Subgoal 1'"
            :use ((:instance sqrt-<-y
                             (x (+ (* (imagpart x) (imagpart x))
                                   (* (realpart x) (realpart x))))
                             (y (imagpart x))))
            :in-theory (disable sqrt-<-y)))))

;; Actually, we can prove a stronger result.  Not only is
;; a<=norm(a+bi), |a|<=norm(a+bi)....

(defthm abs-realpart-imagpart-<=-norm2
  (and (<= (abs (realpart x)) (norm2 x))
       (<= (abs (imagpart x)) (norm2 x)))
  :hints (("Goal" :in-theory (enable-disable (abs) (norm2)))
          ("Subgoal 2.2"
           :use ((:instance realpart-imagpart-<=-norm
                            (x (- x))))
           :in-theory (disable norm2 realpart-imagpart-<=-norm))
          ("Subgoal 1.2"
           :use ((:instance realpart-imagpart-<=-norm
                            (x (- x))))
           :in-theory (disable norm2 realpart-imagpart-<=-norm))))

;; So now, like we argued earlier we see that if norm(a+bi) is small,
;; both a and b must be small.

(local
 (defthm small-norm2-lemma-1
   (implies (i-small (norm2 x))
            (and (i-small (realpart x))
                 (i-small (imagpart x))))
   :hints (("Goal"
            :use ((:instance small-if-<-small
                             (x (norm2 x))
                             (y (realpart x)))
                  (:instance small-if-<-small
                             (x (norm2 x))
                             (y (imagpart x))))
            :in-theory (disable abs small-if-<-small norm2)))))

;; And here's the other half of that important theorem.  We know
;; norm(a+bi) must be larger than |a| and |b|, but it can't be too
;; much bigger.  In particular,  norm(a+bi) <= |a| + |b|.  What this
;; means later is that if norm(a+bi) is large, so must be either a or
;; b.

(defthm norm2-<=-abs-realpart-+-abs-imagpart
  (<= (norm2 x)
      (+ (abs (realpart x)) (abs (imagpart x)))))

;; For now, we content ourselves with completing the proofs for
;; i-small.  If x and y are small, so are abs(x) and abs(y), and
;; therefore abs(x)+abs(y) is small.

(local
 (defthm small-abs-x-+-abs-y
   (implies (and (i-small x)
                 (i-small y))
            (i-small (+ (abs x) (abs y))))))

;; Moreover, abs(x)+abs(y) is real, if both x and y are real.

(local
 (defthm realp-abs-x-+-abs-y
   (implies (and (realp x)
                 (realp y))
            (realp (+ (abs x) (abs y))))))

;; And since we find the term abs(abs(x)+abs(y)) in the proofs to
;; follow, we show here that that must equal abs(x)+abs(y).

(local
 (defthm abs-abs-x-+-abs-y
   (equal (abs (+ (abs x) (abs y)))
          (+ (abs x) (abs y)))))

;; When x isn't a number, its norm is the same as the norm of 0,
;; which is 0.

(local
 (defthm norm2-non-numberp
   (implies (not (acl2-numberp x))
            (equal (norm2 x) 0))))

;; So now we get the converse of our i-small lemma.  We already know
;; that when norm(a+bi) is small, both a and b are small.  Now, we
;; show that if both a and b are small, norm(a+bi) is small.

(local
 (defthm small-norm2-lemma-2
   (implies (and (i-small (realpart x))
                 (i-small (imagpart x)))
            (i-small (norm2 x)))
   :hints (("Goal"
            :use (:instance small-if-<-small
                            (x (+ (abs (realpart x)) (abs (imagpart x))))
                            (y (norm2 x)))
            :in-theory (disable abs small-if-<-small norm2)))))

;; And that allows us to prove that norm(x) is small precisely when x
;; is small.

(defthm small-norm2
  (implies (acl2-numberp x)
           (equal (i-small (norm2 x))
                  (i-small x)))
  :hints (("Goal"
           :use ((:instance complex-small))
           :in-theory (disable norm2 complex-small))
          ("Goal'"
           :cases ((i-small x)))
          ("Subgoal 2''"
           :in-theory (enable norm2))
          ("Subgoal 1'''"
           :in-theory (enable norm2))))

;; Similarly, if norm(a+bi) is limited, so must be both a and b,
;; since they're both smaller than norm(a+bi).

(local
 (defthm limited-norm2-lemma-1
   (implies (i-limited (norm2 x))
            (and (i-limited (realpart x))
                 (i-limited (imagpart x))))
   :hints (("Goal"
            :use ((:instance large-if->-large
                             (x (realpart x))
                             (y (norm2 x)))
                  (:instance large-if->-large
                             (x (imagpart x))
                             (y (norm2 x))))
            :in-theory (disable large-if->-large norm2)))))

;; And moreover, if x and y are limited, so is |x|+|y|....

(local
 (defthm limited-abs-x-+-abs-y
   (implies (and (i-limited x)
                 (i-limited y))
            (i-limited (+ (abs x) (abs y))))))

;; ...and so if a and b are limited, so is norm(a+bi), since that is
;; smaller than |a|+|b|.

(local
 (defthm limited-norm2-lemma-2
   (implies (and (i-limited (realpart x))
                 (i-limited (imagpart x)))
            (i-limited (norm2 x)))
   :hints (("Goal"
            :use (:instance large-if->-large
                            (x (norm2 x))
                            (y (+ (abs (realpart x)) (abs (imagpart x)))))
            :in-theory (disable abs large-if->-large norm2)))))


;; We know that a+bi is limited precisely when a is limited and b is
;; limited.

(local
 (defthm complex-limited-strong
   (implies (complexp x)
            (equal (i-large x)
                   (or (i-large (realpart x))
                       (i-large (imagpart x)))))
   :hints (("Goal"
            :use ((:instance complex-large-1)
                  (:instance complex-large-2))
            :in-theory (disable complex-large-1)))))

;; Therefore, norm(a+bi) is limited precisely when a+bi is limited.

(defthm limited-norm2
  (implies (acl2-numberp x)
           (equal (i-large (norm2 x))
                  (i-large x)))
  :hints (("Goal"
           :use ((:instance complex-limited-strong))
           :in-theory (disable norm2 complex-limited-strong
                               complex-large-1))
          ("Goal'"
           :cases ((i-limited x)))
          ("Subgoal 2''"
           :in-theory (enable norm2))))

;; This simple lemma lets us conclude that a^2+b^2 is limited when
;; a+bi is limited.

(local
 (defthm limited-r*r+s*s
   (implies (and (realp r)
                 (realp s)
                 (i-limited (complex r s)))
            (i-limited (+ (* r r) (* s s))))
   :hints (("Goal" :cases ((= s 0))))))

;; Here's a great theorem!  Standard-part and norm commute!  This is
;; actually true of all continuous functions.  I.e.,
;; fn(standard-part(x)) is just standard-part(fn(x)).

(defthm standard-part-norm2
  (implies (i-limited x)
           (equal (standard-part (norm2 x))
                  (norm2 (standard-part x))))
  :hints (("Goal" :in-theory (disable acl2-sqrt))
; Matt K. v7-1 mod for ACL2 mod on 2/13/2015: "Goal'5'" changed to "Goal'4'".
          ("Goal'4'" :cases ((= s 0)))))

;; Now, we want to talk about the inverses of complex numbers, so we
;; start by defining conjugates.

(local
 (defun conj (x)
   (complex (realpart x) (- (imagpart x)))))

;; We can then give a simpler definition of norm(x) as sqrt(x*x')
;; where x' is the conjugate of x.

(local
 (defthm norm2-product-conj
   (equal (norm2 x)
          (acl2-sqrt (* x (conj x))))))

;; Next, we build up the basic theory of conjugates...the conjugate
;; of a sum is the sum of the conjugates...

(local
 (defthm conj-+
   (equal (conj (+ x y))
          (+ (conj x) (conj y)))))

;; ...and the same holds for products.

(local
 (defthm conj-*
   (equal (conj (* x y))
          (* (conj x) (conj y)))))

;; Next, we show that realpart(x+x') is just 2*realpart(x).

(local
 (defthm x-+-conj-x
   (equal (+ x (conj x))
          (* 2 (realpart x)))))

;; An easy lemma is that norm(x') = norm(x)

(local
 (defthm norm2-conj
   (equal (norm2 (conj x))
          (norm2 x))))

;; Another one is that x'' = x

(local
 (defthm conj-conj
   (equal (conj (conj x)) (fix x))))

;; So now, we can start considering x*x'.  First, we have that it is
;; always real and never negative.

(local
 (defthm x-*-conj-x-type-prescription
   (and (realp (* x (conj x)))
        (<= 0 (* x (conj x))))
   :rule-classes (:rewrite :type-prescription)))

;; Moreover, if x isn't anumber, then x' is just 0.

(local
 (defthm conj-completion
   (implies (not (acl2-numberp x))
            (equal (conj x) 0))))

;; Here's another characterization of the conjugate:

(local
 (defthm realpart-imagpart-conj
   (and (equal (realpart (conj x)) (realpart x))
        (equal (imagpart (conj x)) (- (imagpart x))))))

(local (in-theory (disable conj)))

;; So now, we can prove that norm(x)*norm(x) = x*x' -- since earlier
;; we saw that norm(x)=sqrt(x*x')....

(local
 (defthm norm2-*-norm2
   (equal (* (norm2 x) (norm2 x))
          (* x (conj x)))))

;; Now, from norm(x+y)*norm(x+y) = (x+y)*(x+y)', we get that is equal
;; to xx' + yy' + xy' + x'y = xx' + yy' + xy' + (xy')' =
;; norm(x)*norm(x) + norm(y)*norm(y) + 2*realpart(xy')

(local
 (defthm norm2-triangle-inequality-lemma-1
   (equal (* (norm2 (+ x y)) (norm2 (+ x y)))
          (+ (* (norm2 x) (norm2 x))
             (* (norm2 y) (norm2 y))
             (* 2 (realpart (* x (conj y))))))
   :hints (("Goal"
            :use (:instance x-+-conj-x (x (* x (conj y))))
            :in-theory (disable x-+-conj-x)))))

;; That means we need to find a bound for the 2*realpart(xy') term.
;; We know this is smaller than 2*norm(x*y')

(local
 (defthm norm2-triangle-inequality-lemma-key
   (implies (and (realp i) (realp j)
                 (realp r) (realp s))
            (<= (+ (* 2 i r) (* 2 j s))
                (* 2 (norm2 (* (complex i j) (conj (complex r s)))))))
   :hints (("Goal"
            :use ((:instance realpart-imagpart-<=-norm
                             (x (* (complex i j) (conj (complex r s))))))
            :in-theory (disable realpart-imagpart-<=-norm)))
   :rule-classes nil))

;; We're ready to prove the third law required for norms, namely
;; norm(a+b) <= norm(a) + norm(b).  First, we square each side to get
;; rid of the sqrt's

(local
 (defthm norm2-triangle-inequality-lemma
   (<= (* (norm2 (+ x y)) (norm2 (+ x y)))
       (* (+ (norm2 x) (norm2 y))
          (+ (norm2 x) (norm2 y))))
   :hints (("Goal" :in-theory (disable norm2
                                       norm2-*-norm2
                                       norm2-product-conj))
           ("Subgoal 2"
            :in-theory (enable norm2-product-conj))
           ("Subgoal 1.1'"
            :use ((:instance norm2-triangle-inequality-lemma-key))))))

; Added by Matt K., 1/14/2014:
; The following two lemmas are the versions of lemmas that existed though the
; time of the ACL2 6.4 release.  The new versions, whose conclusions are calls
; of equal instead of iff, cause the proof of lemma-1 below to fail; so we
; :use these old ones instead.

(local
 (defthm <-*-right-cancel-old
   (implies (and (fc (real/rationalp x))
                 (fc (real/rationalp y))
                 (fc (real/rationalp z)))
            (iff (< (* x z) (* y z))
                 (cond ((< 0 z)     (< x y))
                       ((equal z 0) nil)
                       (t           (< y x)))))
   :rule-classes nil))

(local
 (defthm <-*-left-cancel-old
   (implies (and (fc (real/rationalp x))
                 (fc (real/rationalp y))
                 (fc (real/rationalp z)))
            (iff (< (* z x) (* z y))
                 (cond ((< 0 z)     (< x y))
                       ((equal z 0) nil)
                       (t           (< y x)))))
   :rule-classes nil))

;; This is a trivial lemma that we need below.... x<y => x^2 < y^2
;; for positive x, y.

(local
 (defthm obvious-lemma
   (implies (and (realp x)
                 (realp y)
                 (<= 0 x)
                 (<= 0 y)
                 (< x y))
            (< (* x x) (* y y)))
   :hints (("Goal"
            :use ((:instance <-*-left-cancel-old (x x) (y y) (z x))
                  (:instance <-*-right-cancel-old (x x) (y y) (z y)))
            :in-theory (disable <-*-left-cancel <-*-right-cancel)))))

;; And finally, we establish the triangle inequality:

(defthm norm2-triangle-inequality
  (<= (norm2 (+ x y))
      (+ (norm2 x) (norm2 y)))
  :hints (("Goal"
           :use ((:instance obvious-lemma
                            (x (+ (norm2 x) (norm2 y)))
                            (y (norm2 (+ x y)))))
           :in-theory (disable obvious-lemma
                               norm2-product-conj
                               norm2-*-norm2))))

(defthm norm2-triangle-inequality-2
  (<= (- (norm2 x) (norm2 y))
      (norm2 (- x y)))
  :hints (("Goal"
           :use ((:instance norm2-triangle-inequality
                            (x (- x y))
                            (y y)))
           :in-theory (disable norm2-triangle-inequality
                               norm2
                               norm2-product-conj))))

(defthm norm2-of-unity
  (equal (norm2 1) 1))

(defthm norm2-expt
  (implies (and (natp n)
                (acl2-numberp z))
           (equal (norm2 (expt z n))
                  (expt (norm2 z) n)))
  :hints (("Goal"
           :induct (expt z n)
           :in-theory (e/d (expt)
                           (norm2
                            norm2-product-conj)))
          ("Subgoal *1/3"
           :use ((:instance norm2-product
                            (a z)
                            (b (expt z (1- n)))))
           :in-theory (e/d (expt)
                           (norm2
                            norm2-product
                            norm2-product-conj)))
          )
  )

;; The last theorem is that the norms of two close numbers are close


(local (include-book "arithmetic-5/top" :dir :system))
(include-book "complex-lemmas")

(encapsulate
  nil
  
  (local
   (defthm lemma-1
     (implies (and (i-close x y)
                   (i-limited y))
              (i-close (+ (* (realpart x) (realpart x))
                          (* (imagpart x) (imagpart x)))
                       (+ (* (realpart y) (realpart y))
                          (* (imagpart y) (imagpart y)))))
     :hints (("Goal"
              :use ((:instance close-plus
                               (x1 (* (realpart x) (realpart x)))
                               (x2 (* (realpart y) (realpart y)))
                               (y1 (* (imagpart x) (imagpart x)))
                               (y2 (* (imagpart y) (imagpart y))))
                    (:instance close-times-2
                               (x1 (realpart x))
                               (x2 (realpart y))
                               (y1 (realpart x))
                               (y2 (realpart y)))
                    (:instance close-times-2
                               (x1 (imagpart x))
                               (x2 (imagpart y))
                               (y1 (imagpart x))
                               (y2 (imagpart y)))
                    (:instance close-times-2
                               (x1 x)
                               (x2 x)
                               (y1 y)
                               (y2 y))
                    (:instance complex-close (z1 x) (z2 y))
                    (:instance complex-limited-2
                               (x y))
                    (:instance complex-limited-2)
                    (:instance i-close-limited-2)
                    )
              :in-theory (disable i-close-limited i-close-limited-2
                                  i-close-large i-close-large-2
                                  complex-large-1
                                  complex-limited-strong
                                  normalize-factors-gather-exponents)
              ))))

  (local
   (defthm lemma-2
     (implies (and (real/rationalp x)
                   (<= 0 x)
                   (<= x 1))
              (implies (i-small (* x x))
                       (i-small x)))
     :hints (("Goal"
              :use ((:instance standard-part-of-times
                               (x x)
                               (y x))
                    (:instance large-if->-large
                               (x x)
                               (y 1))
                    )
              :in-theory (e/d (i-small) (standard-part-of-times
                                         large-if->-large
                                         normalize-factors-gather-exponents))))
     :rule-classes nil))

  
  (local
   (defthm lemma-3
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (real/rationalp z)
                   (<= x y)
                   (<= 0 z))
              (<= (* x z) (* y z)))
     :rule-classes nil))

  (local
   (defthm lemma-4
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 x)
                   (<= x y))
              (<= (* x x) (* y x)))
     :hints (("Goal"
              :use ((:instance lemma-3
                               (x x)
                               (y y)
                               (z x)))
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-5
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 x)
                   (<= x y))
              (<= (* x x) (* y y)))
     :hints (("Goal"
              :use ((:instance lemma-4)
                    (:instance lemma-3
                               (x x)
                               (y y)
                               (z y)))
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-6
     (implies (and (real/rationalp x)
                   (<= 1 x))
              (<= 1 (* x x)))
     :hints (("Goal"
              :use ((:instance lemma-5
                               (x 1)
                               (y x)))
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-7
     (implies (and (real/rationalp x)
                   (<= 1 x))
              (not (i-small (* x x))))
     :hints (("Goal"
              :use ((:instance small-if-<-small
                               (x (* x x))
                               (y 1))
                    (:instance lemma-6)
                    )
              :in-theory (disable small-if-<-small
                                  normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-8
     (implies (and (real/rationalp x)
                   (<= 0 x))
              (equal (i-small (* x x))
                     (i-small x)))
     :hints (("Goal"
              :use ((:instance lemma-2)
                    (:instance lemma-7)
                    )
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))


  (local
   (defthm lemma-9
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 x)
                   (<= x y)
                   (i-small (* x y)))
              (i-small x))
     :hints (("Goal"
              :use ((:instance lemma-8)
                    (:instance small-if-<-small
                               (x (* x y))
                               (y (* x x)))
                    )
              :in-theory (disable small-if-<-small normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-10
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 y)
                   (<= y x)
                   (i-small (- (* x x) (* y y))))
              (i-small (- x y)))
     :hints (("Goal"
              :use ((:instance lemma-9
                               (x (- x y))
                               (y (+ x y)))
                    )
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-11
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 y)
                   (<= y x)
                   (i-small (- x y)))
              (i-small (- (acl2-sqrt x) (acl2-sqrt y))))
     :hints (("Goal"
              :use ((:instance lemma-10
                               (x (acl2-sqrt x))
                               (y (acl2-sqrt y)))
                    )
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-12
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 x)
                   (<= x y)
                   (i-small (- x y)))
              (i-small (- (acl2-sqrt x) (acl2-sqrt y))))
     :hints (("Goal"
              :use ((:instance lemma-11
                               (x y)
                               (y x))
                    (:instance i-small-uminus
                               (x (- (acl2-sqrt x) (acl2-sqrt y))))
                    )
              :in-theory (disable i-small-uminus normalize-factors-gather-exponents)))
     :rule-classes nil))


  (local
   (defthm lemma-13
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 x)
                   (<= 0 y)
                   (i-small (- x y)))
              (i-small (- (acl2-sqrt x) (acl2-sqrt y))))
     :hints (("Goal"
              :use ((:instance lemma-11)
                    (:instance lemma-12)
                    )
              :in-theory (disable i-small-uminus normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-14
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (<= 0 x)
                   (<= 0 y)
                   (i-close x y))
              (i-close (acl2-sqrt x) (acl2-sqrt y)))
     :hints (("Goal"
              :use ((:instance lemma-13)
                    )
              :in-theory (enable i-close)))
     :rule-classes nil))

  (local
   (defthm lemma-15
     (implies (real/rationalp x)
              (<= 0 (* x x)))
     :hints (("Goal"
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))

  (local
   (defthm lemma-16
     (implies (and (real/rationalp x)
                   (real/rationalp y))
              (<= 0 (+ (* x x) (* y y))))
     :hints (("Goal"
              :use ((:instance lemma-15 (x x))
                    (:instance lemma-15 (x y))
                    (:instance (:theorem (implies (and (<= 0 x) (<= 0 y)) (<= 0 (+ x y))))
                               (x (* x x))
                               (y (* y y))))
              :in-theory (disable normalize-factors-gather-exponents)))
     :rule-classes nil))

   (defthm close-norm
     (implies (and (i-close x y)
                   (i-limited y))
              (i-close (norm2 x) (norm2 y)))
     :hints (("Goal"
              :use ((:instance lemma-1)
                    (:instance lemma-14
                               (x (+ (* (realpart x) (realpart x))
                                     (* (imagpart x) (imagpart x))))
                               (y (+ (* (realpart y) (realpart y))
                                     (* (imagpart y) (imagpart y)))))
                    (:instance lemma-16
                               (x (realpart x))
                               (y (imagpart x)))
                    (:instance lemma-16
                               (x (realpart y))
                               (y (imagpart y)))
                    )
              :in-theory (disable norm2-product-conj
                                  normalize-factors-gather-exponents)))
     )
   
   )

(in-theory (disable norm2))
