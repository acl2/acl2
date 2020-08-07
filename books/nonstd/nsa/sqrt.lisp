;;; In sqrt-iter.lisp, we defined a function, sqrt-iter, which returns an
;;; approximation of the square root of a number.  Now, using ACL2(r), we will
;;; use sqrt-iter to define the real square root function.  The approach is
;;; simple.  First, we establish that sqrt-iter returns a limited number for
;;; limited values.  Thus, if we take the standard-part of sqrt-iter, that will
;;; be a standard result for a standard argument.  Hence, we can use defun-std
;;; to define the square root function, provided we choose a small enough
;;; epsilon -- any infinitesimal will do, but (/ (i-large-integer)) is the
;;; obvious candidate.

(in-package "ACL2")

(include-book "nsa")
(include-book "sqrt-iter")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; First, we need to create a type-prescription rule for sqrt-iter, so
;; that ACL2 can reason about formulas involving sqrt-iter terms.
;; Notice, this also establishes a lower bound on sqrt-iter (namely 0).

(defthm sqrt-iter-type-prescription
  (and (realp (sqrt-iter x epsilon))
       (<= 0 (sqrt-iter x epsilon)))
  :rule-classes (:type-prescription :rewrite))

;; Next, we establish that sqrt-iter is bounded above.

(defthm sqrt-iter-upper-bound-1
  (implies (and (realp x)
                (<= 1 x))
           (<= (sqrt-iter x epsilon) x)))

(defthm sqrt-iter-upper-bound-2
  (implies (and (realp x)
                (< x 1))
           (<= (sqrt-iter x epsilon) 1)))

;; Since sqrt-iter is bounded above by max{1,x}, it is obviously
;; limited when x is limited.

(defthm limited-sqrt-iter
  (implies (and (i-limited x)
                (realp x)
                (<= 0 x))
           (i-limited (sqrt-iter x epsilon)))
  :hints (("Goal"
           :cases ((< x 1))
           :in-theory (disable sqrt-iter))
          ("Subgoal 2"
           :use ((:instance large-if->-large
                            (x (sqrt-iter x epsilon))
                            (y x)))
           :in-theory (disable sqrt-iter
                               large-if->-large))
          ("Subgoal 1"
           :use ((:instance large-if->-large
                            (x (sqrt-iter x epsilon))
                            (y 1)))
           :in-theory (disable sqrt-iter
                               large-if->-large))))

;; A stronger version of the theorem avoids the check on x being
;; real.  The reason this result is still true is that for non-real x,
;; sqrt-iter simply returns 0.

(defthm limited-sqrt-iter-strong
  (implies (i-limited x)
           (i-limited (sqrt-iter x epsilon)))
  :hints (("Goal"
           :cases ((and (realp x) (<= 0 x)))
           :in-theory (disable sqrt-iter))
          ("Subgoal 2"
           :expand (sqrt-iter x epsilon))))

(in-theory (disable sqrt-iter))

;; This means we can now define the square root function in ACL2.  Of
;; course, we are not using any properties of epsilon here, so it is
;; possible to choose a "bad" value.  For example, if 1 is used
;; instead of (/ (i-large-integer)), the resulting function would NOT
;; be the real square root function.  The theorems below will show
;; that (/ (i-large-integer)) is a "good" value, so that acl2-sqrt has
;; the right properties.

(defun-std acl2-sqrt (x)
  (standard-part (sqrt-iter (fix x) (/ (i-large-integer)))))
(in-theory (disable (:executable-counterpart acl2-sqrt)))

(in-theory (disable convergence-of-sqrt-iter))

;; The next theorem restates the convergence of sqrt-iter in terms of
;; infinitesimal scale.  In particular, it shows that the square of
;; sqrt-iter is close to x when epsilon is small -- that's why we
;; wouldn't have been able to choose "1" as epsilon in the definition
;; above!

(defthm convergence-of-sqrt-iter-strong
  (implies (and (realp x)
                (realp epsilon)
                (< 0 epsilon)
                (i-small epsilon)
                (<= 0 x))
           (i-close (* (sqrt-iter x epsilon)
                       (sqrt-iter x epsilon))
                    x))
  :hints (("Goal"
           :use ((:instance convergence-of-sqrt-iter))
           :in-theory (enable i-close))))

;; Now comes the fundamental theorem of the square root function!
;; This establishes that acl2-sqrt *is* the square root function as
;; promised.

(defthm-std sqrt-sqrt
  (implies (and (realp x)
                (<= 0 x))
           (equal (* (acl2-sqrt x) (acl2-sqrt x)) x))
  :hints (("Goal''"
           :use (:instance convergence-of-sqrt-iter-strong
                           (epsilon (/ (i-large-integer))))
           :in-theory (disable convergence-of-sqrt-iter-strong))
          ("Goal'4'"
           :in-theory (enable i-close i-small))))

;; ACL2 is really bad at algebra.  My dog knows more algebra -- and
;; it's not a smart breed.  The following simply states that if x<y,
;; then x^2 < y^2.

(local
 (encapsulate
   ()

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

   (local
    (defthm lemma-1
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

   (defthm x*x-<-y*y
     (implies (and (realp x)
                   (realp y)
                   (<= 0 x)
                   (<= 0 y))
              (equal (< (* x x) (* y y))
                     (< x y)))
     :hints (("Goal"
              :cases ((< x y) (= x y) (< y x)))))))

;; This theorem lets us reason about whether sqrt(x)<y for some y --
;; it rewrites those expressions into x < y^2 which should be easier
;; to prove.

(defthm sqrt-<-y
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y))
           (equal (< (acl2-sqrt x) y)
                  (< x (* y y))))
  :hints (("Goal"
           :use ((:instance x*x-<-y*y (x (acl2-sqrt x))))
           :in-theory (disable x*x-<-y*y))))

;; This is the same theorem, but going the other way....

(defthm y-<-sqrt
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y))
           (equal (< y (acl2-sqrt x))
                  (< (* y y) x)))
  :hints (("Goal"
           :use ((:instance x*x-<-y*y (x y) (y (acl2-sqrt x))))
           :in-theory (disable x*x-<-y*y))))

;; Now comes an important theorem.  If y^2 = x, then we can conclude
;; that y *is* the square root of x -- as long as y is a positive
;; real, anyway.

(defthm y*y=x->y=sqrt-x
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y)
                (equal (* y y) x))
           (equal (acl2-sqrt x) y))
  :hints (("Goal"
           :cases ((< (acl2-sqrt x) y)
                   (< y (acl2-sqrt x))))))

;; This simple theorem helps us decide when a number is equal to the
;; square root of x -- simply square both sides and go from
;; there....at least for positive numbers!

(defthm sqrt-=-y
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y))
           (equal (equal (acl2-sqrt x) y)
                  (equal x (* y y))))
  :hints (("Goal"
           :cases ((equal (acl2-sqrt x) y)))))

;; Ditto, but in the other direction -- no way to tell which way ACL2
;; decided to order these terms...

(defthm y-=-sqrt
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y))
           (equal (equal y (acl2-sqrt x))
                  (equal (* y y) x)))
  :hints (("Goal"
           :use ((:instance sqrt-=-y))
           :in-theory (disable sqrt-=-y))))

;; This theorem settles the question of sqrt(x) being larger than y by
;; squaring both sides.

(defthm sqrt->-y
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y))
           (equal (> (acl2-sqrt x) y)
                  (> x (* y y))))
  :hints (("Goal"
           :use ((:instance y-<-sqrt))
           :in-theory (disable y-<-sqrt))))

;; Ditto.

(defthm y->-sqrt
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y))
           (equal (< y (acl2-sqrt x))
                  (< (* y y) x)))
  :hints (("Goal"
           :use ((:instance sqrt-<-y))
           :in-theory (disable sqrt-<-y))))

;; Ah, useful theorems!  The square root of a product is the product
;; of the square roots (as long as everything is positive....)

(defthm sqrt-*
  (implies (and (realp x)
                (<= 0 x)
                (realp y)
                (<= 0 y))
           (equal (acl2-sqrt (* x y))
                  (* (acl2-sqrt x) (acl2-sqrt y))))
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x
                            (x (* x y))
                            (y (* (acl2-sqrt x) (acl2-sqrt y))))))))

;; And, the square root of an inverse is the inverse of the square root.

(defthm sqrt-/
  (implies (and (realp x)
                (<= 0 x))
           (equal (acl2-sqrt (/ x))
                  (/ (acl2-sqrt x))))
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x
                            (x (/ x))
                            (y (/ (acl2-sqrt x))))
                 (:instance distributivity-of-/-over-*
                            (x (acl2-sqrt x))
                            (y (acl2-sqrt x))))
           :in-theory (disable y*y=x->y=sqrt-x distributivity-of-/-over-*))))

;; It follows, therefore, that the square root of x^2 is |x|.

(defthm sqrt-*-x-x
  (implies (realp x)
           (equal (acl2-sqrt (* x x)) (abs x)))
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x (x (* x x)) (y (abs x)))))))

;; Some useful constants -- sqrt(0) = 0...

(defthm sqrt-0
  (equal (acl2-sqrt 0) 0)
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x (x 0) (y 0))))))

;; ... and sqrt(1) = 1...

(defthm sqrt-1
  (equal (acl2-sqrt 1) 1)
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x (x 1) (y 1))))))

;; ... and sqrt(4) = 2

(defthm sqrt-4
  (equal (acl2-sqrt 4) 2)
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x (x 4) (y 2))))))

;; Sqrt(x) is positive when x is positive -- note that it's zero when
;; x is zero....

(defthm sqrt->-0
  (implies (and (realp x)
                (<= 0 x))
           (equal (< 0 (acl2-sqrt x))
                  (< 0 x))))

;; If x <= 1, then so is its square root.

(defthm-std acl2-sqrt-x-<-1
  (implies (and (realp x)
                (<= 0 x)
                (< x 1))
           (<= (acl2-sqrt x) 1))
  :hints (("Goal''"
           :use ((:instance standard-part-<=
                            (x (SQRT-ITER X (/ (I-LARGE-INTEGER))))
                            (y 1))
                 (:instance sqrt-iter-upper-bound-2
                            (epsilon (/ (i-large-integer)))))
           :in-theory (disable standard-part-<= sqrt-iter-upper-bound-2))))

;; For x >= 1, the square root is no larger than x.

(defthm-std acl2-sqrt-x-<-x
  (implies (and (realp x)
                (<= 0 x)
                (<= 1 x))
           (<= (acl2-sqrt x) x))
  :hints (("Goal''"
           :use ((:instance standard-part-<=
                            (x (sqrt-iter x (/ (i-large-integer))))
                            (y x))
                 (:instance sqrt-iter-upper-bound-1
                            (epsilon (/ (i-large-integer)))))
           :in-theory (disable standard-part-<= sqrt-iter-upper-bound-1))))

;; The two theorems above demonstrate that sqrt(x) is limited as long
;; as x is limited, since sqrt(x) is always bounded by either 1 or x

(defthm limited-sqrt
  (implies (and (realp x)
                (<= 0 x)
                (i-limited x))
           (i-limited (acl2-sqrt x)))
  :hints (("Goal"
           :cases ((< x 1)))
          ("Subgoal 2"
           :use ((:instance large-if->-large
                            (x (acl2-sqrt x))
                            (y x)))
           :in-theory (disable large-if->-large))
          ("Subgoal 1"
           :use ((:instance large-if->-large
                            (x (acl2-sqrt x))
                            (y 1)))
           :in-theory (disable large-if->-large))))

;; An interesting theorem....the standard-part of a square root is the
;; square root of the standard-part of the argument!  This is probably
;; true of all continuous functions, isn't it?

(defthm standard-part-sqrt
  (implies (and (realp x)
                (<= 0 x)
                (i-limited x))
           (equal (standard-part (acl2-sqrt x))
                  (acl2-sqrt (standard-part x))))
  :hints (("Goal"
           :use ((:instance y*y=x->y=sqrt-x
                            (x (standard-part x))
                            (y (standard-part (acl2-sqrt x))))))
          ("Goal'''"
           :use ((:instance standard-part-of-times
                            (x (acl2-sqrt x))
                            (y (acl2-sqrt x)))))))
