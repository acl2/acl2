; This file was created by J Moore and Matt Kaufmann in 1995 in support of
; their proof of the AMD-K5 division code.

;Altered by Daron Vroon for v2-8 to use the new ordinal definitions.

(in-package "ACL2")
(local (include-book "ihs/ihs-definitions" :dir :system))
(local (include-book "ihs/ihs-lemmas" :dir :system))

; The following is (minimal-ihs-theory)
(local (PROGN (IN-THEORY NIL)
              (IN-THEORY (ENABLE BASIC-BOOT-STRAP
                                 IHS-MATH QUOTIENT-REMAINDER-RULES
                                 LOGOPS-LEMMAS-THEORY))))
(local (in-theory (enable logops-definitions-theory)))

(defthm a1 (equal (+ x (+ y z)) (+ y (+ x z))))
(defthm a2 (equal (- x) (* -1 x)))

(local (in-theory (disable functional-commutativity-of-minus-*-right
                           functional-commutativity-of-minus-*-left)))
(defthm a3
  (and
   (implies
    (syntaxp (and (quotep c1) (quotep c2)))
    (and (equal (+ (* c1 x) (* c2 x)) (* (+ c1 c2) x))
         (equal (+ (* c1 x) (+ (* c2 x) y)) (+ (* (+ c1 c2) x) y))))
   (implies
    (syntaxp (quotep c2))
    (and (equal (+ x (* c2 x)) (* (+ 1 c2) x))
         (equal (+ x (+ (* c2 x) y1)) (+ (* (+ 1 c2) x) y1))
         (equal (+ x (+ y1 (* c2 x))) (+ (* (+ 1 c2) x) y1))
         (equal (+ x (+ y1 (+ (* c2 x) y2))) (+ (* (+ 1 c2) x) y1 y2))
         (equal (+ x (+ y1 (+ y2 (* c2 x)))) (+ (* (+ 1 c2) x) y1 y2))
         (equal (+ x (+ y1 (+ y2 (+ y3 (* c2 x)))))
                (+ (* (+ 1 c2) x) y1 y2 y3))
         (equal (+ x (+ y1 (+ y2 (+ (* c2 x) y3))))
                (+ (* (+ 1 c2) x) y1 y2 y3))))
   (and (equal (+ x x) (* 2 x))
        (equal (+ x (+ x y1)) (+ (* 2 x) y1)))))
(defthm a4
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (+ c1 (+ c2 y1)) (+ (+ c1 c2) y1))))
(defthm a5
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (* c1 (* c2 y1)) (* (* c1 c2) y1))))
(defthm a6
  (equal (/ (/ x)) (fix x)))
(defthm a7
  (equal (/ (* x y)) (* (/ x) (/ y))))
(defthm a8
  (implies (and (force (rationalp x))
                (force (not (equal x 0))))
           (and (equal (* x (* (/ x) y)) (fix y))
                (equal (* x (/ x)) 1))))
(in-theory (disable inverse-of-*))
(defthm a9
  (and (equal (* 0 x) 0)
       (equal (* x (* y z)) (* y (* x z)))
       (equal (* x (+ y z)) (+ (* x y) (* x z)))
       (equal (* (+ y z) x) (+ (* y x) (* z x)))))
(defun fl (x) (floor x 1))
(defthm a10
  (and (implies (integerp i) (equal (fl i) i))
       (implies (and (integerp i)
                     (force (rationalp x1)))
                (and (equal (fl (+ i x1)) (+ i (fl x1)))
                     (equal (fl (+ x1 i)) (+ i (fl x1)))))
       (implies (and (integerp i)
                     (force (rationalp x1))
                     (force (rationalp x2)))
                (and (equal (fl (+ x1 (+ i x2))) (+ i (fl (+ x1 x2))))
                     (equal (fl (+ x1 (+ x2 i))) (+ i (fl (+ x1 x2))))))
       (implies (and (integerp i)
                     (force (rationalp x1))
                     (force (rationalp x2))
                     (force (rationalp x3)))
                (and (equal (fl (+ x1 (+ x2 (+ i x3))))
                            (+ i (fl (+ x1 x2 x3))))
                     (equal (fl (+ x1 (+ x2 (+ x3 i))))
                            (+ i (fl (+ x1 x2 x3))))))
       (implies (and (integerp i)
                     (force (rationalp x1))
                     (force (rationalp x2))
                     (force (rationalp x3))
                     (force (rationalp x4)))
                (and (equal (fl (+ x1 (+ x2 (+ x3 (+ i x4)))))
                            (+ i (fl (+ x1 x2 x3 x4))))
                     (equal (fl (+ x1 (+ x2 (+ x3 (+ x4 i)))))
                            (+ i (fl (+ x1 x2 x3 x4))))))))

(defthm a12
  (implies (and (integerp i)
                (integerp j)
                (< 1 j)
                (< j i))
           (and (< (acl2-count (fl (/ i j))) (acl2-count i))
                (< (acl2-count (fl (* (/ j) i))) (acl2-count i))))
  :rule-classes :linear
  :hints
  (("Goal"
    :use (:instance REWRITE-FLOOR-X*Y-Z-RIGHT (x i) (y (/ j)) (z 1)))))

(defthm a13
  (implies (force (rationalp x))
           (and (< (1- x) (fl x))
                (<= (fl x) x)))
  :rule-classes :linear)

(in-theory (disable fl))

(defthm a14
  (and
   (implies (and (integerp i)
                 (<= 0 i)
                 (<= 0 j))
            (and (integerp (expt i j))
                 (<= 0 (expt i j))))
   (implies (and (rationalp i)
                 (not (equal i 0)))
            (not (equal (expt i j) 0))))
  :hints
  (("Goal" :in-theory (enable expt)))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (and (integerp i)
                  (<= 0 i)
                  (<= 0 j))
             (and (integerp (expt i j))
                  (<= 0 (expt i j)))))
   (:type-prescription
    :corollary
    (implies (and (rationalp i)
                  (not (equal i 0)))
             (not (equal (expt i j) 0))))))
(defthm a15
  (implies (and (rationalp i)
                (not (equal i 0))
                (integerp j1)
                (integerp j2))
           (and (equal (* (expt i j1) (expt i j2))
                       (expt i (+ j1 j2)))
                (equal (* (expt i j1) (* (expt i j2) x))
                       (* (expt i (+ j1 j2)) x)))))
(defthm a16
  (equal (expt (* a b) i)
         (* (expt a i) (expt b i)))
  :hints
  (("Goal" :in-theory (enable distributivity-of-expt-over-*))))

#|
(local (defun logior-+-hint (x i)
  (if (= (nfix i) 0)
      x
    (logior-+-hint (floor x 2) (1- i)))))

(local (defthm logior-+-lemma1
  (implies (and (integerp logand)
                (acl2-numberp kterm))
           (equal (equal (+ -1 (- logand)) kterm)
                  (equal logand (- (+ 1 kterm)))))))

(local (defthm evenp--k-lemma
  (equal (equal (integerp x) (integerp y))
         (iff (integerp x) (integerp y)))))

(local (defthm evenp--k
  (implies (integerp k) (equal (evenp (- k)) (evenp k)))
  :hints
  (("Goal" :in-theory (set-difference-theories
                       (enable evenp
                               functional-commutativity-of-minus-*-right
                               functional-commutativity-of-minus-*-left)
                       '(a2 a5))))))

(local (defthm evenp-2k
  (implies (integerp k) (evenp (* 2 k)))
  :hints (("Goal" :in-theory (enable evenp)))))

(local (defthm evenp-expt-2
  (implies (and (integerp k)
                (> k 0))
           (evenp (expt 2 k)))
  :hints (("Goal" :in-theory (enable evenp expt)))))

(local (defthm evenp-+-even
  (implies (evenp j) (equal (evenp (+ i j)) (evenp i)))
  :hints (("Goal" :in-theory (enable evenp)))))

(defthm logior-+
  (implies (and (integerp i)
                (<= 0 i)
                (integerp x)
                (<= 0 x)
                (< x (expt 2 i)))
           (equal (logior (expt 2 i) x)(+ (expt 2 i) x)))
  :hints (("Goal" :induct (logior-+-hint x i)
                  :in-theory
                   (set-difference-theories
                       (enable logior logand lognot
                               functional-commutativity-of-minus-*-right
                               functional-commutativity-of-minus-*-left)
                       '(a2 a5))))
  :rule-classes nil)
|#

(defthm /-weakly-monotonic
  (implies (and (<= y y+)
                (force (rationalp y))
                (force (rationalp y+))
                (< 0 y))
           (<= (/ y+) (/ y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

(defthm /-strongly-monotonic
  (implies (and (< y y+)
                (force (rationalp y))
                (force (rationalp y+))
                (< 0 y))
           (< (/ y+) (/ y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((/ y+) (/ y))) :linear))

(defthm *-weakly-monotonic
  (implies (and (<= y y+)
               (force (rationalp x))   ; This does not hold if x, y, and z are complex!
               (force (rationalp y))
               (force (rationalp y+))
               (<= 0 x))
           (<= (* x y) (* x y+)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (<= y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (<= 0 x))
             (<= (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and (<= y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (<= 0 x))
             (<= (* y x) (* y+ x))))))

#| Here is the complex counterexample to which we alluded above.

(let ((y  #c(1 -1))
      (y+ #c(1 1))
      (x  #c(1 1)))
    (implies (and (<= y y+)
                  (<= 0 x))
             (<= (* x y) (* x y+))))
|#

(defthm *-strongly-monotonic
  (implies (and (< y y+)
                (force (rationalp x))
                (force (rationalp y))
                (force (rationalp y+))
                (< 0 x))
           (< (* x y) (* x y+)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (< y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (< 0 x))
             (< (* y x) (* y+ x))))
   (:linear
    :corollary
    (implies (and (< y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (< 0 x))
             (< (* y x) (* y+ x))))))

(defthm *-weakly-monotonic-negative-multiplier
  (implies (and (<= y y+)
               (force (rationalp x))
               (force (rationalp y))
               (force (rationalp y+))
               (< x 0))
           (<= (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (<= y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (< x 0))
             (<= (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and (<= y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (< x 0))
             (<= (* y+ x) (* y x))))))

(defthm *-strongly-monotonic-negative-multiplier
  (implies (and (< y y+)
                (force (rationalp x))
                (force (rationalp y))
                (force (rationalp y+))
                (< x 0))
           (< (* x y+) (* x y)))
  :rule-classes
  ((:forward-chaining :trigger-terms ((* x y) (* x y+)))
   (:linear)
   (:forward-chaining
    :trigger-terms ((* y x) (* y+ x))
    :corollary
    (implies (and (< y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (< x 0))
             (< (* y+ x) (* y x))))
   (:linear
    :corollary
    (implies (and (< y y+)
                  (force (rationalp x))
                  (force (rationalp y))
                  (force (rationalp y+))
                  (< x 0))
             (< (* y+ x) (* y x))))))

(defthm fl-weakly-monotonic
  (implies (and (<= y y+)
                (force (rationalp y))
                (force (rationalp y+)))
           (<= (fl y) (fl y+)))
  :rule-classes ((:forward-chaining :trigger-terms ((fl y) (fl y+)))
                 (:linear)
                 (:forward-chaining
                  :trigger-terms ((fl y) (fl y+))
                  :corollary (implies (and (< y y+)
                                           (force (rationalp y))
                                           (force (rationalp y+)))
                                      (<= (fl y) (fl y+))))
                 (:linear
                  :corollary (implies (and (< y y+)
                                           (force (rationalp y))
                                           (force (rationalp y+)))
                                      (<= (fl y) (fl y+))))))

; We now prove a bunch of bounds theorems for *.  We are concerned with bounding the
; product of a and b given intervals for a and b.  We consider three kinds of intervals.
; We discuss only the a case.

; abs intervals mean (abs a) < amax or -amax < a < amax, where amax is positive.

; nonneg-open intervals mean 0<=a<amax.

; nonneg-closed intervals mean 0<=a<=amax, where amax is positive.

; We now prove theorems with names like abs*nonneg-open, etc. characterizing
; the product of two elements from two such interals.  All of these theorems
; are made with :rule-classes nil because I don't know how to control their
; use.

(encapsulate nil
  (local
   (defthm renaming
    (implies (and (rationalp a)
                  (rationalp xmax)
                  (rationalp b)
                  (rationalp bmax)
                  (< (- xmax) a)
                  (<= a xmax)
                  (< 0 xmax)
                  (<= 0 b)
                  (< b bmax))
             (and (< (- (* xmax bmax)) (* a b))
                  (< (* a b) (* xmax bmax))))
    :hints (("Goal" :cases ((equal b 0))))))

; This lemma is for lookup * d and lookup * away.  We don't need to consider 0
; < b for the d case because we have 0 < 1 <= d and the conclusion of the new
; lemma would be no different.

  (defthm abs*nonneg-open
    (implies (and (rationalp a)
                  (rationalp amax)
                  (rationalp b)
                  (rationalp bmax)
                  (< (- amax) a)
                  (<= a amax)       ; (< a amax) is all we'll ever use, I bet.
                  (< 0 amax)
                  (<= 0 b)
                  (< b bmax))
             (and (< (- (* amax bmax)) (* a b))
                  (< (* a b) (* amax bmax))))
    :hints (("Goal" :by renaming))
    :rule-classes nil))

(defthm abs*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :cases ((equal b 0))))
  :rule-classes nil)

(defthm nonneg-closed*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* b a))
                (< (* b a) (* amax bmax))))
  :hints (("Goal" :use abs*nonneg-closed))
  :rule-classes nil)

(defthm nonneg-open*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (<= a amax) ; (< a amax) is all we'll ever use, I bet.
                (< 0 amax)
                (<= 0 b)
                (< b bmax))
           (and (< (- (* bmax amax)) (* a b))
                (< (* a b) (* bmax amax))))
    :hints (("Goal" :use abs*nonneg-open))
    :rule-classes nil)

; The next three, which handle nonnegative open intervals in the first argument,
; can actually be seen as uses of the abs intervals above.  Simply observe that
; if 0<=a<amax then -amax<a<amax.

(defthm nonneg-open*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :use abs*nonneg-closed))
  :rule-classes nil)

(defthm nonneg-open*nonneg-open
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (< b bmax))
           (and (<= 0 (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :use abs*nonneg-open))
  :rule-classes nil)

; and the commuted version
(defthm nonneg-closed*nonneg-open
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (< a amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* b a))
                (< (* b a) (* amax bmax))))
  :hints (("Goal" :use nonneg-open*nonneg-closed))
  :rule-classes nil)

(defthm nonneg-closed*nonneg-closed
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (<= 0 a)
                (<= a amax)
                (< 0 amax)
                (<= 0 b)
                (<= b bmax)
                (< 0 bmax))
           (and (<= 0 (* a b))
                (<= (* a b) (* amax bmax))))
  :rule-classes nil)

(defthm abs*abs
  (implies (and (rationalp a)
                (rationalp amax)
                (rationalp b)
                (rationalp bmax)
                (< (- amax) a)
                (< a amax)
                (< 0 amax)
                (< (- bmax) b)
                (<= b bmax)
                (< 0 bmax))
           (and (< (- (* amax bmax)) (* a b))
                (< (* a b) (* amax bmax))))
  :hints (("Goal" :cases ((< b 0) (< 0 b))))
  :rule-classes nil)

(defthm rearrange-negative-coefs-<
  (and (iff (< (* (- c) x) z)
            (< 0 (+ (* c x) z)))
       (iff (< (+ (* (- c) x) y) z)
            (< y (+ (* c x) z)))
       (iff (< (+ y (* (- c) x)) z)
            (< y (+ (* c x) z)))
       (iff (< (+ y1 y2 (* (- c) x)) z)
            (< (+ y1 y2) (+ (* c x) z)))
       (iff (< (+ y1 y2 y3 (* (- c) x)) z)
            (< (+ y1 y2 y3) (+ (* c x) z)))
       (iff (< z (+ (* (- c) x) y))
            (< (+ (* c x) z) y))
       (iff (< z (+ y (* (- c) x)))
            (< (+ (* c x) z) y))
       (iff (< z (+ y1 y2 (* (- c) x)))
            (< (+ (* c x) z) (+ y1 y2)))
       (iff (< z (+ y1 y2 y3 (* (- c) x)))
            (< (+ (* c x) z) (+ y1 y2 y3)))))

(defthm rearrange-negative-coefs-equal
  (and (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp z)))
                (iff (equal (* (- c) x) z)
                     (equal 0 (+ (* c x) z))))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y))
                     (force (rationalp z)))
                (iff (equal (+ (* (- c) x) y) z)
                     (equal y (+ (* c x) z))))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y))
                     (force (rationalp z)))
                (iff (equal (+ y (* (- c) x)) z)
                     (equal y (+ (* c x) z))))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y1))
                     (force (rationalp y2))
                     (force (rationalp z)))
                (iff (equal (+ y1 y2 (* (- c) x)) z)
                     (equal (+ y1 y2) (+ (* c x) z))))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y1))
                     (force (rationalp y2))
                     (force (rationalp y3))
                     (force (rationalp z)))
                (iff (equal (+ y1 y2 y3 (* (- c) x)) z)
                     (equal (+ y1 y2 y3) (+ (* c x) z))))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y))
                     (force (rationalp z)))
                (iff (equal z (+ (* (- c) x) y))
                     (equal (+ (* c x) z) y)))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y))
                     (force (rationalp z)))
                (iff (equal z (+ y (* (- c) x)))
                     (equal (+ (* c x) z) y)))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y1))
                     (force (rationalp y2))
                     (force (rationalp z)))
                (iff (equal z (+ y1 y2 (* (- c) x)))
                     (equal (+ (* c x) z) (+ y1 y2))))
       (implies (and (force (rationalp c))
                     (force (rationalp x))
                     (force (rationalp y1))
                     (force (rationalp y2))
                     (force (rationalp y3))
                     (force (rationalp z)))
                (iff (equal z (+ y1 y2 y3 (* (- c) x)))
                     (equal (+ (* c x) z) (+ y1 y2 y3))))))

(defthm rearrange-fractional-coefs-<
  (and
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (< 0 c))
            (iff (< (* (/ c) x) z)
                 (< x (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y))
                 (< 0 c))
            (iff (< (+ (* (/ c) x) y) z)
                 (< (+ x (* c y)) (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y))
                 (< 0 c))
            (iff (< (+ y (* (/ c) x)) z)
                 (< (+ (* c y) x) (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y1))
                 (force (rationalp y2))
                 (< 0 c))
            (iff (< (+ y1 y2 (* (/ c) x)) z)
                 (< (+ (* c y1) (* c y2) x) (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y1))
                 (force (rationalp y2))
                 (force (rationalp y3))
                 (< 0 c))
            (iff (< (+ y1 y2 y3 (* (/ c) x)) z)
                 (< (+ (* c y1) (* c y2) (* c y3) x) (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (< 0 c))
            (iff (< z (* (/ c) x))
                 (< (* c z) x)))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y))
                 (< 0 c))
            (iff (< z (+ (* (/ c) x) y))
                 (< (* c z) (+ x (* c y)))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y))
                 (< 0 c))
            (iff (< z (+ y (* (/ c) x)))
                 (< (* c z) (+ (* c y) x))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y1))
                 (force (rationalp y2))
                 (< 0 c))
            (iff (< z (+ y1 y2 (* (/ c) x)))
                 (< (* c z) (+ (* c y1) (* c y2) x))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y1))
                 (force (rationalp y2))
                 (force (rationalp y3))
                 (< 0 c))
            (iff (< z (+ y1 y2 y3 (* (/ c) x)))
                 (< (* c z) (+ (* c y1) (* c y2) (* c y3) x))))))

(encapsulate nil
 (local (defthm replace-equals-by-inequalities
          (implies (and (rationalp x)
                        (rationalp y))
                   (equal (equal x y)
                          (and (<= x y)
                               (<= y x))))))

(defthm rearrange-fractional-coefs-equal
  (and
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (< 0 c))
            (iff (equal (* (/ c) x) z)
                 (equal x (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y))
                 (< 0 c))
            (iff (equal (+ (* (/ c) x) y) z)
                 (equal (+ x (* c y)) (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y))
                 (< 0 c))
            (iff (equal (+ y (* (/ c) x)) z)
                 (equal (+ (* c y) x) (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y1))
                 (force (rationalp y2))
                 (< 0 c))
            (iff (equal (+ y1 y2 (* (/ c) x)) z)
                 (equal (+ (* c y1) (* c y2) x) (* c z))))
   (implies (and (force (rationalp c))
                 (force (rationalp z))
                 (force (rationalp x))
                 (force (rationalp y1))
                 (force (rationalp y2))
                 (force (rationalp y3))
                 (< 0 c))
            (iff (equal (+ y1 y2 y3 (* (/ c) x)) z)
                 (equal (+ (* c y1) (* c y2) (* c y3) x) (* c z)))))))

(defthm x*/y=1->x=y
  (implies (and (rationalp x)
                (rationalp y)
                (not (equal x 0))
                (not (equal y 0)))
           (iff (equal (* x (/ y)) 1)
                (equal x y)))
  :rule-classes nil)

(defun point-right-measure (x)
  (floor (if (and (rationalp x) (< 0 x)) (/ x) 0) 1))

(defun point-left-measure (x)
  (floor (if (and (rationalp x) (> x 0)) x 0) 1))

(defthm recursion-by-point-right
  (and (o-p (point-right-measure x))
       (implies (and (rationalp x)
                     (< 0 x)
                     (< x 1))
                (o< (point-right-measure (* 2 x))
                    (point-right-measure x)))))

(defthm recursion-by-point-left
  (and (o-p (point-left-measure x))
       (implies (and (rationalp x)
                     (>= x 2))
                (o< (point-left-measure (* 1/2 x))
                    (point-left-measure x)))))

(in-theory (disable point-right-measure point-left-measure))

(defthm x<x*y<->1<y
  (implies (and (rationalp x)
                (< 0 x)
                (rationalp y))
           (iff (< x (* x y)) (< 1 y)))
  :rule-classes nil)

(defthm cancel-equal-*
  (implies (and (rationalp r)
                (rationalp s)
                (rationalp a)
                (not (equal a 0)))
           (iff (equal (* a r) (* a s))
                (equal r s)))
  :rule-classes nil)

(defthm my-exponents-add
  (implies (and (not (equal 0 r))
                (acl2-numberp r)
                (integerp i)
                (integerp j))
           (equal (expt r (+ i j))
                  (* (expt r i)
                     (expt r j))))
  :rule-classes nil)

(defthm cancel-<-*
  (implies (and (rationalp r)
                (rationalp s)
                (rationalp a)
                (< 0 a))
           (iff (< (* a r) (* a s))
                (< r s)))
  :rule-classes nil)

(defthm fl-minus
 (implies (rationalp x)
          (EQUAL (FL (- X))
                 (IF (INTEGERP X)
                     (- (FL X))
                     (+ -1 (- (FL X))))))
 :rule-classes nil)
