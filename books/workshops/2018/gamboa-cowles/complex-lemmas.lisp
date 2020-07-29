(in-package "ACL2")

; cert_param: (uses-acl2r)


(local (include-book "nonstd/nsa/continuity" :dir :system))
(local (include-book "nonstd/nsa/sqrt" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm complex-uminus
   (implies (and (real/rationalp x)
                 (real/rationalp y))
            (equal (- (complex x y))
                   (complex (- x) (- y))))
   :hints (("Goal"
            :use ((:instance complex-definition)
                  (:instance complex-definition (x (- x)) (y (- y))))))
   :rule-classes nil))

(local
 (defthm realpart-uminnus
   (implies (acl2-numberp z)
            (equal (realpart (- z))
                   (- (realpart z))))
   :hints (("Goal"
            :use ((:instance complex-uminus (x (realpart z)) (y (imagpart z))))))
   ))

(local
 (defthm imagpart-uminus
   (implies (acl2-numberp z)
            (equal (imagpart (- z))
                   (- (imagpart z))))
   :hints (("Goal"
            :use ((:instance complex-uminus (x (realpart z)) (y (imagpart z))))))
   ))

(defthm not-complex-imagpart-is-0
  (implies (not (complexp z))
           (equal (imagpart z) 0)))

(local
 (defthm imagpart-add-is-0
   (implies (not (complexp (+ z1 z2)))
            (equal (imagpart (+ z1 z2))
                   0))))

(defthm realpart-when-not-complexp
  (implies (and (acl2-numberp z)
                (not (complexp z)))
           (equal (realpart z)
                  z)))

(local
 (defthm realpart-when-not-complexp-add
   (implies (not (complexp (+ z1 z2)))
            (equal (realpart (+ z1 z2))
                   (+ z1 z2)))
   :hints (("Goal"
            :use ((:instance realpart-when-not-complexp
                             (z (+ z1 z2))))))
   :rule-classes nil))



(defthm complex-close
  (implies (and (acl2-numberp z1)
                (acl2-numberp z2))
           (equal (i-close z1 z2)
                  (and (i-close (realpart z1) (realpart z2))
                       (i-close (imagpart z1) (imagpart z2)))))
  :hints (("Goal"
           :use ((:instance complex-small
                            (x (- z1 z2)))
                 )
           :in-theory (e/d (i-close)
; Matt K. mod: Avoid loop by disabling |(< (if a b c) x)|.
                           (|(< (if a b c) x)|)))
          ("Subgoal 2"
           :use ((:instance (:theorem (implies (not (complexp (- z1 z2))) (equal (imagpart (- z1 z2)) 0))))
                 (:instance realpart-when-not-complexp-add (z1 z1) (z2 (- z2)))))
          ("Subgoal 1"
           :use ((:instance (:theorem (implies (not (complexp (- z1 z2))) (equal (imagpart (- z1 z2)) 0))))
                 (:instance realpart-when-not-complexp-add (z1 z1) (z2 (- z2))))))
  :rule-classes nil)


(defthm close-plus
  (implies (and (i-close x1 x2)
                (i-close y1 y2))
           (i-close (+ x1 y1) (+ x2 y2)))
  :hints (("Goal"
           :use ((:instance i-small-plus
                            (x (+ x1 (- x2)))
                            (y (+ y1 (- y2)))))
           :in-theory '(i-close
                        associativity-of-+
                        commutativity-of-+
                        commutativity-2-of-+
                        distributivity-of-minus-over-+
                        )))
  :rule-classes nil)

(defthm close-times
  (implies (and (i-close x1 x2)
                (i-limited y))
           (i-close (* x1 y) (* x2 y)))
  :hints (("Goal"
           :use ((:instance small*limited->small
                            (x (- x1 x2))
                            (y y))
                 (:instance (:theorem (equal (* y (- x2)) (- (* x2 y))))))
           :in-theory (enable i-close)))
  :rule-classes nil)

(defthm close-times-2
  (implies (and (i-close x1 x2)
                (i-close y1 y2)
                (i-limited x1)
                (i-limited y1))
           (i-close (* x1 y1) (* x2 y2)))
  :hints (("Goal"
           :use ((:instance close-times (x1 x1) (x2 x2) (y y1))
                 (:instance close-times (x1 y1) (x2 y2) (y x2))
                 (:instance i-close-transitive
                            (x (* x1 y1))
                            (y (* x2 y1))
                            (z (* x2 y2)))
                 (:instance i-close-limited
                            (x x1)
                            (y x2)))
           :in-theory '(commutativity-of-*)
           ))
  :rule-classes nil)

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
