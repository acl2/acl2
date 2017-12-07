; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "arith-nsa4")
(include-book "abs")

(deflabel nsa-theory-start)

(defthm standard-part-abs-0-thm
  (iff (= (standard-part (abs x)) 0)
       (= (standard-part x) 0)))

(defthm standard-numberp-times-type-thm
  (implies
   (and
    (standard-numberp x)
    (standard-numberp y))
   (standard-numberp (* x y)))
  :rule-classes ((:type-prescription)))

(defthm standard-numberp-plus-type-thm
  (implies
   (and
    (standard-numberp x)
    (standard-numberp y))
   (standard-numberp (+ x y)))
  :rule-classes ((:type-prescription)))

(encapsulate
  ()

  (local (defthm arith-4
           (implies
            (and
             (realp x)
             (realp y)
             (not (equal x 0))
             (not (equal y 0))
             (<= (abs x)
                 (abs y)))
            (<= (abs (/ y))
                (abs (/ x))))
           :rule-classes nil))

  (defthm standard-bound-x-implies-limited-x-thm
    (implies
     (and
      (standard-numberp y)
      (realp y)
      (realp x)
      (not (equal y 0))
      (<= (abs x)
          (abs y)))
     (i-limited x))
    :rule-classes nil
    :hints (("Goal" :cases ((equal y 0) (not (equal y 0)))
             :in-theory (disable abs))
            ("Goal'" :use ((:instance arith-4)
                           (:instance standard-part-<= (x (abs (/ y)))
                                      (y (abs (/ x))))))))

  (defthm limited-bound-x-implies-limited-x-thm
    (implies
     (and
      (i-limited y)
      (realp y)
      (realp x)
      (not (equal y 0))
      (<= (abs x)
          (abs y)))
     (i-limited x))
    :rule-classes nil
    :hints (("Goal" :cases ((i-small y) (not (i-small y)))
             :in-theory (disable abs))
            ("Subgoal 2" :use ((:instance arith-4)
                               (:instance standard-part-<= (x (abs (/ y)))
                                          (y (abs (/ x))))))
            ("Subgoal 1" :use ((:instance arith-4)
                               (:instance standard-part-<= (x (abs (/ y)))
                                          (y (abs (/ x)))))))))

(defthm plus-limited
  (implies
   (and
    (realp x)
    (realp y)
    (i-limited x)
    (i-limited y))
   (i-limited (+ x y)))
  :rule-classes :rewrite
  :hints (("Goal" :use ((:instance standard+small->i-limited
                                   (x (standard-part (+ x y)))
                                   (eps (- (+ x y) (standard-part (+ x y)))))))))

(defthm times-limited
  (implies
   (and
    (realp x)
    (realp y)
    (i-limited x)
    (i-limited y))
   (i-limited (* x y)))
  :rule-classes :rewrite
  :hints (("Goal"  :use ((:instance standard+small->i-limited
                                    (x (standard-part (* x y)))
                                    (eps (- (* x y) (standard-part (* x
                                                                      y)))))))))

(defthm divide-limited
  (implies
   (and
    (realp x)
    (realp y)
    (i-limited x)
    (i-limited y)
    (not (i-small y)))
   (i-limited (/ x y)))
  :rule-classes :rewrite
  :hints (("Goal"  :use ((:instance standard+small->i-limited
                                    (x (standard-part (/ x y)))
                                    (eps (- (/ x y) (standard-part (/ x
                                                                      y)))))))))

(defthm btwn-0-and-1-limited-thm
  (implies
   (and
    (realp a)
    (< 0 a)
    (< a 1))
   (i-limited a))
  :rule-classes nil
  :hints (("Goal"  :cases ((i-small a) (not (i-small a))))
          ("Subgoal 1" :use ((:instance (:theorem (implies
                                                   (and
                                                    (realp x)
                                                    (realp y)
                                                    (not (equal x 0))
                                                    (not (equal y 0))
                                                    (< 0 x)
                                                    (< x 1))
                                                   (< 1 (/ x)))))
                             (:instance standard-part-<= (x 1)
                                        (y (/ a)))))))

(defthm sandwich-limited-thm-hint-1
  (implies
   (and
    (realp u)
    (realp v)
    (realp a)
    (< 0 a)
    (< a 1)
    (i-limited u)
    (i-limited v))
   (i-limited (+ v (* a (- u v)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance btwn-0-and-1-limited-thm)))))

(defthm sandwich-limited-thm
  (implies
   (and
    (realp u)
    (realp v)
    (realp x)
    (< u x)
    (< x v)
    (i-limited u)
    (i-limited v))
   (i-limited x))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable i-large
                                      DISTRIBUTIVITY
                                      distributivity-left)
           :use ((:instance  sandwich-limited-thm-hint-1
                             (a (/ (- x v) (- u v))))))))

(defthm /-large-integer-is-ismall-thm
  (i-small (/ (i-large-integer)))
  :hints (("Goal" :in-theory (disable i-large-integer-is-large)
           :use ((:instance i-large-integer-is-large)))))

(deftheory nsa-theory
  (set-difference-theories
   (universal-theory :here)
   (universal-theory 'nsa-theory-start)))

(defthm standard-part-limited-thm
  (implies
   (and
    (realp x)
    (i-limited x))
   (i-limited (standard-part x)))
  :hints (("Goal" :use ((:instance standards-are-limited
                                   (x (standard-part x)))))))

(defthm /-large-integer-standard-part-thm
  (equal (STANDARD-PART (/ (I-LARGE-INTEGER)))
         0)
  :hints (("Goal" :in-theory (disable /-LARGE-INTEGER-IS-ISMALL-THM)
           :use ((:instance /-LARGE-INTEGER-IS-ISMALL-THM)))))

(defthm /-large-integer-limited-thm
  (i-limited (/ (I-LARGE-INTEGER)))
  :rule-classes ((:type-prescription) (:rewrite))
  :hints (("Goal" :in-theory (disable /-LARGE-INTEGER-IS-ISMALL-THM)
           :use ((:instance /-LARGE-INTEGER-IS-ISMALL-THM)))))
