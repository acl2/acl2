; A lightweight book about the built-in operations * and /.
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "times"))

(defthm *-of-/-same
  (equal (* x (/ x))
         (if (equal 0 (fix x))
             0
           1)))

(in-theory (disable inverse-of-*)) ;*-of-/-same is stronger

(defthm *-of-*-of-/-same
  (equal (* x (* (/ x) y))
         (if (equal 0 (fix x))
             0
           (fix y)))
  :hints (("Goal" :use (:instance associativity-of-*
                                  (y (/ x))
                                  (z y))
           :in-theory (disable associativity-of-*))))

(defthm equal-of-*-of-/
  (equal (equal z (* (/ x) y))
         (and (acl2-numberp z)
              (if (equal (fix x) 0)
                  (equal z 0)
                (equal (* x z) (fix y))))))

(defthm equal-of-/
  (implies (syntaxp (not (quotep y)))
           (equal (equal x (/ y))
                  (if (equal 0 (fix y))
                      (equal 0 x)
                    (equal (* x y) 1))))
  :hints (("Goal" :use (:instance equal-of-*-of-/
                                  (z x)
                                  (x y)
                                  (y 1))
           :in-theory (disable equal-of-*-of-/))))

(defthm /-of-*
  (equal (/ (* x y))
         (* (/ x) (/ y)))
  :hints (("Goal" :cases ((acl2-numberp y)))))

(defthm <-of-*-of-/-arg2-arg1
  (implies (and (< 0 x)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< z (* (/ x) y))
                  (< (* x z) y)))
  :hints (("Goal" :cases ((< Z (* (/ X) Y))))))

(defthm <-of-*-of-/-arg2-arg2
  (implies (and (< 0 x)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< z (* y (/ x)))
                  (< (* x z) y)))
  :hints (("Goal" :use (:instance <-of-*-of-/-arg2-arg1)
           :in-theory (disable <-of-*-of-/-arg2-arg1))))

(defthm <-of-*-of-/-arg1-arg1
  (implies (and (< 0 x)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (* (/ x) y) z)
                  (< y (* x z))))
  :hints (("Goal" :cases ((< y (* x z))))))

(defthm <-of-*-of-/-arg1-arg2
  (implies (and (< 0 x)
                (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (* y (/ x)) z)
                  (< y (* x z))))
  :hints (("Goal" :use (:instance <-of-*-of-/-arg1-arg1)
           :in-theory (disable <-of-*-of-/-arg1-arg1))))

(defthm <-of-*-of-/-arg1-arg3
  (implies (and (< 0 x)
                (rationalp x)
                (rationalp y)
                (rationalp y2)
                (rationalp z))
           (equal (< (* y y2 (/ x)) z)
                  (< (* y y2) (* x z))))
  :hints (("Goal" :use (:instance <-of-*-of-/-arg1-arg1 (y (* y y2)))
           :in-theory (disable <-of-*-of-/-arg1-arg1))))
