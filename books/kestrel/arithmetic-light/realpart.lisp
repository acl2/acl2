; A lightweight book about the built-in function realpart.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "complex"))
(local (include-book "imagpart"))

(defthm realpart-when-rationalp
  (implies (rationalp x)
           (equal (realpart x)
                  x)))

(defthmd realpart-redef
  (equal (realpart x)
         (- x
            (* #C(0 1) (imagpart x))))
  :hints (("Goal" :use (:instance realpart-imagpart-elim))))

(local
 (defthm complex-split
   (implies (acl2-numberp x)
            (equal (+ (realpart x)
                      (* #C(0 1) (imagpart x)))
                   x))
   :rule-classes nil
   :hints (("Goal" :use (:instance realpart-imagpart-elim)))))

(local
 (defthmd --becomes-*-of--1
   (equal (- x)
          (* -1 x))))

(local
 (defthm commutativity-2-of-*
   (equal (* x (* y z))
          (* y (* x z)))
   :hints (("Goal" :use ((:instance associativity-of-*)
                         (:instance associativity-of-* (x y) (y x)))
            :in-theory (disable associativity-of-*)))))

(local
 (defthm *-of---arg2
   (equal (* x (- y))
          (- (* x y)))
   :hints (("Goal" :in-theory (enable --becomes-*-of--1)))))

(defthm realpart-of--
  (equal (realpart (- x))
         (- (realpart x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance complex-split)
                 (:instance complex-split (x (- x)))
                 (:instance complex-equal
                            (x1 (realpart x))
                            (y1 (imagpart x))
                            (x2 (- (realpart (- x))))
                            (y2 (- (imagpart (- x)))))))))

(defthm realpart-of-*-of-i
  (implies (rationalp x)
           (equal (realpart (* #C(0 1) x))
                  0))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable realpart-redef))))

(defthm realpart-of-*-when-rationalp-arg1
  (implies (rationalp x)
           (equal (realpart (* x y))
                  (* x (realpart y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance complex-split (x y))))))

(defthm realpart-of-*-when-rationalp-arg2
  (implies (rationalp y)
           (equal (realpart (* x y))
                  (* y (realpart x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (disable realpart-of-*-when-rationalp-arg1)
           :use ((:instance realpart-of-*-when-rationalp-arg1
                            (x y)
                            (y x))))))
