; A lightweight book about the built-in operation /.
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "times"))
(local (include-book "complex"))
(local (include-book "minus"))
(local (include-book "../library-wrappers/arithmetic-inequalities")) ; todo: drop
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;; Exported in times-and-divides.lisp
(local
 (defthm *-of-/-same
   (equal (* x (/ x))
          (if (equal 0 (fix x))
              0
            1))))

(defthm /-of-/
  (equal (/ (/ x))
         (fix x))
  :hints (("Goal"
           :use (:instance equal-of-*-and-*-cancel
                           (x (/ x))
                           (y (/ (/ x)))
                           (z x))
           :in-theory (disable equal-of-*-and-*-cancel))))

(defthm equal-of-/-constant
  (implies (syntaxp (quotep k))
           (equal (equal k (/ x))
                  (and (acl2-numberp k)
                       (equal (fix x) (/ k))))))

(defthm <-of-/-and-constant-1
  (implies (and (syntaxp (quotep k))
                (< 0 k)
                (rationalp k)
                (rationalp y))
           (equal (< k (/ y))
                  (and (not (<= y 0))
                       (< y (/ k)))))
  :hints (("Goal" :cases ((< y 0)
                          (equal y 0)
                          (< k (/ y)))
           :in-theory (disable <-of-*-and-*-cancel)
           :use (:instance <-of-*-and-*-cancel
                           (x1 k)
                           (x2 (/ y))
                           (y y)))))

(defthm <-of-/-and-constant-2
  (implies (and (syntaxp (quotep k))
                (< 0 k)
                (rationalp k)
                (rationalp y))
           (equal (< (/ y) k)
                  (or (<= y 0)
                      (< (/ k) y))))
  :hints (("Goal" :cases ((< y 0)
                          (equal y 0)
                          (< (/ y) k)))))

(defthm <-of-0-and-/
  (implies (rationalp x)
           (equal (< 0 (/ x))
                  (< 0 x)))
  :hints (("Goal" :cases ((equal x 0)
                          (< 0 x))
           :in-theory (disable <-of-*-and-*-cancel)
           :use (:instance <-of-*-and-*-cancel
                           (x1 0)
                           (x2 (/ x))
                           (y (- x))))))

(defthm <-of-/-and-0
  (implies (rationalp x)
           (equal (< (/ x) 0)
                  (< x 0))))

;gen
(defthm <-of-/-and-/
  (implies (and (< 0 x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (equal (< (/ x) (/ y))
                  (< y x)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (x1 (/ y))
                                  (x2 (/ X))
                                  (y (* x y)))
           :in-theory (disable <-of-*-and-*-cancel))))

(defthm <=-of-/-linear
  (implies (and (<= x0 x)
                (< 0 x)
                (< 0 x0)
                (rationalp x)
                (rationalp x0))
           (<= (/ x) (/ x0)))
  :rule-classes :linear)

(defthm complex-rationalp-of-unary-/
  (equal (complex-rationalp (/ y))
         (complex-rationalp y))
  :hints (("Goal" :cases ((complex-rationalp y)))))

;make an alt version
(defthm complex-rationalp-of-*-of-/-when-rationalp-and-complex-rationalp
  (implies (and (complex-rationalp y)
                (rationalp x))
           (equal (complex-rationalp (* x (/ y)))
                  (not (equal 0 x)))))

;make an alt version
(defthm rationalp-of-*-of-/-when-rationalp-and-complex-rationalp
  (implies (and (complex-rationalp y)
                (rationalp x))
           (equal (rationalp (* x (/ y)))
                  (equal 0 x))))

(defthm integerp-of-*-of-/-when-rationalp-and-complex-rationalp
  (implies (and (complex-rationalp y)
                (rationalp x))
           (equal (integerp (* x (/ y)))
                  (equal 0 x))))

(defthm integerp-of-*-of-/-when-rationalp-and-complex-rationalp-alt
  (implies (and (complex-rationalp y)
                (rationalp x))
           (equal (integerp (* (/ y) x))
                  (equal 0 x))))

(defthmd integerp-squeeze-gen
  (implies (and (< low x)
                (< x (+ 1 low))
                (integerp low))
           (not (integerp x))))

;todo: handle the other cases
(defthm <-of-*-of-/-and-1-when-neg
  (implies (and (< x 0)
                (< y 0)
                (rationalp y)
                (rationalp x)
                )
           (equal (< (* x (/ y)) 1)
                  (< y x)))
  :hints (("Goal"
           :use ((:instance <-of-*-and-*-cancel-gen
                            (x1 (* x (/ y)))
                            (x2 1)
                            (y (- y)))))))

;todo: handle the other cases
(defthm integerp-of-*-of-/-when-<-and-negative
  (implies (and (< y x)
                (<= x 0)
                (<= y 0)
                (rationalp y)
                (rationalp x))
           (equal (integerp (* (/ y) x))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal" :use (:instance integerp-squeeze-gen
                                  (low 0)
                                  (x (* (/ y) x))))))

;;comutes the args to * in the lhs
(defthm integerp-of-*-of-/-when-<-and-negative-alt
  (implies (and (< y x)
                (<= x 0)
                (<= y 0)
                (rationalp y)
                (rationalp x))
           (equal (integerp (* x (/ y)))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal" :use (:instance integerp-squeeze-gen
                                  (low 0)
                                  (x (* (/ y) x))))))






;;;
;;; Characterize division of complex numbers
;;;

;; (a+bi)/(c+di) =
;; ((a+bi)/(c+di))*((c-di)/(c-di)) =
;; ((a+bi)*(c-di))/((c+di)*(c-di)) =
;; (ac+bd+(bc-ad)i)/(c^2+d^2) =
;; (ac+bd)/(c^2+d^2) + ((bc-ad)/(c^2+d^2))i

;; Multiply both numerator and denominator by the complex conjugate
(local
 (defthm /-of-complex-and-complex-step1
   (implies (and (rationalp a)
                 (rationalp b)
                 (rationalp c)
                 (rationalp d))
            (equal (/ (complex a b)
                      (complex c d))
                   (* (/ (complex a b)
                         (complex c d))
                      (/ (complex c (- d))
                         (complex c (- d))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable complex-opener)))))

;;gen
(defthm equal-of-+-of-*-of-i
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp k))
           (equal (equal k (+ a (* #c(0 1) b)))
                  (and (equal k a)
                       (equal 0 b))))
  :hints (("Goal" :use (:instance complex-equal
                                  (x1 k)
                                  (y1 0)
                                  (x2 a)
                                  (y2 b)))))

(local
 (defthm distributivity-alt
   (equal (* (+ y z) x)
          (+ (* y x) (* z x)))))

(local
 (defthm conjugate-helper
   (implies (and (rationalp c)
                 (rationalp d))
            (equal (* (/ (+ c (* #c(0 1) d))) (/ (+ c (- (* #c(0 1) d)))))
                   (/ (+ (* c c) (* d d)))))
   :hints (("Goal" :use (:instance distributivity-of-/-over-*
                                   (x (+ c (* #c(0 1) d)))
                                   (y (+ c (- (* #c(0 1) d)))))
            :in-theory (disable distributivity-of-/-over-*)))))

(defthm /-of-complex-and-complex
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp d))
           (equal (/ (complex a b)
                     (complex c d))
                  (complex (/ (+ (* a c) (* b d))
                              (+ (* c c) (* d d)))
                           (/ (- (* b c) (* a d))
                              (+ (* c c) (* d d))))))
  :hints (("Goal" :use (:instance /-of-complex-and-complex-step1)
           :in-theory (enable complex-opener))))

(defthm <-of-*-of-/-arg1
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (* x (/ y)) z)
                  (if (< 0 y)
                      (< x (* y z))
                    (if (equal 0 y)
                        (< 0 z)
                      (< (* y z) x)))))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel-gen
                                  (x1 (* x (/ y))) (x2 z) (y y))
           :in-theory (disable <-of-*-and-*-cancel-gen))))

;; commutes the * in the lhs
(defthm <-of-*-of-/-arg1-alt
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< (* (/ y) x) z)
                  (if (< 0 y)
                      (< x (* y z))
                    (if (equal 0 y)
                        (< 0 z)
                      (< (* y z) x)))))
  :hints (("Goal" :use (:instance <-of-*-of-/-arg1))))

(defthm <-of-*-of-/-arg2
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< z (* x (/ y)))
                  (if (< 0 y)
                      (< (* y z) x)
                    (if (equal 0 y)
                        (< z 0)
                      (< x (* y z))))))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel-gen
                                  (x1 z)
                                  (x2 (* x (/ y))))
           :in-theory (disable <-of-*-and-*-cancel-gen
                               <-*-/-RIGHT
                               <-OF-*-OF-/-arg1))))

;; commutes the * in the lhs
(defthm <-of-*-of-/-arg2-alt
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z))
           (equal (< z (* (/ y) x))
                  (if (< 0 y)
                      (< (* y z) x)
                    (if (equal 0 y)
                        (< z 0)
                      (< x (* y z))))))
  :hints (("Goal" :use (:instance <-of-*-of-/-arg2)
           :in-theory (disable <-of-*-of-/-arg2))))

;combine with rules above?
(defthm integerp-of-*-of-/-when-<-and-mixed-1
  (implies (and (< x (- y))
                (<= 0 x)
                (<= y 0)
                (rationalp y)
                (rationalp x))
           (equal (integerp (* x (/ y)))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal" :use (:instance integerp-squeeze-gen
                                  (low 0)
                                  (x (* (/ (- y)) x))))))

(defthm integerp-of-*-of-/-when-<-and-mixed-2
  (implies (and (< (- x) y)
                (<= x 0)
                (<= 0 y)
                (rationalp y)
                (rationalp x))
           (equal (integerp (* x (/ y)))
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal" :use (:instance integerp-squeeze-gen
                                  (low 0)
                                  (x (* (/ (- y)) x))))))

(defthm /-of--
  (implies (rationalp x)
           (equal (/ (- x))
                  (- (/ x)))))

(defthm /-of-*
  (equal (/ (* x y))
         (* (/ x) (/ y))))
