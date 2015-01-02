; Copyright (C) 2007 by Shant Harutunian
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; Definition of the measure structure less than operator

(defun o<-1 (x y)
  (cond ((o-finp x)
         (or (not (o-finp y)) (<= (+ X 1) Y)))
        ((o-finp y) nil)
        ((equal (o-first-expt x)
                (o-first-expt y))
         (if (equal (o-first-coeff x)
                    (o-first-coeff y))
             (o<-1 (o-rst x) (o-rst y))
           (<= (+ (o-first-coeff x) 1)
               (o-first-coeff y))))
        (t (o<-1 (o-first-expt x)
                 (o-first-expt y)))))

; The following defines a predicate which
; is true if x is a measure structure

(defun o-real-p (x)
  (cond ((o-finp x)
         (and
          (realp X)
          (<= 0 x)))
        ((consp (car x))
         (and (o-real-p (o-first-expt x))
              (if (acl2-numberp (o-first-expt x))
                  (<= 1 (o-first-expt x))
                t)
              (realp (o-first-coeff x))
              (<= 1 (o-first-coeff x))
              (o-real-p (o-rst x))
              (o<-1 (o-first-expt (o-rst x))
                    (o-first-expt x))))
        (t nil)))

; Recursively traverse
; a measure structure applying floor
; to the real values in the structure
; The intent is to convert a measure structure to
; an ordinal.

(defun o-floor1 (x)
  (cond ((o-finp x) (floor1 x))
        ((consp (car x))
         (make-ord (o-floor1 (o-first-expt x))
                   (floor1 (o-first-coeff x))
                   (o-floor1 (o-rst x))))
        (t nil)))

(defthm o<-1-floor1-neq-thm
  (implies
   (and
    (o-real-p x)
    (o-real-p y)
    (o<-1 x y))
   (not (equal (o-floor1 x) (o-floor1 y)))))

; The following theorem states that
; showing a measure structure x is less than y,
; using the o<-1 operator
; implies that the ordinals attained by
; applying o-floor1 to x and y, respectively,
; are less than each other.
; Hence, in our proof obligation, we need only
; show that (o<-1 x y), this theorem may then
; be applied to show the respective ordinals
; attained by applying o-floor1 are less
; than each other.

(defthm o<-1-floor1-o<-thm
  (implies
   (and
    (o-real-p x)
    (o-real-p y)
    (o<-1 x y))
   (o< (o-floor1 x) (o-floor1 y))))

(defthm floor1-posp
  (implies
   (and
    (realp x)
    (<= 1 x))
   (posp (floor1 x))))

(defthm o-floor1-non-zero
  (implies
   (and
    (o-real-p x)
    (o-real-p y)
    (o<-1 y x))
   (not (equal 0 (o-floor1 x)))))

(defthm o-real-p-caadr
  (implies
   (and
    (o-real-p x)
    (consp x)
    (consp (cdr x)))
   (o-real-p (caadr x))))

(defthm o-real-p-caadr-2
  (implies
   (and
    (o-real-p x)
    (consp x))
   (equal (caar (o-floor1 x)) (o-floor1 (caar x))))
  :hints (("Goal" :do-not-induct t)))

(defthm o-floor1-consp
  (implies
   (and
    (consp x)
    (o-real-p x))
   (consp (o-floor1 x))))

(defthm consp-not-zero
  (implies
   (consp x)
   (not (equal 0 x))))

; The following states that if x is a measure
; structure, then (o-floor1 x) is an ordinal.

(defthm o-floor1-thm
  (implies
   (o-real-p x)
   (o-p (o-floor1 x)))
  :hints (("Goal" :do-not '(generalize)
           :induct (o-real-p x)
           :do-not-induct t)))
