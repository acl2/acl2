; A lightweight book about the built-in function expt.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This books deals with EXPT applied to an arbitrary first argument (the base
;; of the exponentiation).  The book expt2.lisp deals with the special case
;; when the base is 2.

(local (include-book "times-and-divide"))
(local (include-book "times"))
(local (include-book "minus"))
(local (include-book "divide"))
(local (include-book "plus"))
(local (include-book "even-and-odd"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(in-theory (disable expt))

;; Note that there are several built-in :type-prescription rules about expt:
;; (:type-prescription expt)
;; rationalp-expt-type-prescription
;; expt-type-prescription-non-zero-base

(defthm integerp-of-expt
  (implies (and (integerp r)
                (<= 0 i))
           (integerp (expt r i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm natp-of-expt
  (implies (and (natp r)
                (<= 0 i))
           (natp (expt r i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm <-of-0-and-expt
  (implies (and (< 0 r)
                (rationalp r))
           (< 0 (expt r i)))
  :hints (("Goal" :in-theory (enable zip expt))))

(defthm <=-of-0-and-expt
  (implies (and (<= 0 r)
                (rationalp r))
           (<= 0 (expt r i)))
  :hints (("Goal" :in-theory (enable zip expt))))

(local
 ;; induction function that subtracts 2 each time
 (defun ind-sub2 (i)
   (if (or (zip i)
           (equal 1 i)
           (equal -1 i))
       i
     (if (< i 0)
         (ind-sub2 (+ 2 i))
       (ind-sub2 (+ -2 i))))))

(defthm <-of-expt-and-0
  (implies (and (rationalp r)
                (integerp i))
           (equal (< (expt r i) 0)
                  (and (< r 0)
                       (not (evenp i)))))
  :hints (("Goal" :induct (ind-sub2 i)
           :expand (expt r i)
           :in-theory (enable expt zip))))

(defthm equal-of-0-and-expt
  (equal (equal 0 (expt r i))
         (and (equal 0 (fix r))
              (integerp i)
              (not (equal 0 i)) ;since r^0 = 1
              ))
  :hints (("Goal" :in-theory (enable zip expt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-expt-type
  (implies (and (integerp r)
                (<= 0 i))
           (integerp (expt r i)))
  :rule-classes :type-prescription)

(defthm <-of-0-and-expt-type
  (implies (and (< 0 r)
                (rationalp r))
           (< 0 (expt r i)))
  :rule-classes :type-prescription)

(defthm <=-of-0-and-expt-type
  (implies (and (<= 0 r)
                (rationalp r))
           (<= 0 (expt r i)))
  :rule-classes :type-prescription)

;; the base can be positive or negative
(defthm expt-type-even-exponent-1
  (implies (and (evenp i)
                (not (equal r 0))
                (rationalp r))
           (< 0 (expt r i)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (ind-sub2 i)
           :expand (expt r i))))

;; the base can be positive, negative, or 0
(defthm expt-type-even-exponent-2
  (implies (and (evenp i)
                (rationalp r))
           (<= 0 (expt r i)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (ind-sub2 i)
           :expand (expt r i)
           :in-theory (enable expt))))

;; The cases of positive r and non-negative r are covered elsewhere.
(defthm expt-type-odd-exponent-negative-base
  (implies (and (not (evenp i))
                (< r 0)
                (rationalp r)
                (integerp i))
           (< (expt r i) 0))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm expt-of-0-arg1
  (equal (expt 0 i)
         (if (zip i)
             1
           0))
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-of-0-arg2
  (equal (expt r 0)
         1)
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-of-1-arg1
  (equal (expt 1 i)
         1)
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-of-1-arg2
  (equal (expt r 1)
         (fix r))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd expt-of-+-of--1-arg2
  (implies (and (integerp i)
                (acl2-numberp r))
           (equal (expt r (+ -1 i))
                  (if (equal 0 r)
                      (if (equal 1 i) 1 0)
                    (* (/ (fix r)) (expt r i)))))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd expt-of-+-of-1-arg2
  (implies (and (integerp i)
                (acl2-numberp r))
           (equal (expt r (+ 1 i))
                  (if (equal 0 r)
                      (if (equal -1 i) 1 0)
                    (* (fix r) (expt r i)))))
  :hints (("Goal" :in-theory (enable expt))))

(local
 (DEFUN EXPT-double-induct (R I j)
   (DECLARE (XARGS :MEASURE (ABS (IFIX I))))
   (COND ((ZIP I) j)
         ((= (FIX R) 0) 0)
         ((> I 0) (* R (EXPT-double-induct R (+ I -1) (+ j -1))))
         (T (* (/ R) (EXPT-double-induct R (+ I 1) (+ j 1)))))))

;try to enable?
(defthmd expt-of-+
  (implies (and (integerp i1)
                (integerp i2))
           (equal (expt r (+ i1 i2))
                  (if (equal 0 (fix r))
                      (if (equal (+ i1 i2) 0)
                          1 ;0^0=1
                        0)
                    (* (expt r i1)
                       (expt r i2)))))
  :hints (("Goal" :induct (EXPT-double-induct r i1 2)
;           :expand (EXPT R (+ I1 I2))
           :expand (EXPT R (+ 1 I1 I2))
           :in-theory (enable expt zp expt-of-+-of--1-arg2))))

;; Opposite of expt-of-+
(defthmd *-of-expt-and-expt-same-base
  (implies (and (integerp i1)
                (integerp i2))
           (equal (* (expt r i1) (expt r i2))
                  (if (equal (fix r) 0)
                      (if (and (equal i1 0)
                               (equal i2 0))
                          1 0)
                    (expt r (+ i1 i2)))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(theory-invariant (incompatible (:rewrite expt-of-+)
                                (:rewrite *-of-expt-and-expt-same-base)))

;todo: param names
(defthm *-of-expt-combine-lemma
  (implies (and (integerp x)
                (integerp y)
                (acl2-numberp r)
                (not (equal 0 r)))
           (equal (* (expt r (+ -1 x))
                     (expt r (+ 1 y)))
                  (* (expt r x) (expt r y))))
  :hints (("Goal" :in-theory (enable expt expt-of-+-of-1-arg2
                                     expt-of-+-of--1-arg2))))

(local
 (defthm integerp-of-expt-helper
   (implies (posp r)
            (equal (integerp (expt r i))
                   (or (equal r 1)
                       (not (integerp i))
                       (<= 0 i))))
   :hints (("Goal" :cases ((equal 1 r))
            :in-theory (enable expt expt-of-+)))))

(defthm integerp-of-expt-when-natp
  (implies (natp r)
           (equal (integerp (expt r i))
                  (or (equal r 0)
                      (equal r 1)
                      (not (integerp i))
                      (<= 0 i))))
  :hints (("Goal" :cases ((equal 1 r))
           :in-theory (enable expt))))

(defthm expt-of--1-arg1
  (implies (integerp i)
           (equal (expt -1 i)
                  (if (evenp i)
                      1
                    -1)))
  :hints (("Goal" :in-theory (enable expt))))

;expt-minus would have a name clash with rtl
(defthm expt-of-unary--
  (equal (expt r (- i))
         (/ (expt r i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd /-of-expt
  (equal (/ (expt r i))
         (expt r (- i)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(theory-invariant (incompatible (:rewrite expt-of-unary--) (:rewrite /-of-expt)))

;seems helpful (e.g., in proving that 2^(i-1) + x < 2^i when x < 2^(i-1)).
(defthm expt-half-linear
  (implies (integerp i)
           (equal (expt 2 i)
                  (+ (expt 2 (+ -1 i))
                     (expt 2 (+ -1 i)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt-of-+))))

;gen the 1
(defthm <-of-1-and-expt
  (implies (integerp n)
           (equal (< 1 (expt 2 n))
                  (< 0 n)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm <-of-1-and-expt-gen
  (implies (and (< 1 r)
                (integerp i)
                (rationalp r)
                )
           (equal (< 1 (expt r i))
                  (< 0 i)))
  :hints (("Goal" :in-theory (e/d (expt)
                                  (commutativity-2-of-*
                                   iff ; saves 3 seconds
                                   )))))

(defthm expt-of-*
  (equal (expt (* r1 r2) i)
         (* (expt r1 i)
            (expt r2 i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd *-of-expt-and-expt-same-exponent
  (equal (* (expt r1 i)
            (expt r2 i))
         (expt (* r1 r2) i)))

(theory-invariant (incompatible (:rewrite expt-of-*)
                                (:rewrite *-of-expt-and-expt-same-exponent)))

;gen?
(local
 (defthm <-of-expt-and-1-small-base
  (implies (and (< r 1)
                (<= 0 r)
                (rationalp r)
                (posp i))
           (< (expt r i) 1))
  :hints (("Goal" :in-theory (enable expt)))))

;; Disabled because we have <-of-expt-and-expt.
(defthmd expt-monotone-strong
  (implies (and (< i j)
                (< 1 r) ; this case
                (rationalp r)
                (integerp i)
                (integerp j))
           (< (expt r i) (expt r j)))
  :hints (("Goal" :in-theory (enable expt-of-+ zip)
           :induct (EXPT-double-induct r i j))))

(defthm expt-type-small-base-negative-exponent
  (implies (and (< r 1) ; unusual
                (< i 0) ; unusual
                (< 0 r)
                (integerp i)
                (rationalp r))
           (< 1 (expt r i)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-type-small-base-non-positive-exponent
  (implies (and (<= r 1) ; unusual
                (<= i 0) ; unusual
                (< 0 r)
                (integerp i)
                (rationalp r))
           (<= 1 (expt r i)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable expt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm <-of-expt-and-expt-small-base
   (implies (and (< r 1) ; this case
                 (< 0 r) ; this case
                 (rationalp r)
                 (integerp i1)
                 (integerp i2))
            (equal (< (expt r i1) (expt r i2))
                   (< i2 i1)))
   :hints (("Goal" :in-theory (enable expt-of-+ zip)
            :induct (expt-double-induct r i2 i1)))))

(local
 (defthmd <-of-expt-and-expt-large-base-helper
  (implies (and (< (expt r i) (expt r j))
                (< 1 r)
                (rationalp r)
                (integerp i)
                (integerp j))
           (< i j))
  :hints (("Goal" :in-theory (enable expt-of-+ zip)
           :induct (expt-double-induct r i j)))))

(local
 (defthm <-of-expt-and-expt-large-base
   (implies (and (< 1 r)
                 (rationalp r)
                 (integerp i)
                 (integerp j))
            (equal (< (expt r i) (expt r j))
                   (< i j)))
   :hints (("Goal" :use (:instance <-of-expt-and-expt-large-base-helper
                                   (i 0)
                                   (j (+ (- i) j)))
            :in-theory (e/d (expt-monotone-strong expt-of-+)
                            (<-of-1-and-expt-gen))))))

;todo: rename vars
(defthm <-of-expt-and-expt-same-base
  (implies (and (< 0 r) ; todo: handle 0?
                (rationalp r)
                (integerp i)
                (integerp j))
           (equal (< (expt r i) (expt r j))
                  (if (< r 1)
                      (< j i)
                    (if (equal r 1)
                        nil
                      ;; usual case:
                      (< i j))))))

(defthm <-of-expt-and-expt-same-base-linear
  (implies (and (< i1 i2)
                ;; prevent huge expt computations:
                (syntaxp (and (not (and (quotep r)
                                        (quotep i1)
                                        (< 1000 (unquote i1))))
                              (not (and (quotep r)
                                        (quotep i2)
                                        (< 1000 (unquote i2))))))
                (< 1 r)
                (rationalp r)
                (integerp i1)
                (integerp i2))
           (< (expt r i1) (expt r i2)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt-monotone-strong))))

(defthm <=-of-expt-and-expt-same-base-linear
  (implies (and (<= i1 i2)
                ;; prevent huge expt computations:
                (syntaxp (and (not (and (quotep r)
                                        (quotep i1)
                                        (< 1000 (unquote i1))))
                              (not (and (quotep r)
                                        (quotep i2)
                                        (< 1000 (unquote i2))))))
                (<= 1 r)
                (rationalp r)
                (integerp i1)
                (integerp i2))
           (<= (expt r i1) (expt r i2)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt-monotone-strong))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm expt-of-/
  (equal (expt (/ x y) i)
         (/ (expt x i) (expt y i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-of-unary-/-arg1
  (equal (expt (/ r) i)
         (/ (expt r i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-of-*-of-expt-and-expt
  (implies (and (integerp i)
                (integerp j))
           (equal (integerp (* (expt 2 i) (expt 2 j)))
                  (<= 0 (+ i j))))
  :hints (("Goal" :in-theory (e/d (expt-of-+)
                                  (;integerp-of-expt
                                   ;;<-OF-0-AND-EXPT
                                   integerp-of-expt-when-natp
                                   INTEGERP-OF-EXPT-HELPER))
           :use (:instance integerp-of-expt-when-natp (r 2) (i (+ i j))))))

(defthm integerp-of-*-of-expt-and-/-of-expt
  (implies (and (integerp i)
                (integerp j))
           (equal (integerp (* (expt 2 i) (/ (expt 2 j))))
                  (<= j i)))
  :hints (("Goal" :in-theory (e/d (expt-of-+)
                                  (;integerp-of-expt
                                   ;;<-OF-0-AND-EXPT
                                   integerp-of-expt-when-natp
                                   INTEGERP-OF-EXPT-HELPER))
           :use (:instance integerp-of-expt-when-natp (r 2) (i (+ i (- j)))))))

;gen the 1
(defthm *-of-expt-and-expt-of-1minus
  (implies (integerp size)
           (equal (* (expt 2 size) (expt 2 (+ 1 (- size))))
                  2))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm expt-of---arg1
  (implies (and (integerp i)
                (rationalp r))
           (equal (expt (- r) i)
                  (if (evenp i)
                      (expt r i)
                    (- (expt r i)))))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd expt-when-<-of-0
  (implies (and (< r 0)
                (integerp i)
                (rationalp i))
           (equal (expt r i)
                  (if (evenp i)
                      (expt (- r) i)
                    (- (expt (- r) i)))))
  :hints (("Goal" :in-theory (enable expt))))

;move? gen?
(local
 (defthm <-of-*-and-1
   (implies (and (< x 1)
                 (< y 1)
                 (rationalp x)
                 (rationalp y)
                 (<= 0 x)
                 (<= 0 y))
            (< (* x y) 1))
   :rule-classes :linear
   :hints (("Goal" :nonlinearp t))))

;; TODO: Make some of these non-local?

(local
 (defthmd <-of-expt-and-1-linear
   (implies (and (< r 1)
                 (<= 0 r)
                 (rationalp r)
                 (posp i))
            (< (expt r i) 1))
   :rule-classes :linear))

(local
 (defthmd <-of-1-and-expt-linear
  (implies (and (< i 0) ; this case
                (< r 1)
                (< 0 r)
                (rationalp r)
                (integerp i))
           (< 1 (expt r i)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt)))))

(local
 (defthmd <=-of-1-and-expt-linear
  (implies (and (<= i 0) ; this case
                (< r 1)
                (< 0 r)
                (rationalp r)
                (integerp i))
           (<= 1 (expt r i)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt)))))

(local
 (defthmd <-of-1-and-expt-linear-alt
  (implies (and (< i 0) ; this case
                (< 1 r) ; this case
                (rationalp r)
                (integerp i))
           (< (expt r i) 1))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt)))))

(local
 (defthmd <=-of-1-and-expt-linear-alt
  (implies (and (<= i 0) ; this case
                (< 1 r) ; this case
                (rationalp r)
                (integerp i))
           (<= (expt r i) 1))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt)))))

;; (local
;;  ;; gen to compare a product with any constant, given a bound on one factor
;;  (defthm not-equal-of-1-helper
;;    (implies (and (< x 1)
;;                  (< y 1)
;;                  (rationalp x)
;;                  (<= 0 x)
;;                  (rationalp y)
;;                  (<= 0 y))
;;             (not (equal (* x y) 1)))
;;    :hints (("Goal" :nonlinearp t))))

;; (local
;;  (defthm not-equal-of-1-helper-2
;;    (implies (and (< 1 x)
;;                  (< 1 y)
;;                  (rationalp x)
;;                  (<= 0 x)
;;                  (rationalp y)
;;                  (<= 0 y))
;;             (not (equal (* x y) 1)))
;;    :hints (("Goal" :nonlinearp t))))

(local
 (defthm <-of-expt-same-linear
   (implies (and (< 1 r)
                 (< 1 i)
                 (integerp i)
                 (rationalp r))
            (< r (expt r i)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable expt)))
   ))

(defthm equal-of-expt-and-1
  (implies (and (rationalp r)
                (<= 0 r) ; gen?
                (integerp i))
           (equal (equal (expt r i) 1)
                  (or (equal r 1)
                      (equal i 0)
                      ;; (and (equal r -1)
                      ;;      (evenp i))
                      )))
  :hints (("subgoal *1/4" :use (<-of-expt-and-1-linear
                                (:instance  <-of-1-and-expt-linear-alt (i (+ 1 i)))
                                <-of-1-and-expt-linear
                                (:instance <-of-expt-same-linear (i (+ 1 i))))
           :cases ((equal 1 i)
                   (and (not (equal 1 i)) (< r 1))
                   (and (not (equal 1 i)) (> r 1)))
           :nonlinearp t)
          ("subgoal *1/3" :use (<-of-expt-and-1-linear
                                (:instance  <-of-1-and-expt-linear-alt (i (+ 1 i)))
                                <-of-1-and-expt-linear
                                (:instance <-of-expt-same-linear (i (+ 1 i))))

           :nonlinearp t)
          ("Goal" :in-theory (enable expt)
           :induct t
           )))

(local
 (defthmd equal-of-expt-same-helper
   (implies (and (<= 0 r)     ; todo: gen
                 (rationalp r) ;(acl2-numberp r)
                 (integerp i))
            (equal (equal (expt r i) r)
                   (if (equal r 0)
                       (not (equal 0 i))
                     (if (equal r 1)
                         t
                       (equal i 1)))))
   :hints (("subgoal *1/4" :cases ((< r 1) (> r 1)))
           ("Goal" :induct t
            :in-theory (enable expt
                               zip
                               <=-of-1-and-expt-linear-alt
                               <=-of-1-and-expt-linear)))))

(defthm equal-of-expt-same
  (implies (and (rationalp r) ;(acl2-numberp r)
                (integerp i))
           (equal (equal (expt r i) r)
                  ;; We split into cases based on R because R is often a constant:
                  (if (equal r 0)
                      (not (equal 0 i))
                    (if (equal r 1)
                        t
                      (if (equal r -1)
                          (oddp i)
                        (equal i 1))))))
  :hints (("Goal" :use (equal-of-expt-same-helper
                        (:instance equal-of-expt-same-helper (r (- r)))
                        expt-when-<-of-0)
           :in-theory (disable EXPT-OF---ARG1))))

(defthm expt-when-not-acl2-numberp-cheap
  (implies (not (acl2-numberp r))
           (equal (expt r i)
                  (if (zip i) 1 0)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-when-not-integerp-arg1-cheap
  (implies (not (integerp i))
           (equal (expt r i)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd expt-of-*-arg2
  (implies (and (integerp i1)
                (integerp i2))
           (equal (expt r (* i1 i2))
                  (expt (expt r i1) i2)))
  :hints (("Goal" :in-theory (enable (:i expt) expt-of-+))))

;; (r^i1)^i2 = r^(i1*i2)
(defthm expt-of-expt-arg1
  (implies (and (integerp i1)
                (integerp i2))
           (equal (expt (expt r i1) i2)
                  (expt r (* i1 i2))))
  :hints (("Goal" :by expt-of-*-arg2)))

(theory-invariant (incompatible (:rewrite expt-of-expt-arg1) (:rewrite expt-of-*-arg2)))

;; Seems good to always leave this version enabled.
(defthm expt-of-expt-arg1-constants
  (implies (and (syntaxp (and (quotep i1)
                              (quotep i2)
                              ;; prevent huge calls to expt:
                              (<= (* (unquote i1) (unquote i2)) 1000)))
                (integerp i1)
                (integerp i2))
           (equal (expt (expt r i1) i2)
                  (expt r (* i1 i2)))))

(defthm <-of-expt-and-expt-same-exponents
  (implies (and (rationalp r1)
                (<= 0 r1)
                (rationalp r2)
                (<= 0 r2)
                (integerp i)
                (<= 0 i) ; todo: gen?
                )
           (equal (< (expt r1 i) (expt r2 i))
                  (if (equal 0 i)
                      nil
                    (< r1 r2))))
  :hints (("subgoal *1/6" :cases ((< r1 r2)))
          ("Goal" :in-theory (enable expt))))

(defthm <-of-expt-and-expt-same-exponents-negative
  (implies (and (< i 0) ; this case
                (rationalp r1)
                (<= 1 r1) ; note this
                (rationalp r2)
                (<= 1 r2) ; note this
                (integerp i))
           (equal (< (expt r1 i) (expt r2 i))
                  (< r2 r1)))
  :hints (("subgoal *1/8" :cases ((< r2 r1)))
          ("Goal" :in-theory (enable expt))))

(defthm <-of-expt-and-expt-same-exponents-middle
  (implies (and (< i 0) ; this case
                (rationalp r1)
                (< 0 r1) ; note this
                (< r1 1) ; note this
                (rationalp r2)
                (< 0 r2) ; note this
                (< r2 1) ; note this
                (integerp i))
           (equal (< (expt r1 i) (expt r2 i))
                  (< r2 r1)))
  :hints (("subgoal *1/8" :cases ((< r2 r1)))
          ("Goal" :in-theory (enable expt))))

;; this is not a very good :type-prescription rule
;; (defthm <-of-1-and-expt-type-1
;;   (implies (and (< i 0)
;;                 (< r 1)
;;                 (< 0 r) ;gen
;;                 (rationalp r)
;;                 (integerp i))
;;            (< 1 (expt r i)))
;;   :rule-classes :type-prescription
;;   :hints (("Goal" :in-theory (enable expt))))

;; negative exponent, r in (0,1)
(defthm expt-when-negative-exponent-linear-1
  (implies (and (< i 0)
                (< r 1)
                (< 0 r)
                (rationalp r)
                (integerp i))
           (< 1 (expt r i)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt))))

;; negative exponent, r in (0,1]
(defthm expt-when-negative-exponent-linear-2
  (implies (and (<= i 0) ; allows i=0 since conclusion uses <=
                (<= r 1)
                (< 0 r)
                (rationalp r)
                (integerp i))
           (<= 1 (expt r i)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt))))

;; negative exponent, r > 1
;todo: why can't this be a :type-prescription rule?
(defthm expt-when-negative-exponent-linear-3
  (implies (and (< i 0)
                (< 1 r)
                (rationalp r)
                (integerp i))
           (< (expt r i) 1))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt))))

;; negative exponent, r >= 1
(defthm expt-when-negative-exponent-linear-4
  (implies (and (<= i 0) ; allows i=0 since conclusion uses <=
                (<= 1 r)
                (rationalp r)
                (integerp i))
           (<= (expt r i) 1))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt))))

(defthm <-of-expt-and-expt-same-exponents-gen
  (implies (and (< 0 r1) ; todo
                (< 0 r2) ; todo
                (rationalp r1)
                (rationalp r2)
                (integerp i))
           (equal (< (expt r1 i) (expt r2 i))
                  (if (equal 0 i)
                      nil ; both sides are equal to 1
                    (if (< 0 i)
                        (< r1 r2)
                      ;; i is negative:
                      (< r2 r1)))))
  :hints (("Goal" :cases ((equal i 0)
                          (and (not (equal i 0)) (<= 1 r1) (not (<= 1 r2)))
                          (and (not (equal i 0)) (<= 1 r1) (<= 1 r2))
                          (and (not (equal i 0)) (not (<= 1 r1)) (not (<= 1 r2)))
                          (and (not (equal i 0)) (not (<= 1 r1)) (<= 1 r2))))))

(defthm <-of-expt-and-expt-same-exponents-linear
  (implies (and (< 0 i) ; this case
                (< r1 r2)
                (rationalp r1)
                (<= 0 r1)
                (rationalp r2)
                (<= 0 r2)
                (integerp i))
           (< (expt r1 i) (expt r2 i)))
  :rule-classes :linear)

(defthm <-of-expt-and-expt-same-exponents-linear-negative-exponent
  (implies (and (< i 0) ; this case
                (< r1 r2)
                (rationalp r1)
                (< 0 r1)
                (rationalp r2)
                (< 0 r2)
                (integerp i))
           (< (expt r2 i) (expt r1 i)))
  :rule-classes :linear
  :hints (("Goal" :cases ((equal 0 r1)))))

;gen?
(local
 (defthm equal-of-expt-and-expt-same-exponent-helper
   (implies (and (<= 0 r1)
                 (<= 0 r2)
                 (rationalp r1)
                 (rationalp r2)
                 (integerp i))
            (equal (equal (expt r1 i) (expt r2 i))
                   (if (equal i 0)
                       t
                     (equal r1 r2))))
   :hints (("Goal" :cases ((and (= 0 r1) (< i 0))
                           (and (= 0 r2) (< i 0))
                           (and (not (= 0 r1)) (not (= 0 r2)) (< r1 r2) (< i 0))
                           (and (not (= 0 r1)) (not (= 0 r2)) (= r1 r2) (< i 0))
                           (and (not (= 0 r1)) (not (= 0 r2)) (< r2 r1) (< i 0))
                           (and (< r1 r2) (< 0 i))
                           (and (= r1 r2) (< 0 i))
                           (and (< r2 r1) (< 0 i))
                           )))))

(defthm equal-of-expt-and-expt-same-exponent
  (implies (and (rationalp r1)
                (rationalp r2)
                (integerp i))
           (equal (equal (expt r1 i) (expt r2 i))
                  (if (equal i 0)
                      t ; since both sides are equal to 1
                    (if (evenp i)
                        (equal (abs r1) (abs r2))
                      (equal r1 r2)))))
  :hints (("Goal" :cases ((evenp i))
           :in-theory (disable equal-of-expt-and-expt-same-exponent-helper)
           :use ((:instance equal-of-expt-and-expt-same-exponent-helper)
                 (:instance equal-of-expt-and-expt-same-exponent-helper (r1 (- r1)) (r2 (- r2)))
                 (:instance equal-of-expt-and-expt-same-exponent-helper (r1 (- r1)) (r2 r2))
                 (:instance equal-of-expt-and-expt-same-exponent-helper (r1 r1) (r2 (- r2)))))))


(local
 (defthm equal-of-expt-and-expt-same-base-small-base
   (implies (and (rationalp r)
                 (< 0 r) ; todo: allow 0 but consider 0^1
                 (< r 1)
                 (integerp i1)
                 (integerp i2))
            (equal (equal (expt r i1) (expt r i2))
                   (or (equal r 0)
                       (equal i1 i2))))
   :hints (("Goal" :use ((:instance <-of-expt-and-expt-small-base)
                         (:instance <-of-expt-and-expt-small-base (i1 i2) (i2 i1)))
            :in-theory (e/d (zip) (<-of-expt-and-expt-small-base
                                   <-of-expt-and-expt-same-base))))))

(local
 (defthm equal-of-expt-and-expt-same-base-large-base
   (implies (and (rationalp r)
                 (<= 1 r) ;this case
                 (integerp i1)
                 (integerp i2))
            (equal (equal (expt r i1) (expt r i2))
                   (or (equal r 1)
                       (equal i1 i2))))
   :hints (("Goal" :cases ((< i1 i2) (< i2 i1))))))

(local
 (defthm equal-of-expt-and-expt-same-base-helper
   (implies (and (rationalp r)
                 (<= 0 r) ; this case
                 (integerp i1)
                 (integerp i2))
            (equal (equal (expt r i1) (expt r i2))
                   (if (equal r 0)
                       ;; either both exponents are 0, giving 0^0=1, or both are not 0, giving 0.
                       (iff (equal i1 0) (equal i2 0))
                     (or (equal r 1)
                         (equal i1 i2)))))
   :hints (("Goal" :cases ((< r 1))))))

(defthm equal-of-expt-and-expt-same-base
  (implies (and (rationalp r)
                (integerp i1)
                (integerp i2))
           (equal (equal (expt r i1) (expt r i2))
                  (if (equal r 0)
                      ;; either both exponents are 0, giving 0^0=1, or both are not 0, giving 0.
                      (iff (equal i1 0) (equal i2 0))
                    (if (equal r 1)
                        t
                      (if (equal r -1)
                          (iff (evenp i1) (evenp i2))
                        (equal i1 i2))))))
  :hints (("Goal" :use ((:instance equal-of-expt-and-expt-same-base-helper)
                        (:instance equal-of-expt-and-expt-same-base-helper (r (- r))))
           :in-theory (disable equal-of-expt-and-expt-same-base-helper))))

;; could loop with the definition of expt?
(defthmd *-of-expt-of-one-less
  (implies (integerp i)
           (equal (* r (expt r (+ -1 i)))
                  (if (equal (fix r) 0)
                      0
                    (expt r i))))
  :hints (("Goal" :in-theory (enable expt))))

(defthm *-of-expt-and-expr-of-+-of---same
  (implies (and (integerp i)
                (integerp j)
                (acl2-numberp r)
                (not (equal 0 r)) ;gen?
                )
           (equal (* (expt r i) (expt r (+ j (- i))))
                  (expt r j))) :hints (("Goal" :in-theory (enable expt-of-+))))
