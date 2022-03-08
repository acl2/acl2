; A lightweight book about the built-in function expt.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
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

(local (include-book "times-and-divides"))
(local (include-book "times"))
(local (include-book "plus"))
(local (include-book "floor"))

(in-theory (disable expt))

(defthm integerp-of-expt
  (implies (and (integerp r)
                (<= 0 i))
           (integerp (expt r i)))
  :hints (("Goal" :in-theory (enable expt))))

;; Note that RATIONALP-EXPT-TYPE-PRESCRIPTION and
;; EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE are built-in.

(defthm natp-of-expt
  (implies (and (natp r)
                (<= 0 i))
           (natp (expt r i)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-of-expt-type
  (implies (and (integerp r)
                (<= 0 i))
           (integerp (expt r i)))
  :rule-classes :type-prescription)

(defthm <-of-0-and-expt
  (implies (and (< 0 r)
                (rationalp r))
           (< 0 (expt r i)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable zip expt))))

(defthm <=-of-0-and-expt
  (implies (and (<= 0 r)
                (rationalp r))
           (<= 0 (expt r i)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable zip expt))))

(defthm equal-of-0-and-expt
  (equal (equal 0 (expt r i))
         (and (equal 0 (fix r))
              (integerp i)
              (not (equal 0 i)) ;since r^0 = 1
              ))
  :hints (("Goal" :in-theory (enable zip expt))))

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
           :in-theory (enable expt zp))))

;todo: param names
(defthm *-of-expt-combine-lemma
  (implies (and (integerp x)
                (integerp y)
                (acl2-numberp r)
                (not (equal 0 r)))
           (equal (* (expt r (+ -1 x))
                     (expt r (+ 1 y)))
                  (* (expt r x) (expt r y))))
  :hints (("Goal" :in-theory (enable expt))))

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



;expt-minus would have a name clash with rtl
(defthm expt-of-unary--
  (equal (expt r (- i))
         (/ (expt r i)))
  :hints (("Goal" :in-theory (enable expt))))

;seems helpful (e.g., in proving that 2^(i-1) + x < 2^i when x < 2^(i-1)).
(defthm expt-half-linear
  (implies (integerp i)
           (equal (expt 2 i)
                  (+ (expt 2 (+ -1 i))
                     (expt 2 (+ -1 i)))))
  :hints (("Goal" :in-theory (enable expt-of-+
                              )))
  :rule-classes :linear)

;gen the 1
(defthm <-of-1-and-expt
  (implies (integerp n)
           (equal (< 1 (expt 2 n))
                  (< 0 n)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm <-of-1-and-expt-gen
  (implies (and (< 1 r)
                (integerp n)
                (rationalp r)
                )
           (equal (< 1 (expt r n))
                  (< 0 n)))
  :hints (("Subgoal *1/4" :cases ((< 1 N)))
          ("Goal" :in-theory (enable expt))))

;where should this go?
(defthm floor-of-expt-2-and-2
  (implies (integerp n)
           (equal (floor (expt 2 n) 2)
                  (if (posp n)
                      (expt 2 (+ -1 n))
                    0)))
  :hints (("Goal" :in-theory (e/d (expt) ()))))

(defthm expt-of-*
  (equal (expt (* r1 r2) i)
         (* (expt r1 i)
            (expt r2 i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthmd expt-monotone-strong
  (implies (and (< i j)
                (< 1 r)
                (rationalp r)
                (integerp i)
                (integerp j))
           (< (expt r i) (expt r j)))
  :hints (("Goal" :in-theory (enable expt-of-+ zip)
           :induct (EXPT-double-induct r i j))))

(defthmd <-of-expt-and-expt-helper
  (implies (and (< (expt r i) (expt r j))
                (< 1 r)
                (rationalp r)
                (integerp i)
                (integerp j))
           (< i j))
  :hints (("Goal" :in-theory (enable expt-of-+ zip)
           :induct (expt-double-induct r i j))))

(defthm <-of-expt-and-expt
  (implies (and (< 1 r)
                (rationalp r)
                (integerp i)
                (integerp j))
           (equal (< (expt r i) (expt r j))
                  (< i j)))
  :hints (("Goal" :use (:instance <-of-expt-and-expt-helper
                                  (i 0)
                                  (j (+ (- I) J)))
           :in-theory (e/d (expt-monotone-strong expt-of-+)
                           (<-OF-1-AND-EXPT-GEN)))))

(defthm expt-of-/
  (equal (expt (/ x y) i)
         (/ (expt x i) (expt y i)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-of-*-of-expt-and-expt
  (implies (and (integerp i)
                (integerp j))
           (equal (integerp (* (expt 2 i) (expt 2 j)))
                  (<= 0 (+ i j))))
  :hints (("Goal" :in-theory (e/d (expt-of-+)
                                  ( ;integerp-of-expt
                                   ;;<-OF-0-AND-EXPT
                                   integerp-of-expt-when-natp
                                   INTEGERP-OF-EXPT-HELPER))
           :use (:instance integerp-of-expt-when-natp (r 2) (i (+ i j))))))

;gen the 1
(defthm *-of-expt-and-expt-of-1minus
  (implies (integerp size)
           (equal (* (expt 2 size) (expt 2 (+ 1 (- size))))
                  2))
  :hints (("Goal" :in-theory (enable expt-of-+))))
