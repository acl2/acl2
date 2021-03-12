; A lightweight book about the built-in function expt.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This books deals with EXPT applied to an arbitrary first argument (the base
;; of the exponentiation).  The book expt2.lisp deals with the special case
;; when the base is 2.

(in-theory (disable expt))

(defthm integerp-of-expt
  (implies (and (integerp r)
                (<= 0 i))
           (integerp (expt r i)))
  :hints (("Goal" :in-theory (enable expt))))

(local (include-book "../../arithmetic-3/top"))

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
            :in-theory (enable expt)))))

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
                       (expt r i2))))))

;expt-minus would have a name clash with rtl
(defthm expt-of-unary--
  (equal (expt r (- i))
         (/ (expt r i))))

;seems helpful (e.g., in proving that 2^(i-1) + x < 2^i when x < 2^(i-1)).
(defthm expt-half-linear
  (implies (natp i)
           (equal (expt 2 i)
                  (+ (expt 2 (+ -1 i))
                     (expt 2 (+ -1 i)))))
  :hints (("Goal" :in-theory (enable ;expt-of-+
                              )))
  :rule-classes :linear)

;gen the 1
(defthm <-of-1-and-expt
  (implies (integerp n)
           (equal (< 1 (expt 2 n))
                  (< 0 n))))
