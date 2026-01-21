; Mixed theorems about getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "getbit")
(include-book "bitnot")
(include-book "kestrel/arithmetic-light/ceiling-of-lg-def" :dir :system)
(local (include-book "slice-rules"))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling-of-lg" :dir :system))

(defthm getbit-of-minus
  (implies (and (integerp x) ;todo: gen?
                (natp n)
                )
           (equal (getbit n (- x))
                  (if (EQUAL (BVCHOP N X) 0)
                      (getbit n x)
                    (bitnot (getbit n x)))))
  :hints (("Goal" ;; :cases ((integerp x))
           :in-theory (e/d (getbit bitnot)
                                  (

                                   ;BITNOT-OF-SLICE ;bozo
                                   ;BITXOR-OF-SLICE-ARG2 ;loops with defn getbit
                                   )))))

(local
 (DEFTHM GETBIT-OF-MINUS-EXPT-when->=
  (IMPLIES (AND (>= SIZE SIZE2)
                (NATP SIZE)
                (NATP SIZE2))
           (EQUAL (GETBIT SIZE (- (EXPT 2 SIZE2)))
                  1))))

(DEFTHM GETBIT-OF-MINUS-EXPT-gen
  (IMPLIES (AND (NATP SIZE)
                (NATP SIZE2))
           (EQUAL (GETBIT SIZE (- (EXPT 2 SIZE2)))
                  (if (>= SIZE SIZE2)
                      1
                    0))))

(defthmd floor-when-equal-of-floor-and-0-and->=
  (implies (and (equal (floor x y) 0)
                (<= xsmall x)
                (posp y)
                (natp n)
                (natp x)
                (natp xsmall))
           (equal (floor xsmall y)
                  0)))

(defthmd logtail-when-equal-of-logtail-and-0-and->=
  (implies (and (equal (logtail$inline n x) 0)
                (<= xsmall x)
                (natp n)
                (integerp x)
                (natp xsmall)
                )
           (equal (logtail$inline n xsmall)
                  0))
  :hints (("Goal" :in-theory (enable logtail
                                     floor-when-equal-of-floor-and-0-and->=))))

(defthm getbit-of-floor-when-top-bit-0
  (implies (and (equal (getbit n x) 0)
                (unsigned-byte-p (+ 1 n) x)
                (posp y)
                ;; (integerp x)
                (natp n))
           (equal (getbit n (floor x y))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit slice logtail-when-equal-of-logtail-and-0-and->=)
                                  (
                                   )))))

(defthm getbit-when-<=-of-constant-high
  (implies (and (syntaxp (quotep n)) ; to ensure this is cheap
                (<= k x) ; k is a free var
                (syntaxp (quotep k))
                (< n (ceiling-of-lg k))
                (<= (- (expt 2 (ceiling-of-lg k)) (expt 2 n)) k) ; k is a bit less than a power of 2
                (unsigned-byte-p (ceiling-of-lg k) x)
                (natp n))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when->=-of-high-helper
                                  (size (ceiling-of-lg k))))))

(defthm getbit-when-<-of-constant-high
  (implies (and (syntaxp (quotep n)) ; to ensure this is cheap
                (< k x) ; k is a free var
                (syntaxp (quotep k))
                (< n (ceiling-of-lg k))
                (<= (+ -1 (- (expt 2 (ceiling-of-lg k)) (expt 2 n))) k) ; k is a bit less than a power of 2
                (unsigned-byte-p (ceiling-of-lg k) x)
                (natp n))
           (equal (getbit n x)
                  1))
  :hints (("Goal" :use (:instance getbit-when->=-of-high-helper
                                  (size (ceiling-of-lg k))))))
