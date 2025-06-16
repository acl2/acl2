; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "kestrel/utilities/digits-any-base/core" :dir :system)

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Karatsuba's multiplication algorithm
; (see https://en.wikipedia.org/wiki/Karatsuba_algorithm).
; We capture the algorithm as a function that takes a base,
; two equal-length lists of digits in that base,
; and the number of low digits,
; and returns the product of the two numbers using Karatsuba's calculation.
; A theorem shows that this is indeed the product.

; We actually define two functions, and prove two theorems:
; one for little endian digits, one for big endian digits.
; The one for big endian is a little less streamlined,
; due to the fact that n is the number of digits
; but len - n must be used for take and nthcdr.

; The ACL2 proof works by decomposing the digits
; via acl2::append-of-take-and-nthcdr,
; enabling acl2::lendian=>nat-of-append or acl2::bendian=>nat-of-append
; to bring out the values of the digit chunks,
; and then arithmetic rules (from arithmetic-3, but other may work)
; take care of additions and multiplications.

; See babbage-multiplication.lisp for a related multiplication method,
; also described in the Wikipedia page mentioned above.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define karatsuba-mul-lendian ((base acl2::dab-basep)
                               (x-digits (acl2::dab-digit-listp base x-digits))
                               (y-digits (acl2::dab-digit-listp base y-digits))
                               (n natp))
  :guard (and (equal (len y-digits)
                     (len x-digits))
              (< n (len x-digits)))
  :returns (product natp)
  (b* ((base (acl2::dab-base-fix base))
       (n (nfix n))
       (x0 (acl2::lendian=>nat base (take n x-digits)))
       (y0 (acl2::lendian=>nat base (take n y-digits)))
       (x1 (acl2::lendian=>nat base (nthcdr n x-digits)))
       (y1 (acl2::lendian=>nat base (nthcdr n y-digits)))
       (z0 (* x0 y0))
       (z2 (* x1 y1))
       (z1 (+ (* (+ x1 x0)
                 (+ y1 y0))
              (- z2)
              (- z0))))
    (+ z0
       (* z1 (expt base n))
       (* z2 (expt base (* 2 n)))))
  :hooks (:fix)
  ///

  (defruled karatsuba-mul-lendian-correct
    (implies (and (acl2::dab-basep base)
                  (equal (len y-digits) (len x-digits))
                  (natp n)
                  (< n (len x-digits)))
             (equal (karatsuba-mul-lendian base x-digits y-digits n)
                    (* (acl2::lendian=>nat base x-digits)
                       (acl2::lendian=>nat base y-digits))))
    :use ((:instance acl2::append-of-take-and-nthcdr (n n) (x x-digits))
          (:instance acl2::append-of-take-and-nthcdr (n n) (x y-digits)))
    :disable acl2::append-of-take-and-nthcdr
    :enable acl2::lendian=>nat-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define karatsuba-mul-bendian ((base acl2::dab-basep)
                               (x-digits (acl2::dab-digit-listp base x-digits))
                               (y-digits (acl2::dab-digit-listp base y-digits))
                               (n natp))
  :guard (and (equal (len y-digits)
                     (len x-digits))
              (< n (len x-digits)))
  :returns (product natp)
  (b* ((base (acl2::dab-base-fix base))
       (n (nfix n))
       (l-n (nfix (- (len x-digits) n)))
       (x0 (acl2::bendian=>nat base (nthcdr l-n x-digits)))
       (y0 (acl2::bendian=>nat base (nthcdr l-n y-digits)))
       (x1 (acl2::bendian=>nat base (take l-n x-digits)))
       (y1 (acl2::bendian=>nat base (take l-n y-digits)))
       (z0 (* x0 y0))
       (z2 (* x1 y1))
       (z1 (+ (* (+ x1 x0)
                 (+ y1 y0))
              (- z2)
              (- z0))))
    (+ z0
       (* z1 (expt base n))
       (* z2 (expt base (* 2 n)))))
  :hooks (:fix)
  ///

  (defruled karatsuba-mul-bendian-correct
    (implies (and (acl2::dab-basep base)
                  (equal (len y-digits) (len x-digits))
                  (natp n)
                  (< n (len x-digits)))
             (equal (karatsuba-mul-bendian base x-digits y-digits n)
                    (* (acl2::bendian=>nat base x-digits)
                       (acl2::bendian=>nat base y-digits))))
    :use ((:instance acl2::append-of-take-and-nthcdr
                     (n (- (len x-digits) n))
                     (x x-digits))
          (:instance acl2::append-of-take-and-nthcdr
                     (n (- (len x-digits) n))
                     (x y-digits)))
    :disable acl2::append-of-take-and-nthcdr
    :enable acl2::bendian=>nat-of-append))
