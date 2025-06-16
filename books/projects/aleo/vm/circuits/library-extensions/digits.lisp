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

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

(local (include-book "arithmetic"))
(local (include-book "bit-lists"))
(local (include-book "bit-lists-fixing"))
(local (include-book "lists"))

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled lebits=>nat-of-repeat-of-1
  (implies (natp n)
           (equal (lebits=>nat (repeat n 1))
                  (1- (expt 2 n))))
  :enable (lebits=>nat
           acl2::lendian=>nat-of-all-base-minus-1))

(defruled bebits=>nat-of-repeat-of-1
  (implies (natp n)
           (equal (bebits=>nat (repeat n 1))
                  (1- (expt 2 n))))
  :enable (bebits=>nat
           acl2::bendian=>nat-of-all-base-minus-1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled len-of-nat=>lebits*-is-integer-length
  (implies (natp n)
           (equal (len (nat=>lebits* n))
                  (integer-length n)))
  :enable (nat=>lebits*
           acl2::nat=>lendian*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nat=>lebits*-msb-is-1
  (implies (posp n)
           (equal (car (last (nat=>lebits* n)))
                  1))
  :enable (nat=>lebits*
           acl2::nat=>lendian*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If we have m bits, with m < n, where n is the number of bits of p,
; then the value of the bits is < 2^m, and thus <= 2^(n-1) by monotonicity,
; because m <= n-1 if m < n.
; But since p >= 2^(n-1) (see positive->=-expt2-of-integer-length-minus-1),
; then we must have that the value of the bits is < p:
;   value of bits < 2^m <= 2^(n-1) <= p.

(defruled lebits=>nat-less-when-len-less
  (implies (and (posp p)
                (< (len bs)
                   (integer-length p)))
           (< (lebits=>nat bs)
              p))
  :rule-classes :linear
  :do-not-induct t
  :enable lebits=>nat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If the most significant digit is 0, it can be eliminated.

(defruled bebits=>nat-when-msb-is-0
  (implies (equal (car bits) 0)
           (equal (bebits=>nat bits)
                  (bebits=>nat (cdr bits))))
  :enable (bebits=>nat
           acl2::bendian=>nat-when-most-significant-is-0))

(defruled lebits=>nat-when-msb-is-0
  (implies (equal (car (last bits)) 0)
           (equal (lebits=>nat bits)
                  (lebits=>nat (butlast bits 1))))
  :enable (lebits=>nat
           acl2::lendian=>nat-when-most-significant-is-0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Least significant digit in little endian order (i.e. last).

(defruled lendian=>nat-of-last
  (equal (acl2::lendian=>nat base (last digits))
         (acl2::dab-digit-fix base (car (last digits))))
  :enable acl2::lendian=>nat)

(defruled lebits=>nat-of-last
  (implies (and (bit-listp bits)
                (consp bits))
           (equal (lebits=>nat (last bits))
                  (car (last bits))))
  :enable (lebits=>nat
           lendian=>nat-of-last))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Upper bound when the most significant bit is 0.

(defruled lebits=>nat-upper-bound-when-msb-is-0
  (implies (and (consp bits)
                (equal (car (last bits)) 0))
           (< (lebits=>nat bits)
              (expt 2 (1- (len bits)))))
  :rule-classes ((:linear :trigger-terms ((lebits=>nat bits))))
  :enable lebits=>nat-when-msb-is-0)

; Lower bound when the most significant bit is 1.

(defruled lebits=>nat-lower-bound-when-msb-is-1
  (implies (and (consp bits)
                (bit-listp bits)
                (equal (car (last bits)) 1))
           (>= (lebits=>nat bits)
               (expt 2 (1- (len bits)))))
  :do-not-induct t
  :prep-lemmas
  ((defrule lemma
     (implies (and (consp bits)
                   (bit-listp bits)
                   (equal (car (last bits)) 1))
              (equal (lebits=>nat bits)
                     (+ (lebits=>nat (butlast bits 1))
                        (expt 2 (1- (len bits))))))
     :do-not-induct t
     :cases ((>= (len bits) 1))
     :enable (acl2::lebits=>nat-of-cons
              lebits=>nat-of-last
              append-of-butlast-of-1-and-last
              len-of-butlast)
     :disable butlast
     :use (:instance acl2::lebits=>nat-of-append
                     (lodigits (butlast bits 1))
                     (hidigits (last bits))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Interpret little-endian list of bits as two's complement integer.
; The sign bit is the last one, if present.

(define lebits=>int ((bs bit-listp))
  :returns (int integerp)
  (if (and (consp bs)
           (equal (bfix (car (last bs))) 1))
      (- (lebits=>nat bs)
         (expt 2 (len bs)))
    (lebits=>nat bs))
  ///
  (fty::deffixequiv lebits=>int
    :hints (("Goal" :in-theory (enable last-of-bit-list-fix)))))

(defrule lebits=>nat-injectvity
  (implies (equal (len x) (len y))
           (equal (equal (lebits=>int x)
                         (lebits=>int y))
                  (equal (bit-list-fix x)
                         (bit-list-fix y))))
  :use lemma
  :prep-lemmas
  ((defruled lemma
     (implies (equal (len x) (len y))
              (implies (equal (lebits=>int x)
                              (lebits=>int y))
                       (equal (bit-list-fix x)
                              (bit-list-fix y))))
     :enable lebits=>int
     :use (:instance acl2::lebits=>nat-injectivity (digits1 x) (digits2 y))
     :disable acl2::lebits=>nat-injectivity)))

(defrule lebits=>int-of-all-zeros
  (equal (lebits=>int (repeat n 0))
         0)
  :enable (lebits=>int repeat))

(defruled lebits=>int-upper-bound
  (implies (consp bs)
           (< (lebits=>int bs)
              (expt 2 (1- (len bs)))))
  :rule-classes ((:linear :trigger-terms ((lebits=>int bs))))
  :use (:instance lemma (bs (bit-list-fix bs)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (bit-listp bs)
                   (consp bs))
              (< (lebits=>int bs)
                 (expt 2 (1- (len bs)))))
     :do-not-induct t
     :cases ((or (equal (car (last bs)) 0)
                 (equal (car (last bs)) 1)))
     :enable lebits=>int
     :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits bs))
           (:instance bitp-of-car-of-last-when-bit-listp (bits bs))))))

(defruled lebits=>int-lower-bound
  (implies (consp bs)
           (>= (lebits=>int bs)
               (- (expt 2 (1- (len bs))))))
  :rule-classes ((:linear :trigger-terms ((lebits=>int bs))))
  :use (:instance lemma (bs (bit-list-fix bs)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (bit-listp bs)
                   (consp bs))
              (>= (lebits=>int bs)
                  (- (expt 2 (1- (len bs))))))
     :do-not-induct t
     :cases ((or (equal (car (last bs)) 0)
                 (equal (car (last bs)) 1)))
     :enable lebits=>int
     :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits bs))
           (:instance bitp-of-car-of-last-when-bit-listp (bits bs))))))
