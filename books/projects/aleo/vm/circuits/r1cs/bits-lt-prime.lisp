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

(include-book "bits-lte-const")

(local (include-book "../library-extensions/digits"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget specializes the bits-lte-const gadget to the case in which
; the constant bits cs are the ones for the prime minus one.
; That is, this gadget checks that the integer (not field) value of
; x = x(0) + 2*x(1) + 4*x(2) + ... + 2^(n-1)*x(n-1)
; is less than the prime p, i.e. that x < p,
; where x is expressed in bits x(0), ..., x(n-1).

; The bits-lte-const gadget requires
; cs to contain at least a 0 bit and to have 1 as most significant bit.
; If p is odd, then p-1 is even and has the same number of bits,
; so both requirements are satisfied.
; If p is even, it must be p = 2:
; this is not used in zero-knowledge applications,
; so the restriction to an odd prime is not a real limitation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We start by proving the aforementioned properties of p and p - 1.
; Actually, we do not need p to be prime for these properties to hold;
; we just need it to be an odd integer above 1.

; The bit length of p - 1 is the same as p.

(defruledl p-and-pm1-same-integer-length
  (implies (and (integerp p)
                (> p 1)
                (oddp p))
           (equal (integer-length (1- p))
                  (integer-length p)))
  :induct t
  :enable oddp
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

; If an integer is even and not 0,
; it has at least a 0 bit in its bit expansion.
; We are interested in this property for p - 1.

(defruledl even-above-0-has-0-bit
  (implies (and (integerp n)
                (> n 0)
                (evenp n))
           (member-equal 0 (nat=>lebits* n)))
  :enable (nat=>lebits*
           acl2::nat=>lendian*)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

; If p is an odd integer above 1, p-1 is an even integer above 0.
; This will let us establish the hypotheses of the previous theorem.

(defruledl even-above-0-of-one-less-when-odd-above-1
  (implies (and (integerp p)
                (> p 1)
                (oddp p))
           (and (integerp (1- p))
                (> (1- p) 0)
                (evenp (1- p))))
  :enable oddp
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

; Putting the above two theorems together,
; if p is an odd integer above 1,
; p-1 has a 0 bit in its bit expansion.

(defruledl one-less-than-odd-above-1-has-0-bit
  (implies (and (integerp p)
                (> p 1)
                (oddp p))
           (member-equal 0 (nat=>lebits* (1- p))))
  :use ((:instance even-above-0-has-0-bit (n (1- p)))
        even-above-0-of-one-less-when-odd-above-1))

; The fact that p - 1 has a most significant bit of 1
; is expressed by a theorem about binary digits.

(thm
 (implies (posp n)
          (equal (car (last (nat=>lebits* n)))
                 1))
 :hints (("Goal" :by nat=>lebits*-msb-is-1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The number of rs variables in the bits-lte-const gadget
; depends on the prime, and is expressed by bits-lte-const-rlen.
; Here we introduce a wrapper of that, for this bits-lt-prime gadget.

(define bits-lt-prime-rlen ((p primep))
  :guard (oddp p)
  :returns (len natp)
  (bits-lte-const-rlen (nat=>lebits* (1- p)))
  :prepwork ((local (in-theory (enable nat=>lebits*-msb-is-1
                                       one-less-than-odd-above-1-has-0-bit
                                       len-of-nat=>lebits*-is-integer-length
                                       p-and-pm1-same-integer-length))))
  ///

  (more-returns
   (len posp
        :hyp (and (primep p)
                  (oddp p))
        :rule-classes :type-prescription)))

; We define the gadget by wrapping the bits-lte-const gadget.

(define bits-lt-prime-gadget ((xs symbol-listp) (rs symbol-listp) (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (bits-lte-const-gadget xs (nat=>lebits* (1- p)) rs p)
  :prepwork ((local (in-theory (enable bits-lt-prime-rlen
                                       nat=>lebits*-msb-is-1
                                       one-less-than-odd-above-1-has-0-bit
                                       len-of-nat=>lebits*-is-integer-length
                                       p-and-pm1-same-integer-length)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The soundness of the gadget follows from the one of bits-lte-const.

(defruled bits-lt-prime-soundness
  (implies (and (primep p)
                (oddp p)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (bits-lt-prime-gadget xs rs p) asg p)
                      (implies (bit-listp xs$)
                               (iff (< (lebits=>nat xs$) p)
                                    (equal (car (last rs$)) 0))))))
  :use (:instance bits-lte-const-soundness (cs (nat=>lebits* (1- p))))
  :enable (bits-lt-prime-gadget
           bits-lt-prime-rlen
           len-of-nat=>lebits*-is-integer-length
           p-and-pm1-same-integer-length
           nat=>lebits*-msb-is-1
           one-less-than-odd-above-1-has-0-bit
           last-of-lookup-equal-list
           car-of-lookup-equal-list)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))
