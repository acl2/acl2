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

(include-book "zero")
(include-book "bits-lt-prime")
(include-book "pow2sum")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

(local (include-book "../library-extensions/arithmetic"))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget converts a sequence of bits to a field element.
; The bits are in the variables in the list xs,
; which has no length limitations.
; We assume that xs is in little endian order.
; The resulting field element x is
; the powers-of-two weighted sum of the bits in xs,
; provided that that weighted (in integer, not prime, arithmetic)
; is below the prime.

; If xs has more bits than the prime,
; we use the zero gadget to enforce that the extra bits are all 0;
; otherwise, there is no way that they can add up to a field element.
; If xs at least as many bits as the prime (possible more),
; we use the bits-lt-prime and zero gadgets to constrain them
; to add up to something below the prime;
; note that we exclude any excess bit, which is constrained to be 0,
; as explained above.
; If xs has fewer bits than xs,
; there is no need to use the bits-lt-prime gadget,
; because the weighted sum is certainly below the prime.

; In all cases, we use the pow2sum gadget to constrain x
; to be the weighted sum of xs in the prime field,
; which by the above constraints is also the weighted sum in the integers.

; The rs variables are used for the bits-lt-prime gadget.
; They are absent (i.e. their length is 0) when xs has fewer bits than p.

; The hypothesis, in the guard, that p is odd
; serves for the bits-lt-prime gadget.
; It could be weakened by not requiring it when xs has fewer bits than p,
; but in practical applications p is always odd,
; so this is not a real limitation.

; snarkVM uses the variant of the zero gadget that uses a public variable;
; see zero-unit-gadget for details.

(define field-from-bits-gadget ((xs symbol-listp)
                                    (x symbolp)
                                    (rs symbol-listp)
                                    (u symbolp)
                                    (p primep))
  :guard (and (oddp p)
              (equal (len rs) (if (>= (len xs)
                                      (integer-length p))
                                  (bits-lt-prime-rlen p)
                                0)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (and (> (len xs)
                  (integer-length p))
               (zero-gadget-b-list (nthcdr (integer-length p) xs)))
          (and (>= (len xs)
                   (integer-length p))
               (append
                (bits-lt-prime-gadget (take (integer-length p) xs) rs p)
                ; TODO: replace the next line by something like zero-gadget-list
                (zero-unit-gadget (car (last rs)) u p)))
          (pow2sum-gadget x xs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We prove the soundness of the gadget by distinguishing two cases:
; either the length of xs is less than the bit length of p,
; or it is greater than or equal to it.

; In the first case, the key property to prove is that
; the value of xs is less than p,
; because the high bit of p is 1.

; We use positive->=-expt2-of-integer-length-minus-1
; and lebits=>nat-less-when-len-less
; to prove the soundness of the gadget when xs has fewer bits than p.

(defruledl soundness-case-1
  (implies (and (primep p)
                (oddp p)
                (symbol-listp xs)
                (symbolp x)
                (symbol-listp rs)
                (symbolp u)
                (< (len xs)
                   (integer-length p))
                (< (len rs) (integer-length p))
                (equal (len rs) 0)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u))
           (b* ((xs$ (lookup-equal-list xs asg))
                (x$ (lookup-equal x asg))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (implies (r1cs::r1cs-constraints-holdp
                                (field-from-bits-gadget xs x rs u p) asg p)
                               (implies (bit-listp xs$)
                                        (equal x$ (lebits=>nat xs$)))))))
  :enable (field-from-bits-gadget
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           lebits=>nat-less-when-len-less)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

; For the second case, in which xs has at least as many bits as p,
; the key point is that xs can be split into the low and high bits,
; where the low bits are the same in number as p.
; But the zero gadgets applied to the high bits force them to be 0,
; so the value of all the xs bits is the same as the value of the low ones.
; The bits-lt-prime gadget, and the zero gadget on its result,
; forces those the value of those low bits to be below p,
; and thus the value of all the xs bits is below p.
; The pow2sum gadget forces x to be equal to the value of xs modulo p,
; but because of the inequality just discussed, the modulo operation goes away.

(defruledl soundness-case-2
  (implies (and (primep p)
                (oddp p)
                (symbol-listp xs)
                (symbolp x)
                (symbol-listp rs)
                (symbolp u)
                (>= (len xs)
                    (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u))
           (b* ((xs$ (lookup-equal-list xs asg))
                (x$ (lookup-equal x asg))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (implies (r1cs::r1cs-constraints-holdp
                                (field-from-bits-gadget xs x rs u p) asg p)
                               (implies (bit-listp xs$)
                                        (equal x$ (lebits=>nat xs$)))))))
  :do-not-induct t
  :cases ((consp rs))
  :use ((:instance bits-lt-prime-soundness
                   (xs (take (integer-length p) xs)))
        (:instance acl2::lebits=>nat-of-append
                   (hidigits (nthcdr (integer-length p)
                                     (lookup-equal-list xs asg)))
                   (lodigits (take (integer-length p)
                                   (lookup-equal-list xs asg)))))
  :enable (field-from-bits-gadget
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           zero-gadget-b-list-to-all-equal-0
           lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           zero-unit-gadget-to-equal-0
           last-of-lookup-equal-list
           car-of-lookup-equal-list)
  :prep-books ((include-book "arithmetic/top" :dir :system)
               (include-book "std/lists/nthcdr" :dir :system)
               (include-book "kestrel/arithmetic-light/mod" :dir :system)))


; We put the two cases together to prove soundness for every length of xs.

(defruled field-from-bits-soundness
  (implies (and (primep p)
                (oddp p)
                (symbol-listp xs)
                (symbolp x)
                (symbol-listp rs)
                (symbolp u)
                (equal (len rs) (if (>= (len xs)
                                        (integer-length p))
                                    (bits-lt-prime-rlen p)
                                  0))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u))
           (b* ((xs$ (lookup-equal-list xs asg))
                (x$ (lookup-equal x asg))
                (u$ (lookup-equal u asg)))
             (implies (equal u$ 1)
                      (implies (r1cs::r1cs-constraints-holdp
                                (field-from-bits-gadget xs x rs u p) asg p)
                               (implies (bit-listp xs$)
                                        (equal x$ (lebits=>nat xs$)))))))
  :do-not-induct t
  :use (soundness-case-1 soundness-case-2))
