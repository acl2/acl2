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

(include-book "boolean-check")
(include-book "pow2sum")
(include-book "bits-lt-prime")
(include-book "zero")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget turns a field element x into its bit representation.
; It introduces boolean variables xs for the bits,
; as many as the number of bits of the prime p.
; It constrains the powers-of-two weighted sum of the xs bits
; to be equal to the field element x.
; Since this equality is modular,
; the constraints mentioned so far are insufficient in general:
; the gadget also ensures that
; the (non-modular) powers-of-two weighted sum of the xs bits
; is below the prime p.

; The bits-lt-prime gadget needs additional variables rs,
; whose length is given by bits-lt-prime-rlen.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We define the field-to-bits gadget
; by putting together the aforementioned gadgets.

(define field-to-bits-gadget ((x symbolp)
                              (xs symbol-listp)
                              (rs symbol-listp)
                              (u symbolp) ; unit var
                              (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len rs) (bits-lt-prime-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list xs p)
          (pow2sum-gadget x xs)
          (bits-lt-prime-gadget xs rs p)
          (zero-unit-gadget (car (last rs)) u p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Now we prove the soundness of the gadget.

(defruled field-to-bits-soundness
  (implies (and (primep p)
                (oddp p)
                (symbolp x)
                (symbol-listp xs)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len rs) (bits-lt-prime-rlen p))
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u)
                )
           (b* ((x$ (lookup-equal x asg))
                (xs$ (lookup-equal-list xs asg))
                (u$ (lookup-equal u asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-to-bits-gadget x xs rs u p) asg p)
                      (implies (equal u$ 1)
                               (and (bit-listp xs$)
                                    (equal x$ (lebits=>nat xs$)))))))
  :use bits-lt-prime-soundness
  :cases ((consp rs))
  :enable (field-to-bits-gadget
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           zero-unit-gadget-to-equal-0
           last-of-lookup-equal-list
           car-of-lookup-equal-list)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))
