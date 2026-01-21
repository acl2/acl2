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

(include-book "pow2sum-vectors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is used to check if
;   x * y = z,
; for small unsigned integers of the same type x, y, and z.
; The type must be small enough for the product z to fit in the scalar field p.
; The "checked" part means if the product (x * y) does not fit in the type,
; the circuit will have no solutions.

; Since integers are represented as vectors of N bits,
; there are N R1CS variables representing each of x, y, and z.

; There is only one constraint, which reconstructs x, y, and z
; from bits and asserts that x * y = z.

(define unsigned-small-mul-and-check-gadget ((xs symbol-listp)
                                             (ys symbol-listp)
                                             (zs symbol-listp)
                                             (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len xs) (len zs))
              (< (+ (len xs) (len ys))
                 (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)

  (declare (ignorable p)) ; the mention in :guard doesn't count!
  (list (r1cs::make-r1cs-constraint
         :a (pow2sum-vector xs 0)
         :b (pow2sum-vector ys 0)
         :c (pow2sum-vector zs 0))))

; Spec.
; Similar in concept (wrt i/o and error case) to
; field-inverse in r1cs/field-inverse.lisp
; The spec does not need to be different for different nbits.

(include-book "kestrel/fty/integer-result" :dir :system)
; defines integer-resultp
; (in ACL2 package, which is imported into the current package)

(define unsigned-mul-and-check ((x natp)
                                 (y natp)
                                 (nbits natp))
  :guard (and (< 1 nbits)
              (<= (integer-length x) nbits)
              (<= (integer-length y) nbits))
  :returns (product integer-resultp :hyp :guard)
  (let ((z (* x y)))
    (if (< nbits (integer-length z))
        (reserr z)
        z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Correctness.

#|| WIP
(defruled unsigned-small-mul-and-check-gadget-soundness
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (primep p)

                (equal (len xs) (len ys))
                (equal (len xs) (len zs))

                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))

           (b*
               ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (nbits (len xs$)))

             (implies (r1cs::r1cs-constraints-holdp
                       (unsigned-small-mul-and-check-gadget xs ys zs p) asg p)

                      (implies (and (bit-listp xs$)
                                    (bit-listp ys$)
                                    (bit-listp zs$))
                               (equal (lebits=>nat zs$)
                                      (unsigned-mul-and-check (lebits=>nat xs$)
                                                              (lebits=>nat ys$)
                                                              nbits))))))
  :enable (unsigned-small-mul-and-check-gadget r1cs::r1cs-constraint-holdsp
           r1cs::dot-product unsigned-mul-and-check))
||#

; for soundness we want to capture both cases of the converse
; 1. z = spec(x,y) & integerp(z) & some other size limitations => constraints-hold(gadget(x,y,z))
; 2. z = spec(x,y) & reserrp(z) => not(constraints-hold(gadget(x,y,z)))
