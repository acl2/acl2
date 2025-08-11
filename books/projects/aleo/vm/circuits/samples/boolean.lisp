; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains specifications and proofs
; for the Aleo instruction operations:
;   and, is.eq, is.neq, nand, nor, not, or, ternary, and xor
; for boolean (single bit) arguments.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "boolean-json")

(include-book "projects/aleo/vm/circuits/sampling/prime-field-macros" :dir :system)
(include-book "projects/aleo/vm/circuits/sampling/gadget-json-message-to-r1cs-defagg" :dir :system)

;(include-book "../equiv")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See top.lisp for documentation about the following definitions and theorems.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; and

(include-book "projects/aleo/vm/circuits/r1cs/boolean-and" :dir :system)

; operation specification

(define boolean-and--pre (x y)
  :returns (yes/no booleanp)
  (and (bitp x) (bitp y)))

(define boolean-and--post (z)
  :returns (yes/no booleanp)
  (bitp z))

(define boolean-and--fun (x y)
  :guard (boolean-and--pre x y)
  :returns (z boolean-and--post)
  (if (and (= x 1) (= y 1))
      1
    0)
  :prepwork ((local (in-theory (enable boolean-and--pre)))))

; gadget specification

(define boolean-and--hyps (x y z)
  :returns (yes/no booleanp)
  (and (boolean-and--pre x y)
       (efep z)))

(define boolean-and--spec (x y z)
  :guard (boolean-and--hyps x y z)
  :returns (yes/no booleanp)
  (equal z (boolean-and--fun x y))
  :guard-hints (("Goal" :in-theory (enable boolean-and--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-and-json*)))
   `(define boolean-and--constraints ()
      (cddr ',constraints)
      ///
      (defruled boolean-and--constraints-to-boolean-and-gadget
        (equal (boolean-and--constraints)
               (boolean-and-gadget 'r1cs::|w0| 'r1cs::|w1| 'r1cs::|w2|))))))

(define boolean-and--gadget (x y z)
  :guard (and (efep x) (efep y) (efep z))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-and--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      (cons 'r1cs::|w2| z))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-and--equiv
  (implies (boolean-and--hyps x y z)
           (iff (boolean-and--gadget x y z)
                (boolean-and--spec x y z)))
  :enable (boolean-and--hyps
           boolean-and--pre
           boolean-and--spec
           boolean-and--fun
           boolean-and--gadget
           boolean-and--constraints-to-boolean-and-gadget
           boolean-and-gadget-to-bitand
           bitand
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-and--constraints)
            (:e boolean-and-gadget)))

(defruled boolean-and--spec-post
  (implies (and (boolean-and--hyps x y z)
                (boolean-and--spec x y z))
           (boolean-and--post z))
  :in-theory '(boolean-and--hyps
               boolean-and--spec
               boolean-and--post-of-boolean-and--fun))

(defruled boolean-and--gadget-post
  (implies (and (boolean-and--hyps x y z)
                (boolean-and--gadget x y z))
           (boolean-and--post z))
  :in-theory nil
  :use (boolean-and--spec-post
        boolean-and--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; is.eq

(include-book "projects/aleo/vm/circuits/r1cs/boolean-xor" :dir :system)

; operation specification

(define boolean-is.eq--pre (x y)
  :returns (yes/no booleanp)
  (and (bitp x) (bitp y)))

(define boolean-is.eq--post (z)
  :returns (yes/no booleanp)
  (bitp z))

(define boolean-is.eq--fun (x y)
  :guard (boolean-is.eq--pre x y)
  :returns (z boolean-is.eq--post)
  (if (equal x y) 1 0))

; gadget specification

(define boolean-is.eq--hyps (x y z)
  :returns (yes/no booleanp)
  (and (boolean-is.eq--pre x y)
       (efep z)))

(define boolean-is.eq--spec (x y z)
  :guard (boolean-is.eq--hyps x y z)
  :returns (yes/no booleanp)
  (equal z (boolean-is.eq--fun x y))
  :guard-hints (("Goal" :in-theory (enable boolean-is.eq--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-equal-json*)))
   `(define boolean-is.eq--constraints ()
      (cddr ',constraints)
      ///
      (defruled boolean-is.eq--constraints-to-boolean-xor-gadget
        (equal (boolean-is.eq--constraints)
               (boolean-xor-gadget 'r1cs::|w0|
                                           'r1cs::|w1|
                                           'r1cs::|w2|
                                           (eprime)))))))

(define boolean-is.eq--gadget (x y z)
  :guard (and (efep x) (efep y) (efep z))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-is.eq--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      ;; adjust to negated result:
                                      (cons 'r1cs::|w2| (esub 1 z)))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-is.eq--equiv
  (implies (boolean-is.eq--hyps x y z)
           (iff (boolean-is.eq--gadget x y z)
                (boolean-is.eq--spec x y z)))
  :enable (boolean-is.eq--hyps
           boolean-is.eq--pre
           boolean-is.eq--spec
           boolean-is.eq--fun
           boolean-is.eq--gadget
           boolean-is.eq--constraints-to-boolean-xor-gadget
           boolean-xor-gadget-to-bitxor
           bitxor
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-is.eq--constraints)
            (:e boolean-xor-gadget))
  :prep-books
  ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)))

(defruled boolean-is.eq--spec-post
  (implies (and (boolean-is.eq--hyps x y z)
                (boolean-is.eq--spec x y z))
           (boolean-is.eq--post z))
  :in-theory '(boolean-is.eq--hyps
               boolean-is.eq--spec
               boolean-is.eq--post-of-boolean-is.eq--fun))

(defruled boolean-is.eq--gadget-post
  (implies (and (boolean-is.eq--hyps x y z)
                (boolean-is.eq--gadget x y z))
           (boolean-is.eq--post z))
  :in-theory '(boolean-is.eq--spec-post
               boolean-is.eq--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; is.neq

(include-book "projects/aleo/vm/circuits/r1cs/boolean-xor" :dir :system)

; operation specification

(define boolean-is.neq--pre (x y)
  :returns (yes/no booleanp)
  (and (bitp x)
       (bitp y)))

(define boolean-is.neq--post (z)
  :returns (yes/no booleanp)
  (bitp z))

(define boolean-is.neq--fun (x y)
  :guard (boolean-is.neq--pre x y)
  :returns (z boolean-is.neq--post)
  (if (equal x y) 0 1))

; gadget specification

(define boolean-is.neq--hyps (x y z)
  :returns (yes/no booleanp)
  (and (boolean-is.neq--pre x y)
       (efep z)))

(define boolean-is.neq--spec (x y z)
  :guard (boolean-is.neq--hyps x y z)
  :returns (yes/no booleanp)
  (equal z (boolean-is.neq--fun x y))
  :guard-hints (("Goal" :in-theory (enable boolean-is.neq--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-xor-json*)))
   `(define boolean-is.neq--constraints ()
      (cddr ',constraints)
      ///
      (defruled boolean-is.neq--constraints-to-boolean-xor-gadget
        (equal (boolean-is.neq--constraints)
               (boolean-xor-gadget 'r1cs::|w0| 'r1cs::|w1| 'r1cs::|w2| (eprime)))))))

(define boolean-is.neq--gadget (x y z)
  :guard (and (efep x) (efep y) (efep z))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-is.neq--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      (cons 'r1cs::|w2| z))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-is.neq--equiv
  (implies (boolean-is.neq--hyps x y z)
           (iff (boolean-is.neq--gadget x y z)
                (boolean-is.neq--spec x y z)))
  :enable (boolean-is.neq--hyps
           boolean-is.neq--pre
           boolean-is.neq--spec
           boolean-is.neq--fun
           boolean-is.neq--gadget
           boolean-is.neq--constraints-to-boolean-xor-gadget
           boolean-xor-gadget-to-bitxor
           bitxor
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-is.neq--constraints)
            (:e boolean-xor-gadget)))

(defruled boolean-is.neq--spec-post
  (implies (and (boolean-is.neq--hyps x y z)
                (boolean-is.neq--spec x y z))
           (boolean-is.neq--post z))
  :in-theory '(boolean-is.neq--hyps
               boolean-is.neq--spec
               boolean-is.neq--post-of-boolean-is.neq--fun))

(defruled boolean-is.neq--gadget-post
  (implies (and (boolean-is.neq--hyps x y z)
                (boolean-is.neq--gadget x y z))
           (boolean-is.neq--post z))
  :in-theory '(boolean-is.neq--spec-post
               boolean-is.neq--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nand

(include-book "projects/aleo/vm/circuits/r1cs/boolean-nand" :dir :system)

; operation specification

(define boolean-nand--pre (x y)
  :returns (yes/no booleanp)
  (and (bitp x) (bitp y)))

(define boolean-nand--post (z)
  :returns (yes/no booleanp)
  (bitp z))

(define boolean-nand--fun (x y)
  :guard (boolean-nand--pre x y)
  :returns (z boolean-nand--post)
  (if (not (and (= x 1) (= y 1)))
      1
    0)
  :prepwork ((local (in-theory (enable boolean-nand--pre)))))

; gadget specification

(define boolean-nand--hyps (x y z)
  :returns (yes/no booleanp)
  (and (boolean-nand--pre x y)
       (efep z)))

(define boolean-nand--spec (x y z)
  :guard (boolean-nand--hyps x y z)
  :returns (yes/no booleanp)
  (equal z (boolean-nand--fun x y))
  :guard-hints (("Goal" :in-theory (enable boolean-nand--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-nand-json*)))
   `(define boolean-nand--constraints ()
      (cddr ',constraints)
      ///
      (defruled boolean-nand--constraints-to-boolean-nand-gadget
        (equal (boolean-nand--constraints)
               (boolean-nand-gadget 'r1cs::|w0|
                                            'r1cs::|w1|
                                            'r1cs::|w2|
                                            (eprime)))))))

(define boolean-nand--gadget (x y z)
  :guard (and (efep x) (efep y) (efep z))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-nand--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      (cons 'r1cs::|w2| z))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-nand--equiv
  (implies (boolean-nand--hyps x y z)
           (iff (boolean-nand--gadget x y z)
                (boolean-nand--spec x y z)))
  :enable (boolean-nand--hyps
           boolean-nand--pre
           boolean-nand--spec
           boolean-nand--fun
           boolean-nand--gadget
           boolean-nand--constraints-to-boolean-nand-gadget
           boolean-nand-gadget-to-bitnand
           bitnand
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-nand--constraints)
            (:e boolean-nand-gadget)))

(defruled boolean-nand--spec-post
  (implies (and (boolean-nand--hyps x y z)
                (boolean-nand--spec x y z))
           (boolean-nand--post z))
  :in-theory '(boolean-nand--hyps
               boolean-nand--spec
               boolean-nand--post-of-boolean-nand--fun))

(defruled boolean-nand--gadget-post
  (implies (and (boolean-nand--hyps x y z)
                (boolean-nand--gadget x y z))
           (boolean-nand--post z))
  :in-theory nil
  :use (boolean-nand--spec-post
        boolean-nand--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nor

(include-book "projects/aleo/vm/circuits/r1cs/boolean-nor" :dir :system)

; operation specification

(define boolean-nor--pre (x y)
  :returns (yes/no booleanp)
  (and (bitp x)
       (bitp y)))

(define boolean-nor--post (z)
  :returns (yes/no booleanp)
  (bitp z))

(define boolean-nor--fun (x y)
  :guard (boolean-nor--pre x y)
  :returns (z boolean-nor--post)
  (if (not (or (= x 1) (= y 1)))
      1
    0)
  :prepwork ((local (in-theory (enable boolean-nor--pre)))))

; gadget specification

(define boolean-nor--hyps (x y z)
  :returns (yes/no booleanp)
  (and (boolean-nor--pre x y)
       (efep z)))

(define boolean-nor--spec (x y z)
  :guard (boolean-nor--hyps x y z)
  :returns (yes/no booleanp)
  (equal z (boolean-nor--fun x y))
  :guard-hints (("Goal" :in-theory (enable boolean-nor--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-nor-json*)))
   `(define boolean-nor--constraints ()
      (cddr ',constraints)
      ///
      (defruled boolean-nor--constraints-to-boolean-nor-gadget
        (equal (boolean-nor--constraints)
               (boolean-nor-gadget 'r1cs::|w0|
                                           'r1cs::|w1|
                                           'r1cs::|w2|
                                           (eprime)))))))

(define boolean-nor--gadget (x y z)
  :guard (and (efep x) (efep y) (efep z))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-nor--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      (cons 'r1cs::|w2| z))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-nor--equiv
  (implies (boolean-nor--hyps x y z)
           (iff (boolean-nor--gadget x y z)
                (boolean-nor--spec x y z)))
  :enable (boolean-nor--hyps
           boolean-nor--pre
           boolean-nor--spec
           boolean-nor--fun
           boolean-nor--gadget
           boolean-nor--constraints-to-boolean-nor-gadget
           boolean-nor-gadget-to-bitnor
           bitnor
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-nor--constraints)
            (:e boolean-nor-gadget)))

(defruled boolean-nor--spec-post
  (implies (and (boolean-nor--hyps x y z)
                (boolean-nor--spec x y z))
           (boolean-nor--post z))
  :in-theory '(boolean-nor--hyps
               boolean-nor--spec
               boolean-nor--post-of-boolean-nor--fun))

(defruled boolean-nor--gadget-post
  (implies (and (boolean-nor--hyps x y z)
                (boolean-nor--gadget x y z))
           (boolean-nor--post z))
  :in-theory '(boolean-nor--spec-post
               boolean-nor--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; not

; operation specification

(define boolean-not--pre (x)
  :returns (yes/no booleanp)
  (bitp x))

(define boolean-not--post (y)
  :returns (yes/no booleanp)
  (bitp y))

(define boolean-not--fun (x)
  :guard (boolean-not--pre x)
  :returns (y boolean-not--post)
  (if (= x 1) 0 1)
  :prepwork ((local (in-theory (enable boolean-not--pre)))))

; gadget specification

(define boolean-not--hyps (x y)
  :returns (yes/no booleanp)
  (and (boolean-not--pre x)
       (efep y)))

(define boolean-not--spec (x y)
  :guard (boolean-not--hyps x y)
  :returns (yes/no booleanp)
  (equal y (boolean-not--fun x))
  :guard-hints (("Goal" :in-theory (enable boolean-not--hyps))))

; gadget implementation

; There are no actual JSON constraints, because negation is done on the fly.
; Thus we write a gadget manually for this operation for now.

(define boolean-not--gadget (x y)
  :guard (and (efep x) (efep y))
  :returns (yes/no booleanp)
  ;; (y) = (1 - x)
  (equal y (esub 1 x)))

; theorems

(defruled boolean-not--equiv
  (implies (boolean-not--hyps x y)
           (iff (boolean-not--gadget x y)
                (boolean-not--spec x y)))
  :enable (boolean-not--hyps
           boolean-not--pre
           boolean-not--spec
           boolean-not--gadget))

(defruled boolean-not--spec-post
  (implies (and (boolean-not--hyps x y)
                (boolean-not--spec x y))
           (boolean-not--post y))
  :enable boolean-not--spec)

(defruled boolean-not--gadget-post
  (implies (and (boolean-not--hyps x y)
                (boolean-not--gadget x y))
           (boolean-not--post y))
  :in-theory nil
  :use (boolean-not--spec-post
        boolean-not--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; or

(include-book "projects/aleo/vm/circuits/r1cs/boolean-or" :dir :system)

; operation specification

(define boolean-or--pre (x y)
  :returns (yes/no booleanp)
  (and (bitp x) (bitp y)))

(define boolean-or--post (z)
  :returns (yes/no booleanp)
  (bitp z))

(define boolean-or--fun (x y)
  :guard (boolean-or--pre x y)
  :returns (z boolean-or--post)
  (if (or (= x 1) (= y 1))
      1
    0)
  :prepwork ((local (in-theory (enable boolean-or--pre)))))

; gadget specification

(define boolean-or--hyps (x y z)
  :returns (yes/no booleanp)
  (and (boolean-or--pre x y)
       (efep z)))

(define boolean-or--spec (x y z)
  :guard (boolean-or--hyps x y z)
  :returns (yes/no booleanp)
  (equal z (boolean-or--fun x y))
  :guard-hints (("Goal" :in-theory (enable boolean-or--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-or-json*)))
   `(define boolean-or--constraints ()
      (cddr ',constraints)
      ///
      (defruled boolean-or--constraints-to-boolean-or-gadget
        (equal (boolean-or--constraints)
               (boolean-or-gadget 'r1cs::|w0|
                                          'r1cs::|w1|
                                          'r1cs::|w2|
                                          (eprime)))))))

(define boolean-or--gadget (x y z)
  :guard (and (efep x) (efep y) (efep z))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-or--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      (cons 'r1cs::|w2| z))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-or--equiv
  (implies (boolean-or--hyps x y z)
           (iff (boolean-or--gadget x y z)
                (boolean-or--spec x y z)))
  :enable (boolean-or--hyps
           boolean-or--pre
           boolean-or--spec
           boolean-or--fun
           boolean-or--gadget
           boolean-or--constraints-to-boolean-or-gadget
           boolean-or-gadget-to-bitor
           bitor
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-or--constraints)
            (:e boolean-or-gadget)))

(defruled boolean-or--spec-post
  (implies (and (boolean-or--hyps x y z)
                (boolean-or--spec x y z))
           (boolean-or--post z))
  :in-theory '(boolean-or--hyps
               boolean-or--spec
               boolean-or--post-of-boolean-or--fun))

(defruled boolean-or--gadget-post
  (implies (and (boolean-or--hyps x y z)
                (boolean-or--gadget x y z))
           (boolean-or--post z))
  :in-theory nil
  :use (boolean-or--spec-post
        boolean-or--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ternary

(include-book "projects/aleo/vm/circuits/r1cs/if" :dir :system)

; operation specification

(define boolean-ternary--pre (x y z)
  :returns (yes/no booleanp)
  (and (bitp x)
       (bitp y)
       (bitp z)))

(define boolean-ternary--post (w)
  :returns (yes/no booleanp)
  (bitp w))

(define boolean-ternary--fun (x y z)
  :guard (boolean-ternary--pre x y z)
  :returns (w boolean-ternary--post
              :hyp (boolean-ternary--pre x y z)
              :hints (("Goal" :in-theory (enable boolean-ternary--pre
                                                 boolean-ternary--post))))
  (if (= x 1) y z)
  :guard-hints (("Goal" :in-theory (enable boolean-ternary--pre))))

; gadget specification

(define boolean-ternary--hyps (x y z w)
  :returns (yes/no booleanp)
  (and (boolean-ternary--pre x y z)
       (efep w)))

(define boolean-ternary--spec (x y z w)
  :guard (boolean-ternary--hyps x y z w)
  :returns (yes/no booleanp)
  (equal w (boolean-ternary--fun x y z))
  :guard-hints (("Goal" :in-theory (enable boolean-ternary--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-ternary-json*)))
   `(define boolean-ternary--constraints ()
      (cdddr ',constraints)
      ///
      (defruled boolean-ternary--constraints-to-if-gadget
        ; We would like to use r1cs::equiv here, once we have congruences defined;
        ; and then switch from if-gadget-variant to if-gadget.
        (equal (boolean-ternary--constraints)
               (if-gadget-variant 'r1cs::|w0|
                                          'r1cs::|w1|
                                          'r1cs::|w2|
                                          'r1cs::|w3|
                                          (eprime)))))))

(define boolean-ternary--gadget (x y z w)
  :guard (and (efep x) (efep y) (efep z) (efep w))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-ternary--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      (cons 'r1cs::|w2| z)
                                      (cons 'r1cs::|w3| w))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-ternary--equiv
  (implies (boolean-ternary--hyps x y z w)
           (iff (boolean-ternary--gadget x y z w)
                (boolean-ternary--spec x y z w)))
  :enable (boolean-ternary--hyps
           boolean-ternary--pre
           boolean-ternary--spec
           boolean-ternary--fun
           boolean-ternary--gadget
           boolean-ternary--constraints-to-if-gadget
           if-gadget-variant-to-if
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-ternary--constraints)
            (:e if-gadget-variant)))

(defruled boolean-ternary--spec-post
  (implies (and (boolean-ternary--hyps x y z w)
                (boolean-ternary--spec x y z w))
           (boolean-ternary--post w))
  :in-theory '(boolean-ternary--hyps
               boolean-ternary--spec
               boolean-ternary--post-of-boolean-ternary--fun))

(defruled boolean-ternary--gadget-post
  (implies (and (boolean-ternary--hyps x y z w)
                (boolean-ternary--gadget x y z w))
           (boolean-ternary--post w))
  :in-theory nil
  :use (boolean-ternary--spec-post
        boolean-ternary--equiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; xor

(include-book "projects/aleo/vm/circuits/r1cs/boolean-xor" :dir :system)

;; Note, these definitions are the same as those for boolean-is.neq

; operation specification

(define boolean-xor--pre (x y)
  :returns (yes/no booleanp)
  (and (bitp x)
       (bitp y)))

(define boolean-xor--post (z)
  :returns (yes/no booleanp)
  (bitp z))

(define boolean-xor--fun (x y)
  :guard (boolean-xor--pre x y)
  :returns (z boolean-xor--post)
  (if (equal x y) 0 1))

;; Note, it would be possible to define xor in a more speclike way:
;;  (if (and (or (= a 1) (= b 1))
;;           (not (and (= a 1) (= b 1))))
;;      1
;;    0))
;; and one could then prove equivalence of that with boolean-is.neq--fun

; gadget specification

(define boolean-xor--hyps (x y z)
  :returns (yes/no booleanp)
  (and (boolean-xor--pre x y)
       (efep z)))

(define boolean-xor--spec (x y z)
  :guard (boolean-xor--hyps x y z)
  :returns (yes/no booleanp)
  (equal z (boolean-xor--fun x y))
  :guard-hints (("Goal" :in-theory (enable boolean-xor--hyps))))

; gadget implementation

(make-event ; JSON constraints, without boolean constraints on inputs
 (b* (((mv & constraints)
       (json-gadget-string-to-r1cs *boolean-xor-json*)))
   `(define boolean-xor--constraints ()
      (cddr ',constraints)
      ///
      (defruled boolean-xor--constraints-to-boolean-xor-gadget
        (equal (boolean-xor--constraints)
               (boolean-xor-gadget 'r1cs::|w0|
                                           'r1cs::|w1|
                                           'r1cs::|w2|
                                           (eprime)))))))

(define boolean-xor--gadget (x y z)
  :guard (and (efep x) (efep y) (efep z))
  :returns (yes/no booleanp)
  (r1cs::r1cs-constraints-holdp (boolean-xor--constraints)
                                (list (cons 'r1cs::|w0| x)
                                      (cons 'r1cs::|w1| y)
                                      (cons 'r1cs::|w2| z))
                                (primes::bls12-377-scalar-field-prime))
  :guard-hints (("Goal" :in-theory (enable r1cs::r1cs-valuationp))))

; theorems

(defruled boolean-xor--equiv
  (implies (boolean-xor--hyps x y z)
           (iff (boolean-xor--gadget x y z)
                (boolean-xor--spec x y z)))
  :enable (boolean-xor--hyps
           boolean-xor--pre
           boolean-xor--spec
           boolean-xor--fun
           boolean-xor--gadget
           boolean-xor--constraints-to-boolean-xor-gadget
           boolean-xor-gadget-to-bitxor
           bitxor
           r1cs::r1cs-valuationp
           r1cs::valuation-bindsp)
  :disable ((:e boolean-xor--constraints)
            (:e boolean-xor-gadget)))

(defruled boolean-xor--spec-post
  (implies (and (boolean-xor--hyps x y z)
                (boolean-xor--spec x y z))
           (boolean-xor--post z))
  :in-theory '(boolean-xor--hyps
               boolean-xor--spec
               boolean-xor--post-of-boolean-xor--fun))

(defruled boolean-xor--gadget-post
  (implies (and (boolean-xor--hyps x y z)
                (boolean-xor--gadget x y z))
           (boolean-xor--post z))
  :in-theory '(boolean-xor--spec-post
               boolean-xor--equiv))
