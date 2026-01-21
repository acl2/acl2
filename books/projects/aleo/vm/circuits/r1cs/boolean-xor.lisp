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

(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/list-fix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification

; We define a function for the exlusive disjunction of two bits,
; even though perhaps we could just use the built-in LOGXOR.

(define bitxor ((x bitp) (y bitp))
  :returns (z bitp)
  (if (= x y) 0 1))

; We introduce a function that lifts BITXOR to lists.

(define bitxor-list ((xs bit-listp) (ys bit-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs bit-listp)
  (cond ((endp xs) nil)
        (t (cons (bitxor (car xs) (car ys))
                 (bitxor-list (cdr xs) (cdr ys)))))
  ///

  (defret len-of-bitxor-list
    (equal (len zs) (len xs)))

  (defruled bitxor-list-of-append
    (implies (equal (len xs1) (len ys1))
             (equal (bitxor-list (append xs1 xs2)
                                 (append ys1 ys2))
                    (append (bitxor-list xs1 ys1)
                            (bitxor-list xs2 ys2)))))

  (defruled bitxor-list-of-rev
    (implies (equal (len xs) (len ys))
             (equal (bitxor-list (rev xs) (rev ys))
                    (rev (bitxor-list xs ys))))
    :enable bitxor-list-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is exclusive boolean disjunction.
; It assumes that x and y are booleans,
; and constrains z to be their exclusive disjunction,
; i.e. 1 if they differ and 0 if they are the same.
; The gadget consists of a single constraint
;   (2x) (y) = (y + x + (p-1)z)
; i.e.
;   (2x) (y) = (y + x - z)
; i.e.
;   z = x + y - 2xy
; Thus z = 1 if x and y differ (i.e. one is 0 and one is 1),
; because x + y = 1 and 2xy = 0;
; while z = 0 if x and y are the same (i.e. either both 0 or both 1),
; because 2x - 2xx = 2x(1-x).

(define boolean-xor-gadget ((x symbolp) (y symbolp) (z symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 2 x))
         :b (list (list 1 y))
         :c (list (list 1 y)
                  (list 1 x)
                  (list (1- p) z)))))

; The gadget is equivalent to its specification,
; i.e. that z is the exclusive disjunctoin of x and y,
; assuming x and y are booleans.

(defruled boolean-xor-gadget-to-bitxor
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (implies (and (bitp x$)
                           (bitp y$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (boolean-xor-gadget x y z p) asg p)
                             (equal z$ (bitxor x$ y$))))))
  ;; Attempting to prove the above directly seems to run into issues.
  ;; so we stage the proof in two steps:
  ;; we introduce a predicate for the shallowly embedded gadget;
  ;; we prove the (deeply embedded) gadget equivalent to the predicate;
  ;; we prove the predicate equivalent to the specification;
  ;; we compose the two equivalences.
  :prep-lemmas
  ((defund shallow (x y z p)
     (equal (pfield::mul (pfield::mul 2 x p)
                         y
                         p)
            (pfield::add (pfield::add y x p)
                         (pfield::mul (1- p) z p)
                         p)))
   (defrule deep-to-shallow
     (implies (and (symbolp x)
                   (symbolp y)
                   (symbolp z)
                   (primep p)
                   (r1cs::r1cs-valuationp asg p)
                   (r1cs::valuation-bindsp asg x)
                   (r1cs::valuation-bindsp asg y)
                   (r1cs::valuation-bindsp asg z))
              (b* ((x$ (lookup-equal x asg))
                   (y$ (lookup-equal y asg))
                   (z$ (lookup-equal z asg)))
                (implies (and (bitp x$)
                              (bitp y$))
                         (equal (r1cs::r1cs-constraints-holdp
                                 (boolean-xor-gadget x y z p) asg p)
                                (shallow x$ y$ z$ p)))))
     :enable (boolean-xor-gadget
              r1cs::r1cs-constraint-holdsp
              r1cs::dot-product
              shallow))
   (defrule shallow-to-bitxor
     (implies (and (bitp x)
                   (bitp y)
                   (pfield::fep z p)
                   (primep p))
              (equal (shallow x y z p)
                     (equal z (if (equal x y) 0 1))))
     :enable (shallow
              pfield::add
              pfield::neg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of exclusive disjunction gadgets.

(define boolean-xor-gadget-list ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp)
                                 (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len zs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (boolean-xor-gadget (car xs) (car ys) (car zs) p)
                   (boolean-xor-gadget-list (cdr xs) (cdr ys) (cdr zs) p)))))

; A list of exclusive disjunction gadgets is equivalent to its specification,
; which is in terms of BITXOR-LIST.

(defruled boolean-xor-gadget-list-to-bitxor-list
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len xs) (len ys))
                (equal (len ys) (len zs))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (boolean-xor-gadget-list xs ys zs p) asg p)
                             (equal zs$ (bitxor-list xs$ ys$))))))
  :induct (ind xs ys zs)
  :enable (boolean-xor-gadget-list
           boolean-xor-gadget-to-bitxor
           bitxor-list
           lookup-equal-list)
  :disable bitp
  :prep-lemmas
  ((defun ind (x y z)
     (cond ((or (atom x) (atom y) (atom z)) nil)
           (t (ind (cdr x) (cdr y) (cdr z)))))))
