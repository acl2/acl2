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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification

; We define a function for the negated disjunction of two bits,
; even though perhaps we could just use the built-in LOGNOR.

(define bitnor ((x bitp) (y bitp))
  :returns (z bitp)
  (if (or (= x 1) (= y 1)) 0 1))

; We introduce a function that lifts BITNOR to lists.

(define bitnor-list ((xs bit-listp) (ys bit-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs bit-listp)
  (cond ((endp xs) nil)
        (t (cons (bitnor (car xs) (car ys))
                 (bitnor-list (cdr xs) (cdr ys)))))
  ///

  (defret len-of-bitnor-list
    (equal (len zs) (len xs)))

  (defruled bitnor-list-of-append
    (implies (equal (len xs1) (len ys1))
             (equal (bitnor-list (append xs1 xs2)
                                 (append ys1 ys2))
                    (append (bitnor-list xs1 ys1)
                            (bitnor-list xs2 ys2)))))

  (defruled bitnor-list-of-rev
    (implies (equal (len xs) (len ys))
             (equal (bitnor-list (rev xs) (rev ys))
                    (rev (bitnor-list xs ys))))
    :enable bitnor-list-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is negated (inclusive) disjunction.
; It assumes that x and y are booleans,
; and constrains z to be their negated disjunction,
; i.e. 1 iff both are 0.
; The gadget consists of a single constraint
;   ((p-1)x + 1) ((p-1)y + 1) = (z)

(define boolean-nor-gadget ((x symbolp) (y symbolp) (z symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list (1- p) x)
                  (list 1 1))
         :b (list (list (1- p) y)
                  (list 1 1))
         :c (list (list 1 z)))))

; The gadget is equivalent to its specification,
; i.e. that z is the negated disjunction of x and y
; assuming x and y are booleans.

(defruled boolean-nor-gadget-to-bitnor
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
                              (boolean-nor-gadget x y z p) asg p)
                             (equal z$ (bitnor x$ y$))))))
  :enable (boolean-nor-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of negated disjunction gadgets.

(define boolean-nor-gadget-list ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp)
                                 (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len zs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (boolean-nor-gadget (car xs) (car ys) (car zs) p)
                   (boolean-nor-gadget-list (cdr xs) (cdr ys) (cdr zs) p)))))

; A list of negated disjunction gadgets is equivalent to its specification,
; which is in terms of BITNOR-LIST.

(defruled boolean-nor-gadget-list-to-bitnor-list
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
                              (boolean-nor-gadget-list xs ys zs p) asg p)
                             (equal zs$ (bitnor-list xs$ ys$))))))
  :induct (ind xs ys zs)
  :enable (boolean-nor-gadget-list
           boolean-nor-gadget-to-bitnor
           bitnor-list
           lookup-equal-list)
  :disable bitp
  :prep-lemmas
  ((defun ind (x y z)
     (cond ((or (atom x) (atom y) (atom z)) nil)
           (t (ind (cdr x) (cdr y) (cdr z)))))))
