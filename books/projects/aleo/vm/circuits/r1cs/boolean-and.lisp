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

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification

; We define a function for the conjunction of two bits,
; even though perhaps we could just use the built-in LOGAND.

(define bitand ((x bitp) (y bitp))
  :returns (z bitp)
  (if (and (= x 1) (= y 1)) 1 0))

; We introduce a function that lifts BITAND to lists.

(define bitand-list ((xs bit-listp) (ys bit-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs bit-listp)
  (cond ((endp xs) nil)
        (t (cons (bitand (car xs) (car ys))
                 (bitand-list (cdr xs) (cdr ys)))))
  ///

  (defret len-of-bitand-list
    (equal (len zs) (len xs)))

  (defruled bitand-list-of-append
    (implies (equal (len xs1) (len ys1))
             (equal (bitand-list (append xs1 xs2)
                                 (append ys1 ys2))
                    (append (bitand-list xs1 ys1)
                            (bitand-list xs2 ys2)))))

  (defruled bitand-list-of-rev
    (implies (equal (len xs) (len ys))
             (equal (bitand-list (rev xs) (rev ys))
                    (rev (bitand-list xs ys))))
    :enable bitand-list-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is boolean conjunction.
; It assumes that x and y are booleans,
; and constrains z to be their conjunction,
; i.e. 1 iff both are 1.
; The gadget consists of a single constraint
;   (x) (y) = (z)

(define boolean-and-gadget ((x symbolp) (y symbolp) (z symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 z)))))

; The gadget is equivalent to its specification,
; i.e. that z is the conjunction of x and y
; assuming x and y are booleans.

(defruled boolean-and-gadget-to-bitand
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
                              (boolean-and-gadget x y z) asg p)
                             (equal z$ (bitand x$ y$))))))
  :enable (boolean-and-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of conjunction gadgets.

(define boolean-and-gadget-list ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (zs symbol-listp))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len zs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (boolean-and-gadget (car xs) (car ys) (car zs))
                   (boolean-and-gadget-list (cdr xs) (cdr ys) (cdr zs))))))

; A list of conjunction gadgets is equivalent to its specification,
; which is in terms of BITAND-LIST.

(defruled boolean-and-gadget-list-to-bitand-list
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
                              (boolean-and-gadget-list xs ys zs) asg p)
                             (equal zs$ (bitand-list xs$ ys$))))))
  :induct (ind xs ys zs)
  :enable (boolean-and-gadget-list
           boolean-and-gadget-to-bitand
           bitand-list
           lookup-equal-list)
  :disable bitp
  :prep-lemmas
  ((defun ind (x y z)
     (cond ((or (atom x) (atom y) (atom z)) nil)
           (t (ind (cdr x) (cdr y) (cdr z)))))))
