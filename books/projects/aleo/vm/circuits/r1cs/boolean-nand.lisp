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

; We define a function for the negated conjunction of two bits,
; even though perhaps we could just use the built-in LOGNAND.

(define bitnand ((x bitp) (y bitp))
  :returns (z bitp)
  (if (and (= x 1) (= y 1)) 0 1))

; We introduce a function that lifts BITNAND to lists.

(define bitnand-list ((xs bit-listp) (ys bit-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs bit-listp)
  (cond ((endp xs) nil)
        (t (cons (bitnand (car xs) (car ys))
                 (bitnand-list (cdr xs) (cdr ys)))))
  ///

  (defret len-of-bitnand-list
    (equal (len zs) (len xs)))

  (defruled bitnand-list-of-append
    (implies (equal (len xs1) (len ys1))
             (equal (bitnand-list (append xs1 xs2)
                                  (append ys1 ys2))
                    (append (bitnand-list xs1 ys1)
                            (bitnand-list xs2 ys2)))))

  (defruled bitnand-list-of-rev
    (implies (equal (len xs) (len ys))
             (equal (bitnand-list (rev xs) (rev ys))
                    (rev (bitnand-list xs ys))))
    :enable bitnand-list-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is negated conjunction.
; It assumes that x and y are booleans,
; and constrains z to be their negated conjunction,
; i.e. 0 iff both are 1.
; The gadget consists of a single constraint
;   (x) (y) = ((p-1)z + 1)

(define boolean-nand-gadget ((x symbolp) (y symbolp) (z symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list (1- p) z)
                  (list 1 1)))))

; The gadget is equivalent to its specification,
; i.e. that z is the negated conjunction of x and y
; assuming x and y are booleans.

(defruled boolean-nand-gadget-to-bitnand
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
                              (boolean-nand-gadget x y z p) asg p)
                             (equal z$ (bitnand x$ y$))))))
  :enable (boolean-nand-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of negated conjunction gadgets.

(define boolean-nand-gadget-list ((xs symbol-listp)
                                  (ys symbol-listp)
                                  (zs symbol-listp)
                                  (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len zs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (boolean-nand-gadget (car xs) (car ys) (car zs) p)
                   (boolean-nand-gadget-list (cdr xs) (cdr ys) (cdr zs) p)))))

; A list of negated conjunction gadgets is equivalent to its specification,
; which is in terms of BITNAND-LIST.

(defruled boolean-nand-gadget-list-to-bitnand-list
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
                              (boolean-nand-gadget-list xs ys zs p) asg p)
                             (equal zs$ (bitnand-list xs$ ys$))))))
  :induct (ind xs ys zs)
  :enable (boolean-nand-gadget-list
           boolean-nand-gadget-to-bitnand
           bitnand-list
           lookup-equal-list)
  :disable bitp
  :prep-lemmas
  ((defun ind (x y z)
     (cond ((or (atom x) (atom y) (atom z)) nil)
           (t (ind (cdr x) (cdr y) (cdr z)))))))
