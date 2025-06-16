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

(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A ternary conditional gadget,
; which constrains w to be either y or z,
; based on whether x (assumed boolean) is 1 or 0.

; There is a single constraint equivalent to
;   (x) (y + (p-1)z) = (w + (p-1)z)
; i.e.
;   (x) (y - z) = (w - z)
; Thus, if x = 0, we have w - z = 0, i.e. w = z;
; while, if x = 1, we have y - z = w - z, i.e. w = y.

; Note, currently in snarkVM, a field ternary (y, z and w are fields) results
; in the above operand order, but a boolean ternary returns the addends in the
; other order (despite identical-looking Rust code) resulting in
;   (x) ((p-1)z + y) = ((p-1)z + w)
; i.e.
;   (x) (-z + y) = (-z + w)
; so we have if-gadget-variant below that we can use for boolean
; ternaries, until we get normalization/equiv/congruence of R1CS to handle
; this sort of minor difference when rewriting.

; snarkVM field ternary turns into this
(define if-gadget ((x symbolp)
                   (y symbolp)
                   (z symbolp)
                   (w symbolp)
                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y)
                  (list (1- p) z))
         :c (list (list 1 w)
                  (list (1- p) z)))))

; snarkVM boolean ternary turns into this
(define if-gadget-variant ((x symbolp)
                           (y symbolp)
                           (z symbolp)
                           (w symbolp)
                           (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list (1- p) z)
                  (list 1 y))
         :c (list (list (1- p) z)
                  (list 1 w)))))

; The gadget is equivalent to its specification,
; written in terms of the built-in function IF.
; assuming that x is boolean.

(defruled if-gadget-to-if
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg))
                (w$ (lookup-equal w asg)))
             (implies (bitp x$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (if-gadget x y z w p) asg p)
                             (equal w$ (if (= x$ 1) y$ z$))))))
  :enable (if-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

(defruled if-gadget-variant-to-if
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg))
                (w$ (lookup-equal w asg)))
             (implies (bitp x$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (if-gadget-variant x y z w p) asg p)
                             (equal w$ (if (= x$ 1) y$ z$))))))
  :enable (if-gadget-variant
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a version of the if-gadget-variant above
; where the condition is negated.
; It arises as a sub-gadget of certain snarkVM gadgets.

(define if-not-gadget-variant ((x symbolp)
                               (y symbolp)
                               (z symbolp)
                               (w symbolp)
                               (one symbolp)
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list (1- p) x)
                  (list 1 one))
         :b (list (list (1- p) z)
                  (list 1 y))
         :c (list (list (1- p) z)
                  (list 1 w)))))

(defruled if-not-gadget-variant-to-if
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg))
                (w$ (lookup-equal w asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bitp x$)
                           (equal one$ 1))
                      (equal (r1cs::r1cs-constraints-holdp
                              (if-not-gadget-variant x y z w one p) asg p)
                             (equal w$ (if (= x$ 0) y$ z$))))))
  :enable (if-not-gadget-variant
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of conditional gadgets.

(define if-gadget-list ((xs symbol-listp)
                        (ys symbol-listp)
                        (zs symbol-listp)
                        (ws symbol-listp)
                        (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len zs))
              (equal (len zs) (len ws)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (if-gadget (car xs) (car ys) (car zs) (car ws) p)
                   (if-gadget-list (cdr xs) (cdr ys) (cdr zs) (cdr ws) p)))))

; Function used in the specification of the list of conditional gadgets.

(define if-list ((xs bit-listp)
                 (ys (pfield::fe-listp ys p))
                 (zs (pfield::fe-listp zs p))
                 (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len zs)))
  :returns (ws (pfield::fe-listp ws p) :hyp (and (pfield::fe-listp ys p)
                                                 (pfield::fe-listp zs p)
                                                 (equal (len xs) (len ys))
                                                 (equal (len ys) (len zs))))
  (cond ((endp xs) nil)
        (t (cons (if (= (car xs) 1) (car ys) (car zs))
                 (if-list (cdr xs) (cdr ys) (cdr zs) p)))))

; The list of gadgets if correct with respect to its specification,
; assuming the elements of xs are all boolean.

(defruled if-gadget-list-to-if-list
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbol-listp ws)
                (equal (len xs) (len ys))
                (equal (len ys) (len zs))
                (equal (len zs) (len ws))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bit-listp xs$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (if-gadget-list xs ys zs ws p) asg p)
                             (equal ws$ (if-list xs$ ys$ zs$ p))))))
  :induct (ind xs ys zs ws)
  :enable (if-gadget-list
           if-gadget-to-if
           if-list
           lookup-equal-list)
  :prep-lemmas
  ((defun ind (xs ys zs ws)
     (cond ((or (atom xs) (atom ys) (atom zs) (atom ws)) nil)
           (t (ind (cdr xs) (cdr ys) (cdr zs) (cdr ws)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialized version of the gadget with 'else' = 0.
; It consists of a single constraint
;   (x) (y) = (z)
; which can be obtained from the one of the general gadget
; by setting 'else' to 0.

(define if0-gadget ((x symbolp) (y symbolp) (z symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 z)))))

; Function used in the specification.

(define if0 ((x bitp) (y (pfield::fep y p)) (p primep))
  (declare (ignore p))
  :returns (z (pfield::fep z p) :hyp (pfield::fep y p))
  (if (= x 1) y 0))

; The specialized conditional gadget
; is correct with respect to its specification,
; expressed in terms of IF0.

(defruled if0-gadget-to-if0
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
             (implies (bitp x$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (if0-gadget x y z) asg p)
                             (equal z$ (if0 x$ y$ p))))))
  :enable (if0-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           if0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialized version of the gadget with 'else' = 1.
; It consists of a single constraint
;   (x) (y + (p-1)) = (z + (p-1))
; i.e.
;   (x) (y - 1) = (z - 1)
; which can be obtained from the general gadget
; by setting 'else' to 1.

(define if1-gadget ((x symbolp) (y symbolp) (z symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y)
                  (list (1- p) 1))
         :c (list (list 1 z)
                  (list (1- p) 1)))))

; Function used in the specification.

(define if1 ((x bitp) (y (pfield::fep y p)) (p primep))
  (declare (ignore p))
  :returns (z (pfield::fep z p):hyp (and (pfield::fep y p) (primep p)))
  (if (= x 1) y 1))

; The specialized conditional gadget
; is correct with respect to its specification,
; expressed in terms of IF1.

(defruled if1-gadget-to-if1
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
             (implies (bitp x$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (if1-gadget x y z p) asg p)
                             (equal z$ (if1 x$ y$ p))))))
  :enable (if1-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           if1))
