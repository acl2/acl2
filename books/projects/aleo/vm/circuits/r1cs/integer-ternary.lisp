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

(include-book "if")

(local (include-book "kestrel/lists-light/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a ternary gadget on integers (on lists of bits, really).
; It is the same for signed and unsigned intgers.
; Based on whether x (assume boolean) is 1 or 0, ws is either ys or zs.

(define integer-ternary-gadget ((x symbolp)
                                (ys symbol-listp)
                                (zs symbol-listp)
                                (ws symbol-listp)
                                (p primep))
  :guard (and (equal (len zs) (len ys))
              (equal (len ws) (len ys)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp ys) nil)
        (t (append (if-gadget-variant x (car ys) (car zs) (car ws) p)
                   (integer-ternary-gadget x (cdr ys) (cdr zs) (cdr ws) p)))))

(defruled integer-ternary-gadget-correctness
  (implies (and (primep p)
                (symbolp x)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbol-listp ws)
                (equal (len zs) (len ys))
                (equal (len ws) (len ys))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((x$ (lookup-equal x asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bitp x$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (integer-ternary-gadget x ys zs ws p) asg p)
                             (equal ws$ (if (= x$ 1) ys$ zs$))))))
  :induct (ind ys zs ws)
  :enable (integer-ternary-gadget
           if-gadget-variant-to-if
           lookup-equal-list)
  :prep-lemmas
  ((defun ind (ys zs ws)
     (cond ((or (atom ys) (atom zs) (atom ws)) nil)
           (t (ind (cdr ys) (cdr zs) (cdr ws)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a variant of the above gadget in which the test is negated.

(define integer-ternary-not-gadget ((x symbolp)
                                    (ys symbol-listp)
                                    (zs symbol-listp)
                                    (ws symbol-listp)
                                    (one symbolp)
                                    (p primep))
  :guard (and (equal (len zs) (len ys))
              (equal (len ws) (len ys)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp ys) nil)
        (t (append
            (if-not-gadget-variant x (car ys) (car zs) (car ws) one p)
            (integer-ternary-not-gadget x (cdr ys) (cdr zs) (cdr ws) one p)))))

(defruled integer-ternary-not-gadget-correctness
  (implies (and (primep p)
                (symbolp x)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbol-listp ws)
                (symbolp one)
                (equal (len zs) (len ys))
                (equal (len ws) (len ys))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg ws)
                (r1cs::valuation-bindsp asg one))
           (b* ((x$ (lookup-equal x asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (ws$ (lookup-equal-list ws asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bitp x$)
                           (equal one$ 1))
                      (equal (r1cs::r1cs-constraints-holdp
                              (integer-ternary-not-gadget x ys zs ws one p)
                              asg
                              p)
                             (equal ws$ (if (= x$ 0) ys$ zs$))))))
  :induct (ind ys zs ws)
  :enable (integer-ternary-not-gadget
           if-not-gadget-variant-to-if
           lookup-equal-list)
  :prep-lemmas
  ((defun ind (ys zs ws)
     (cond ((or (atom ys) (atom zs) (atom ws)) nil)
           (t (ind (cdr ys) (cdr zs) (cdr ws)))))))
