; Correctness of the ACL2 system function type-set-quote
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; TYPE-SET-QUOTE (in type-set-b.lisp) computes the type-set of a constant: one
;; of the primitive type-set bits (e.g., *ts-zero*, *ts-integer>1*,
;; *ts-proper-cons*).  It is soundness-critical: type-set uses it for every
;; quoted constant.

;; What a type-set means is given by ACL2's type-set-inverter rules: "A
;; type-set-inverter-rule states that x has type-set ts iff the conjunction of
;; terms{X/x} is true" (see the defrec of type-set-inverter-rule in tau.lisp).
;; Convert-type-set-to-term uses these rules to turn type-sets into terms.  We
;; prove that the type-set computed for every object agrees with every one of
;; the built-in rules, *initial-type-set-inverter-rules*: the object satisfies
;; the terms of a rule exactly when its type-set is a subset of the rule's
;; type-set.  (This book is for ACL2 without non-standard analysis, which has
;; additional type-set bits.)

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)

;; An evaluator for the terms in the built-in type-set-inverter rules.
(defevaluator+ type-set-inverter-eval
  atom acl2-numberp rationalp integerp complex-rationalp symbolp consp true-listp
  stringp characterp not equal < if)

;; Checks that, for each of the RULES, X satisfies the rule's terms iff the
;; type-set of X (as a constant) is a subset of the rule's type-set.
(defund type-set-quote-agrees-with-type-set-inverter-rules-p (rules x)
  (declare (xargs :verify-guards nil))
  (if (endp rules)
      t
    (let ((rule (car rules)))
      (and (iff (ts-subsetp (type-set-quote x)
                            (access type-set-inverter-rule rule :ts))
                (type-set-inverter-eval (conjoin (access type-set-inverter-rule rule :terms))
                                        (acons 'x x nil)))
           (type-set-quote-agrees-with-type-set-inverter-rules-p (cdr rules) x)))))

;; X must not be a "bad atom" (an object that is not a cons, number, symbol,
;; string, or character, if there are any such objects), for which
;; type-set-quote returns *ts-character*.  Bad atoms cannot appear in quoted
;; constants in terms.
(defthm type-set-quote-correct
  (implies (not (bad-atom x))
           (type-set-quote-agrees-with-type-set-inverter-rules-p *initial-type-set-inverter-rules* x))
  :hints (("Goal" :in-theory (enable type-set-quote-agrees-with-type-set-inverter-rules-p
                                     type-set-quote))))
