; Tests for prune-with-contexts
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "prune-with-contexts")
(include-book "make-term-into-dag-array-basic")
(include-book "dag-to-term")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defthm not-myquotep-when-not-equal-of-car-and-quote
  (implies (not (equal (car item) 'quote))
           (not (myquotep item)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defun prunes-to (term expected-result-term)
  (declare (xargs :guard (pseudo-termp term)
                  :guard-hints (("Goal" :in-theory (disable myquotep)))
                  :guard-debug t
                  ))
  (b* (((mv erp dag-or-quotep) (make-term-into-dag-basic term nil)) ;todo: use a version that doesn't simplify/eval!
       ((when erp)
        (er hard? 'prunes-to "Error making term into dag.")
        nil)
       ((when (quotep dag-or-quotep))
        (er hard? 'prunes-to "Attempting to call prune-dag on the constant ~x0." dag-or-quotep)
        nil)
       ((mv erp dag-or-quotep)
        (prune-with-contexts dag-or-quotep))
       ((when erp)
        (er hard? 'prunes-to "Error pruning dag.")
        nil)
       (result-term (dag-to-term dag-or-quotep)))
    (if (equal result-term expected-result-term)
        t
      (er hard? 'prunes-to "Term ~x0 did not prune to ~x1.  Instead, as we got ~x2." term expected-result-term result-term))))

(assert-event (prunes-to 'a 'a))
;(assert-event (prunes-to '(cons '1 '2) '3)) ;todo: the constant gets computed before pruning
