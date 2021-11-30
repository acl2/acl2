; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file is more general than ATC; it may be moved to a more general library.
; This file provides a macro to generate theorems
; about two or more unary predicates P1, ..., Pn being disjoint.
; The generated theorems have the form (IMPLIES (Pi X) (NOT (Pj X))),
; for each i /= j, saying that if something is a Pi then it is not a Pj.
; The theorems are generated as disabled rewrite rules;
; even if they are all enabled,
; ACL2's ancestor check (also the trivial one) should prevent rewriting loops.
; In fact, in ATC's symbolic execution proofs,
; we enable these theorems to handle case splits on values.
; The macro assumes that each theorem can be proved
; by simply enabling Pi and Pj.
; Besides the theorems, the macro also generates a constant
; with the names of all the theorems,
; so it can be used to enable all the theorems in the symbolic execution.

; The macro is called as (DEFTHM-DISJOINT *RULES* P1 ... Pn),
; where *RULES* is used as the name of the constant
; whose value is the list of names of the generated theorems.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defthm-disjoint-inner-loop ((pi symbolp) (pjs symbol-listp))
  :returns (mv (events pseudo-event-form-listp)
               (names symbol-listp))
  (b* (((when (endp pjs)) (mv nil nil))
       (pj (car pjs))
       ((when (eq pi pj)) (defthm-disjoint-inner-loop pi (cdr pjs)))
       (name (packn-pos (list "NOT-" pj "-WHEN-" pi) 'atc))
       (event `(defruled ,name
                 (implies (,pi x)
                          (not (,pj x)))
                 :enable (,pi ,pj)))
       ((mv more-events more-names) (defthm-disjoint-inner-loop pi (cdr pjs))))
    (mv (cons event more-events)
        (cons name more-names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defthm-disjoint-outer-loop ((pis symbol-listp) (pjs symbol-listp))
  :returns (mv (events pseudo-event-form-listp)
               (names symbol-listp))
  (b* (((when (endp pis)) (mv nil nil))
       ((mv events names) (defthm-disjoint-inner-loop (car pis) pjs))
       ((mv more-events more-names) (defthm-disjoint-outer-loop (cdr pis) pjs)))
    (mv (append events more-events)
        (append names more-names)))
  :prepwork
  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defthm-disjoint-fn ((c symbolp) (ps symbol-listp))
  :returns (event pseudo-event-formp)
  (b* (((mv thms names) (defthm-disjoint-outer-loop ps ps))
       (const `(defconst ,c ',names)))
    `(progn ,const ,@thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defthm-disjoint (c &rest ps)
  `(make-event (defthm-disjoint-fn ',c ',ps)))
