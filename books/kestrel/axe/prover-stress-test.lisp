; Stress testing the Axe Prover and comparing it to ACL2
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Since Axe and ACL2 are two provers for the same logic, we can test them
;; against each other.  This book contains a tool to do that by systematically
;; generating small formulas and calling both provers on each.  Formulas
;; rejected by both provers or proved by both provers are not very interesting
;; (though the latter could be added to a test suite).  Formulas proved by one
;; prover but rejected by the other may indicate a problem (a completeness
;; problem in one prover or a soundness bug in the other).

;; Currently, the formulas are so simple that we don't even provide Axe with
;; any rewrite rules to use.  Thus, these mostly test its handling of clauses,
;; literals, contradictions, equalities, generalized booleans, etc.

;; TODO: Try to get Axe to prove more of the formulas that ACL2 can prove.

;; TODO: Avoid formulas that are equivalent up to variable renaming.

(include-book "prover-basic")
(include-book "kestrel/utilities/prove-interface" :dir :system)

;; Returns state
(defun compare-axe-and-acl2-on-formula (formula state)
  (declare (xargs :stobjs state
                  :mode :program))
  (b* (;; Try to prove FORMULA with ACL2:
       ((mv & acl2-provedp state)
        (prove$ formula))
       ;; Try to prove FORMULA with Axe:
       ((mv failedp & state)
        (prove-implication-with-basic-prover-fn
         *t* ;use a hyp of t
         '(:rep :rewrite :subst)
         formula
         nil ; no rules
         nil ; no global rules
         nil ; no ifns
         nil ; no-splitp
         nil ; no monitored rules
         nil ;print
         state))
       (axe-provedp (not failedp)))
    (if (and acl2-provedp
             axe-provedp)
        (prog2$ (cw "Proved by both provers.~%")
                state)
      (if (and (not acl2-provedp)
               (not axe-provedp))
          (prog2$ (cw "Rejected by both provers.~%")
                  state)
        (if (and acl2-provedp
                 (not axe-provedp))
            (prog2$ (cw "(!! Proved only by ACL2: ~x0)~%" formula)
                    state)
          (prog2$ (cw "(!! Proved only by Axe: ~x0)~%" formula)
                  state))))))

;; Returns state
(defun compare-axe-and-acl2-on-formulas-aux (formulas state)
  (declare (xargs :stobjs state
                  :mode :program))
  (if (endp formulas)
      (mv (cw "DONE COMPARING PROVERS)~%")
          state)
    (let ((state (compare-axe-and-acl2-on-formula (first formulas) state)))
      (compare-axe-and-acl2-on-formulas-aux (rest formulas) state))))

;; Returns state
(defun compare-axe-and-acl2-on-formulas (formulas state)
  (declare (xargs :stobjs state
                  :mode :program))
  (prog2$ (cw "(COMPARING PROVERS on ~x0 formulas~%" (len formulas))
          (compare-axe-and-acl2-on-formulas-aux formulas state)))


;; constants and variables to use
(defconst *atoms* '(t nil 7 a b c))

(defconst *fns-and-arities*
  '((if . 3)
    (equal . 2)
    ;; (iff 2)))
    ))

(defun rev-cons-onto-all (item lsts acc)
  (declare (xargs :guard (true-listp lsts)))
  (if (endp lsts)
      acc
      (rev-cons-onto-all item (cdr lsts) (cons (cons item (car lsts)) acc))))

;; not sure about the order of the returned value
(defun cons-each-onto-all (items lst acc)
  (if (endp items)
      acc
    (cons-each-onto-all (rest items)
                        lst
                        (rev-cons-onto-all (first items) lst acc))))

(defun arg-combinations (arity args)
  (if (or (zp arity) ; should not happen
          (= arity 1))
      (enlist-all args)
    (cons-each-onto-all args (arg-combinations (+ -1 arity) args) nil)))

(defun make-all-calls (fns-and-arities args acc)
  (if (endp fns-and-arities)
      acc
    (let* ((fn-and-arity (first fns-and-arities))
           (fn (car fn-and-arity))
           (arity (cdr fn-and-arity))
           (arg-lists (arg-combinations arity args))
           )
      (make-all-calls (rest fns-and-arities)
                      args
                      (rev-cons-onto-all fn arg-lists acc)))))

;; (make-all-calls *fns-and-arities* '(a b) nil)

;; Make all formulas with up-to DEPTH nested function calls
(defun make-formulas (atoms fns-and-arities depth)
  (if (zp depth)
      atoms ; a list of formulas!
    (let ((shallower-formulas (make-formulas atoms fns-and-arities (+ -1 depth))))
      ;; Include the shallower formulas themselves:
      (revappend shallower-formulas
                 (make-all-calls fns-and-arities shallower-formulas nil)))))

;;(make-formulas *atoms* *fns-and-arities* 1)

;(compare-axe-and-acl2-on-formulas (make-formulas *atoms* *fns-and-arities* 1) state)
;(compare-axe-and-acl2-on-formulas (make-formulas *atoms* *fns-and-arities* 2) state)

;; (compare-axe-and-acl2-on-formulas (make-formulas
;;                                    '(t nil 7 a b)
;;                                    '((if . 3)
;;                                      (equal . 2)
;;                                      (iff . 2)
;;                                      (not . 1))
;;                                    2)
;;                                   state)
