; Another experiment verifying a rewriter-like tool
;
; Copyright (C) 2020-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book is like rewriter0.lisp except we extract the formula of the rule
;; separately from where we use it.  The goal is to see whether we can pass
;; around meta-extracted facts and what we have to say about them in
;; correctness proofs.

(include-book "clause-processors/meta-extract-user" :dir :system)

;; Evaluator needed to state the :meta rule
(defevaluator evl evl-list
  ;; If any of these is missing, the def-meta-extract machinery doesn't work:
  ((typespec-check ts x) ;; why needed?
   (if x y z)
   (equal x y)
   (not x)
   (iff x y)
   (implies x y)))

;; Generates some very helpful machinery
(def-meta-extract evl evl-list)

;; This checks whether FORMULA is an equality whose left-hand-side is TERM.  If
;; so, this returns the right-hand-side of the equality, indicating a
;; replacement of TERM.  Note that the match must be exact; we don't do any
;; unification of TERM with the left-hand-side.  We also don't rewrite any
;; subterms of TERM.
(defund rewrite-term-with-formula (term formula)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp formula))))
  ;; Check that the formula is an equality of TERM with something:
  (if (and (= 3 (len formula))
           (eq 'equal (ffn-symb formula))
           (equal term (fargn formula 1)))
      ;; Replace TERM with the thing it's equated to in the formula:
      (fargn formula 2)
    ;; Formula has the wrong form, so make no change:
    term))

;; Proves that rewrite-term-with-formula is correct; it replaces TERM with
;; and equivalent term assuming FORMULA is true.
(defthm eval-of-rewrite-term-with-formula
  (implies (evl formula a)
           (equal (evl (rewrite-term-with-formula term formula) a)
                  (evl term a)))
  :hints (("Goal" :in-theory (enable rewrite-term-with-formula))))

;; The metafunction. This checks whether a theorem named MY-RULE exists. Is so,
;; and if it is an equality whose left-hand-side is TERM, this replaces TERM
;; with the right-hand-side of the equality.  Note that the match must be
;; exact; we don't do any unification of TERM with the left-hand-side.  We also
;; don't rewrite any subterms of TERM.
(defun apply-rule-to-term (term mfc state)
  (declare (xargs :stobjs state
                  :guard (pseudo-termp term))
           (ignore mfc) ; always passed in to extended metafunctions
           )
  ;; Get the formula for the theorem out of the state.  It must be named
  ;; MY-RULE.
  (let ((formula (meta-extract-formula 'my-rule state)))
    (if (not (pseudo-termp formula))
        (prog2$ (er hard? 'apply-rule-to-term "Non-pseudo-term formula, ~x0, found for ~x1." formula 'myrule)
                term ;; no change
                )
      (rewrite-term-with-formula term formula))))

;; The :meta rule.  The machinery provided by def-meta-extract helps us state
;; and prove this.
(defthm apply-rule-to-term-meta-rule
  (implies (evl-meta-extract-global-facts :state state)
           (equal (evl x a)
                  (evl (apply-rule-to-term x mfc state) a)))
  ;;  Having to list the :trigger-fns here makes this rule somewhat un-general.
  ;;  We include CAR and LEN since those are used in the examples below:
  :rule-classes ((:meta :trigger-fns (car len)))
  :hints (("Goal" :use (:instance evl-meta-extract-formula
                                  (st state)
                                  (name 'my-rule))
           :in-theory (disable evl-meta-extract-formula))))

;;;
;;; Examples
;;;

;; First example, using a rule like car-cons.
(encapsulate
  ()
  ;; Note that this is defined after the :meta rule, so we know that this fact is
  ;; not built-in to the :meta rule.  Only the name (MY-RULE) and the
  ;; trigger-fn (CAR) are built in.
  (local
   (defthm my-rule
     (equal (car (cons x y))
            x)))

  ;; Test the :meta rule:
  (thm
   (equal (car (cons x y))
          x)
   ;; Do the proof using only the :meta rule:
   :hints (("Goal" :in-theory '(apply-rule-to-term-meta-rule)))))

;; Second example, using a fact about len
(encapsulate
  ()
  (local
   ;; Here we give MY-RULE a totally different body than in the example just
   ;; above, showing that the :meta rule is quite general.  It works no matter
   ;; what formula MY-RULE has.
   (defthm my-rule
     (equal (len (list x y z))
            3)))

  ;; Test the :meta rule:
  (thm
   (equal (len (list x y z))
          3)
   ;; Do the proof using only the :meta rule:
   :hints (("Goal" :in-theory '(apply-rule-to-term-meta-rule)))))
