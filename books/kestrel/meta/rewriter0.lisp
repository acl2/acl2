; An experiment verifying a rewriter-like tool
;
; Copyright (C) 2020-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book shows an example of using meta-extract and def-meta-extract to
;; verify a rewriter-like tool that applies a theorem from the world.  It is
;; designed to be as simple as possible.

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

;; The metafunction. This checks whether a theorem named MY-RULE exists. If so,
;; and if it is an equality whose left-hand-side is TERM, this replaces TERM
;; with the right-hand-side of the equality.  Note that the match must be
;; exact; we don't do any unification of TERM with the left-hand-side.  We also
;; don't rewrite any subterms of TERM.
(defun apply-rule-to-term (term mfc state)
  (declare (xargs :stobjs state)
           (ignore mfc) ; always passed in to extended metafunctions
           )
  ;; Get the formula for the theorem out of the state.  It must be named
  ;; MY-RULE.
  (let ((formula (meta-extract-formula 'my-rule state)))
    ;; Check that the formula is an equality of TERM with something:
    (if (and (= 3 (len formula))
             (eq 'equal (ffn-symb formula))
             (equal term (fargn formula 1)))
        ;; Replace TERM with the thing it's equated to in the formula:
        (fargn formula 2)
      ;; Formula has the wrong form, so make no change:
      term)))

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
