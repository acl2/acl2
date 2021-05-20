; Polarity-based rewriting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "translate")
(include-book "kestrel/terms-light/sublis-var-simple" :dir :system)

;; This book contains utilities to support "polarity-based rewriting," in which
;; how you want to rewrite a term depends on whether it appears as a hypothesis
;; (in which case you want to strengthen it, so that it provides more
;; information) or as a conclusion (in which case you want to weaken it, so
;; that it is easier to prove).

;; For example, if we know that x is an integer, then the following two terms
;; are equivalent: (< x 3) (<= x 2).  But note that these terms are not
;; equivalent in an absolute sense (i.e., if we do *not* know that x is an
;; integer).  If we do know that x is an integer, we can choose either of the
;; two forms, and which one we prefer depends on whether the term is a
;; hypothesis, in which case we prefer the stronger form, (<= x 2), or a
;; conclusion, in which case we prefer the weaker form, (< x 3).

;; NOTE: I had thought that ACL2's "rewrite objective" could indicate whether
;; we want to strengthen or weaken, but it seems that the rewrite objective is
;; not a reliable indicator of this; in particular, it can be ? when you'd
;; expect it to be T or NIL.

;; NOTE: See tests in polarity-tests.lisp

;; TODO: Add support for using this to weaken a hyp during backchaining
;; (currently, requires term to be weakened to be found in the clause).

;; A previous version of this tool caused a rewrite loop in roughly the
;; following scenaro: We are rewriting a hyp of (not "negative"), and we know
;; not 0, and we are trying to prove "positive". So we weaken "negative" in the
;; hyp to (not "positive").  So the hyp becomes (not (not "positive")). But
;; then we rerwrite "positive" because it is also a conclusion, indicating (to
;; the old version of this tool) that we want to weaken it!  Now this tool
;; actually checks the current literal, rather than looking for TERM in teh
;; entire clause.

;; This tool essentially does the following: Strip NOTs from TERM, flipping the
;; desired polarity each time.  Then, if the resulting TERM is the current
;; literal, we want to weaken TERM.  If instead the current literal is (not
;; TERM), we try to strengthen TERM (thus weakening (not TERM)).  Otherwise, we
;; do nothing (TODO: think about what to do if TERM arises during
;; back-chaining).

;; This tool is similar to the tool in books/std/lists/mfc-utils.lisp but
;; provides a nicer interface to the user.  In particular, it applies the
;; unify-subst to the term in the syntaxp hyp (after translating it), so the
;; user doesn't have to supply an untranslated term with a backquote.

;; Same as the one in books/std/lists/mfc-utils.lisp except doesn't take state.
;; Returns the "rewrite constant from the mfc (metafunction context).
(defun mfc-rcnst2 (mfc)
  (declare (xargs :mode :program))
  (access metafunction-context mfc :rcnst))

;; Same as the one in books/std/lists/mfc-utils.lisp except doesn't take state.
;; Returns (cons NOT-FLG ATM) where if not-flag is non-nil, then the current
;; literal is (not ATM) and if if not-flag is nil, then the current literal is
;; ATM.
(defun mfc-current-literal2 (mfc)
  (declare (xargs :mode :program))
  (let ((rcnst (mfc-rcnst2 mfc)))
    (access rewrite-constant rcnst :current-literal)))

;; ;; Check whether LIT appears in CLAUSE (for equalities, also check with
;; ;; reordered arguments [why?]):
;; (defun appears-in-clausep (lit clause)
;;   (declare (xargs :guard (and (pseudo-termp lit)
;;                               (pseudo-term-listp clause))))
;;   (if (ffn-symb-p lit 'equal)
;;       ;; If it's an equal, look for it with the args in the given order or reversed:
;;       (or (member-equal lit clause)
;;           (member-equal `(equal ,(fargn lit 2) ,(fargn lit 1)) clause))
;;     ;; Not an equal, so do the normal thing:
;;     (member-equal lit clause)))

(mutual-recursion
 (defun want-to-strengthen-fn (term mfc state)
   (declare (xargs :stobjs state
                   :mode :program ;because we call translate-term
                   :guard (and (true-listp mfc)
                               (pseudo-termp term))))
   (if (and (consp term)
            (eq 'not (ffn-symb term)))
       ;;TODO: perhaps this should be an error or warning (instead use the
       ;;argument of the NOT with the opposite polarity)
       (want-to-weaken-fn (fargn term 1) mfc state)
     (and (not (mfc-ancestors mfc)) ;the term is part of the current goal..
          (let* ( ;; Translate the term (very easy for the user to forget and
                 ;; give an untranslated term):
                 (term (translate-term term 'want-to-strengthen (w state))) ;TODO: Can we do this once, when the rule is created?
                 ;; Apply the unify subst (so the user doesn't have to give a term with backquote):
                 (unify-subst (mfc-unify-subst mfc))
                 (term (sublis-var-simple unify-subst term)) ;TODO, can we save the consing here?
                 (not-flg/atm (mfc-current-literal2 mfc))
                 (not-flg (car not-flg/atm))
                 (current-literal-core (cdr not-flg/atm)))
            ;; we want to strengthen hyps, and they are negated in the clause
            ;; that represents the goal, so check if the current literal is
            ;; (not <term>):
            (and not-flg
                 (equal term current-literal-core))))))

 (defun want-to-weaken-fn (term mfc state)
   (declare (xargs :stobjs state
                   :mode :program ;because we call translate-term
                   :guard (and (true-listp mfc)
                               (pseudo-termp term))))
   (if (and (consp term)
            (eq 'not (ffn-symb term)))
       ;;TODO: perhaps this should be an error or warning (instead use the
       ;;argument of the NOT with the opposite polarity)
       (want-to-strengthen-fn (fargn term 1) mfc state)
     (and (not (mfc-ancestors mfc)) ;the term is part of the current goal..
          (let* ( ;; Translate the term (very easy for the user to forget and
                 ;; give an untranslated term):
                 (term (translate-term term 'want-to-weaken (w state)))
                 ;; Apply the unify subst (so the user doesn't have to give a term with backquote):
                 (unify-subst (mfc-unify-subst mfc))
                 (term (sublis-var-simple unify-subst term))
                 (not-flg/atm (mfc-current-literal2 mfc))
                 (not-flg (car not-flg/atm))
                 (current-literal-core (cdr not-flg/atm)))
            ;; we want to weaken conclusions and they are non-negated in the
            ;; clause that represents the goal, so check if the current
            ;; literal is <term>:
            (and (not not-flg)
                 (equal term current-literal-core)))))))

;; Here is a suggestion on how to trace these functions without printing the MFC:
;; (trace$ (want-to-strengthen-fn :entry (list 'want-to-strengthen-fn term (mfc-clause mfc))))

;; Test whether strengthening TERM will help us prove the goal (because it
;; appears as a hypothesis of the current goal).
(defmacro want-to-strengthen (term)
  `(want-to-strengthen-fn ',term mfc state))

;; Test whether weakening TERM will help us prove the goal (because it
;; appears as a conclusion of the current goal).
(defmacro want-to-weaken (term)
  `(want-to-weaken-fn ',term mfc state))
