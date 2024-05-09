; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, May, 2008
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines a function, computed-hint-rewrite, that makes it easy to
; call the ACL2 rewriter in a computed hint.  For details see the comment in
; the definition of computed-hint-rewrite, below.  Thanks to Jared Davis for
; requesting this utility.

; This utility does not attempt to build a linear database for the given hyps.
; But it probably could with a little work.

; (depends-on "build/defrec-certdeps/REWRITE-CONSTANT.certdep" :dir :system)
; (depends-on "build/defrec-certdeps/PROVE-SPEC-VAR.certdep" :dir :system)

(in-package "ACL2")

(program)
(set-state-ok t)

(defun computed-hint-rewrite (term hyps provep
                                   cl hist pspv wrld ctx state)

; This function returns an error triple (mv erp val state).  Erp is t if we
; find a contradiction in the hypotheses.  Otherwise erp is nil and val is a
; pair (cons rewritten-term ttree), where rewritten-term and ttree are
; respectively the rewritten value of term together with the justifying
; tag-tree.  If you want only the rewritten term, check that erp is nil and
; then use (car val).

; Set provep to t or nil for optimal results if you are trying to prove term or
; its negation, respectively; otherwise set it to ?.

  (mv-let (rcnst signal)
    (simplify-clause-rcnst cl hist pspv wrld)
    (declare (ignore signal))
    (let* ((ens (access rewrite-constant rcnst :current-enabled-structure))
           (gstack nil))
      (mv-let
        (flg hyps-type-alist ttree)
        (hyps-type-alist hyps ens wrld state)
        (cond (flg (er hard ctx
                       "~x0 found a contradiction in the hypotheses."
                       'computed-hint-rewrite))
              (t (sl-let (new-term new-ttree)
                         (rewrite-entry
                          (rewrite term nil 'computed-hint-rewrite)
                          :rdepth (rewrite-stack-limit wrld)
                          :type-alist hyps-type-alist
                          :obj provep
                          :geneqv (if (member-eq provep '(t nil)) *geneqv-iff* nil)
                          :pequiv-info nil
                          :fnstack nil
                          :ancestors nil
                          :backchain-limit (backchain-limit wrld :rewrite)
                          :step-limit (initial-step-limit wrld state)
                          :simplify-clause-pot-lst nil
                          :rcnst rcnst
                          :gstack gstack
                          :ttree ttree)
                         (declare (ignorable step-limit))
                         (cons new-term new-ttree))))))))

; Silly example:

#||
(defun my-computed-hint (clause hist pspv wrld ctx state)
  (declare (xargs :mode :program
                  :stobjs state))
  (cond ((null (cdr clause))
         (value nil))
        (t
         (let ((hyps (dumb-negate-lit-lst (butlast clause 1)))
               (conc (car (last clause))))
           (mv-let (erp term-ttree state)
                   (computed-hint-rewrite conc hyps t clause hist pspv wrld ctx
                                          state)
                   (cond ((and (not erp) term-ttree)
                          (prog2$ (cw "~%NOTE: computed-hint-rewrite returned ~
                                       term-ttree pair ~x0.~|~@1"
                                      term-ttree
                                      (if (and (gag-mode)
                                               (@ print-clause-ids))
                                          "~%"
                                        ""))
                                  (value (and (equal (car term-ttree)
                                                     ''t)
                                              '(:use car-cons)))))
                         (t (value nil))))))))

(add-default-hints '((my-computed-hint clause hist pspv world ctx state)))

; Optional:
(in-theory (disable (:definition binary-append)))

(thm (equal (append (append x y) z) (append (car (cons x x)) y z)))

||#
