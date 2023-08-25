; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file defthm.lisp.

; Last updated for git commit: b590f39f0599d9bffe5f32708b7c555240986325

(defun defthm-fn1 (name term state
                        rule-classes
                        instructions
                        hints
                        otf-flg
                        event-form
                        #+:non-standard-analysis std-p)
  (with-ctx-summarized
   (cons 'defthm name)

; At one time we thought that event-form could be nil.  It is simplest, for
; checking redundancy, not to consider the case of manufacturing an event-form,
; so now we insist on event-form being supplied (not nil).

   (assert$
    event-form
    (let ((wrld (w state))
          (event-form (or event-form
                          (list* 'defthm name term
                                 (append (if (not (equal rule-classes
                                                         '(:REWRITE)))
                                             (list :rule-classes rule-classes)
                                           nil)
                                         (if instructions
                                             (list :instructions instructions)
                                           nil)
                                         (if hints
                                             (list :hints hints)
                                           nil)
                                         (if otf-flg
                                             (list :otf-flg otf-flg)
                                           nil)))))
          (ld-skip-proofsp (ld-skip-proofsp state)))
      (pprogn
       (warn-on-inappropriate-defun-mode ld-skip-proofsp event-form ctx state)
       #+acl2-par
       (erase-acl2p-checkpoints-for-summary state)
       (with-waterfall-parallelism-timings
        name
        (er-let*
            ((ignore (chk-all-but-new-name name ctx nil wrld state))
             (cert-data-flg/tterm0
              (translate-for-defthm name term ctx wrld state))
             (cert-data-flg (value (car cert-data-flg/tterm0)))
             (tterm0 (value (cdr cert-data-flg/tterm0)))
             (tterm
              #+:non-standard-analysis
              (if std-p
                  (er-progn
                   (chk-classical-term-or-standardp-of-classical-term
                    tterm0 term ctx wrld state)
                   (translate (weaken-using-transfer-principle term)
                              t t t ctx wrld state))
                (value tterm0))
              #-:non-standard-analysis
              (value tterm0))
             (classes

; (#+:non-standard-analysis) We compute rule classes with respect to the
; original (translated) term.  The modified term is only relevant for proof.

              (translate-rule-classes name rule-classes tterm0 ctx (ens state)
                                      wrld state)))
          (cond
           ((redundant-theoremp name tterm0 classes event-form wrld)
            (stop-redundant-event ctx state))
           (t
            (enforce-redundancy
             event-form ctx wrld
             (with-useless-runes
              name
              wrld
              (er-let*
                  ((ens (value (ens state)))
                   (ttree1 (chk-acceptable-rules name classes ctx ens wrld
                                                 state))
                   (wrld1 (chk-just-new-name name nil 'theorem nil ctx wrld
                                             state))
                   (instructions (if (or (eq ld-skip-proofsp 'include-book)
                                         (eq ld-skip-proofsp
                                             'include-book-with-locals)
                                         (eq ld-skip-proofsp 'initialize-acl2))
                                     (value nil)
                                   (translate-instructions instructions ctx
                                                           state)))

; Observe that we do not translate the hints if ld-skip-proofsp is non-nil.
; Once upon a time we translated the hints unless ld-skip-proofsp was
; 'include-book, which meant we translated them if it was t, which meant we did
; it during initialize-acl2.  That caused a failure due to the fact that ENABLE
; was not defined when it was first used in axioms.lisp.  This choice is
; a little unsettling because it means

                   (thints (if (or (eq ld-skip-proofsp 'include-book)
                                   (eq ld-skip-proofsp 'include-book-with-locals)
                                   (eq ld-skip-proofsp 'initialize-acl2))
                               (value nil)
                             (translate-hints+ name
                                               hints

; If there are :instructions, then default hints are to be ignored; otherwise
; the error just below will prevent :instructions in the presence of default
; hints.

                                               (and (null instructions)
                                                    (default-hints wrld1))
                                               ctx wrld1 state)))
                   (ttree2 (cond (instructions
                                  (er-progn
                                   (cond (thints (er soft ctx
                                                     "It is not permitted to ~
                                                      supply both ~
                                                      :INSTRUCTIONS and ~
                                                      :HINTS to DEFTHM."))
                                         (t (value nil)))
                                   #+:non-standard-analysis
                                   (if std-p

; How could this happen?  Presumably the user created a defthm event using the
; proof-builder, and then absent-mindedly somehow suffixed "-std" on to the
; car, defthm, of that form.

                                       (er soft ctx
                                           ":INSTRUCTIONS are not supported ~
                                            for defthm-std events.")
                                     (value nil))
                                   (proof-builder name term
                                                  tterm classes instructions
                                                  wrld1 state)))
; patch file: skip prove call when skipping proofs ;patch;
                                 ((ld-skip-proofsp state) ;patch;
                                  (value nil)) ; replaces prove call ;patch;
; patch file: new case
                                 ((not (f-get-global 'certify-book-info ;patch;
                                                     state)) ;patch;

; This case arises when we are loading a portcullis file.  In that case, the
; defthm form isn't lexically in the book, so reports based on it could be
; misleading.  This issue was discovered when an assertion in the book
; event-symbol-table.lisp fired because state global 'certify-book-info was nil
; -- and thus we can't know the current book for the symbol-table.  I could fix
; that in the present patch file by setting some other state global before
; loading portcullis files; but I think it's best to stick to theorems in the
; actual book, to avoid potential confusion.

; The following call is the original code that goes here for defthm-fn1.

                                  (prove tterm ;patch;
                                         (make-pspv ens wrld1 state ;patch;
                                                    :displayed-goal term ;patch;
                                                    :otf-flg otf-flg) ;patch;
                                         thints ens wrld1 ctx state)) ;patch;
; patch file: modified prove call (also see just above)
#|
                                 (t (prove tterm
                                           (make-pspv ens wrld1 state
                                                      :displayed-goal term
                                                      :otf-flg otf-flg)
                                           thints ens wrld1 ctx state))))
|#
                                 (t ;patch;
                                  (er-let* ((pspv ;patch;
                                             (value ;patch;
                                              (make-pspv ens wrld1 state ;patch;
                                                         :displayed-goal term ;patch;
                                                         :otf-flg otf-flg))) ;patch;
                                            (ttree ;patch;
                                             (prove-set-time tterm pspv thints ;patch;
                                                             ens wrld1 ctx ;patch;
                                                             state)) ;patch;
                                            (used-induction ;patch;
                                             (value ;patch;
                                              (not (induction-free-ttree ;patch;
                                                    ttree)))) ;patch;
                                            (pspv1 ;patch;
                                             (value (if used-induction ;patch;
                                                        pspv ;patch;
                                                      (change prove-spec-var ;patch;
                                                              pspv ;patch;
                                                              :otf-flg t)))) ;patch;
                                            (wrld1a ;patch;
                                             (value ;patch;
                                              (if used-induction ;patch;
                                                  wrld1 ;patch;
                                                (putprop ;patch;
                                                 'induction-depth-limit-table ;patch;
                                                 'table-alist ;patch;
                                                 '((t . 0)) ;patch;
                                                 wrld1)))) ;patch;
                                            (acl2data-time-limit ;patch;
                                             (value (acl2data-time-limit ;patch;
                                                     *acl2data-prove-time*))) ;patch;
                                            #-skip-hyp ;patch;
                                            (hyp-alist ;patch;
                                             (note-retries ;patch;
                                              :hyp ;patch;
                                              (remove-hyp-checkpoints ;patch;
                                               term pspv1 thints ;patch;
                                               acl2data-time-limit ;patch;
                                               event-form ;patch;
                                               ens wrld1a ctx state))) ;patch;
                                            #-skip-hint-setting ;patch;
                                            (hint-setting-alist ;patch;
                                             (note-retries ;patch;
                                              :hint-setting ;patch;
                                              (remove-hint-setting-checkpoints ;patch;
                                               tterm pspv1 hints thints ;patch;
                                               acl2data-time-limit ;patch;
                                               event-form ;patch;
                                               ens wrld1a ctx state))) ;patch;
                                            #-skip-book-runes ;patch;
                                            (book-runes-alist ;patch;
                                             (note-retries ;patch;
                                              :book-runes ;patch;
                                              (remove-book-runes-checkpoints ;patch;
                                               tterm pspv1 ;patch;
                                               (all-runes-in-ttree ttree nil) ;patch;
                                               thints acl2data-time-limit ens ;patch;
                                               wrld1a ctx state))) ;patch;
                                            #-skip-rune ;patch;
                                            (rune-alist ;patch;
                                             (note-retries ;patch;
                                              :rune ;patch;
                                              (remove-rune-checkpoints ;patch;
                                               tterm pspv1 ;patch;
                                               ttree ;patch;
                                               thints acl2data-time-limit ens ;patch;
                                               wrld1a ctx state)))) ;patch;
                                    (pprogn ;patch;
                                     (cond ;patch;
                                      ((and #-skip-rune ;patch;
                                            (null rune-alist) ;patch;
                                            #-skip-hyp ;patch;
                                            (null hyp-alist) ;patch;
                                            #-skip-hint-setting ;patch;
                                            (null hint-setting-alist) ;patch;
                                            #-skip-book-runes ;patch;
                                            (null book-runes-alist)) ;patch;
; This happens for example when proofs are skipped or all retries are skipped.
                                       state) ;patch;
                                      (t (let ((rec (make acl2data ;patch;
                                                          :hash ;patch;
                                                          (check-sum-obj tterm) ;patch;
                                                          :expansion-stack ;patch;
                                                          *expansion-stack* ;patch;
                                                          :goal ;patch;
                                                          tterm ;patch;
                                                          :goal-clauses ;patch;
                                                          (acl2data-clausify+ ;patch;
                                                           tterm state) ;patch;
                                                          :event ;patch;
                                                          event-form ;patch;
                                                          :rule-classes ;patch;
                                                          rule-classes ;patch;
                                                          :used-induction ;patch;
                                                          used-induction ;patch;
                                                          #-skip-rune ;patch;
                                                          :rune-alist ;patch;
                                                          #-skip-rune ;patch;
                                                          rune-alist ;patch;
                                                          #-skip-hyp ;patch;
                                                          :hyp-alist ;patch;
                                                          #-skip-hyp ;patch;
                                                          hyp-alist ;patch;
                                                          #-skip-hint-setting ;patch;
                                                          :hint-setting-alist ;patch;
                                                          #-skip-hint-setting ;patch;
                                                          hint-setting-alist ;patch;
                                                          #-skip-book-runes ;patch;
                                                          :book-runes-alist ;patch;
                                                          #-skip-book-runes ;patch;
                                                          book-runes-alist ;patch;
                                                          :symbol-table ;patch;
                                                          (defthm-symbol-table ;patch;
                                                            tterm ;patch;
                                                            #-skip-rune rune-alist ;patch;
                                                            #+skip-rune nil ;patch;
                                                            hints ;patch;
                                                            thints ;patch;
                                                            wrld1 ;patch;
                                                            state)))) ;patch;
                                           (f-put-global ;patch;
                                            'acl2data-entry ;patch;
                                            #-acl2-advice ;patch;
                                            (cons name rec) ;patch;
                                            #+acl2-advice ;patch;
                                            (list* name ;patch;
                                                   tterm ;patch;
                                                   acl2data-time-limit ;patch;
                                                   rec) ;patch;
                                            state)))) ;patch;
                                     (value ttree)))))) ;patch;
                   (ttree3 (cond (ld-skip-proofsp (value nil))
                                 (t (prove-corollaries name tterm0 classes
                                                       ens wrld1 ctx
                                                       state)))))
                (let* ((wrld2 (add-rules name classes tterm0 term ens wrld1
                                         state))
                       (wrld3 (if cert-data-flg
                                  (update-translate-cert-data
                                   name wrld wrld2
                                   :type :defthm
                                   :inputs name
                                   :value tterm0
                                   :fns (all-fnnames tterm0)
                                   :vars (state-globals-set-by tterm0 nil))
                                wrld2))
                       (wrld4 (update-meta-props name ttree1 wrld3 state))
                       (ttree4 (cons-tag-trees ttree1
                                               (cons-tag-trees ttree2
                                                               ttree3))))
                  (er-progn
                   (chk-assumption-free-ttree ttree4 ctx state)
                   (print-rule-storage-dependencies name ttree1 state)
                   (install-event name
                                  event-form
                                  'defthm
                                  name
                                  ttree4
                                  nil :protect ctx wrld4
                                  state)))))))))))))
   :event-type 'defthm
   :event event-form))

(defun defthm-fn (name term state
                       rule-classes
                       instructions
                       hints
                       otf-flg
                       event-form
                       #+:non-standard-analysis std-p)

; Important Note:  Don't change the formals of this function without
; reading the *initial-event-defmacros* discussion in axioms.lisp.

  (when-logic
   "DEFTHM"
   (pprogn ;patch;
    (f-put-global 'acl2data-entry nil state) ;patch;
    (er-let* (#+acl2-advice ;patch;
              (old-w (value (w state))) ;patch;
              (val ;patch;
               (defthm-fn1 name term state
                 rule-classes
                 instructions
                 hints
                 otf-flg
                 event-form
                 #+:non-standard-analysis std-p)))
;;; Open a new er-let* to support syntactic match with original definition,
;;; which ends above in three right parens.
      (er-let* (#+acl2-advice ;patch;
                (new-w (value (w state))) ;patch;
                (entry (value (f-get-global 'acl2data-entry state))) ;patch;
                #+acl2-advice ;patch;
                (new-hint-setting-alist ;patch;
                 (if entry ;patch;
                     (revert-world-on-error ; may help for hard-error from advice ;patch;
                      (pprogn ;patch;
                       (set-w! old-w state) ;patch;
                       (er-progn ;patch;
                        (if (access acl2data (cdddr entry) :used-induction) ;patch;
                            (value nil) ;patch;

; Since table is just nil in raw Lisp, we use the single-step macroexpansion in
; the logic (i.e., using :trans1) of (table induction-depth-limit-table t 0).

                          (table-fn 'induction-depth-limit-table ;patch;
                                    '(t 0) ;patch;
                                    state ;patch;
                                    '(table induction-depth-limit-table t 0))) ;patch;
                        (advice-recs (cadr entry) ; tterm ;patch;
                                     (access acl2data (cdddr entry) ;patch;
                                             :hint-setting-alist) ;patch;
                                     (caddr entry) ;patch;
                                     state)))) ;patch;
                   (value nil))) ;patch;
                #+acl2-advice ;patch;
                (entry (if entry ; (name tterm . acl2data) ;patch;
                           (pprogn ;patch;
                            (set-w! new-w state) ;patch;
                            (value (cons (car entry) ;patch;
                                         (change acl2data (cdddr entry) ;patch;
                                                 :hint-setting-alist ;patch;
                                                 new-hint-setting-alist)))) ;patch;
                         (value nil)))) ;patch;
        (pprogn (if entry ;patch;
                    (f-put-global 'acl2data-alist ;patch;
                                  (cons entry ;patch;
                                        (f-get-global 'acl2data-alist state)) ;patch;
                                  state) ;patch;
                  state) ;patch;
                (value val))))))) ;patch;
