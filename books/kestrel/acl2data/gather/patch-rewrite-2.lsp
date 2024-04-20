; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file rewrite.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun rewrite-with-lemma (term lemma ; &extra formals
                                rdepth step-limit
                                type-alist obj geneqv pequiv-info wrld state
                                fnstack ancestors
                                backchain-limit
                                simplify-clause-pot-lst rcnst gstack
                                ttree)

; The four values returned by this function are: a new step-limit, t or nil
; indicating whether lemma was used to rewrite term, the rewritten version of
; term, and the final version of ttree.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

  (declare (type (unsigned-byte #.*fixnat-bits*) rdepth)
           (type (signed-byte #.*fixnum-bits*) step-limit))
  (the-mv
   4
   (signed-byte #.*fixnum-bits*)
   (let ((gstack (push-gframe 'rewrite-with-lemma nil term lemma))
         (rdepth (adjust-rdepth rdepth)))
     (declare (type (unsigned-byte #.*fixnat-bits*) rdepth))
     (cond ((zero-depthp rdepth)
; patch file: my-rdepth-error instead of rdepth-error
#|
            (rdepth-error
|#
            (my-rdepth-error ;patch;
             (mv step-limit nil term ttree)))
           ((eq (access rewrite-rule lemma :subclass) 'meta)

; See the Essay on Correctness of Meta Reasoning, above, and :doc meta.

            (cond
             ((geneqv-refinementp (access rewrite-rule lemma :equiv)
                                  geneqv
                                  wrld)

; We assume that the meta function has defun-mode :logic.  How could it
; be :program if we proved it correct?

; Metafunctions come in two flavors.  Vanilla metafunctions take just
; one arg, the term to be rewritten.  Extended metafunctions take
; three args.  We cons up the args here and use this list of args
; twice below, once to eval the metafunction and once to eval the hyp
; fn.  The :rhs of the rewrite-rule is the special flag 'extended
; if we are in the extended case; otherwise, :rhs is nil.  We must
; manufacture a context in the former case.

              (let* ((meta-fn (access rewrite-rule lemma :lhs))
                     (args
                      (cond
                       ((eq (access rewrite-rule lemma :rhs)
                            'extended)
                        (list term
                              (make metafunction-context
                                    :rdepth rdepth
                                    :type-alist type-alist
                                    :obj obj
                                    :geneqv geneqv
                                    :wrld wrld
                                    :fnstack fnstack
                                    :ancestors ancestors
                                    :backchain-limit backchain-limit
                                    :simplify-clause-pot-lst
                                    simplify-clause-pot-lst
                                    :rcnst rcnst
                                    :gstack gstack
                                    :ttree ttree
                                    :unify-subst nil)
                              (coerce-state-to-object state)))
                       (t (list term))))
                     (rune (access rewrite-rule lemma :rune)))
                (with-accumulated-persistence
                 rune
                 ((the (signed-byte #.*fixnum-bits*) step-limit) flg term ttree)
                 flg
                 (mv-let
                  (erp val latches)
                  (pstk
                   (ev-fncall-meta meta-fn args state))
                  (declare (ignore latches))
                  (cond
                   (erp
                    (mv step-limit nil term ttree))
                   ((equal term val)
                    (mv step-limit nil term ttree))
                   (t

; Skip logic-termp checks if either we're told to via skip-meta-termp-checks
; or they are unnecessary because of the meta fn (and its hyp-fn) have
; well-formedness guarantees.  If we skip the checks because of guarantees, we
; must check the arity assumptions.

                    (let* ((user-says-skip-termp-checkp
                            (skip-meta-termp-checks meta-fn wrld))
                           (well-formedness-guarantee
                            (access rewrite-rule lemma :heuristic-info))
                           (not-skipped
                            (and (not user-says-skip-termp-checkp)
                                 (not well-formedness-guarantee)))
                           (bad-arity-info
                            (if (and well-formedness-guarantee
                                     (not user-says-skip-termp-checkp))
                                (collect-bad-fn-arity-info
                                 (cdr well-formedness-guarantee)
                                 wrld nil nil)
                              nil)))
                      (cond
                       (bad-arity-info
                        (let ((name (nth 0 (car well-formedness-guarantee)))
                              (fn (nth 1 (car well-formedness-guarantee)))
                              (thm-name1
                               (nth 2 (car well-formedness-guarantee)))
                              (hyp-fn (nth 3 (car well-formedness-guarantee)))
                              (thm-name2
                               (nth 4 (car well-formedness-guarantee))))
                          (mv step-limit
                              (er hard 'rewrite-with-lemma
                                  "~@0"
                                  (bad-arities-msg name :META fn hyp-fn
                                                   thm-name1 thm-name2
                                                   bad-arity-info))
                              term ttree)))
; Check logic-termp by checking both termp and (not (program-termp)).
                       ((and not-skipped
                             (not (termp val wrld)))
                        (mv step-limit
                            (er hard 'rewrite-with-lemma
                                "The metafunction ~x0 produced the non-termp ~
                                 ~x1 on the input term ~x2. The proof of the ~
                                 correctness of ~x0 establishes that the ~
                                 quotations of these two s-expressions have ~
                                 the same value, but our implementation ~
                                 additionally requires that ~x0 produce a ~
                                 term.  See :DOC termp.  You might consider ~
                                 proving a well-formedness guarantee to avoid ~
                                 this runtime test altogether.  See :DOC ~
                                 well-formedness-guarantee."
                                meta-fn val term)
                            term ttree))
                       ((and not-skipped
                             (not (logic-termp val wrld)))
                        (mv step-limit
                            (er hard 'rewrite-with-lemma
                                "The metafunction ~x0 produced the termp ~x1 ~
                                 on the input term ~x2.  The proof of the ~
                                 correctness of ~x0 establishes that the ~
                                 quotations of these two s-expressions have ~
                                 the same value, but our implementation ~
                                 additionally requires that ~x0 produce a ~
                                 term with no :program mode function symbols. ~
                                 ~ The term produced has :program mode ~
                                 function symbol~#3~[~/s~] ~&3.  You might ~
                                 consider proving a well-formedness guarantee ~
                                 to avoid this runtime test altogether.  See ~
                                 :DOC well-formedness-guarantee."
                                meta-fn val term
                                (collect-programs (all-ffn-symbs val nil)
                                                  wrld))
                            term ttree))
                       ((and not-skipped
                             (forbidden-fns-in-term
                              val
                              (access rewrite-constant rcnst :forbidden-fns)))
                        (mv step-limit
                            (er hard 'rewrite-with-lemma
                                "The metafunction ~x0 produced the termp ~x1 ~
                                 on the input term ~x2.  The proof of the ~
                                 correctness of ~x0 establishes that the ~
                                 quotations of these two s-expressions have ~
                                 the same value, but our implementation ~
                                 additionally requires that certain forbidden ~
                                 function symbols not be called.  However, ~
                                 the forbidden function symbol~#3~[ ~&3 is~/s ~
                                 ~&3 are~] called in the term produced by ~
                                 ~x0.  See :DOC meta and :DOC ~
                                 set-skip-meta-termp-checks and :DOC ~
                                 well-formedness-guarantee."
                                meta-fn val term
                                (forbidden-fns-in-term
                                 val
                                 (access rewrite-constant rcnst :forbidden-fns)))
                            term ttree))
                       (t
                        (mv-let
                         (extra-evaled-hyp val)
                         (cond ((and (ffn-symb-p val 'if)
                                     (equal (fargn val 3) term))
                                (mv (fargn val 1) (fargn val 2)))
                               (t (mv *t* val)))
                         (let ((hyp-fn (access rewrite-rule lemma :hyps)))
                           (mv-let
                            (erp evaled-hyp latches)
                            (if (eq hyp-fn nil)
                                (mv nil *t* nil)
                              (pstk
                               (ev-fncall-meta hyp-fn args state)))
                            (declare (ignore latches))
                            (cond
                             (erp
                              (mv step-limit nil term ttree))
                             (t
                              (let* ((user-says-skip-termp-checkp
                                      (skip-meta-termp-checks hyp-fn wrld))
;                                    (well-formedness-guarantee  ; already bound
;                                     (access rewrite-rule lemma
;                                             :heuristic-info))
                                     (not-skipped
                                      (and (not user-says-skip-termp-checkp)
                                           (not well-formedness-guarantee)))

; It is easy to think that it is unnecessary to do this computation and binding
; because the non-nil result will be exactly the same as it was above
; (depending as it does only on the guarantee and the wrld) and we have already
; (above) checked and caused an error if it is non-nil.  But that reasoning is
; faulty.  Suppose the user told us to skip the termp check on metafn's output
; but to do the check on hyp-fn's output.  Then the earlier binding of
; bad-arity-info is nil but this binding may find something.

                                     (bad-arity-info
                                      (if (and
                                           well-formedness-guarantee
                                           (not user-says-skip-termp-checkp))
                                          (collect-bad-fn-arity-info
                                           (cdr well-formedness-guarantee)
                                           wrld nil nil)
                                        nil)))
                                (cond
                                 (bad-arity-info
                                  (let ((name
                                         (nth 0
                                              (car well-formedness-guarantee)))
                                        (hyp-fn
                                         (nth 3
                                              (car well-formedness-guarantee)))
                                        (thm-name2
                                         (nth 4
                                              (car well-formedness-guarantee))))
                                    (mv step-limit
                                        (er hard 'rewrite-with-lemma
                                            "~@0"
                                            (bad-arities-msg name
                                                             :META
                                                             nil ; fn
                                                             hyp-fn
                                                             thm-name2
                                                             nil
                                                             bad-arity-info))
                                        term ttree)))
                                 ((and not-skipped
                                       (not (termp evaled-hyp wrld)))
                                  (mv step-limit
                                      (er hard 'rewrite-with-lemma
                                          "The hypothesis metafunction ~x0 ~
                                           produced the non-termp ~x1 on the ~
                                           input term ~x2.  Our ~
                                           implementation requires that ~x0 ~
                                           produce a term.  See :DOC termp.  ~
                                           You might consider proving a ~
                                           well-formedness guarantee.  See ~
                                           :DOC well-formedness-guarantee to ~
                                           avoid this runtime check ~
                                           altogether.  See :DOC ~
                                           well-formedness-guarantee."
                                          hyp-fn evaled-hyp term)
                                      term ttree))
                                 ((and not-skipped
                                       (not (logic-termp evaled-hyp wrld)))
                                  (mv step-limit
                                      (er hard 'rewrite-with-lemma
                                          "The hypothesis metafunction ~x0 ~
                                           produced the termp ~x1 on the ~
                                           input term ~x2.  The proof of the ~
                                           correctness of ~x0 establishes ~
                                           that the quotations of these two ~
                                           s-expressions have the same value, ~
                                           but our implementation ~
                                           additionally requires that ~x0 ~
                                           produce a term with no :program ~
                                           mode function symbols.  The term ~
                                           produced has :program mode ~
                                           function symbol~#3~[~/s~] ~&3.  ~
                                           You might consider proving a ~
                                           well-formedness guarantee to avoid ~
                                           this runtime test altogether.  See ~
                                           :DOC well-formedness-guarantee."
                                          hyp-fn evaled-hyp term
                                          (collect-programs
                                           (all-ffn-symbs evaled-hyp nil)
                                           wrld))
                                      term ttree))
                                 ((and not-skipped
                                       (forbidden-fns-in-term
                                        evaled-hyp
                                        (access rewrite-constant rcnst
                                                :forbidden-fns)))
                                  (mv step-limit
                                      (er hard 'rewrite-with-lemma
                                          "The hypothesis metafunction ~x0 ~
                                           produced the termp ~x1 on the ~
                                           input term ~x2.  Our ~
                                           implementation additionally ~
                                           requires that certain forbidden ~
                                           function symbols not be called.  ~
                                           However, the forbidden function ~
                                           symbol~#3~[ ~&3 is~/s ~&3 are~] ~
                                           called in the term produced by ~
                                           ~x0.  See :DOC meta and :DOC ~
                                           set-skip-meta-termp-checks and ~
                                           :DOC well-formedness-guarantee."
                                          hyp-fn evaled-hyp term
                                          (forbidden-fns-in-term
                                           evaled-hyp
                                           (access rewrite-constant rcnst
                                                   :forbidden-fns)))
                                      term ttree))
                                 (t
                                  (let* ((hyps0 (flatten-ands-in-lit

; Note: The quote-normal-form call below normalizes the explicit constant
; constructors, e.g., (cons '1 '2) becomes '(1 . 2).  See the comment in
; extend-unify-subst.

                                                 (quote-normal-form
                                                  evaled-hyp)))
                                         (extra-hyps (flatten-ands-in-lit

; Note: The quote-normal-form call below normalizes the explicit constant
; constructors, e.g., (cons '1 '2) becomes '(1 . 2).  See the comment in
; extend-unify-subst.

                                                 (quote-normal-form
                                                  extra-evaled-hyp)))
                                         (hyps (append? hyps0 extra-hyps))
                                         (vars (and hyps

; We avoid the cost of computing (all-vars term) when there are no hypotheses
; (which is presumably a common case).  We have seen this reduce an event's
; processing time from 67 seconds to 19 seconds.

                                                    (all-vars term)))
                                         (rule-backchain-limit
                                          (access rewrite-rule lemma
                                                  :backchain-limit-lst))
                                         (bad-synp-hyp-msg
                                          (and hyps0

; Vars should be (all-vars term) if we call bad-synp-hyp-msg, but if hyps0 is
; nil then bad-synp-hyp-msg returns nil regardless of vars, so we avoid calling
; it.

                                               (bad-synp-hyp-msg hyps0 vars nil
                                                                 wrld)))
                                         (bad-synp-hyp-msg-extra
                                          (and extra-hyps ; optimize, as above
                                               (bad-synp-hyp-msg extra-hyps
                                                                 vars nil
                                                                 wrld))))
                                    (cond
                                     (bad-synp-hyp-msg
                                      (mv step-limit
                                          (er hard 'rewrite-with-lemma
                                              "The hypothesis metafunction ~
                                               ~x0, when applied to the input ~
                                               term ~x1, produced a term ~
                                               whose use of synp is illegal ~
                                               because ~@2"
                                              hyp-fn term bad-synp-hyp-msg)
                                          term ttree))
                                     (bad-synp-hyp-msg-extra
                                      (mv step-limit
                                          (er hard 'rewrite-with-lemma
                                              "The metafunction ~x0, when ~
                                               applied to the input term ~x1, ~
                                               produced a term with an ~
                                               implicit hypothesis (see :DOC ~
                                               meta-implicit-hypothesis), ~
                                               whose use of synp is illegal ~
                                               because ~@2"
                                              meta-fn term
                                              bad-synp-hyp-msg-extra)
                                          term ttree))
                                     (t
                                      (sl-let
                                       (relieve-hyps-ans failure-reason
                                                         unify-subst
                                                         ttree)
                                       (rewrite-entry
                                        (relieve-hyps

; The next argument of relieve-hyps is a rune on which to "blame" a
; possible force.  We could blame such a force on a lot of things, but
; we'll blame it on the metarule and the term that it's applied to.

                                         rune
                                         term
                                         hyps
                                         (and rule-backchain-limit
                                              (assert$
                                               (natp rule-backchain-limit)
                                               (make-list
                                                (length hyps)
                                                :initial-element
                                                rule-backchain-limit)))

; The meta function has rewritten term to val and has generated a
; hypothesis called evaled-hyp.  Now ignore the metafunction and just
; imagine that we have a rewrite rule (implies evaled-hyp (equiv term
; val)).  The unifying substitution just maps the vars of term to
; themselves.  There may be additional vars in both evaled-hyp and in
; val.  But they are free at the time we do this relieve-hyps.

; If hyps is nil, then relieve-hyps returns immediately with nil as the
; unifying substitution.  That's OK, as explained in a comment below ("At one
; point we ignored the unify-subst....").

                                         (and hyps
                                              (pairlis$ vars vars))
                                         nil ; allp=nil for meta rules
                                         )
                                        :obj nil         ; ignored
                                        :geneqv nil      ; ignored
                                        :pequiv-info nil ; ignored
                                        )

; If relieve hyps succeeds we get back a unifying substitution that extends
; the identity substitution above.  This substitution might bind free vars
; in the evaled-hyp.

; Why are we ignoring failure-reason?  Do we need to be calling one of the
; brkpt functions?  No, because we don't break on meta rules.  But perhaps we
; should consider allowing breaks on meta rules.

                                       (declare (ignore failure-reason))
                                       (cond
                                        (relieve-hyps-ans
                                         (sl-let
                                          (rewritten-rhs ttree)
                                          (with-accumulated-persistence
                                           rune
                                           ((the (signed-byte #.*fixnum-bits*) step-limit)
                                            rewritten-rhs ttree)

; This rewrite of the body is considered a success unless the parent with-acc-p
; fails.

                                           t
                                           (rewrite-entry (rewrite

; Note: The quote-normal-form call below normalizes the explicit constant
; constructors, e.g., (cons '1 '2) becomes '(1 . 2).  See the comment in
; extend-unify-subst.

                                                 (quote-normal-form val)

; At one point we ignored the unify-subst constructed above and used a nil
; here.  That was unsound if val involved free vars bound by the relief of the
; evaled-hyp.  We must rewrite val under the extended substitution.  Often that
; is just the identity substitution.  If there are no hypotheses, however, then
; there are no such free vars, so it is fine to rewrite with nil as the
; unify-subst.

                                                           unify-subst
                                                           'meta))
                                           :conc
                                           hyps)
                                          (mv step-limit t rewritten-rhs

; Should we be pushing executable-counterparts into ttrees when we applying
; metafunctions on behalf of meta rules?  NO:  We should only do that if the
; meta-rule's use is sensitive to whether or not they're enabled, and it's not
; -- all that matters is if the rule itself is enabled.

                                              (push-lemma
                                               (geneqv-refinementp
                                                (access rewrite-rule lemma
                                                        :equiv)
                                                geneqv
                                                wrld)
                                               (push-lemma+ rune ttree rcnst ancestors
                                                            val rewritten-rhs)))))
                                        (t (mv step-limit nil term ttree))))))))))))))))))))))))
             (t (mv step-limit nil term ttree))))
           ((not (geneqv-refinementp (access rewrite-rule lemma :equiv)
                                     geneqv
                                     wrld))
            (mv step-limit nil term ttree))
           ((eq (access rewrite-rule lemma :subclass) 'definition)
            (sl-let (rewritten-term ttree)
                    (rewrite-entry (rewrite-fncall lemma term))
                    (mv step-limit
                        (not (equal term rewritten-term))
                        rewritten-term
                        ttree)))
           ((and (or (null (access rewrite-rule lemma :hyps))
                     (not (eq obj t))
                     (not (equal (access rewrite-rule lemma :rhs) *nil*)))
                 (or (flambdap (ffn-symb term)) ; hence not on fnstack
                     (not (being-openedp (ffn-symb term)
                                         fnstack
                                         (recursivep (ffn-symb term) t wrld)
                                         (eq (access rewrite-constant rcnst
                                                     :rewriter-state)
                                             'settled-down)))
                     (not (ffnnamep (ffn-symb term)
                                    (access rewrite-rule lemma :rhs)))))
            (let ((lhs (access rewrite-rule lemma :lhs))
                  (rune (access rewrite-rule lemma :rune)))
              (mv-let (unify-ans unify-subst)
                      (one-way-unify-restrictions
                       lhs
                       term
                       (cdr (assoc-equal
                             rune
                             (access rewrite-constant rcnst
                                     :restrictions-alist))))
                      (cond
                       ((and unify-ans
                             (null (brkpt1 lemma term unify-subst
                                           type-alist ancestors
                                           ttree
                                           gstack rcnst simplify-clause-pot-lst
                                           state)))
                        (cond
                         ((null (loop-stopperp
                                 (access rewrite-rule lemma :heuristic-info)
                                 unify-subst
                                 wrld))
                          (prog2$
                           (brkpt2 nil 'loop-stopper
                                   unify-subst gstack nil nil
                                   rcnst ancestors state)
                           (mv step-limit nil term ttree)))
                         (t
                          (with-accumulated-persistence
                           rune
                           ((the (signed-byte #.*fixnum-bits*) step-limit) flg term ttree)
                           flg
                           (sl-let
                            (relieve-hyps-ans failure-reason unify-subst ttree)
                            (rewrite-entry
                             (relieve-hyps
                              rune
                              term
                              (access rewrite-rule lemma :hyps)
                              (access rewrite-rule lemma
                                      :backchain-limit-lst)
                              unify-subst
                              (not (oncep (access rewrite-constant
                                                  rcnst
                                                  :oncep-override)
                                          (access rewrite-rule
                                                  lemma
                                                  :match-free)
                                          rune
                                          (access rewrite-rule
                                                  lemma
                                                  :nume))))
                             :obj nil         ; ignored
                             :geneqv nil      ; ignored
                             :pequiv-info nil ; ignored
                             )
                            (cond
                             (relieve-hyps-ans
                              (sl-let
                               (rewritten-rhs ttree)
                               (with-accumulated-persistence
                                rune
                                ((the (signed-byte #.*fixnum-bits*) step-limit)
                                 rewritten-rhs ttree)

; This rewrite of the body is considered a success unless the parent with-acc-p
; fails.

                                t
                                (rewrite-entry
                                 (rewrite
                                  (access rewrite-rule lemma :rhs)
                                  unify-subst
                                  'rhs))
                                :conc
                                (access rewrite-rule lemma :hyps))
                               (prog2$
                                (brkpt2 t nil unify-subst gstack rewritten-rhs
                                        ttree rcnst ancestors state)
                                (mv step-limit t rewritten-rhs
                                    (push-lemma
                                     (geneqv-refinementp
                                      (access rewrite-rule lemma
                                              :equiv)
                                      geneqv
                                      wrld)
                                     (push-lemma+ rune ttree rcnst ancestors
                                                  (access rewrite-rule lemma
                                                          :rhs)
                                                  rewritten-rhs))))))
                             (t (prog2$
                                 (brkpt2 nil failure-reason
                                         unify-subst gstack nil nil
                                         rcnst ancestors state)
                                 (mv step-limit nil term ttree)))))))))
                       (t (progn$
                           (near-miss-brkpt1 lemma term type-alist
                                             ancestors ttree
                                             gstack rcnst
                                             simplify-clause-pot-lst
                                             state)
                           (brkpt2 nil 'near-miss
                                   unify-subst gstack nil nil
                                   rcnst ancestors state)
                           (mv step-limit nil term ttree)))))))
           (t (mv step-limit nil term ttree))))))

(defun rewrite-quoted-constant-with-lemma
  (term lemma ; &extra formals
        rdepth step-limit
        type-alist obj geneqv pequiv-info wrld state
        fnstack ancestors
        backchain-limit
        simplify-clause-pot-lst rcnst gstack
        ttree)

; The structure of this function and its immediate,
; rewrite-quoted-constant-with-lemmas, is based on rewrite-with-lemma and
; rewrite-with-lemmas.  Term is a quoted evg, i.e., 'evg, and lemma is an
; enabled :rewrite-quoted-constant rule whose :heuristic-info field contains (n
; . loop-stopper), where n is the form number as per the Essay on Rewriting
; Quoted Constants:

; [1] (IMPLIES hyps (equiv 'lhs-evg 'rhs-evg))
; [2] (IMPLIES hyps (equiv (fn x) x)), where x is a variable.
; [3] (IMPLIES hyps (equiv lhs-term rhs-term))

; In all cases below, we check that equiv is a refinement of geneqv.  Roughly
; speaking, if n is 1 and evg is lhs-evg, we backchain to establish the hyps
; and if successful replace term by 'rhs-evg.  If n is 2 and backchaining
; succeeds and (fn 'evg) returns a non-erroneous result, we replace term with
; the quoted result.  If n is 3, we unify lhs-term with 'evg and if successful
; backchain and rewrite as with an ordinary rewrite rule.

; The four values returned by this function are: a new step-limit, t or nil
; indicating whether lemma was used to rewrite term, the rewritten version of
; term, and the final version of ttree.

; This function is a No-Change Loser modulo rw-cache: only the values of
; 'rw-cache-any-tag and 'rw-cache-nil-tag may differ between the input and
; output ttrees.

  (declare (type (unsigned-byte #.*fixnat-bits*) rdepth)
           (type (signed-byte #.*fixnum-bits*) step-limit))
  (the-mv
   4
   (signed-byte #.*fixnum-bits*)
   (let* ((gstack (push-gframe 'rewrite-quoted-constant-with-lemma nil term lemma))
          (rdepth (adjust-rdepth rdepth))
          (temp (access rewrite-rule lemma :heuristic-info))
          (n (car temp))
          (loop-stopper (cdr temp)))
     (declare (type (unsigned-byte #.*fixnat-bits*) rdepth)
              (type integer n))
     (cond ((zero-depthp rdepth)
; patch file: my-rdepth-error instead of rdepth-error
#|
            (rdepth-error
|#
            (my-rdepth-error ;patch;
             (mv step-limit nil term ttree)))
           ((not (geneqv-refinementp (access rewrite-rule lemma :equiv)
                                     geneqv
                                     wrld))
            (mv step-limit nil term ttree))
           (t
; Note below we swap the lhs and rhs of form [2] rules!  The rule is written
; and stored as (equiv (fn var) var), but actually used as though it were
; (equiv var (fn var)), so in this code we actually let lhs be the var and rhs
; be the normalizer expression.

            (let ((lhs (if (eql n 2)
                           (access rewrite-rule lemma :rhs)
                           (access rewrite-rule lemma :lhs)))
                  (rhs (if (eql n 2)
                           (access rewrite-rule lemma :lhs)
                           (access rewrite-rule lemma :rhs)))
                  (rune (access rewrite-rule lemma :rune)))
              (mv-let (unify-ans unify-subst)
                (cond
                 ((eql n 1)
                  (mv (equal term lhs) nil))
                 ((eql n 2)
                  (mv t (list (cons lhs term))))
                 ((eql n 3)
                  (one-way-unify-restrictions
                   lhs
                   term
                   (cdr (assoc-equal
                         rune
                         (access rewrite-constant rcnst
                                 :restrictions-alist)))))
                 (t (mv nil
                        (er hard 'rewrite-quoted-constant-with-lemma
                            "We've encountered a :rewrite-quoted-constant ~
                             rule, namely ~x0, with an unrecognized form ~
                             number, ~x1."
                            rune
                            n))))
                (cond
                 ((and unify-ans
                       (null (brkpt1 lemma term unify-subst
                                     type-alist ancestors
                                     ttree
                                     gstack rcnst simplify-clause-pot-lst
                                     state)))
                  (cond
                   ((null (loop-stopperp loop-stopper unify-subst wrld))
                    (prog2$
                     (brkpt2 nil 'loop-stopper
                             unify-subst gstack nil nil
                             rcnst ancestors state)
                     (mv step-limit nil term ttree)))
                   (t
                    (with-accumulated-persistence
                     rune
                     ((the (signed-byte #.*fixnum-bits*) step-limit) flg term ttree)
                     flg
                     (sl-let
                      (relieve-hyps-ans failure-reason unify-subst ttree)
                      (rewrite-entry
                       (relieve-hyps
                        rune
                        term
                        (access rewrite-rule lemma :hyps)
                        (access rewrite-rule lemma
                                :backchain-limit-lst)
                        unify-subst
                        (not (oncep (access rewrite-constant
                                            rcnst
                                            :oncep-override)
                                    (access rewrite-rule
                                            lemma
                                            :match-free)
                                    rune
                                    (access rewrite-rule
                                            lemma
                                            :nume))))
                       :obj nil         ; ignored
                       :geneqv nil      ; ignored
                       :pequiv-info nil ; ignored
                       )
                      (cond
                       (relieve-hyps-ans
                        (sl-let
                         (rewritten-rhs ttree)
                         (with-accumulated-persistence
                          rune
                          ((the (signed-byte #.*fixnum-bits*) step-limit)
                           rewritten-rhs ttree)

; This rewrite of the body is considered a success unless the parent with-acc-p
; fails.

                          t
                          (rewrite-entry
                           (rewrite
                            rhs
                            unify-subst
                            'rhs))
                          :conc
                          (access rewrite-rule lemma :hyps))
                         (cond
                          ((or (eql n 1)
                               (and (eql n 2)
                                    (quotep rewritten-rhs)
                                    (not (equal term rewritten-rhs)))
                               (eql n 3))
                           (prog2$
                            (brkpt2 t nil unify-subst gstack rewritten-rhs
                                    ttree rcnst ancestors state)
                            (mv step-limit
                                t
                                rewritten-rhs
                                (push-lemma
                                 (geneqv-refinementp
                                  (access rewrite-rule lemma
                                          :equiv)
                                  geneqv
                                  wrld)
                                 (push-lemma+ rune ttree rcnst ancestors
                                              rhs
                                              rewritten-rhs)))))
                          (t (prog2$
; We can only get here if n is 2 but either rewritten-rhs is not a quote or
; it is equal to term.
                              (brkpt2 nil
                                      (list
                                       (if (quotep rewritten-rhs)
                                           'normalizer-returned-same-constant
                                           'normalizer-failed-to-evaluate)
                                       (sublis-var unify-subst rhs)
                                       rewritten-rhs)
                                      unify-subst gstack nil nil
                                      rcnst ancestors state)
                              (mv step-limit nil term ttree))))))
                       (t (prog2$
                           (brkpt2 nil failure-reason
                                   unify-subst gstack nil nil
                                   rcnst ancestors state)
                           (mv step-limit nil term ttree)))))))))
                 (t (mv step-limit nil term ttree))))))))))
