; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides a flexible and convenient interface to the ACL2 rewriter,
; which can be called programmatically.  See :DOC rewrite$.  It is based on
; community book misc/expander.lisp, originally written by Matt Kaufmann but
; with contributions from Pete Manolios and Daron Vroon.

;;; Possible future work to consider if there is a need:

; - Consider adding a version that simplifies hypotheses first, perhaps by
;   first writing a tool that simplifies a list of terms.  (This could replace
;   the call of sd-simplify-hyps in
;   books/kestrel/apt/simplify-defun-impl.lisp.)

; - Think more about output.  In particular, appearance of "Goal'" (for
;   example) when proving forced-assumptions is probably distracting.

; - Maybe control whether override hints are used.

; - Consider having rewrite$ return a ctx-msg pair and not take state.  At the
;   least, hint translation would have to be changed to avoid state (which is
;   already the case for ACL2(p)).

; - Avoid hard error in step-limit.  This will probably involve major changes
;   to the handling of step-limit in the ACL2 sources.

; - Consider returning something other than what is returned by
;   rewrite$-return.  In particular, the "pairs" isn't easy to use without some
;   documentation.

; - Try replacing uses of expander with rewrite$.  (But leave
;   misc/expander.lisp for historical reasons.)

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)

(program)
(set-state-ok t)

(defxdoc rewrite$
  :parents (proof-automation)
  :short "Rewrite a term"
  :long "<p>@('Rewrite$') is a macro that provides a convenient and flexible
 interface to the ACL2 @(see rewrite)r, which can be called programmatically.
 The following example shows a call of @('rewrite$').  The keyword option
 @(':translate t') is used because the first argument is not a translated @(see
 term), due to the call of the macro, @(tsee append).  We see that the call of
 @('rewrite$') produces a 2-element list consisting of the result, @('X'), of
 rewriting the input term, together with a list of @(see rune)s justifying that
 rewrite.</p>

 @({
 ACL2 !>(rewrite$ '(car (append (cons x y) z)) :translate t)
  (X ((:DEFINITION BINARY-APPEND)
      (:REWRITE CDR-CONS)
      (:REWRITE CAR-CONS)
      (:FAKE-RUNE-FOR-TYPE-SET NIL)))
 ACL2 !>
 })

 <p>Other simple examples may be found in community book
 @('books/tools/rewrite-dollar-tests.lisp').</p>

 <h3>Return values</h3>

 <p>A call @('(rewrite$ term ...)') returns an @(see error-triple), @('(mv erp
 val state)').  @('Erp') is non-@('nil') when an error has occurred.  Otherwise
 @('val') is of the form @('(rewritten-term runes . pairs)') where @('pairs')
 is typically @('nil') (as discussed further below) and:</p>

 <ul>

 <li>@('rewritten-term') is the result of rewriting @('term') as directed by
 the other inputs; and</li>

 <li>@('runes') is a list containing the @(see rune)s that participated in the
 rewriting of @('term') to @('rewritten-term').</li>

 </ul>

 <p>Because of forcing (see @(see force)), rewriting of the input term may
 generate goals to be proved later, based on the forced hypotheses encountered
 during rewriting that were not relieved at that time.  We call these ``forced
 assumptions''.  If there are forced assumptions, then they are conjoined into
 a single goal, which by default is the target of a separate call to the
 prover, much like a call of @(tsee thm).  The return value @('pairs'),
 mentioned above, is @('nil') exactly when there are no forced assumptions.  We
 say no more here about @('pairs'), as it will suffice for most users to view
 them solely as an indicator of forced assumptions.  (Technical note for
 advanced users: these are the pairs returned by ACL2 source function
 @('extract-and-clausify-assumptions').)</p>

 <p>There are many keyword arguments that control the rewriting process.  One
 of particular importance semantically is @(':alist').  When this argument is
 @('nil') then the resulting rewritten term is provably equivalent (with
 respect to the current ACL2 @(see world)) to the input term.  Otherwise the
 rewritten term is provably equivalent to the result of substituting the
 specified alist into the input term.</p>

 <h3>General Form</h3>

 <p>All arguments of @('rewrite$') except the first are keyword arguments,
 hence are optional, with appropriate defaults.</p>

 @({
 (rewrite$ term

; Basic options (in alphabetical order):

           :alist                    ; default nil
           :ctx                      ; default 'rewrite$
           :default-hints-p          ; default t
           :equiv                    ; default nil
           :geneqv                   ; default nil
           :hyps                     ; default nil
           :must-rewrite             ; default nil
           :prove-forced-assumptions ; default t
           :repeat                   ; default 1
           :step-limit               ; default *default-step-limit*
           :translate                ; default nil
           :untranslate              ; default nil

; Hint options (in alphabetical order), each with default nil:

           :backchain-limit-rw :expand :hands-off :in-theory
           :no-thanks :nonlinearp :restrict :rw-cache-state

; Advanced options (in alphabetical order):

           :obj        ; default '?
           :rcnst      ; default nil
           :saved-pspv ; default nil
           :wrld       ; default (w state)
           )
 })

 <p>@('Term') should evaluate to a translated or untranslated term (see @(see
 term)) according to whether the value of @(':translate') is @('nil') or
 non-@('nil'), respectively.  If @(':translate') is @('nil') (the default),
 @('term') should already be in translated form; otherwise @('term') will be
 translated.</p>

 <p>IMPORTANT: The keyword options, discussed below according to the groups
 above, are all evaluated.  So for example:</p>

 @({
 ; Correct
 (rewrite$ '(cons a (cdr x)) :alist '((a . (car x))) :hyps '((consp x)))

 ; WRONG!
 (rewrite$ '(cons a (cdr x)) :alist ((a . (car x))) :hyps ((consp x)))
 })

 <h3>Basic options</h3>

 <ul>

 <li>@(':alist') (default @('nil'))<br/>
 is an association list mapping variables to terms, where each term is already
 translated or else is untranslated according to whether the value of
 @(':translate') is @('nil') or non-@('nil'), respectively.</li>

 <li>@(':ctx') (default @(''rewrite$'))<br/>
 is a ``context'', such as the @('ctx') argument of @(tsee er).</li>

 <li>@(':default-hints-p') (default @('t'))<br/> is non-@('nil') when the
 construction of hints for the rewriter call is to take into account the @(see
 default-hints) in the current @(see world).</li>

 <li>@(':equiv') and @(':geneqv') (both with default @('nil'))<br/>
 specify the equivalence relation(s) to be preserved by (@(see
 congruence)-based) rewriting.  It is illegal to specify a non-@('nil') value
 for more than one of these.  Most users will prefer to use @(':equiv'), which
 should be a function symbol that is a known (to ACL2) equivalence relation.
 The keyword option @(':geneqv') is really only for those who know how
 generated equivalence relations are represented in the ACL2 system.</li>

 <li>@(':hyps') (default @('nil'))<br/>
 is a non-empty list of hypotheses under which rewriting takes place.  Each
 hypothesis is already translated or is untranslated according to whether the
 value of @(':translate') is @('nil') or non-@('nil'), respectively.</li>

 <li>@(':must-rewrite') (default @('nil'))<br/> indicates, when non-@('nil'),
 that the rewritten term must not be equal to the input term.  It is illegal to
 supply non-@('nil') values for both @(':alist') and @(':must-rewrite').</li>

 <li>@(':prove-forced-assumptions') (default @('t'))<br/> affects the proof of
 the forced assumptions.  It has the following legal values.

 <ul>

 <li>@('t'): prove the forced assumptions as mentioned above: a single prover
 call to prove their conjunction.</li>

 <li>@(':same-hints'): same as @('t'), except generate the same @(':hints') for
 the prover call as are generated for the rewriting (from the eight hint
 options discussed below).</li>

 <li>@('nil'): do not attempt a proof of the forced assumptions, instead
 returning a non-@('nil') `@('pairs')' value as discussed above.</li>

 <li>@(':none-forced'): cause an error if there are any forced
 assumptions.</li>

 <li>Otherwise, the value of @(':prove-forced-assumptions') should be of the
 form expected for the value of @(':hints') supplied to @(tsee defthm).  For
 example, the following might follow @(':prove-forced-assumptions') in a call
 of @('rewrite$'): @(''((\"Goal\" :in-theory (enable reverse)))').</li>

 </ul></li>

 <li>@(':repeat') (default @('1'))<br/>
 indicates how many times to call the rewriter.  The value should be a positive
 integer.  If the value of @(':repeat') is greater than 1, then the term
 resulting from the first call is the input term for the second call, whose
 result (if the value of @(':repeat') is greater than 2) is the input term for
 the third call, and so on.  Note that the value of @(':alist') is @('nil') for
 all calls after the first.</li>

 <li>@(':step-limit') (default @('*default-step-limit*'))<br/> is the number of
 prover steps allowed for the entire call of @('rewrite$'), including the
 proof (if any) of the forced assumptions.  See @(see
 with-prover-step-limit).</li>

 <li>@(':translate') (default @('nil'))<br/>
 indicates whether or not terms in the input are to be translated or not (see
 @(see term) for a discussed of ``translate'').  If the value is @('nil') then
 translation will not take place, so the given terms &mdash; not only the input
 term, but also terms in the @('cdr') positions of the @(':alist') and terms in
 the @(':hyps') &mdash; should already be in translated form.  But if the value
 is not @('nil'), then all of these will be translated.</li>

 <li>@(':untranslate') (default @('nil'))<br/>
 indicates whether the rewritten term will be given in translated or
 untranslated form.  It also specifies, when not @('nil'), that certain error
 messages display terms in untranslated form.</li>

 </ul>

 <h3>Hint options, each with default @('nil')</h3>

 <p>The eight hint options displayed above are the same as discussed in the
 documentation topic, @(see hints).  These are the only legal hint keywords for
 @('rewrite$').</p>

 <h3>Advanced options</h3>

 <p>The ``advanced options'' @(':obj'), @(':wrld'), @(':rcnst'), and
 @(':saved-pspv') can generally be ignored, so we say little about them here.
 @(':Obj') is the ``obj'' argument of the rewriter, typically the symbol
 `@('?')' but @('t') when backchaining.  See community book
 @('books/kestrel/apt/simplify-defun-impl.lisp') for how @(':rcnst') can avoid
 translating @(see hints) repeatedly and for how @(':saved-pspv') can avoid
 repeatedly consing up the same structure.  @(':Wrld') should probably be left
 as its default, which is the current ACL2 logical @(see world).</p>

 <h3>Related tools</h3>

 <p>For related tools see @(see expander) and @(see easy-simplify-term).  In
 particular, code from the expander function @('tool2-fn') served as a guide to
 the coding of @('rewrite$'); see @(see community-book)
 @('books/misc/expander.lisp').</p>")

(defun rewrite$* (term alist
                       repeat-limit completed-iters
                       type-alist geneqv obj step-limit
                       simplify-clause-pot-lst
                       rcnst gstack ttree
                       must-rewrite wrld state)

; Rewrite term repeatedly, (- repeat-limit completed-iters) times or until the
; term doesn't change, whichever comes first.

; Note that alist is nil after the first iteration.

; This function is adapted from rewrite* in books/misc/expander.lisp.

; This returns (mv step-limit term ttree state) except when must-rewrite causes
; a failure, in which case the return value is (mv :no-change nil nil state).
; (This happens only when there is no change and we have completed only a
; single iteration, starting with a null alist.  The function rewrite$-main
; checks equality when starting with a null alist in the case of more than one
; iteration; doing the single-iteration check here is just a very minor
; optimization to avoid repeating the equality check.)

  (sl-let (val new-ttree)
          (rewrite-entry (rewrite term alist 'rewrite$)
                         :rdepth (rewrite-stack-limit wrld)
                         :step-limit step-limit ; explicit to avoid decrement
                         :pequiv-info nil
                         :fnstack nil
                         :ancestors nil
                         :backchain-limit 500)
          (let ((completed-iters (1+ completed-iters)))
            (cond
             ((equal val term)
              (cond
               ((and must-rewrite
                     (int= completed-iters 1))
                (mv :no-change nil nil state))
               (t (mv step-limit term ttree state))))
             ((int= repeat-limit completed-iters)
              (mv step-limit val new-ttree state))
             (t (pprogn (if (int= completed-iters 0)
                            state
                          (io? prove nil state
                               (completed-iters)
                               (fms "NOTE:  Starting ~n0 call of the rewriter.~%"
                                    (list (cons #\0
                                                (list (1+ completed-iters))))
                                    (proofs-co state) state nil)))
                        (rewrite$* val nil
                                   repeat-limit
                                   completed-iters
                                   type-alist geneqv obj step-limit
                                   simplify-clause-pot-lst
                                   rcnst gstack new-ttree
                                   must-rewrite wrld state)))))))

(defun rewrite$-return (rewritten-term ttree pairs untranslate step-limit
                                       wrld state)

; Pairs is nil unless rewrite$ argument :prove-forced-assumptions has value
; nil, in which case it is a "pairs" value as returned by
; extract-and-clausify-assumptions.  The important thing about pairs is that if
; it is non-nil, then its clauses (cdrs) must be proved in order to justify the
; rewriting of the input term (implicit here) to rewritten-term.

  (b* ((new-term (if untranslate
                     (untranslate rewritten-term nil wrld)
                   rewritten-term))
       ((er ?)
        (accumulate-ttree-and-step-limit-into-state ttree step-limit state)))
    (value (list* new-term
                  (all-runes-in-ttree ttree nil)
                  pairs))))

(defun rewrite$-process-assumptions-msg (n0 pairs untranslate clause-set
                                            forced-goal wrld state)

; This variant of ACL2 source function process-assumptions-msg is crafted to
; print something appropriate for rewrite$.

  (let ((to-print (if untranslate
                      (prettyify-clause-set clause-set
                                            (let*-abstractionp state)
                                            wrld)
                    forced-goal)))
    (io? prove nil state
         (n0 to-print pairs)
         (fms "Rewriting is complete for the input term, but it remains to ~
               prove the goal generated by cleaning up ~n1 forced ~
               ~#0~[hypothesis~/hypotheses (and conjoining into a single ~
               term)~], as follows:~|~%~x2~|~%"
              (list (cons #\0 (if (cdr pairs) 1 0))
                    (cons #\1 n0)
                    (cons #\2 to-print))
              (proofs-co state)
              state
              nil))))

(defstub rewrite$-last-literal-fn () t)

(defconst *rewrite$-last-literal*
  (fcons-term* 'rewrite$-last-literal-fn))

(defconst *rewrite$-hint-keywords*

; Warning: Keep this in sync with the "hints" keywords of rewrite$ and where
; hint keywords are used in rewrite$-fn.

  '(:backchain-limit-rw :expand :hands-off :in-theory
                        :no-thanks :nonlinearp :restrict :rw-cache-state))

(defun rewrite$-rcnst (hyps-clause saved-pspv hints ctx wrld state)

; Much of the code below is adapted from tool2-fn1 in books/misc/expander.lisp.

  (b* (((er pair) ; from waterfall1
        (find-applicable-hint-settings
         *initial-clause-id*
         (add-literal *rewrite$-last-literal* hyps-clause t)
         nil saved-pspv ctx
         hints wrld nil state))
       (hint-settings (car pair))
       (bad-keywords (set-difference-eq (strip-cars hint-settings)
                                        *rewrite$-hint-keywords*))
       ((when bad-keywords) ; probably impossible
        (er soft ctx
            "The hints keyword~#0~[ ~&0 is~/s ~&0 are~] illegal for rewrite$."
            bad-keywords))
       ((mv hint-settings state)
        (cond ((null hint-settings)
               (mv nil state))
              (t (thanks-for-the-hint nil hint-settings nil state))))
       ((er rcnst)
        (load-hint-settings-into-rcnst ; including theory
         hint-settings
         (access prove-spec-var saved-pspv :rewrite-constant)
         *initial-clause-id* wrld ctx state)))
    (value (change rewrite-constant rcnst

; As in books/misc/expander.lisp, we set :current-clause because of its use by
; mfc-clause, and it (heuristically) doesn't include the literal for the given
; term, so as to prevent hypotheses from expanding excessively.  (And there is
; no need to include *rewrite$-last-literal* either.)

                   :current-clause hyps-clause

; It is bold to set :force-info to t here, since simplify-clause is more
; restrictive.  However, we already have hypotheses separated out, and we don't
; want to miss out on forcing, so we take a chance here.  An alternative would
; be to do this in rewrite$*, where perhaps :force-info would be t in
; iterations only after the first, when (ffnnamep 'if term) is true.  But
; perhaps only a few users will do more than one iteration.

                   :force-info t))))

(defun rewrite$-main (term alist hyps geneqv obj
                           hints step-limit
                           prove-forced-assumptions forced-assumptions-hints
                           untranslate
                           must-rewrite repeat
                           saved-pspv ctx wrld
                           rcnst ; either nil or a weak-rewrite-constant-p
                           state)

; Term, alist, hyps, and hints are already translated.

; Much of the code below is adapted from tool2-fn1 in books/misc/expander.lisp.

  (b* ((step-limit-saved step-limit)
       (pts nil)
       (hyps-clause (dumb-negate-lit-lst hyps))
       ((er rcnst)
        (cond
         (rcnst (value rcnst))
         (t (rewrite$-rcnst hyps-clause saved-pspv hints ctx wrld state))))
       ((mv contradictionp type-alist fc-pair-lst) ; from simplify-clause1
        (forward-chain-top 'rewrite$
                           hyps-clause
                           pts
                           (access rewrite-constant rcnst :force-info)
                           nil ; do-not-reconsiderp
                           wrld
                           (access rewrite-constant rcnst
                                   :current-enabled-structure)
                           (access rewrite-constant rcnst
                                   :oncep-override)
                           state))
       ((when contradictionp)
        (er soft ctx
            "An attempt has been made to simplify the following ~
             hypotheses:~|~%~x0~|~%However, that list is contradictory!  ~
             (Technical note: the contradiction was found using type-set ~
             reasoning.)"
            hyps))
       ((mv step-limit
            contradictionp
            simplify-clause-pot-lst) ; from simplify-clause1
        (setup-simplify-clause-pot-lst hyps-clause
                                       (pts-to-ttree-lst pts)
                                       fc-pair-lst type-alist rcnst wrld state
                                       step-limit))
       ((when contradictionp)
        (er soft ctx
            "An attempt has been made to simplify the following ~
             hypotheses:~|~%~x0~|~%However, that list is contradictory!  ~
             (Technical note: the contradiction was found using linear ~
             arithmetic reasoning.)"
            hyps))

; We skip the calls of process-equational-polys and remove-trivial-equivalence
; in simplify-clause1.  Those cause simplify-clause1 to return with the
; resulting clause, without any rewriting.  We might consider including those
; on at least the first iteration, at least if repeat > 1.

       (local-rcnst
        (change rewrite-constant rcnst
                :current-literal
                (make current-literal
                      :not-flg nil
                      :atm *rewrite$-last-literal*)))
       (bkptr nil)
       (gstack nil)
       (gstack (push-gframe 'rewrite bkptr term alist obj))
       ((mv step-limit rewritten-term ttree state)
        (rewrite$* term alist
                   repeat
                   0
                   type-alist geneqv obj step-limit
                   simplify-clause-pot-lst
                   rcnst gstack nil
                   must-rewrite wrld state))
       ((when (or (eq step-limit :no-change)
                  (and must-rewrite
                       (< 1 repeat)
                       (equal term rewritten-term))))
        (er soft ctx
            "The term~|  ~x0~|failed to rewrite to a new term under ~
             hypotheses~|  ~x1."
            (if untranslate
                (untranslate term nil wrld)
              term)
            (if untranslate
                (untranslate-lst hyps t wrld)
              hyps)))
       ((mv step-limit bad-ass ttree)
        (resume-suspended-assumption-rewriting
         ttree nil gstack simplify-clause-pot-lst
         local-rcnst wrld state step-limit))
       ((when bad-ass)
        (er soft ctx
            "Generated false assumption, ~x0! ~ So, rewriting is aborted, ~
             just as it would be in the course of a regular ACL2 proof."
            bad-ass))

; We deal now with the forced-assumptions, much as process-assumptions does in
; prove-loop2.  Unlike process-assumptions, we don't have the post-rewrite pspv
; available.  So below we call extract-and-clausify-assumptions, which is the
; workhorse in process-assumptions.

       (ttree

; We need to call set-cl-ids-of-assumptions to avoid a hard Lisp error in
; rewrite$-process-assumptions-msg below.

        (set-cl-ids-of-assumptions ttree *initial-clause-id*))
       ((mv n0 assns pairs ttree)
        (extract-and-clausify-assumptions
         nil ;;; irrelevant with only-immediatep = nil
         ttree
         nil ;;; all forced assumptions, not only-immediatep
         (access rewrite-constant rcnst :current-enabled-structure)
         wrld
         (splitter-output)))

; The ttree produced by extract-and-clausify-assumptions (above) records not
; only the rewriting of the original term but also the runes used in building
; clauses from the (forced-)assumptions produced by that rewriting, from the
; type-alists stored in the assumption records.  That ttree is also
; assumption-free.

       ((when (or (null pairs)
                  (not prove-forced-assumptions)))
        (rewrite$-return rewritten-term ttree pairs untranslate
                         step-limit wrld state))
       (clause-set (strip-cdrs pairs))
       (forced-goal (termify-clause-set clause-set))
       (state (rewrite$-process-assumptions-msg n0 pairs
                                                untranslate
                                                clause-set forced-goal
                                                wrld state))
       ((when (eq prove-forced-assumptions :none-forced))
        (er soft ctx
            "The call of rewrite$ has failed because there were forced ~
             assumptions and keyword option :PROVE-FORCED-ASSUMPTIONS ~
             :NONE-FORCED was supplied."))
       ((mv erp val state)
        (with-prover-step-limit! step-limit-saved
                                 (prove forced-goal
                                        saved-pspv forced-assumptions-hints
                                        (ens state) wrld ctx state)))
       ((when erp)
        (er soft ctx
            "The call of rewrite$ has failed because of failure to prove all ~
             of the forced assumptions.  Either disable forcing (see :DOC ~
             disable-forcing) or, if you are willing to ignore the forced ~
             assumptions, specify option :PROVE-FORCED-ASSUMPTIONS NIL for ~
             rewrite$."))
       (ttree

; Extract-and-clausify-assumptions returns a ttree that includes runes to
; justify building the clause from the type-alist in the assumption record.
; But we have not yet collected the runes that justify those type-alists.  That
; is done in process-assumptions by calling process-assumptions-ttree, but we
; bypassed process-assumptions by calling extract-and-clausify-assumptions
; directly, so we make that call here.

        (process-assumptions-ttree assns ttree)))
    (rewrite$-return rewritten-term
                     (cons-tag-trees val ttree)
                     nil untranslate step-limit wrld state)))

(defun collect-non-termp-cdrs (alist wrld)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) nil)
        ((termp (cdar alist) wrld)
         (collect-non-termp-cdrs (cdr alist) wrld))
        (t (cons (cdar alist)
                 (collect-non-termp-cdrs (cdr alist) wrld)))))

(defun rewrite$-pspv (thints wrld state)
  (make-pspv (ens state) wrld state

; It is tempting to add a :displayed-goal field of term.  But term is not a
; goal.  Fortunately, :displayed-goal is not used in the ACL2 sources, so we
; can get away with omitting this field rather than putting something
; unsuitable into it.

             :user-supplied-term ; from e.g. prove
             *rewrite$-last-literal*
             :orig-hints thints))

(defun rewrite$-check-args (alist must-rewrite
                                  backchain-limit-rw expand hands-off in-theory
                                  no-thanks nonlinearp restrict rw-cache-state
                                  step-limit rcnst
                                  ctx state)

; We check arguments not directly checked in rewrite$-fn.

  (er-progn
   (cond ((and must-rewrite alist)
          (er soft ctx
                "It is illegal for rewrite$ to specify non-nil values for ~
                 both :ALIST and :MUST-REWRITE."))
         (t (value nil)))
   (cond ((or (eq step-limit nil)
              (and (natp step-limit)
                   (<= step-limit *default-step-limit*)))
          (value nil))
         (t (er soft ctx
                "The :step-limit argument that was supplied rewrite$, ~x0, is ~
                 illegal.  It must be a natural number not exceeding ~
                 *default-step-limit* (~x1)."
                step-limit *default-step-limit*)))
   (cond ((null rcnst)
          (value nil))
         ((and rcnst
               (or backchain-limit-rw expand hands-off in-theory
                   no-thanks nonlinearp restrict rw-cache-state))
          (er soft ctx
              "It is illegal for a call of rewrite$ to supply values both to ~
               :RCNST and to any of ~v0."
              *rewrite$-hint-keywords*))
         ((and rcnst
               (not (weak-rewrite-constant-p rcnst)))
          (er soft ctx
              "The value of :RCONST in a call of rewrite$ must have the shape ~
               of a rewrite-constant record, but that value has been supplied ~
               as ~x0, which fails to satisfy the predicate ~x1."
              rcnst
              'weak-rewrite-constant-p))
         (t (value nil)))))

(defun collect-non-terms (lst wrld)
  (cond ((endp lst) nil)
        ((termp (car lst) wrld)
         (collect-non-terms (cdr lst) wrld))
        (t (cons (car lst)
                 (collect-non-terms (cdr lst) wrld)))))

(defun rewrite$-fn (term alist hyps equiv geneqv obj

; Hints (Warning: Keep this in sync with *rewrite$-hint-keywords* and with
; rewrite$):

                         backchain-limit-rw expand hands-off in-theory
                         no-thanks nonlinearp restrict rw-cache-state

; Other basic options:

                         step-limit
                         prove-forced-assumptions translate untranslate
                         default-hints-p
                         must-rewrite repeat
                         ctx wrld

; Advanced options:

                         rcnst saved-pspv

;

                         state)
  (b* (((er repeat)
        (cond ((posp repeat) (value repeat))
              (t (er soft ctx
                     "The :REPEAT argument of rewrite$ must be a positive ~
                      integer; ~x0 is thus illegal."
                     repeat))))
       ((er ?)
        (rewrite$-check-args alist must-rewrite
                             backchain-limit-rw expand hands-off in-theory
                             no-thanks nonlinearp restrict rw-cache-state
                             step-limit rcnst ctx state))
       ((er tterm)
        (cond (translate
               (translate term
                          t ; stobjs-out for theorems
                          t ; logic-modep
                          t ; known-stobjs, probably irrelevant
                          ctx wrld state))
              ((termp term wrld) (value term))
              (t (er soft ctx
                     "The first argument of rewrite$ must be a term unless ~
                      :translate is specifed, but ~x0 is not a term."
                     term))))
       ((er translated-alist)
        (cond ((not (symbol-alistp alist))
               (er soft ctx
                   "The :ALIST argument that was supplied rewrite$ is not a ~
                    symbol-alistp:~|~x0."
                   alist))
              (translate
               (b* (((er cdrs)
                     (translate-term-lst (strip-cdrs alist)
                                         t ; stobjs-out
                                         t ; logic-modep
                                         t ; known-stobjs-lst
                                         ctx wrld state)))
                 (value (pairlis$ (strip-cars alist) cdrs))))
              (t (b* ((bad (collect-non-termp-cdrs alist wrld))
                      ((when bad)
                       (er soft ctx
                           "Non-term value~#0~[~/s~] in :ALIST argument of ~
                            rewrite$:~|~&0"
                           bad)))
                   (value alist)))))
       ((er thyps)
        (cond ((not (true-listp hyps))
               (er soft ctx
                   "The :HYPS argument that was supplied rewrite$ is not a ~
                    true-list:~|~x0."
                   hyps))
              (translate
               (translate-term-lst hyps
                                   t ; stobjs-out for theorems
                                   t ; logic-modep
                                   t ; known-stobjs-lst
                                   ctx wrld state))
              (t (let ((bad (collect-non-terms hyps wrld)))
                   (cond ((null bad) (value hyps))
                         (t (er soft ctx
                                "The :hyps argument of rewrite$ must be a ~
                                 list of terms unless :translate t is ~
                                 specifed.  However, ~&0 ~#0~[is not a ~
                                 (translated) term~/are not (translated) ~
                                 terms~]."
                                bad)))))))
       ((er geneqv)
        (cond ((null equiv)
               (value geneqv)) ; Note that the alleged geneqv isn't checked.
              (geneqv
               (er soft ctx
                   "It is illegal for a call of rewrite$ to include values ~
                    for both the :EQUIV and :GENEQV options."))
              ((eq equiv 'equal)
               (value nil))
              ((not (symbolp equiv))
               (er soft ctx
                   "The :EQUIV argument of rewrite$ must be a symbol, unlike ~
                    ~x0."
                   equiv))
              ((equivalence-relationp equiv wrld)
               (value
                (cadr (car (last (getpropc equiv 'congruences nil wrld))))))
              (t (er soft ctx
                     "The :EQUIV argument of rewrite$ must denote an ~
                      equivalence relation, unlike ~x0."
                     equiv))))
       ((er thints)
        (cond
         (saved-pspv
          (cond ((not (weak-prove-spec-var-p saved-pspv))

; This is definitely an inadequate check!  Users of :saved-pspv are taking
; responsibility for supplying an authentic pspv.  Here we are just doing a
; trivial syntactic check to catch basic errors and to protect the access just
; below.

                 (er soft ctx
                     "The value of :SAVED-PSPV in a call of rewrite$ must ~
                      have the shape of a prove-spec-var record, but that ~
                      value has been supplied as ~x0, which fails to satisfy ~
                      the predicate ~x1."
                     saved-pspv
                     'weak-prove-spec-var-p))
                (t (value (access prove-spec-var saved-pspv :orig-hints)))))
         (t
          (b* ((kwd-alist

; Warning: Keep this in sync with *rewrite$-hint-keywords* and the "hints"
; keywords of rewrite$.

                (append (and backchain-limit-rw (list :backchain-limit-rw
                                                      backchain-limit-rw))
                        (and expand (list :expand expand))
                        (and hands-off (list :hands-off hands-off))
                        (and in-theory (list :in-theory in-theory))
                        (and no-thanks (list :no-thanks no-thanks))
                        (and nonlinearp (list :nonlinearp nonlinearp))
                        (and restrict (list :restrict restrict))
                        (and rw-cache-state (list :rw-cache-state
                                                  rw-cache-state))))
               (hints0 `(("Goal" ,@kwd-alist)))
               (default-hints (default-hints wrld)))
            (cond
             ((or kwd-alist default-hints)
              (if default-hints-p
                  (translate-hints+ 'rewrite$ hints0 default-hints ctx wrld
                                    state)
                (translate-hints 'rewrite$ hints0 ctx wrld state)))
             (t (value nil)))))))
       ((er saved-pspv)
        (cond ((null saved-pspv)
               (value (rewrite$-pspv thints wrld state)))
              (t ; see basic check on saved-pspv above and associated comment
               (value saved-pspv))))
       ((er forced-assumptions-hints)
        (cond ((consp prove-forced-assumptions)
               (translate-hints 'rewrite$ prove-forced-assumptions ctx wrld
                                state))
              ((eq prove-forced-assumptions :same-hints)
               (value thints))
              ((member-eq prove-forced-assumptions '(t nil :none-forced))
               (value nil))
              (t (er soft ctx
                     "The :prove-forced-assumptions argument supplied to ~
                      rewrite$, ~x0, is illegal."
                     prove-forced-assumptions))))

; The following two initializations will be redone by prove if forcing requires
; it to be called to dispatch forced assumptions.  It was tempting to call
; initialize-proof-tree as well, as is done in the ACL2 source function,
; waterfall when proof-tree output is enabled; however, we don't expect any
; such output during execution of rewrite$ except perhaps in
; forced-assumptions, where we call prove, whose generated call of waterfall
; will take care of that.

       (- (initialize-brr-stack state))
       (- (initialize-fc-wormhole-sites)))
    (rewrite$-main tterm translated-alist thyps geneqv obj
                   thints step-limit
                   prove-forced-assumptions forced-assumptions-hints
                   untranslate
                   must-rewrite repeat saved-pspv
                   ctx wrld rcnst state)))

(defmacro rewrite$ (term
                    &key
                    alist
                    hyps
                    equiv geneqv
                    (obj ''?) ; obj of ACL2's rewrite function

; Hints (Warning: Keep this in sync with *rewrite$-hint-keywords* and where
; hint keywords are used in rewrite$-fn.

                    backchain-limit-rw expand hands-off in-theory
                    no-thanks nonlinearp restrict rw-cache-state

; Other basic options:

                    (step-limit '*default-step-limit*)
                    (prove-forced-assumptions 't)
                    translate untranslate
                    (default-hints-p 't)
                    must-rewrite
                    (repeat '1)
                    (ctx ''rewrite$)
                    (wrld '(w state)) ; probably rarely set by user

; Advanced options:

                    rcnst saved-pspv)
  (let ((form
         `(rewrite$-fn ,term ,alist ,hyps ,equiv ,geneqv ,obj
                       ,backchain-limit-rw ,expand ,hands-off ,in-theory
                       ,no-thanks ,nonlinearp ,restrict ,rw-cache-state
                       ,step-limit ,prove-forced-assumptions
                       ,translate ,untranslate
                       ,default-hints-p ,must-rewrite ,repeat
                       ,ctx ,wrld
                       ,rcnst ,saved-pspv
                       state)))
    (cond (step-limit

; We create a legal call of with-prover-step-limit!, so that an illegal
; step-limit will result in a more helpful error (from rewrite$-check-args,
; rather than from with-prover-step-limit!).

           `(with-prover-step-limit! (let ((step-limit ,step-limit))
                                       (and (natp step-limit)
                                            (<= step-limit *default-step-limit*)
                                            step-limit))
                                     ,form))
          (t form))))
