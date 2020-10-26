; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides a flexible and convenient interface to the ACL2 rewriter,
; which can be called programmatically.  See :DOC rewrite$.  It is based on
; community book misc/expander.lisp, originally written by Matt Kaufmann but
; with contributions from Pete Manolios and Daron Vroon.

;;; Possible future work to consider if there is a need:

; - Complete documentation and comments.

;   - Explain in :doc rewrite$-hyps and comments that the rewriter is set up,
;     for example for mfc-clause, so that the clause being simplified is shown
;     as the top-level hypotheses (see :current-clause setting in
;     rewrite$-rcnst).  Also perhaps document the notion of
;     *rewrite$-last-literal* as something that could for example show up with
;     cw-gstack.  These are kind of subtle and documenting them might be more
;     confusing than helpful.

;   - Add :doc rewrite$-translate-hints.

; - Consider printing runes summary even when failing.

; - Maybe share code for handling forced assumptions in rewrite$,
;   rewrite$-hyps, and rewrite$-context.

; - Permit verbose output, especially to track progress, e.g., when simplifying
;   hyps.  More generally, think more about output.  In particular, appearance
;   of "Goal'" (for example) when proving forced-assumptions is probably
;   distracting.

; - Do at least a rudimentary check on the thints argument of rewrite$-hyps
;   (e.g., in rewrite$-hyps-main).

; - Maybe allow :untranslate to take a value that means "untranslate for all
;   output, but return a translated result."

; - Maybe control whether override hints are used.

; - Consider having rewrite$ return a ctx-msg pair and not take state.  At the
;   least, hint translation would have to be changed to avoid state (which is
;   already the case for ACL2(p)).

; - Consider adding :step-limit argument and returning step-limit values to
;   pass along.  It could be tricky to track the step-limit through calls to
;   the prover for forced assumptions: (get-event-data may return nil after
;   those calls, and (@ last-step-limit) might return -1.

; - Consider returning something other than what is returned by
;   rewrite$-return.  In particular, the "pairs" isn't easy to use without some
;   documentation.

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
 The documentation below is divided into the following sections.</p>

 <ul>

 <li>An introductory example</li>
 <li>Return values</li>
 <li>General Form</li>
 <li>Basic options</li>
 <li>Hint options, each with default @('nil')</li>
 <li>Advanced options</li>
 <li>Summary of algorithm</li>
 <li>Related tools</li>

 </ul>

 <h3>An introductory example</h3>

 <p>We begin with the following example of a call of @('rewrite$').  The
 keyword option @(':translate t') is used because the first argument is not a
 translated @(see term), due to the call of the macro, @(tsee append).  We see
 that the call of @('rewrite$') produces a 2-element list consisting of the
 result, @('X'), of rewriting the input term, together with a list of @(see
 rune)s justifying that rewrite.</p>

 @({
 ACL2 !>(rewrite$ '(car (append (cons x y) z)) :translate t)
  (X ((:DEFINITION BINARY-APPEND)
      (:REWRITE CDR-CONS)
      (:REWRITE CAR-CONS)
      (:FAKE-RUNE-FOR-TYPE-SET NIL)))
 ACL2 !>
 })

 <p>Notice the ``fake rune'' that is returned.  Fake runes are easy to remove;
 see for example the constant @('*fake-rune-alist*') in the ACL2 sources or
 function @('drop-fake-runes') defined in community book
 @('kestrel/utilities/runes.lisp').</p>

 <p>Other simple examples may be found in community book
 @('books/demos/rewrite-dollar-input.lsp').</p>

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
 specified alist into the input term.  Another important keyword argument is
 @(':hyps'), which provides hypotheses under which the given term is to be
 rewritten.  The hypotheses themselves may be rewritten, using keyword argument
 @(':rewrite-hyps').  All keywords are documented below.</p>

 <h3>General Form</h3>

 <p>All arguments of @('rewrite$') except the first are keyword arguments,
 hence are optional, with appropriate defaults.  All are evaluated.</p>

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
           :translate                ; default nil
           :untranslate              ; default nil

; Hint options (in alphabetical order), each with default nil:

           :backchain-limit-rw :expand :hands-off :in-theory
           :no-thanks :nonlinearp :restrict :rw-cache-state

; Advanced options (in alphabetical order):

           :obj        ; default '?
           :rrec       ; default nil
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

 <li>@(':must-rewrite') (default @('nil'))<br/> indicates, when its value is
 non-@('nil'), that the rewritten term must not be equal to the input term.  It
 is illegal to supply non-@('nil') values for both @(':alist') and
 @(':must-rewrite'), since it's usually not a sensible combination since at the
 least, the alist will be substituted into the term.</li>

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

 <p>The ``advanced options'' @(':obj'), @(':wrld'), and @(':rrec') can
 generally be ignored, so we say little about them here.  @(':Obj') is the
 ``obj'' argument of the rewriter, typically the symbol `@('?')' but @('t')
 when backchaining.  See @(see rewrite$-hyps) and its use in community book
 @('books/kestrel/apt/simplify-defun-impl.lisp') for how @(':rrec') can avoid
 repeating some computations.  @(':Wrld') should probably be left as its
 default, which is the current ACL2 logical @(see world).</p>

 <h3>Summary of algorithm</h3>

 <p>Here we provide a brief summary of the algorithm used by @('rewrite$').
 Most users can probably skip this section.</p>

 <p>Not surprisingly, the primary simplification technique used by
 @('rewrite$') is rewriting.  However, @(see forward-chaining) and @(see
 linear-arithmetic) are also used, as follows.</p>

 <p>Initially, a function called @('rewrite$-setup') is invoked on the given
 @(':hyps') to produce data structures that record facts from forward-chaining
 &mdash; a so-called @('fc-pair-lst') data structure &mdash; and linear
 arithmetic &mdash; a so-called @('pot-lst') data structure.  (Exception: this
 step is skipped if @(':rrec') is supplied, since the value of that option
 already contains such information.)  Then we loop through @(':repeat')
 iterations, where each iteration proceeds according the the following
 pseudocode.  Note that the initial alist is given by @(':alist'), but
 subsequent alists are all @('nil').</p>

 @({
 Replace term with its rewrite with respect to the alist, hyps, fc-pair-lst,
   and pot-lst.
 If the alist is empty and the term didn't change, exit the loop.
 })

 <h3>Related tools</h3>

 <p>See @(see rewrite$-hyps) for a tool that rewrites a list of hypotheses.
 That tool does more than just apply rewriting directly to each hypothesis: it
 also uses @(see forward-chaining) and @(see linear-arithmetic) derived from
 the hypotheses.  A related tool @(see rewrite$-context), is similar but takes
 an ``@('rrec')'' input that already contains any @(see forward-chaining) and
 @(see linear-arithmetic) information.</p>

 <p>For related tools see @(see expander) and @(see easy-simplify-term).  In
 particular, code from the expander function @('tool2-fn') served as a guide to
 the coding of @('rewrite$'); see @(see community-book)
 @('books/misc/expander.lisp').</p>")

(defxdoc rewrite$-hyps
  :parents (proof-automation)
  :short "Rewrite a list of hypotheses"
  :long "<p>See @(see rewrite$) for relevant background.</p>

 <p>Roughly speaking, @('rewrite$-hyps') applies rewriting to each term in a
 given list.  However, it treats that input as a list of hypotheses: each term
 in the list is rewritten under the assumption that the other terms in the list
 are true.  Both @(see forward-chaining) and @(see linear-arithmetic) are
 used.</p>

 <h3>General Form</h3>

 <p>All arguments of @('rewrite$-hyps') except the first are keyword arguments,
 hence are optional, with appropriate defaults.  All are evaluated.</p>

 @({
 (rewrite$-hyps hyps
                &key

 ; Hint options:

                thints ; must be nil if any other hint options are supplied
                backchain-limit-rw expand hands-off in-theory
                no-thanks nonlinearp restrict rw-cache-state
                default-hints-p           ; default t

 ; Other options:

                ctx                       ; default 'rewrite$-hyps
                prove-forced-assumptions  ; default t
                repeat                    ; default 1
                translate                 ; default nil
                untranslate               ; default nil
                update-rrec               ; default t
                wrld                      ; default (w state)
                )
 })

 <p>This macro returns an @(see error-triple) whose non-erroneous value is a
 list of the form @('(rewritten-hyps rrec ttree . pairs)').  Here,
 @('rewritten-hyps') is (of course) the result of rewriting the input,
 @('hyps'); @('rrec') is a so-called ``@('rewrite$-record')'' that can be
 passed as the @(':rrec') input of @(tsee rewrite$); @('ttree') is the @(see
 tag-tree) that records information from the rewriting, including the @(see
 rune)s used; and @('pairs') is @('nil') unless there are @(see force)d
 assumptions, which should never happen if input @(':prove-forced-assumptions')
 has its default value of @('t').</p>

 <p>Additional documentation may be provided here if desired.  It may suffice
 to see community book @('books/kestrel/apt/simplify-defun-impl.lisp') for an
 illustration of how @(see rewrite$-hyps) may be used.  The key idea there is
 for @('rewrite$-hyps') to produce the @(':rrec') input of @(tsee rewrite$)
 when there are repeated calls of @('rewrite$') under the same @(':hyps'), and
 especially when you want first to simplify those hypotheses (perhaps together
 with subterm governors).</p>")

(defxdoc rewrite$-context
  :parents (proof-automation)
  :short "Rewrite a list of contextual assumptions"
  :long "<p>See @(see rewrite$) for relevant background.  The macro
 @('rewrite$-context') is similar to @(see rewrite$-hyps), but it takes a
 @('rewrite$-record') (``@('rrec')'') as an input to provide any @(see
 forward-chaining) and @(see linear-arithmetic) assumptions.</p>

 <p>Additional documentation may be provided here if requested by someone who
 is considering use of this utility.  As of its initial introduction, it is not
 used in any of the @(see community-books)</p>")

(defconst *simplify$-hyps-contradiction-string*
  "An attempt has been made to simplify the following ~
   hypotheses:~|~%~x0.~|~%However, that list is contradictory!  (Technical ~
   note: the contradiction was found ~@1.)")

(defrec rewrite$-record

; This record holds values precomputed for calls of rewrite$ and
; rewrite$-clause.  The shape here isn't very important, since fields are not
; read or written very often.

  ((saved-pspv rcnst . type-alist)
   gstack fc-pair-lst . pot-lst)
  nil)

(defun rewrite$-clause-type-alist (clause fc-pair-lst rcnst wrld pot-lst)

; This is a variant of ACL2 source function rewrite-clause-type-alist.  We use
; it in rewrite$, below, to set things up for rewriting a term.  We are guided
; by how rewrite-clause-type-alist sets things up for rewriting a literal.

  (mv-let
    (lits ttree-lst)
    (select-forward-chained-concls-and-ttrees fc-pair-lst nil nil nil)
    (mv-let (current-clause current-ttree-lst)
      (mv (append clause lits)
          (make-list-ac (len clause) nil ttree-lst))
      (mv-let (contradictionp type-alist ttree)
        (type-alist-clause
         current-clause
         current-ttree-lst
         nil            ; force-flg
         nil            ; initial type-alist
         (access rewrite-constant rcnst :current-enabled-structure)
         wrld
         pot-lst
         nil)
        (mv contradictionp type-alist ttree)))))

(defun rewrite$-setup (hyps-clause rcnst untranslate ctx wrld state)

; We return an error triple whose non-error value is (list* type-alist pot-lst
; fc-pair-lst).  The type-alist is useful for rewrite$ but not for
; rewrite$-hyps, where a new type-alist is generated for each literal while
; rewriting a clause.

  (b* (((when (null hyps-clause)) ; optimization for possibly common case
        (value (list* nil nil)))
       (pts (enumerate-elements hyps-clause 0))
       ((mv contradictionp type-alist fc-pair-lst)
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
            *simplify$-hyps-contradiction-string*
            (let ((x (dumb-negate-lit-lst hyps-clause)))
              (if untranslate
                  (untranslate-lst x t wrld)
                x))
            "using type-set reasoning, based perhaps on forward chaining"))
       ((mv ?step-limit contradictionp pot-lst)
        (setup-simplify-clause-pot-lst hyps-clause
                                       (pts-to-ttree-lst pts)
                                       fc-pair-lst type-alist rcnst wrld state
                                       *default-step-limit*))
       ((when contradictionp)
        (er soft ctx
            *simplify$-hyps-contradiction-string*
            (dumb-negate-lit-lst hyps-clause)
            "using linear arithmetic reasoning"))
       ((mv contradictionp type-alist ?ttree)
        (rewrite$-clause-type-alist hyps-clause fc-pair-lst rcnst wrld
                                    pot-lst))
       ((when contradictionp)
        (er soft ctx
            *simplify$-hyps-contradiction-string*
            (dumb-negate-lit-lst hyps-clause)
            "using type-set reasoning (after forward chaining and linear ~
             arithmetic)")))
    (value (list* type-alist pot-lst fc-pair-lst))))

(defstub rewrite$-last-literal-fn () t)

(defconst *rewrite$-last-literal*
  (fcons-term* 'rewrite$-last-literal-fn))

(defconst *rewrite$-note-msg*
  "<<Rewrite$ NOTE:>>~|")

(defun rewrite$* (term alist bkptr
                       repeat-limit completed-iters
; some &extra formals
                       type-alist obj geneqv pot-lst
                       rcnst gstack ttree rewrite-stack-limit
; remaining arguments
                       ctx wrld state)

; Rewrite term repeatedly, (- repeat-limit completed-iters) times or until the
; term doesn't change with input alist nil, whichever comes first.

; Note that alist is nil after the first iteration.

; This function is adapted from rewrite* in books/misc/expander.lisp.

; We return an error triple with non-erroneous value (list* flg term ttree),
; where flg is t when the iteration stops because the term is not changed by
; rewriting and the alist is empty.  Code could perhaps be simplified since it
; is illegal to call rewrite$ with non-nil values for both :alist and
; :must-rewrite; but we don't rely on that restriction.

  (b* (((mv ?step-limit val new-ttree)
        (rewrite-entry (rewrite term alist bkptr)
; Need keywords arguments for missing "&extra formals" noted above:
                       :rdepth rewrite-stack-limit
                       :step-limit *default-step-limit*
                       :pequiv-info nil
                       :fnstack nil
                       :ancestors nil
                       :backchain-limit (access rewrite-constant rcnst
                                                :backchain-limit-rw)
                       :simplify-clause-pot-lst pot-lst))
       (completed-iters (1+ completed-iters))
       ((when (and (null alist)
                   (equal val term)))
        (value (list* t term ttree)))
       ((when (int= repeat-limit completed-iters)) ; note repeat-limit > 0
        (value (list* nil val new-ttree)))
       (state (io? prove nil state
                   (completed-iters)
                   (fms "~@0Starting ~n1 call of the rewriter.~%"
                        (list (cons #\0 *rewrite$-note-msg*)
                              (cons #\1 (list (1+ completed-iters))))
                        (proofs-co state) state nil)))
       ((mv ?step-limit bad-ass new-ttree)
        (resume-suspended-assumption-rewriting new-ttree nil gstack pot-lst
                                               rcnst wrld state
                                               *default-step-limit*))
       ((when bad-ass)
        (er soft ctx
            "Generated false assumption (from force or case-split):~|~x0"
            bad-ass)))
    (rewrite$* val nil bkptr
               repeat-limit completed-iters
               type-alist obj geneqv pot-lst
               rcnst gstack new-ttree rewrite-stack-limit
               ctx wrld state)))

(defun rewrite$-return (rewritten-term ttree pairs untranslate wrld state)

; Pairs is nil unless rewrite$ argument :prove-forced-assumptions has value
; nil, in which case it is a "pairs" value as returned by
; extract-and-clausify-assumptions.  The important thing about pairs is that if
; it is non-nil, then its clauses (cdrs) must be proved in order to justify the
; rewriting of the input term (implicit here) to rewritten-term.

; At one time, when we attempted to track step-limits,
; accumulate-ttree-and-step-limit-into-state was called here.  We don't track
; step-limits now and we see no need to update the global 'accumulated-ttree,
; so we don't bother.

  (b* ((new-term (if untranslate
                     (untranslate rewritten-term nil wrld)
                   rewritten-term)))
    (value (list* new-term
                  (all-runes-in-ttree ttree nil)
                  pairs))))

(defun rewrite$-process-assumptions-msg (n0 pairs untranslate clause-set
                                            forced-goal wrld state)

; This variant of ACL2 source function process-assumptions-msg is crafted to
; print something appropriate for rewrite$.

  (io? prove nil state
       (n0 pairs untranslate clause-set forced-goal wrld)
       (fms "~@0Rewriting is complete for the input term, but ~
             it remains to prove the goal generated by cleaning up ~n1 forced ~
             ~#2~[hypothesis~/hypotheses (and conjoining into a single ~
             term)~], as follows:~|~%~x3~|~%"
            (list (cons #\0 *rewrite$-note-msg*)
                  (cons #\1 n0)
                  (cons #\2 (if (cdr pairs) 1 0))
                  (cons #\3 (if untranslate
                                (prettyify-clause-set clause-set
                                                      (let*-abstractionp state)
                                                      wrld)
                              forced-goal)))
            (proofs-co state)
            state
            nil)))

(defconst *rewrite$-hint-keywords*

; Warning: Keep this in sync with the "hints" keywords of rewrite$ and where
; hint keywords are used in rewrite$-fn.

  '(:backchain-limit-rw :expand :hands-off :in-theory
                        :no-thanks :nonlinearp :restrict :rw-cache-state))

(defun rewrite$-main (term alist geneqv obj
                           prove-forced-assumptions forced-assumptions-hints
                           untranslate
                           must-rewrite repeat
                           rrec ctx wrld state)

; Term and alist are already translated.

; Much of the code below is adapted from tool2-fn1 in books/misc/expander.lisp.
; That in turn adapts code from ACL2 source function simplify-clause1.  Note
; that here we skip the calls of process-equational-polys and
; remove-trivial-equivalences in simplify-clause1.  Those cause
; simplify-clause1 to return with the resulting clause, without any rewriting.
; We could consider including those on at least the first iteration, at least
; if repeat > 1.

  (b* ((rcnst (access rewrite$-record rrec :rcnst))
       (type-alist (access rewrite$-record rrec :type-alist))
       (gstack (access rewrite$-record rrec :gstack))
       (pot-lst (access rewrite$-record rrec :pot-lst))
       (bkptr 0) ; Cw-gstack will say that we're rewriting the zeroth literal.
       ((er (list* flg rewritten-term ttree))
        (rewrite$* term alist bkptr
                   repeat
                   0 ; completed-iters
                   type-alist obj geneqv pot-lst
                   rcnst gstack nil (rewrite-stack-limit wrld)
                   ctx wrld state))
       ((when (and must-rewrite
                   (if (and (int= repeat 1)
                            (null alist))
                       flg
                     (equal term rewritten-term))))
        (er soft ctx
            "The term~|  ~x0~|failed to rewrite to a new term."
            (if untranslate
                (untranslate term nil wrld)
              term)))

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
        (rewrite$-return rewritten-term ttree pairs untranslate wrld state))
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
       (state (io? prove nil state
                   ()
                   (fms "~@0Beginning forcing round.~|"
                        (list (cons #\0 *rewrite$-note-msg*))
                        (proofs-co state) state nil)))
       ((mv erp val state)
        (prove forced-goal
               (change prove-spec-var
                       (access rewrite$-record rrec :saved-pspv)
                       :user-supplied-term forced-goal)
               forced-assumptions-hints
               (ens state) wrld ctx state))
       ((when erp)
        (er soft ctx
            "Rewriting has failed because of failure to prove all of the ~
             assumptions forced during rewriting.  Either disable forcing ~
             (see :DOC disable-forcing) or, if you are willing to ignore the ~
             forced assumptions, specify option :PROVE-FORCED-ASSUMPTIONS NIL ~
             for rewrite$."))
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
                     nil untranslate wrld state)))

(defun rewrite$-pspv (thints wrld state)
  (make-pspv (ens state) wrld state

; It is tempting to add a :displayed-goal field of the term to be rewritten.
; But term is not a goal.  Fortunately, :displayed-goal is not used in the ACL2
; sources, so we can get away with omitting this field rather than putting
; something unsuitable into it.

; It is also tempting to specify that :user-supplied-term, for example as
; *rewrite$-last-literal*.  But the :user-supplied-term isn't used during
; rewriting, so that seems unnecessary.  If we decide to specify
; :user-supplied-term here, then think about whether it needs to be updated
; elsewhere, in particular in code that supports rewrite$-clause.

             :orig-hints thints))

(defun weak-type-alistp (x wrld)
  (and (alistp x)
       (let ((a (strip-cars x))
             (d (strip-cdrs x)))
         (and (term-listp a wrld)
              (alistp d)
              (integer-listp (strip-cars d))))))

(defun chk-rrec-p (rrec ctx wrld state)

; This is only a partial check, both because it doesn't fully explore the
; saved-pspv or rcnst structures and because it doesn't check at all the values
; of gstack, pts, fc-pair-lst, or pot-lst.

  (b* (((unless (weak-rewrite$-record-p rrec))
        (er soft ctx
            "The value of :RREC in a call of rewrite$ must have the shape of ~
             a rewrite$-record record, but that value has been supplied as ~
             ~x0, which fails to satisfy the predicate ~x1."
            rrec
            'weak-rewrite$-record-p))
       ((unless (weak-rewrite-constant-p (access rewrite$-record rrec
                                                 :rcnst)))
        (er soft ctx
            "The value of :RREC in a call of rewrite$ must have an :RCNST ~
             field that is the shape of a rewrite-constant record.  But that ~
             field has been supplied as ~x0, which fails to satisfy the ~
             predicate ~x1."
            (access rewrite$-record rrec :rcnst)
            'weak-rewrite-constant-p))
       ((unless (weak-prove-spec-var-p (access rewrite$-record rrec
                                               :saved-pspv)))
        (er soft ctx
            "The value of :RREC in a call of rewrite$ must have a :SAVED-PSPV ~
             field that is the shape of a prove-spec-var record.  But that ~
             field has been supplied as ~x0, which fails to satisfy the ~
             predicate ~x1."
            (access rewrite$-record rrec :saved-pspv)
            'weak-prove-spec-var-p))
       ((unless (weak-type-alistp (access rewrite$-record rrec :type-alist)
                                  wrld))
        (er soft ctx
            "The value of :RREC in a call of rewrite$ must have a :TYPE-ALIST ~
             field that is a type-alist.  But that field has been supplied as ~
             ~x0, which fails to satisfy the predicate ~x1."
            (access rewrite$-record rrec :type-alist)
            'weak-type-alistp)))
    (value nil)))

(defun chk-repeat (repeat ctx state)
  (cond ((posp repeat) (value nil))
        (t (er soft ctx
               "The :REPEAT argument must be a positive integer; ~x0 is thus ~
                 illegal."
               repeat))))

(defun rewrite$-check-args (alist must-rewrite repeat hyps
                                  backchain-limit-rw expand hands-off in-theory
                                  no-thanks nonlinearp restrict rw-cache-state
                                  rrec ctx wrld state)

; We check arguments not directly checked in rewrite$-fn.

  (er-progn
   (cond ((and must-rewrite alist)
          (er soft ctx
              "It is illegal for rewrite$ to specify non-nil values for both ~
               :ALIST and :MUST-REWRITE."))
         (t (value nil)))
   (chk-repeat repeat ctx state)

; Next we check rrec when it is non-nil.  This is definitely an inadequate
; check!  Those who supply a non-nil value of rrec are taking responsibility
; for supplying one that is suitable.  Here we are just doing trivial syntactic
; checks to catch basic errors.

   (cond ((null rrec)
          (value nil))
         ((or hyps
              backchain-limit-rw expand hands-off in-theory
              no-thanks nonlinearp restrict rw-cache-state)
          (er soft ctx
              "It is illegal for a call of rewrite$ to supply values both to ~
               :RREC and to ~v0."
              `(,@(and backchain-limit-rw '(:backchain-limit-rw))
                ,@(and expand '(:expand))
                ,@(and hands-off '(:hands-off))
                ,@(and in-theory '(:in-theory))
                ,@(and no-thanks '(:no-thanks))
                ,@(and nonlinearp '(:nonlinearp))
                ,@(and restrict '(:restrict))
                ,@(and rw-cache-state '(:rw-cache-state)))))
         (t (chk-rrec-p rrec ctx wrld state)))))

(defun rewrite$-rcnst (clause saved-pspv hints ctx wrld state)

; Much of the code below is adapted from tool2-fn1 in books/misc/expander.lisp.

  (b* (((er pair) ; from waterfall1
        (find-applicable-hint-settings
         *initial-clause-id*
         clause
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
; term, so as to prevent hypotheses from expanding excessively.

                   :current-clause clause

; As of this writing, the :current-literal is not used by ACL2.  However, tools
; (in particular, metafunctions) can look at it.  The notion of "current
; literal" doesn't really make a lot of sense here, so we use a placeholder
; that may suggest that we are using rewrite$.

                   :current-literal (make current-literal
                                          :not-flg nil
                                          :atm *rewrite$-last-literal*)

; It is bold to set :force-info to t here, since simplify-clause is more
; restrictive.  However, we already have hypotheses separated out, and we don't
; want to miss out on forcing, so we take a chance here; after all, the user
; can disable forcing if desired.

                   :force-info t))))

(defun make-rrec (thyps thints untranslate ctx wrld state)

; Thyps is a list of translations of terms that have been supplied as
; hypotheses (not yet negated into a clause).  Thints is translated hints or
; nil, for example as produced by rewrite$-thints (or translate-hints or
; translate-hints+).

  (b* ((saved-pspv (rewrite$-pspv thints wrld state))
       (hyps-clause (dumb-negate-lit-lst thyps))
       (clause (add-literal *rewrite$-last-literal* hyps-clause t))
       ((er rcnst)
        (rewrite$-rcnst clause saved-pspv thints ctx wrld state))
       (gstack

; I think we need a standard sort of invocation of initial-gstack here.  For
; example, cw-gframe expects the :sys-fn to be one of just a few symbols, one
; of which is simplify-clause.  This might make output from cw-gstack or dmr a
; bit weird, since we aren't really under simplify-clause -- oh well, should be
; close enough!

        (initial-gstack 'simplify-clause nil clause))
       ((er (list* type-alist pot-lst fc-pair-lst))

; We use hyps-clause here rather than clause.  The reason is that we will be
; using forward-chaining, linear arithmetic, and rewrite$-clause-type-alist to
; set things up, and those operations don't make as much sense with the added
; literal.

        (rewrite$-setup hyps-clause rcnst untranslate ctx wrld state)))
    (value (make rewrite$-record
                 :saved-pspv saved-pspv
                 :rcnst rcnst
                 :type-alist type-alist
                 :gstack gstack
                 :fc-pair-lst fc-pair-lst
                 :pot-lst pot-lst))))

(defun rewrite$-forced-assumptions-hints (prove-forced-assumptions
                                          thints ctx wrld state)
  (cond ((consp prove-forced-assumptions)
         (translate-hints 'rewrite$ prove-forced-assumptions ctx wrld
                          state))
        ((eq prove-forced-assumptions :same-hints)
         (value thints))
        ((member-eq prove-forced-assumptions '(t nil :none-forced))
         (value nil))
        (t (er soft ctx
               "The :prove-forced-assumptions argument, ~x0, is illegal."
               prove-forced-assumptions))))

(defun collect-non-termp-cdrs (alist wrld)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) nil)
        ((termp (cdar alist) wrld)
         (collect-non-termp-cdrs (cdr alist) wrld))
        (t (cons (cdar alist)
                 (collect-non-termp-cdrs (cdr alist) wrld)))))

(defun collect-non-terms (lst wrld)
  (cond ((endp lst) nil)
        ((termp (car lst) wrld)
         (collect-non-terms (cdr lst) wrld))
        (t (cons (car lst)
                 (collect-non-terms (cdr lst) wrld)))))

(defun rewrite$-translate-hints-fn (backchain-limit-rw
                                    expand hands-off in-theory
                                    no-thanks nonlinearp restrict
                                    rw-cache-state
                                    default-hints-p ctx wrld state)
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
          (translate-hints+ ctx hints0 default-hints ctx wrld state)
        (translate-hints ctx hints0 ctx wrld state)))
     (t (value nil)))))

(defun rewrite$-translate-lst (lst translate ctx wrld state)
  (cond ((null lst) (value nil))
        ((not (true-listp lst))
         (er soft ctx
             "Not a true-list:~|~x0."
             lst))
        (translate
         (translate-term-lst lst
                             t       ; stobjs-out for theorems
                             t       ; logic-modep
                             t       ; known-stobjs-lst
                             ctx wrld state))
        (t (let ((bad (collect-non-terms lst wrld)))
             (cond ((null bad) (value lst))
                   (t (er soft ctx
                          "A supplied list of terms included the following, ~
                           which ~#0~[is not a term~/are not terms~]: ~&0.  ~
                           Specify :translate t to avoid this error."
                          bad)))))))

(defun rewrite$-fn (term alist hyps equiv geneqv obj

; Hints (Warning: Keep this in sync with *rewrite$-hint-keywords*):

                         backchain-limit-rw expand hands-off in-theory
                         no-thanks nonlinearp restrict rw-cache-state
                         default-hints-p

; Other basic options:

                         prove-forced-assumptions translate untranslate
                         must-rewrite repeat

; Advanced options:

                         ctx wrld rrec state)
  (with-guard-checking-error-triple
   nil ; as in prove-loop0
   (b* (((er ?)
         (rewrite$-check-args alist must-rewrite repeat hyps
                              backchain-limit-rw expand hands-off in-theory
                              no-thanks nonlinearp restrict rw-cache-state
                              rrec ctx wrld state))
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
         (cond (rrec (value :ignored)) ; optimization: thyps are ignored
               (t (rewrite$-translate-lst hyps translate ctx wrld state))))
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
                      "The :EQUIV argument of rewrite$ must denote a known ~
                       equivalence relation, unlike ~x0."
                      equiv))))
        ((er thints)
         (cond
          (rrec
           (value (access prove-spec-var
                          (access rewrite$-record rrec :saved-pspv)
                          :orig-hints)))
          (t
           (rewrite$-translate-hints-fn
            backchain-limit-rw expand hands-off in-theory
            no-thanks nonlinearp restrict rw-cache-state
            default-hints-p ctx wrld state))))
        ((er rrec)
         (cond (rrec (value rrec))
               (t (make-rrec thyps thints untranslate ctx wrld state))))
        ((er forced-assumptions-hints)
         (rewrite$-forced-assumptions-hints prove-forced-assumptions thints
                                            ctx wrld state))

; The following two initializations will be redone by prove if forcing requires
; it to be called to dispatch forced assumptions.  It was tempting to call
; initialize-proof-tree as well, as is done in the ACL2 source function,
; waterfall when proof-tree output is enabled; however, we don't expect any
; such output during execution of rewrite$ except perhaps in
; forced-assumptions, where we call prove, whose generated call of waterfall
; will take care of that.

        (- (initialize-brr-stack state))
        (- (initialize-fc-wormhole-sites)))
     (rewrite$-main tterm translated-alist geneqv obj
                    prove-forced-assumptions forced-assumptions-hints
                    untranslate
                    must-rewrite repeat
                    rrec ctx wrld state))))

(defmacro rewrite$ (term
                    &key
                    alist
                    (ctx ''rewrite$)
                    hyps
                    equiv geneqv

; Hints (Warning: Keep this in sync with *rewrite$-hint-keywords*):

                    backchain-limit-rw expand hands-off in-theory
                    no-thanks nonlinearp restrict rw-cache-state
                    (default-hints-p 't)

; Other basic options:

                    (prove-forced-assumptions 't)
                    translate untranslate
                    must-rewrite
                    (repeat '1)

; Advanced options:

                    (obj ''?) ; obj of ACL2's rewrite function
                    rrec
                    (wrld '(w state)))
  `(rewrite$-fn ,term ,alist ,hyps ,equiv ,geneqv ,obj
                ,backchain-limit-rw ,expand ,hands-off ,in-theory
                ,no-thanks ,nonlinearp ,restrict ,rw-cache-state
                ,default-hints-p
                ,prove-forced-assumptions
                ,translate ,untranslate
                ,must-rewrite ,repeat ,ctx ,wrld ,rrec state))

; Below we develop rewrite$-hyps, largely in analogy to the development of
; rewrite$ above.  See comments in the analogous functions for rewrite$.

(defun flatten-ors-in-lit (term)
  (case-match term
    (('not ('if & & &))
     (dumb-negate-lit-lst (flatten-ands-in-lit (fargn term 1))))
    (('if t1 t2 t3)
     (cond ((or (equal t2 *t*)
                (equal t2 t1))
            (append (flatten-ors-in-lit t1)
                    (flatten-ors-in-lit t3)))
           ((equal t3 *t*)
            (append (flatten-ors-in-lit (dumb-negate-lit t1))
                    (flatten-ors-in-lit t2)))
           (t (list term))))
    (& (cond ((equal term *nil*) nil)
             (t (list term))))))

(defun flatten-ors-in-lit-lst (x)
  (if (endp x)
      nil
    (append (flatten-ors-in-lit (car x))
            (flatten-ors-in-lit-lst (cdr x)))))

(defun rewrite$-clause-tail (tail
                             pts bkptr gstack new-clause
                             fc-pair-lst wrld pot-lst
                             rcnst ; incorporates hints
                             ttree state)

; We rewrite the given clause tail, much as ACL2 source function rewrite-clause
; does, to produce a new clause and a corresponding type-alist.  As with that
; function, we accumulate literals into new-clause, which is nil at the top
; level.  A major difference between the present function and rewrite-clause is
; that the present function returns a single clause rather than, after possibly
; splitting, a list of clauses.

  (cond
   ((null tail)
    (mv nil
        (flatten-ors-in-lit-lst new-clause)
        ttree))
   (t
    (b* (((mv not-flg atm)
          (strip-not (car tail)))
         (new-pts (cons (car pts)
                        (access rewrite-constant rcnst :pt)))
         (local-rcnst (change rewrite-constant rcnst
                              :current-literal (make current-literal
                                                     :not-flg not-flg
                                                     :atm atm)
                              :pt new-pts))
         ((mv contradictionp type-alist ttree0 current-clause)
          (rewrite-clause-type-alist tail new-clause fc-pair-lst local-rcnst
                                     wrld pot-lst))
         ((when contradictionp)
          (mv nil (list *t*) (cons-tag-trees ttree0 ttree)))
         (rw-cache-state (access rewrite-constant rcnst :rw-cache-state))
         ((mv ?step-limit val ttree1 ?fttree1)
          (pstk
           (rewrite-atm atm not-flg bkptr gstack type-alist wrld
                        pot-lst local-rcnst current-clause state
                        *default-step-limit*
                        (cond ((eq rw-cache-state :atom)
                               (erase-rw-cache ttree))
                              (t ttree)))))
         (ttree1 (cond ((eq rw-cache-state :atom)
                        (erase-rw-cache ttree1))
                       (t ttree1)))
         ((mv ?step-limit bad-ass ttree1)
          (resume-suspended-assumption-rewriting
           ttree1 nil gstack pot-lst local-rcnst wrld state
           *default-step-limit*))
         (val ; We revert to ttree later below, not here, when bad-ass.
          (cond (bad-ass (car tail))
                (not-flg (dumb-negate-lit val))
                (t val)))
         ((when (equal val *t*))
          (mv "by rewriting a negated hypothesis, ~x0, to T"
              (car tail)
              nil)))
      (rewrite$-clause-tail (cdr tail)
                            (cdr pts)
                            (1+ bkptr)
                            gstack
                            (add-literal val new-clause t)
                            fc-pair-lst wrld pot-lst

; Avoid the current literal iff it's non-nil.

                            (if (equal val *nil*) local-rcnst rcnst)

; For the new ttree we could check whether (equal val (car tail)) and, if so,
; it could be ttree1.

                            (cond (bad-ass ttree)
                                  ((eq rw-cache-state :atom) ttree1)
                                  (t (accumulate-rw-cache t
                                                          ttree1
                                                          ttree)))
                            state)))))

(defun rewrite$-clause* (clause
                         repeat-limit completed-iters
                         rcnst gstack ttree
                         fc-pair-lst pot-lst untranslate
                         ctx wrld state)
  (b* (((mv str new-clause new-ttree)
        (rewrite$-clause-tail clause
                              (enumerate-elements clause 0)
                              1 gstack nil
                              fc-pair-lst wrld pot-lst
                              rcnst ttree state))
       ((when str)
        (let ((term new-clause) ; yes, really a term
              (cl (dumb-negate-lit-lst clause)))
          (er soft ctx
              *simplify$-hyps-contradiction-string*
              (if untranslate
                  (untranslate-lst cl t wrld)
                cl)
              (msg str
                   (if untranslate
                       (untranslate term t wrld)
                     term)))))
       ((when (equal clause new-clause))
        (value (list* clause ttree)))
       (completed-iters (1+ completed-iters))
       ((er (list* ?type-alist new-pot-lst new-fc-pair-lst))
        (rewrite$-setup new-clause rcnst untranslate ctx wrld state))
       ((when (int= repeat-limit completed-iters))
        (value (list* new-clause new-ttree)))
       (state (io? prove nil state
                   (completed-iters)
                   (fms "NOTE:  Starting ~n0 iteration for rewrite$-hyps.~%"
                        (list (cons #\0 (list (1+ completed-iters))))
                        (proofs-co state) state nil)))
       (rcnst (change rewrite-constant rcnst
                      :current-clause new-clause))
       ((mv ?step-limit bad-ass new-ttree)
        (resume-suspended-assumption-rewriting
         new-ttree nil gstack pot-lst rcnst wrld state *default-step-limit*))
       ((mv fc-pair-lst pot-lst)
        (cond (bad-ass (mv fc-pair-lst pot-lst))
              (t (mv new-fc-pair-lst new-pot-lst)))))
    (rewrite$-clause* new-clause
                      repeat-limit completed-iters
                      rcnst gstack new-ttree
                      fc-pair-lst pot-lst untranslate ctx wrld state)))

(defun update-rrec (rrec hyps-clause untranslate ctx wrld state)
  (b* ((clause (add-literal *rewrite$-last-literal* hyps-clause t))
       (rcnst (change rewrite-constant
                      (access rewrite$-record rrec :rcnst)
                      :current-clause clause))
       ((er (list* type-alist pot-lst fc-pair-lst))

; We use hyps-clause here rather than clause.  The reason is that we will be
; using forward-chaining, linear arithmetic, and rewrite$-clause-type-alist to
; set things up, and those operations don't make as much sense with the added
; literal.

        (rewrite$-setup hyps-clause rcnst untranslate ctx wrld state)))
    (value (change rewrite$-record rrec
                   :rcnst rcnst
                   :type-alist type-alist
                   :fc-pair-lst fc-pair-lst
                   :pot-lst pot-lst))))

(defun rewrite$-hyps-return (clause update-rrec rrec ttree pairs
                                    untranslate ctx wrld state)
  (b* (((er rrec)
        (cond ((not update-rrec) (value rrec))
              (t (update-rrec rrec clause untranslate ctx wrld state)))))
    (value (list* (dumb-negate-lit-lst clause)
                  rrec
                  ttree pairs))))

(defmacro rewrite$-translate-hints (ctx
                                    &key
                                    backchain-limit-rw
                                    expand
                                    hands-off
                                    in-theory
                                    no-thanks
                                    nonlinearp
                                    restrict
                                    rw-cache-state
                                    default-hints-p
                                    (wrld '(w state)))

; This macro returns translated hints that can be used as an input to
; make-rrec.

  `(rewrite$-translate-hints-fn
    ctx
    ,backchain-limit-rw ,expand ,hands-off ,in-theory
    ,no-thanks ,nonlinearp ,restrict ,rw-cache-state
    ,default-hints-p ,ctx ,wrld state))

(defun rewrite$-hyps-main (hyps

; Hints (Warning: Keep this in sync with *rewrite$-hint-keywords*):

                           thints
                           backchain-limit-rw expand hands-off in-theory
                           no-thanks nonlinearp restrict rw-cache-state
                           default-hints-p default-hints-p-p

                           update-rrec prove-forced-assumptions
                           translate untranslate repeat-limit
                           ctx wrld state)

; Warning: Keep this in sync with rewrite$-main and rewrite$-context-main.
; Note that there is no function rewrite$-hyps-fn analogous to rewrite$-fn.

; See comments in rewrite$-main for more information.

  (with-guard-checking-error-triple
   nil ; as in prove-loop0
   (b* (((er ?) (chk-repeat repeat-limit ctx state))
        ((er thyps)
         (rewrite$-translate-lst hyps translate ctx wrld state))
        ((er thints)
         (cond
          ((and thints
                (or backchain-limit-rw expand hands-off in-theory
                    no-thanks nonlinearp restrict rw-cache-state
                    default-hints-p-p))
           (er soft ctx
               "It is illegal to supply keyword :THINTS to rewrite$-hyps if ~
                any individual hints keywords are supplied, in this case: ~&0."
               `(,@(and backchain-limit-rw '(:backchain-limit-rw))
                 ,@(and expand '(:expand))
                 ,@(and hands-off '(:hands-off))
                 ,@(and in-theory '(:in-theory))
                 ,@(and no-thanks '(:no-thanks))
                 ,@(and nonlinearp '(:nonlinearp))
                 ,@(and restrict '(:restrict))
                 ,@(and rw-cache-state '(:rw-cache-state))
                 ,@(and default-hints-p-p '(:default-hints-p-p)))))
          (thints (value thints))
          (t (rewrite$-translate-hints-fn
              backchain-limit-rw expand hands-off in-theory
              no-thanks nonlinearp restrict rw-cache-state
              default-hints-p ctx wrld state))))
        ((er rrec)
         (make-rrec thyps thints untranslate ctx wrld state))
        (rcnst (access rewrite$-record rrec :rcnst))
        (gstack (access rewrite$-record rrec :gstack))
        (fc-pair-lst (access rewrite$-record rrec :fc-pair-lst))
        (pot-lst (access rewrite$-record rrec :pot-lst))
        (saved-pspv (access rewrite$-record rrec :saved-pspv))
        ((er (list* clause ttree))
         (rewrite$-clause* (dumb-negate-lit-lst thyps)
                           repeat-limit 0
                           rcnst gstack nil
                           fc-pair-lst pot-lst untranslate
                           ctx wrld state))
        (ttree
         (set-cl-ids-of-assumptions ttree *initial-clause-id*))
        ((mv n0 assns pairs ttree)
         (extract-and-clausify-assumptions
          nil ;;; irrelevant with only-immediatep = nil
          ttree
          nil ;;; all forced assumptions, not only-immediatep
          (access rewrite-constant rcnst :current-enabled-structure)
          wrld
          (splitter-output)))
        ((when (or (null pairs)
                   (not prove-forced-assumptions)))
         (rewrite$-hyps-return clause update-rrec rrec ttree pairs
                               untranslate ctx wrld state))
        ((when (eq prove-forced-assumptions :none-forced))
         (er soft ctx
             "There were forced assumptions from simplifying hypotheses, ~
              which is not allowed in this context."))
        (clause-set (strip-cdrs pairs))
        (forced-goal (termify-clause-set clause-set))
        (state (rewrite$-process-assumptions-msg n0 pairs
                                                 untranslate
                                                 clause-set forced-goal
                                                 wrld state))
        ((er forced-assumptions-hints)
         (rewrite$-forced-assumptions-hints prove-forced-assumptions thints
                                            ctx wrld state))
        ((mv erp val state)
         (prove forced-goal
                (change prove-spec-var saved-pspv
                        :user-supplied-term forced-goal)
                forced-assumptions-hints
                (ens state) wrld ctx state))
        ((when erp)
         (er soft ctx
             "Rewriting of hypotheses has failed because of failure to prove ~
              all of the assumptions forced during the rewriting.  Either ~
              disable forcing (see :DOC disable-forcing) or, if you are ~
              willing to ignore the forced assumptions, specify option ~
              :PROVE-FORCED-ASSUMPTIONS NIL for rewrite$-hyps."))
        (ttree (process-assumptions-ttree assns ttree)))
     (rewrite$-hyps-return clause update-rrec rrec
                           (cons-tag-trees val ttree)
                           pairs
                           untranslate ctx wrld state))))

(defmacro rewrite$-hyps (hyps
                         &key

; Hints (Warning: Keep this in sync with *rewrite$-hint-keywords*):

                         thints ; must be nil if any are supplied just below
                         backchain-limit-rw expand hands-off in-theory
                         no-thanks nonlinearp restrict rw-cache-state
                         (default-hints-p 't default-hints-p-p)

; Other options:

                         (update-rrec 't)
                         (prove-forced-assumptions 't)
                         translate untranslate
                         (repeat '1)
                         (ctx ''rewrite$-hyps)
                         (wrld '(w state))) ; probably rarely set by user
  `(rewrite$-hyps-main ,hyps
                       ,thints
                       ,backchain-limit-rw ,expand ,hands-off ,in-theory
                       ,no-thanks ,nonlinearp ,restrict ,rw-cache-state
                       ,default-hints-p ,default-hints-p-p
                       ,update-rrec ,prove-forced-assumptions
                       ,translate ,untranslate ,repeat
                       ,ctx ,wrld state))

(defconst *rewrite$-false-context*
  (list *nil*))

(defconst *rewrite$-true-context*
  nil)

(defun rewrite$-context-tail (tail bkptr rdepth gstack type-alist wrld pot-lst
                                   rcnst ; incorporates hints
                                   ttree state step-limit ts-backchain-limit
                                   acc)

; In contrast to rewrite$-clause-tail, the tail here is generally a tail of a
; list of IF tests, not negated.  That is: here we assume the first element of
; tail to be true when rewriting the rest of tail, rather than assuming it
; false.

  (cond
   ((null tail)
    (mv nil (reverse acc) type-alist ttree))
   (t
    (b* (((mv not-flg atm)
          (strip-not (car tail)))
         ((mv step-limit val ttree1)
          (rewrite-entry (rewrite atm nil bkptr)
                         :rdepth rdepth
                         :step-limit step-limit
                         :type-alist type-alist
                         :obj '?
                         :geneqv *geneqv-iff*
                         :pequiv-info nil
                         :wrld wrld
                         :state state
                         :fnstack nil
                         :ancestors nil
                         :backchain-limit (access rewrite-constant rcnst
                                                  :backchain-limit-rw)
                         :simplify-clause-pot-lst nil
                         :rcnst rcnst
                         :gstack gstack
                         :ttree ttree))
         ((mv step-limit bad-ass ttree1)
          (resume-suspended-assumption-rewriting
           ttree1 nil gstack pot-lst rcnst wrld state step-limit))
         ((mv term ttree)
          (cond (bad-ass (mv (car tail) ttree))
                (not-flg (mv (dumb-negate-lit val) ttree1))
                (t (mv val ttree1))))
         (ens (access rewrite-constant rcnst :current-enabled-structure))
         ((mv must-be-true
              must-be-false
              true-type-alist
              ?false-type-alist
              ts-ttree)

; We essentiallly copy the call of assume-true-false[-bc] from rewrite-if,
; except that the final argument is :fta because we don't care about the
; false-type-alist.  Notice that since we are not concerned here about
; tail-biting, we use pt = nil.

          (assume-true-false-bc term nil
                                (ok-to-force rcnst)
                                nil type-alist ens wrld pot-lst nil :fta
                                ts-backchain-limit))
         ((when must-be-true) ; just drop the test
          (rewrite$-context-tail (cdr tail) (1+ bkptr) rdepth gstack
                                 type-alist wrld pot-lst rcnst
                                 (cons-tag-trees ts-ttree ttree)
                                 state step-limit ts-backchain-limit acc))
         ((when must-be-false)
          (mv "by rewriting a contextual test term, ~x0, to NIL"
              (car tail)
              nil ; type-alist is kind of meaningless
              (cons-tag-trees ts-ttree ttree))))
      (rewrite$-context-tail (cdr tail) (1+ bkptr) rdepth gstack
                             true-type-alist wrld pot-lst rcnst ttree state
                             step-limit ts-backchain-limit
                             (cons term acc))))))

(defun rewrite$-context* (lst repeat-limit completed-iters rdepth gstack
                              type-alist wrld pot-lst rcnst contradiction-ok
                              untranslate ttree step-limit ts-backchain-limit
                              ctx state)
  (b* (((mv str new-lst new-type-alist new-ttree)
        (rewrite$-context-tail lst 1 rdepth gstack type-alist wrld pot-lst rcnst
                               ttree state step-limit ts-backchain-limit nil))
       ((when str)
        (cond
         (contradiction-ok
          (value (list* *rewrite$-false-context* new-type-alist new-ttree)))
         (t (let ((term new-lst)) ; yes, really a term
              (er soft ctx
                  *simplify$-hyps-contradiction-string*
                  (if untranslate
                      (untranslate-lst lst t wrld)
                    lst)
                  (msg str
                       (if untranslate
                           (untranslate term t wrld)
                         term)))))))
       ((when (equal lst new-lst))
        (value (list* lst new-type-alist ttree)))
       (completed-iters (1+ completed-iters))
       ((when (int= repeat-limit completed-iters))
        (value (list* (flatten-ands-in-lit-lst new-lst)
                      new-type-alist
                      new-ttree)))
       (state (io? prove nil state
                   (completed-iters)
                   (fms "NOTE:  Starting ~n0 iteration for rewrite$-context.~%"
                        (list (cons #\0 (list (1+ completed-iters))))
                        (proofs-co state) state nil))))
    (rewrite$-context* new-lst repeat-limit completed-iters rdepth gstack
                       type-alist wrld pot-lst rcnst contradiction-ok
                       untranslate new-ttree step-limit ts-backchain-limit ctx
                       state)))

(defun rewrite$-context-return (lst type-alist rrec ttree pairs)
  (list* lst
         (change rewrite$-record rrec
                 :type-alist type-alist)
         ttree
         pairs))

(defun rewrite$-context-main (lst rrec
                                  contradiction-ok
                                  prove-forced-assumptions
                                  translate untranslate repeat-limit
                                  ctx wrld state)

; Warning: Keep this in sync with rewrite$-hyps-main.

; Note that the returned type-alist could have entries whose ttrees have
; 'assumption tags.  Those assumptions will show up later if we use such an
; entry.

  (with-guard-checking-error-triple
   nil ; as in prove-loop0
   (b* (((er ?) (chk-repeat repeat-limit ctx state))
        (rcnst (access rewrite$-record rrec :rcnst))
        (gstack (access rewrite$-record rrec :gstack))
        (type-alist (access rewrite$-record rrec :type-alist))
        (pot-lst (access rewrite$-record rrec :pot-lst))
        (saved-pspv (access rewrite$-record rrec :saved-pspv))
        ((er tlst)
         (rewrite$-translate-lst lst translate ctx wrld state))
        ((er (list* lst2 type-alist ttree))
         (rewrite$-context* tlst repeat-limit 0
                            (rewrite-stack-limit wrld)
                            gstack type-alist wrld pot-lst rcnst
                            contradiction-ok untranslate
                            nil ; ttree
                            *default-step-limit*
                            (backchain-limit wrld :ts)
                            ctx state))
        (ttree
         (set-cl-ids-of-assumptions ttree *initial-clause-id*))
        ((mv n0 assns pairs ttree)
         (extract-and-clausify-assumptions
          nil ;;; irrelevant with only-immediatep = nil
          ttree
          nil ;;; all forced assumptions, not only-immediatep
          (access rewrite-constant rcnst :current-enabled-structure)
          wrld
          (splitter-output)))
        ((when (or (null pairs)
                   (not prove-forced-assumptions)))
         (value (rewrite$-context-return lst2 type-alist rrec ttree pairs)))
        ((when (eq prove-forced-assumptions :none-forced))
         (er soft ctx
             "There were forced assumptions from simplifying the context, but ~
              proving of forced assumptions has been disabled for this call ~
              of rewrite$-context."))
        (clause-set (strip-cdrs pairs))
        (forced-goal (termify-clause-set clause-set))
        (state (rewrite$-process-assumptions-msg n0 pairs
                                                 untranslate
                                                 clause-set forced-goal
                                                 wrld state))
        (thints (access prove-spec-var saved-pspv :orig-hints))
        ((er forced-assumptions-hints)
         (rewrite$-forced-assumptions-hints prove-forced-assumptions thints
                                            ctx wrld state))
        ((mv erp val state)
         (prove forced-goal
                (change prove-spec-var saved-pspv
                        :user-supplied-term forced-goal)
                forced-assumptions-hints
                (ens state) wrld ctx state))
        ((when erp)
         (er soft ctx
             "Rewriting of hypotheses has failed because of failure to prove ~
              all of the assumptions forced during the rewriting.  Either ~
              disable forcing (see :DOC disable-forcing) or, if you are ~
              willing to ignore the forced assumptions, specify option ~
              :PROVE-FORCED-ASSUMPTIONS NIL for rewrite$-context."))
        (ttree (process-assumptions-ttree assns ttree)))
     (value (rewrite$-context-return lst2 type-alist rrec
                                     (cons-tag-trees val ttree)
                                     pairs)))))

(defmacro rewrite$-context (lst rrec
                                &key


; Other basic options:

                                contradiction-ok
                                (prove-forced-assumptions 't)
                                translate untranslate
                                (repeat '1)
                                (ctx ''rewrite$-context)
                                (wrld '(w state))) ; probably rarely set by user
  `(rewrite$-context-main ,lst ,rrec
                          ,contradiction-ok ,prove-forced-assumptions
                          ,translate ,untranslate ,repeat
                          ,ctx ,wrld state))
