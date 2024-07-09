; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file rewrite.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun rewrite (term alist bkptr ; &extra formals
                     rdepth step-limit
                     type-alist obj geneqv pequiv-info wrld state fnstack
                     ancestors backchain-limit
                     simplify-clause-pot-lst rcnst gstack ttree)

; Comments on the function REWRITE

; The Input
; c term:        the "matrix" term we are to rewrite.
; c alist:       a substitution we are to apply to term before rewriting it.
; h type-alist:  a list of assumptions governing this rewrite
;   obj:         (objective of rewrite) t, nil, or ? - of heuristic use only.
; c geneqv:      a generated equivalence relation to maintain
; c pequiv-info: info on patterned equivalence relations (pequivs) to maintain
;   wrld:        the current world
;   fnstack:     fns and terms currently being expanded - of heuristic use only
; h ancestors:   a list of terms assumed true, modified as we backchain.
; h backchain-limit: of heuristic use only
; h simplify-clause-pot-lst: a pot-lst of polys
; h rcnst:       the rewrite constant arguments
; h ttree:       the evolving ttree describing the rewrites.
;   rdepth:      maximum allowed stack depth - of heuristic use only
;   step-limit:  number of recursive calls permitted for rewrite

; The Output:
; a new step-limit, a term term', and a tag-tree ttree'

; The Specification of Rewrite: The axioms in wrld permit us to infer that the
; Rewrite Assumption implies that term' is equivalent via geneqv+pequiv-info to
; term/alist.  One can write this "wrld |- h -> c."  The args are tagged with h
; and c according to how they are involved in this spec.

; The Rewrite Assumption: the conjunction of (a) the assumptions in type-alist,
; (b) the assumptions in ancestors, (c) the assumption of every "active" poly
; in simplify-clause-pot-lst (where a poly is inactive iff its tag-tree
; contains a 'pt containing some literal number that occurs in the :pt field of
; rcnst), and (d) the 'assumptions in the final tag-tree ttree'.

; Observe that if there are 'assumptions in the incoming ttree they are unioned
; into those made by this rewrite.  Thus, unless you want the assumptions to
; accumulate across many rewrites, you must use the empty initial tag-tree.  It
; would be incorrect to attempt to split on the "new" assumptions in the new
; tag-tree because of the unioning.

; The first value is the rewritten term.  The second is the final
; value of ttree.

  (declare (type #.*fixnat-type* rdepth)
           (type #.*fixnum-type* step-limit))
  (the-mv
   3
   #.*fixnum-type*
   (let ((gstack (push-gframe 'rewrite bkptr term alist obj geneqv))
         (rdepth (adjust-rdepth rdepth)))
     (declare (type #.*fixnat-type* rdepth))
     (cond
      ((zero-depthp rdepth)
; patch file: my-rdepth-error instead of rdepth-error
#|
       (rdepth-error
|#
       (my-rdepth-error ;patch;
        (mv step-limit (sublis-var alist term) ttree)))
      ((time-limit5-reached-p
        "Out of time in the rewriter (rewrite).") ; nil, or throws
       (mv step-limit nil nil))
      ((variablep term)
       (rewrite-entry
        (rewrite-solidify-plus (let ((temp (assoc-eq term alist)))
                                 (cond (temp (cdr temp))
                                       (t term))))))
      ((fquotep term)
       (rewrite-entry
        (rewrite-quoted-constant term)))
      ((eq (ffn-symb term) 'if)

; Normally we rewrite (IF a b c) by rewriting a and then one or both
; of b and c, depending on the rewritten a.  But in the special case
; (IF a b b) we just rewrite and return b.  We have seen examples
; where this comes up, e.g., before nth-update-rewriter was removed in
; Version_7.0, it could produce such IFs.

       (cond
        ((equal (fargn term 2) (fargn term 3))
         (rewrite-entry
          (rewrite (fargn term 2) alist 2)))
        (t
         (sl-let (rewritten-test ttree)
                 (rewrite-entry
                  (rewrite (fargn term 1) alist 1)

; When we rewrite the test of the if we use geneqv iff.  What about
; obj.  Mostly we'll use '?.  But there are a few special cases.
; Suppose you are rewriting (if t1 'nil 't) with the objective t.
; Then you should rewrite t1 with the objective nil.  This actually
; comes up in the handling of (<= x y).  That term opens to (if (< y
; x) 'nil 't).  If we had an obj of t initially, and we don't look
; into the if to see which way the branches go, then we rewrite the (<
; y x) with obj '? and miss an opportunity to use linear arithmetic.

; After Version_3.2.1 we added some more special cases.  Consider the
; following example supplied by Robert Krug.

;    (defstub quux (x) t)
;
;    (defaxiom quux-thm-1
;      (<= x (quux x))
;      :rule-classes :linear)
;
;    (defaxiom quux-thm-2
;      (integerp (quux x)))
;
;    ; Good
;
;    (defstub foo-1 (x) t)
;
;    (defun bar-1 (x)
;      (or (not (integerp x))
;          (< 4 x)))
;
;    (defaxiom foo-1-thm
;      (implies (bar-1 (quux x))
;               (foo-1 x)))
;
;    (thm  ; good
;     (implies (and (integerp x)
;                   (integerp y)
;                   (< 2 x)
;                   (< 2 y))
;              (foo-1 (+ x y))))

; Robert pointed out that if instead we switched the order of
; disjuncts in bar-1, the thm fails: (< 4 x) has moved to a test
; position and we had only passed a t or nil :obj down to the true and
; false branches.

;    (defstub foo-2 (x) t)
;
;    (defun bar-2 (x)
;      (or (< 4 x)
;          (not (integerp x))))
;
;    (defaxiom foo-2-thm
;      (implies (bar-2 (quux x))
;               (foo-2 x)))
;
;    (thm  ; bad
;     (implies (and (integerp x)
;                   (integerp y)
;                   (< 2 x)
;                   (< 2 y))
;              (foo-2 (+ x y))))

; Our goal, then, is to recognize the symmetry of OR, AND, and the
; like.  But if we do that naively then we miss the proof of the thm
; in the following case, because (or u v) expands to (if u u v) rather than to
; (if u t v).

;    (defstub foo-3 (x) t)
;
;    (defstub bar-3 (x) t)
;
;    (defaxiom bar-3-open
;      (equal (bar-3 x)
;             (or (< 4 x)
;                 (foo-3 (append x x)) ; optional extra challenge, since this
;                                      ; doesn't rewrite to a constant
;                 (not (integerp x)))))
;
;    (defaxiom foo-3-thm
;      (implies (bar-3 (quux x))
;               (foo-3 x)))
;
;    (thm  ; bad
;     (implies (and (integerp x)
;                   (integerp y)
;                   (< 2 x)
;                   (< 2 y))
;              (foo-3 (+ x y))))

; Therefore, we treat (if u u v) the same as (if u t v) for purposes
; of establishing the :obj.

                  :obj
                  (cond
                   ((eq obj '?) '?)
                   (t (let ((arg2 (if (equal (fargn term 1)
                                             (fargn term 2))
                                      *t*
                                    (fargn term 2))))
                        (cond ((quotep arg2)

; Since (if u  t  v) is essentially (or u v), :obj is same for u and v
; Since (if u nil v) is essentially (and (not u) v), :obj flips for u and v

                               (if (unquote arg2) obj (not obj)))
                              (t (let ((arg3 (fargn term 3)))
                                   (cond ((quotep arg3)

; Since (if u v  t ) is essentially (or (not u) v), :obj flips for u and v
; Since (if u v nil) is essentially (and u v), :obj is same for u and v

                                          (if (unquote arg3) (not obj) obj))
                                         (t '?))))))))
                  :geneqv *geneqv-iff*
                  :pequiv-info nil)
                 (rewrite-entry (rewrite-if rewritten-test
                                            (fargn term 1)
                                            (fargn term 2)
                                            (fargn term 3)
                                            alist))))))
      ((and (eq (ffn-symb term) 'return-last)

; We avoid special treatment for a return-last term when the first argument is
; 'progn, since the user may have intended the first argument to be rewritten
; in that case; consider for example (prog2$ (cw ...) ...).  But it is useful
; in the other cases, in particular for calls of return-last generated by calls
; of mbe, to avoid spending time rewriting the next-to-last argument.

            (not (equal (fargn term 1) ''progn)))
       (rewrite-entry
        (rewrite (fargn term 3) alist 3)
        :ttree (push-lemma
                (fn-rune-nume 'return-last nil nil wrld)
                ttree)))
      ((eq (ffn-symb term) 'hide)

; We are rewriting (HIDE x).  Recall the substitution alist.  We must
; stuff it into x.  That is, if the term is (HIDE (fn u v)) and alist
; is ((u . a) (v . b)), then we must return something equal to (HIDE
; (fn a b)).  We used to sublis-var the alist into the term.  But that
; may duplicate large terms.  So as of Version  2.6 we actually create
; (HIDE ((lambda (u v) x) a b)) or, equivalently, (HIDE (LET ((u a) (v
; b)) x)).

; Care must be taken to ensure that there are no free vars in the
; lambda.  We therefore use make-stack-from-alist to create a stack.
; This stack contains (at most) a single frame consisting of the
; appropriate formals and actuals.

; Also recall :EXPAND hints.  We must check whether we have been told
; to expand this guy.  But which guy?  (HIDE (fn a b)) or (HIDE (LET
; ((u a) (v b)) x))?  We actually ask about the latter because the
; former may be prohibitive to compute.  The fact that HIDEs are
; changed a little may make it awkward for the user to formulate
; :EXPAND or HIDE-rewrite hints without waiting to see what comes out.


       (let* ((stack (make-stack-from-alist (fargn term 1) alist))
              (inst-term (if alist
                             (fcons-term* 'hide
                                          (make-lambda-application
                                           (caar stack)
                                           (fargn term 1)
                                           (cdar stack)))
                           term))
              (new-rcnst (expand-permission-p inst-term rcnst geneqv
                                              wrld)))
         (cond
          (new-rcnst

; We abandon inst-term and rewrite the hidden part under the alist.

           (rewrite-entry (rewrite (fargn term 1) alist 1)
                          :ttree (push-lemma
                                  (fn-rune-nume 'hide nil nil wrld)
                                  ttree)
                          :rcnst new-rcnst))
          (t (rewrite-entry
              (rewrite-with-lemmas inst-term))))))
      ((lambda-nest-hidep term)

; This clause of rewrite implements ``lambda-hide commuting''.  The
; idea is that ((LAMBDA (x) (HIDE body)) actual) can be rewritten to
; (HIDE ((LAMBDA (x) body) actual)).  But, as above, we must be
; careful with the free vars.  (Note: the term is a well-formed lambda
; application, so we know the obvious about the free vars of its body
; versus its formals.  But that is not the question!  The question is:
; what variables are bound in alist?  There is no a priori
; relationship between term and alist.)

       (let* ((new-body (lambda-nest-unhide term))
              (stack (make-stack-from-alist new-body alist))
              (inst-term
               (fcons-term* 'HIDE
                            (if alist
                                (make-lambda-application
                                 (caar stack)
                                 new-body
                                 (cdar stack))
                              new-body)))
              (new-rcnst (expand-permission-p inst-term rcnst geneqv
                                              wrld)))
         (cond
          (new-rcnst

; We rewrite the ``instantiated'' term under the empty substitution.

           (rewrite-entry (rewrite (fargn inst-term 1) nil 1)
                          :ttree (push-lemma
                                  (fn-rune-nume 'hide nil nil wrld)
                                  ttree)
                          :rcnst new-rcnst))
          (t (rewrite-entry
              (rewrite-with-lemmas inst-term))))))
      ((eq (ffn-symb term) 'IMPLIES)

; We handle IMPLIES specially.  We rewrite both the hyps and the
; concl under the original type-alist, and then immediately return the
; resulting expansion.  This prevents the concl from being rewritten
; under the (presumably) more powerful type-alist gotten from assuming
; the hyps true until after any normalization has occurred.  See the
; mini-essay at assume-true-false-if.

; It is possible that this rewriting will force some hypotheses in a
; ``context free'' way, i.e., forcing might occur while rewriting the
; concl but the forced assumption won't record the hypotheses that
; might actually be necessary to establish the assumption.  This is
; not supposed to happen because the only IMPLIES we should see
; (barring any introduced by user supplied rewrite rules) are in :USE
; hyps, and their hyps are normally provable under the hyps of the
; original theorem -- and those original hyps are in the type-alist
; defining this context.

       (sl-let
        (rewritten-test ttree)
        (rewrite-entry (rewrite (fargn term 1) alist 1)
                       :obj '?
                       :geneqv *geneqv-iff*
                       :pequiv-info nil)
        (cond
         ((equal rewritten-test *nil*)
          (mv step-limit *t* ttree))
         (t
          (sl-let (rewritten-concl ttree)
                  (rewrite-entry (rewrite (fargn term 2) alist 2)
                                 :obj '?
                                 :geneqv *geneqv-iff*
                                 :pequiv-info nil)
                  (cond
                   ((equal rewritten-concl *nil*)
                    (mv step-limit
                        (dumb-negate-lit rewritten-test)
                        ttree))
                   ((or (quotep rewritten-concl) ; not *nil*
                        (equal rewritten-test rewritten-concl))
                    (mv step-limit *t* ttree))
                   ((quotep rewritten-test) ; not *nil*

; We already handle the case above that rewritten-test is *nil*.  So (implies
; test concl) almost simplifies to rewritten-concl, the issue being that
; implies returns a boolean but rewritten-concl might not be Boolean.  At this
; point we have already handled the case that rewritten-concl is a quotep (so,
; there is no opportunity at this point to simplify, for example, '3 to 't);
; but we could perhaps simplify here by checking that the rewritten-concl has a
; Boolean type-set.  However, it seems unlikely that such extra computational
; effort would be worthwhile, since calls of implies can generally be expected
; to be in a Boolean context, and we already optimize for that case just below.

                    (let ((rune
                           (geneqv-refinementp 'iff geneqv wrld)))
                      (cond
                       (rune (mv step-limit
                                 rewritten-concl
                                 (push-lemma rune ttree)))
                       (t (mv step-limit
                              (fcons-term* 'if
                                           rewritten-concl
                                           *t*
                                           *nil*)
                              ttree)))))
                   (t (mv step-limit
                          (subcor-var

; It seems reasonable to keep this in sync with the corresponding use of
; subcor-var in rewrite-atm.

                           (formals 'IMPLIES wrld)
                           (list rewritten-test rewritten-concl)
                           (bbody 'IMPLIES))
                          ttree))))))))
      ((eq (ffn-symb term) 'double-rewrite)
       (sl-let
        (term ttree)
        (rewrite-entry (rewrite (fargn term 1) alist 1))
        (rewrite-entry (rewrite term nil bkptr)
                       :ttree (push-lemma (fn-rune-nume 'double-rewrite
                                                        nil nil wrld)
                                          ttree))))
      ((not-to-be-rewrittenp
        term
        alist
        (access rewrite-constant rcnst
                :terms-to-be-ignored-by-rewrite))
       (prepend-step-limit
        2
        (rewrite-solidify (sublis-var alist term)
                          type-alist obj geneqv
                          (access rewrite-constant rcnst
                                  :current-enabled-structure)
                          wrld ttree
                          simplify-clause-pot-lst
                          (access rewrite-constant rcnst :pt))))
      (t
       (let ((fn (ffn-symb term)))
         (mv-let (term ttree)
           (if (and (eq fn 'DO$)
                    (quotep (fargn term 6))
                    (unquote (fargn term 6)))

; We rewrite any non-nil quoted irrelevant arg of a DO$ call to 'nil and blame
; DO$.  It's a mild stretch to blame this on DO$ since technically it's an
; inductively proved lemma about DO$.

               (mv (cons-term fn
                              (list (fargn term 1)
                                    (fargn term 2)
                                    (fargn term 3)
                                    (fargn term 4)
                                    (fargn term 5)
                                    *nil*))
                   (push-lemma (fn-rune-nume 'do$ nil nil wrld)
                               ttree))
               (mv term ttree))
           (mv-let (mv-nth-result mv-nth-rewritep)
             (if (eq fn 'mv-nth)
                 (simplifiable-mv-nth term alist)
                 (mv nil nil))
             (cond
              (mv-nth-result

; This is a special case.  We are looking at a term/alist of the form (mv-nth
; 'i (cons x0 (cons x1 ... (cons xi ...)...))) and we immediately rewrite it to
; xi.  The mv-nth-result either needs further rewriting under the alist (when
; mv-nth-rewritep is t) or was taken from the alist and needs no further
; rewriting (in which case we finish by calling rewrite-solidify-plus, since
; this case is similar to the variablep case of rewrite).  Before we did this,
; we would rewrite x0, x1, etc., all of which are irrelevant.  This code is
; helpful because of the way (mv-let (v0 v1 ... vi ...) (foo ...)  (p v0 ...))
; is translated.  Note however that the bkptr we report in the rewrite entry
; below is 2, i.e., we say we are rewriting the 2nd arg of the mv-nth, when in
; fact we are rewriting a piece of it (namely xi).

               (let ((ttree (push-lemma
                             (fn-rune-nume 'mv-nth nil nil wrld)
                             ttree))
                     (step-limit (1+f step-limit)))
                 (declare (type #.*fixnum-type* step-limit))
                 (if mv-nth-rewritep
                     (rewrite-entry
                      (rewrite mv-nth-result alist 2))
                     (rewrite-entry
                      (rewrite-solidify-plus mv-nth-result)))))
              (t
               (let ((ens (access rewrite-constant rcnst
                                  :current-enabled-structure)))
                 (mv-let
                   (deep-pequiv-lst shallow-pequiv-lst)
                   (pequivs-for-rewrite-args fn geneqv pequiv-info wrld ens)
                   (sl-let
                    (rewritten-args ttree)
                    (rewrite-entry
                     (rewrite-args (fargs term) alist 1 nil
                                   deep-pequiv-lst shallow-pequiv-lst
                                   geneqv fn)
                     :obj '?
                     :geneqv
                     (geneqv-lst fn geneqv ens wrld)
                     :pequiv-info nil ; ignored
                     )
                    (cond
                     ((and
                       (or (flambdap fn)
                           (logicp fn wrld))
                       (all-quoteps rewritten-args)
                       (or
                        (flambda-applicationp term)
                        (and (enabled-xfnp fn ens wrld)

; We don't mind disallowing constrained functions that have attachments,
; because the call of ev-fncall below disallows the use of attachments (last
; parameter, aok, is nil).  Indeed, we rely on this check in chk-live-state-p.

                             (not (getpropc fn 'constrainedp nil wrld)))))

; Note: The test above, if true, leads here where we execute the
; executable-counterpart of the fn (or just go into the lambda
; expression if it's a lambda application).  The test however is
; obscure.  What it says is "run the function if (a) it is either a
; lambda or a :logic function symbol, (b) all of its args are quoted
; constants, and either (c1) the fn is a lambda expression, or (c2)
; the fn is enabled and fn is not a constrained fn."  Thus,
; constrained fns fail the test.  Defined functions pass the test
; provided such functions are currently toggled.  Undefined functions
; (e.g., car) pass the test.

                      (cond
                       ((flambda-applicationp term)
                        (rewrite-entry
                         (rewrite (lambda-body fn)
                                  (pairlis$ (lambda-formals fn)
                                            rewritten-args)
                                  'lambda-body)))
                       (t
                        (let ((ok-to-force (ok-to-force rcnst)))
                          (mv-let
                            (erp val apply$ed-fns)
                            (pstk
                             (ev-fncall+ fn
                                         (strip-cadrs rewritten-args)

; The strictp argument is nil here, as we will deal with required true warrants
; in push-warrants, below.  See the Essay on Evaluation of Apply$ and Loop$
; Calls During Proofs.

                                         nil
                                         state))
                            (mv-let
                              (erp2 ttree)
                              (cond ((or erp

; No special action is necessary if apply$ed-fns is nil, as opposed to a
; non-empty list.

                                         (null apply$ed-fns))
                                     (mv erp ttree))
                                    (t (push-warrants
                                        apply$ed-fns
                                        (cons-term fn rewritten-args)
                                        type-alist ens wrld ok-to-force
                                        ttree ttree)))
                              (cond
                               (erp2

; We following a suggestion from Matt Wilding and attempt to rewrite the term
; before applying HIDE.  This is really a heuristic choice; we could choose
; always to apply HIDE, as we did before v2-8.  So we do not apply
; rewrite-primitive (as in the last COND clause, below) as this would only
; apply in the rare case that the current function symbol (whose evaluation has
; errored out) is a compound recognizer.

                                (let ((new-term1
                                       (cons-term fn rewritten-args)))
                                  (sl-let
                                   (new-term2 ttree)
                                   (rewrite-entry
                                    (rewrite-with-lemmas new-term1))
                                   (cond
                                    ((equal new-term1 new-term2)
                                     (mv step-limit
                                         (hide-with-comment
                                          (if erp
                                              (cons :non-executable erp)
                                              (cons :missing-warrant erp2))
                                          new-term1
                                          wrld state)
                                         (push-lemma
                                          (fn-rune-nume 'hide nil nil
                                                        wrld)
                                          ttree)))
                                    (t (mv step-limit new-term2 ttree))))))
                               (t (mv step-limit
                                      (kwote val)
                                      (push-lemma
                                       (fn-rune-nume fn nil t wrld)
                                       ttree))))))))))
                     ((and (eq fn 'EV$)
                           (global-val 'projects/apply/base-includedp wrld)
                           (active-runep '(:rewrite ev$-opener)) ; uses ens!
                           (quotep (car rewritten-args)))

; We're looking at (EV$ 'x y).  Under certain conditions we'll rewrite this EV$
; call by rewriting x under sigma'.  If those conditions are not met we just
; ``fall through'' to the rewriter's normal handling of a non-special-case
; function call.

; The conditions are that x must be a tame term, every function in it has been
; warranted, all the warrants are true in type-alist or can be forced, we can
; recover from y a substitution, sigma.  Sigma', mentioned above, is just the
; extension of sigma obtained by binding to 'nil all free variables of x that
; are not bound in sigma.

; This special processing of certain EV$ calls can be skipped by disabling
; (:rewrite ev$-opener), a rewrite rule in projects/apply/base.lisp.  We
; confirm that that book has been included so that we know the rewrite rule of
; that name really is our rule.

                     (let ((x (unquote (car rewritten-args)))
                           (y (cadr rewritten-args)))
                       (mv-let (flg sigma)
                         (recover-subst-from-formal-var-alist y)
                         (cond
                          ((null flg)
                           (rewrite-standard-exit fn rewritten-args))
                          ((not (and (termp x wrld)
                                     (executable-tamep x wrld)))
                           (rewrite-standard-exit fn rewritten-args))
                          (t (mv-let (warranted-fns unwarranted-fns)
                             (partition-userfns-by-warrantp (all-fnnames x)
                                                            wrld nil nil)
                             (cond
                              (unwarranted-fns
                               (rewrite-standard-exit fn rewritten-args))
                              (t (let ((new-alist
                                        (extend-subst-on-unbound-vars
                                         (all-vars x)
                                         sigma)))
                                   (mv-let (erp ttree1)
                                     (push-warrants
                                      warranted-fns
                                      term type-alist ens wrld
                                      (ok-to-force rcnst)
                                      (push-lemma?
                                       (active-runep '(:rewrite ev$-opener))
                                       ttree)
                                      ttree)
                                  (cond
                                   (erp
                                    (rewrite-standard-exit fn rewritten-args))
                                   (t

; Note that every variable in x is bound in new-alist to a term that has been
; recovered from rewritten-args, so the type-alist and the other data being
; passed into this recursive call of rewrite legitimately describes the current
; context.  Note also that as soon as rewrite sees a variable symbol it looks
; it up in alist, transferring its attention to the binding.

                                    (rewrite-entry
                                     (rewrite x new-alist
                                              'expansion)
                                     :ttree ttree1)))))))))))))
                     (t (rewrite-standard-exit fn rewritten-args))))))))))))))))
