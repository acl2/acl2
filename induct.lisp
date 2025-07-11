; ACL2 Version 8.6 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2025, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; Section:  PREPROCESS-CLAUSE

; The preprocessor is the first clause processor in the waterfall when
; we enter from prove.  It contains a simple term rewriter that expands
; certain "abbreviations" and a gentle clausifier.

; We first develop the simple rewriter, called expand-abbreviations.

; Rockwell Addition: We are now concerned with lambdas, where we
; didn't used to treat them differently.  This extra argument will
; show up in several places during a compare-windows.

(mutual-recursion

(defun abbreviationp1 (lambda-flg vars term2)

; This function returns t if term2 is not an abbreviation of term1
; (where vars is the bag of vars in term1).  Otherwise, it returns the
; excess vars of vars.  If lambda-flg is t we look out for lambdas and
; do not consider something an abbreviation if we see a lambda in it.
; If lambda-flg is nil, we treat lambdas as though they were function
; symbols.

  (cond ((variablep term2)
         (cond ((null vars) t) (t (cdr vars))))
        ((fquotep term2) vars)
        ((and lambda-flg
              (flambda-applicationp term2))
         t)
        ((member-eq (ffn-symb term2) '(if not implies)) t)
        (t (abbreviationp1-lst lambda-flg vars (fargs term2)))))

(defun abbreviationp1-lst (lambda-flg vars lst)
  (cond ((null lst) vars)
        (t (let ((vars1 (abbreviationp1 lambda-flg vars (car lst))))
             (cond ((eq vars1 t) t)
                   (t (abbreviationp1-lst lambda-flg vars1 (cdr lst))))))))

)

(defun abbreviationp (lambda-flg vars term2)

; Consider the :REWRITE rule generated from (equal term1 term2).  We
; say such a rule is an "abbreviation" if term2 contains no more
; variable occurrences than term1 and term2 does not call the
; functions IF, NOT or IMPLIES or (if lambda-flg is t) any LAMBDA.
; Vars, above, is the bag of vars from term1.  We return non-nil iff
; (equal term1 term2) is an abbreviation.

  (not (eq (abbreviationp1 lambda-flg vars term2) t)))

(mutual-recursion

(defun all-vars-bag (term ans)
  (cond ((variablep term) (cons term ans))
        ((fquotep term) ans)
        (t (all-vars-bag-lst (fargs term) ans))))

(defun all-vars-bag-lst (lst ans)
  (cond ((null lst) ans)
        (t (all-vars-bag-lst (cdr lst)
                             (all-vars-bag (car lst) ans)))))
)

(defun find-abbreviation-lemma (term geneqv lemmas ens wrld)

; Term is a function application, geneqv is a generated equivalence
; relation and lemmas is the 'lemmas property of the function symbol
; of term.  We find the first (enabled) abbreviation lemma that
; rewrites term maintaining geneqv.  A lemma is an abbreviation if it
; is not a meta-lemma, has no hypotheses, has no loop-stopper, and has
; an abbreviationp for the conclusion.

; If we win we return t, the rune of the :CONGRUENCE rule used, the
; lemma, and the unify-subst.  Otherwise we return four nils.

  (cond ((null lemmas) (mv nil nil nil nil))
        ((and (enabled-numep (access rewrite-rule (car lemmas) :nume) ens)
              (eq (access rewrite-rule (car lemmas) :subclass) 'abbreviation)
              (geneqv-refinementp (access rewrite-rule (car lemmas) :equiv)
                                 geneqv
                                 wrld))
         (mv-let
             (wonp unify-subst)
           (one-way-unify (access rewrite-rule (car lemmas) :lhs) term)
           (cond (wonp (mv t
                           (geneqv-refinementp
                            (access rewrite-rule (car lemmas) :equiv)
                            geneqv
                            wrld)
                           (car lemmas)
                           unify-subst))
                 (t (find-abbreviation-lemma term geneqv (cdr lemmas)
                                             ens wrld)))))
        (t (find-abbreviation-lemma term geneqv (cdr lemmas)
                                    ens wrld))))

(mutual-recursion

(defun expand-abbreviations-with-lemma (term geneqv pequiv-info
                                             fns-to-be-ignored-by-rewrite
                                             rdepth step-limit ens wrld state
                                             ttree)
  (mv-let
    (wonp cr-rune lemma unify-subst)
    (find-abbreviation-lemma term geneqv
                             (getpropc (ffn-symb term) 'lemmas nil wrld)
                             ens
                             wrld)
    (cond
     (wonp
      (with-accumulated-persistence
       (access rewrite-rule lemma :rune)
       ((the #.*fixnum-type* step-limit) term ttree)
       t
       (expand-abbreviations
        (access rewrite-rule lemma :rhs)
        unify-subst
        geneqv
        pequiv-info
        fns-to-be-ignored-by-rewrite
        (adjust-rdepth rdepth) step-limit ens wrld state
        (push-lemma cr-rune
                    (push-lemma (access rewrite-rule lemma :rune)
                                ttree)))))
     (t (mv step-limit term ttree)))))

(defun expand-abbreviations (term alist geneqv pequiv-info
                                  fns-to-be-ignored-by-rewrite
                                  rdepth step-limit ens wrld state ttree)

; This function is essentially like rewrite but is more restrictive in its use
; of rules.  We rewrite term/alist maintaining geneqv and pequiv-info, avoiding
; the expansion or application of lemmas to terms whose fns are in
; fns-to-be-ignored-by-rewrite.  We return a new term and a ttree (accumulated
; onto our argument) describing the rewrite.  We only apply "abbreviations"
; which means we expand lambda applications and non-rec fns provided they do
; not duplicate arguments or introduce IFs, etc. (see abbreviationp), and we
; apply those unconditional :REWRITE rules with the same property.

; It used to be written:

;  Note: In a break with Nqthm and the first four versions of ACL2, in
;  Version 1.5 we also expand IMPLIES terms here.  In fact, we expand
;  several members of *expandable-boot-strap-non-rec-fns* here, and
;  IFF.  The impetus for this decision was the forcing of impossible
;  goals by simplify-clause.  As of this writing, we have just added
;  the idea of forcing rounds and the concomitant notion that forced
;  hypotheses are proved under the type-alist extant at the time of the
;  force.  But if the simplifier sees IMPLIES terms and rewrites their
;  arguments, it does not augment the context, e.g., in (IMPLIES hyps
;  concl) concl is rewritten without assuming hyps and thus assumptions
;  forced in concl are context free and often impossible to prove.  Now
;  while the user might hide propositional structure in other functions
;  and thus still suffer this failure mode, IMPLIES is the most common
;  one and by opening it now we make our context clearer.  See the note
;  below for the reason we expand other
;  *expandable-boot-strap-non-rec-fns*.

; This is no longer true.  We now expand the IMPLIES from the original theorem
; in preprocess-clause before expand-abbreviations is called, and do not expand
; any others here.  These changes in the handling of IMPLIES (as well as
; several others) are caused by the introduction of assume-true-false-if.  See
; the mini-essay at assume-true-false-if.

  (cond
   ((zero-depthp rdepth)
    (rdepth-error
     (mv step-limit term ttree)
     t))
   ((time-limit5-reached-p ; nil, or throws
     "Out of time in preprocess (expand-abbreviations).")
    (mv step-limit nil nil))
   (t
    (let ((step-limit (decrement-step-limit step-limit)))
      (cond
       ((variablep term)
        (let ((temp (assoc-eq term alist)))
          (cond (temp (mv step-limit (cdr temp) ttree))
                (t (mv step-limit term ttree)))))
       ((fquotep term) (mv step-limit term ttree))
       ((and (eq (ffn-symb term) 'return-last)

; We avoid special treatment for return-last when the first argument is progn,
; since the user may have intended the first argument to be rewritten in that
; case; for example, the user might want to see a message printed when the term
; (prog2$ (cw ...) ...) is encountered.  But it is useful in the other cases,
; in particular for calls of return-last generated by calls of mbe, to avoid
; spending time simplifying the next-to-last argument.

             (not (equal (fargn term 1) ''progn)))
        (expand-abbreviations (fargn term 3)
                              alist geneqv pequiv-info
                              fns-to-be-ignored-by-rewrite rdepth
                              step-limit ens wrld state
                              (push-lemma
                               (fn-rune-nume 'return-last nil nil wrld)
                               ttree)))
       ((eq (ffn-symb term) 'hide)
        (mv step-limit
            (sublis-var alist term)
            ttree))
       (t
        (mv-let
         (deep-pequiv-lst shallow-pequiv-lst)
         (pequivs-for-rewrite-args (ffn-symb term) geneqv pequiv-info wrld ens)
         (sl-let
          (expanded-args ttree)
          (expand-abbreviations-lst (fargs term)
                                    alist
                                    1 nil deep-pequiv-lst shallow-pequiv-lst
                                    geneqv (ffn-symb term)
                                    (geneqv-lst (ffn-symb term) geneqv ens wrld)
                                    fns-to-be-ignored-by-rewrite
                                    (adjust-rdepth rdepth) step-limit
                                    ens wrld state ttree)
          (let* ((fn (ffn-symb term))
                 (term (cons-term fn expanded-args)))

; If term does not collapse to a constant, fn is still its ffn-symb.

            (cond
             ((fquotep term)

; Term collapsed to a constant.  But it wasn't a constant before, and so
; it collapsed because cons-term executed fn on constants.  So we record
; a use of the executable-counterpart.

              (mv step-limit
                  term
                  (push-lemma (fn-rune-nume fn nil t wrld) ttree)))
             ((member-equal fn fns-to-be-ignored-by-rewrite)
              (mv step-limit (cons-term fn expanded-args) ttree))
             ((and (all-quoteps expanded-args)
                   (enabled-xfnp fn ens wrld)
                   (or (flambda-applicationp term)
                       (not (getpropc fn 'constrainedp nil wrld))))
              (cond ((flambda-applicationp term)
                     (expand-abbreviations
                      (lambda-body fn)
                      (pairlis$ (lambda-formals fn) expanded-args)
                      geneqv pequiv-info
                      fns-to-be-ignored-by-rewrite
                      (adjust-rdepth rdepth) step-limit ens wrld state ttree))
                    ((programp fn wrld)

; We formerly thought this case was possible during admission of recursive
; definitions.  Best if it's not!  So we cause an error; if we ever hit this
; case, we can think about whether allowing :program mode functions into the
; prover processes is problematic.  Our concern about :program mode functions
; in proofs has led us in May 2016 to change the application of meta functions
; and clause-processors to insist that the result is free of :program mode
; function symbols.

                     (mv step-limit
;                        (cons-term fn expanded-args)
                         (er hard! 'expand-abbreviations
                             "Implementation error: encountered :program mode ~
                              function symbol, ~x0"
                             fn)
                         ttree))
                    (t
                     (mv-let
                      (erp val bad-fn)
                      (pstk
                       (ev-fncall+ fn (strip-cadrs expanded-args) t state))
                      (declare (ignore bad-fn))
                      (cond
                       (erp

; We originally followed a suggestion from Matt Wilding and attempt to simplify
; the term before applying HIDE.  Now, we partially follow an idea from Eric
; Smith of avoiding the application of HIDE -- we do this only here in
; expand-abbreviations, expecting that the rewriter will apply HIDE if
; appropriate.

                        (expand-abbreviations-with-lemma
                         (cons-term fn expanded-args)
                         geneqv pequiv-info
                         fns-to-be-ignored-by-rewrite
                         rdepth step-limit ens wrld state ttree))
                       (t (mv step-limit
                              (kwote val)
                              (push-lemma (fn-rune-nume fn nil t wrld)
                                          ttree))))))))
             ((flambdap fn)
              (cond ((abbreviationp nil
                                    (lambda-formals fn)
                                    (lambda-body fn))
                     (expand-abbreviations
                      (lambda-body fn)
                      (pairlis$ (lambda-formals fn) expanded-args)
                      geneqv pequiv-info
                      fns-to-be-ignored-by-rewrite
                      (adjust-rdepth rdepth) step-limit ens wrld state ttree))
                    (t

; Once upon a time (well into v1-9) we just returned (mv term ttree)
; here.  But then Jun Sawada pointed out some problems with his proofs
; of some theorems of the form (let (...) (implies (and ...)  ...)).
; The problem was that the implies was not getting expanded (because
; the let turns into a lambda and the implication in the body is not
; an abbreviationp, as checked above).  So we decided that, in such
; cases, we would actually expand the abbreviations in the body
; without expanding the lambda itself, as we do below.  This in turn
; often allows the lambda to expand via the following mechanism.
; Preprocess-clause calls expand-abbreviations and it expands the
; implies into IFs in the body without opening the lambda.  But then
; preprocess-clause calls clausify-input which does another
; expand-abbreviations and this time the expansion is allowed.  We do
; not imagine that this change will adversely affect proofs, but if
; so, well, the old code is shown on the first line of this comment.

                     (sl-let (body ttree)
                             (expand-abbreviations
                              (lambda-body fn)
                              nil
                              geneqv
                              nil ; pequiv-info
                              fns-to-be-ignored-by-rewrite
                              (adjust-rdepth rdepth) step-limit ens wrld state
                              ttree)

; Rockwell Addition:

; Once upon another time (through v2-5) we returned the fcons-term
; shown in the t clause below.  But Rockwell proofs indicate that it
; is better to eagerly expand this lambda if the new body would make
; it an abbreviation.

                             (cond
                              ((abbreviationp nil
                                              (lambda-formals fn)
                                              body)
                               (expand-abbreviations
                                body
                                (pairlis$ (lambda-formals fn) expanded-args)
                                geneqv pequiv-info
                                fns-to-be-ignored-by-rewrite
                                (adjust-rdepth rdepth) step-limit ens wrld state
                                ttree))
                              (t
                               (mv step-limit
                                   (mcons-term (list 'lambda (lambda-formals fn)
                                                     body)
                                               expanded-args)
                                   ttree)))))))
             ((member-eq fn '(iff synp mv-list cons-with-hint return-last
                                  wormhole-eval force case-split
                                  double-rewrite))

; The list above is an arbitrary subset of *expandable-boot-strap-non-rec-fns*.
; Once upon a time we used the entire list here, but Bishop Brock complained
; that he did not want EQL opened.  So we have limited the list to just the
; propositional function IFF and the no-ops.

; Note: Once upon a time we did not expand any propositional functions
; here.  Indeed, one might wonder why we do now?  The only place
; expand-abbreviations was called was from within preprocess-clause.
; And there, its output was run through clausify-input and then
; remove-trivial-clauses.  The latter called tautologyp on each clause
; and that, in turn, expanded all the functions above (but discarded
; the expansion except for purposes of determining tautologyhood).
; Thus, there is no real case to make against expanding these guys.
; For sanity, one might wish to keep the list above in sync with
; that in tautologyp, where we say about it: "The list is in fact
; *expandable-boot-strap-non-rec-fns* with NOT deleted and IFF added.
; The main idea here is to include non-rec functions that users
; typically put into the elegant statements of theorems."  But now we
; have deleted IMPLIES from this list, to support the assume-true-false-if
; idea, but we still keep IMPLIES in the list for tautologyp because
; if we can decide it's a tautology by expanding, all the better.

              (with-accumulated-persistence
               (fn-rune-nume fn nil nil wrld)
               ((the #.*fixnum-type* step-limit) term ttree)
               t
               (expand-abbreviations (bbody fn)
                                     (pairlis$ (formals fn wrld) expanded-args)
                                     geneqv pequiv-info
                                     fns-to-be-ignored-by-rewrite
                                     (adjust-rdepth rdepth)
                                     step-limit ens wrld state
                                     (push-lemma (fn-rune-nume fn nil nil wrld)
                                                 ttree))))

; Rockwell Addition:  We are expanding abbreviations.  This is new treatment
; of IF, which didn't used to receive any special notice.

             ((eq fn 'if)

; There are no abbreviation (or rewrite) rules hung on IF, so coming out
; here is ok.

              (let ((a (car expanded-args))
                    (b (cadr expanded-args))
                    (c (caddr expanded-args)))
                (cond
                 ((equal b c) (mv step-limit b ttree))
                 ((quotep a)
                  (mv step-limit
                      (if (eq (cadr a) nil) c b)
                      ttree))
                 ((and (equal geneqv *geneqv-iff*)
                       (equal b *t*)
                       (or (equal c *nil*)
                           (ffn-symb-p c 'HARD-ERROR)))

; Some users keep HARD-ERROR disabled so that they can figure out
; which guard proof case they are in.  HARD-ERROR is identically nil
; and we would really like to eliminate the IF here.  So we use our
; knowledge that HARD-ERROR is nil even if it is disabled.  We don't
; even put it in the ttree, because for all the user knows this is
; primitive type inference.

                  (mv step-limit a ttree))
                 (t (mv step-limit
                        (mcons-term 'if expanded-args)
                        ttree)))))

; Rockwell Addition: New treatment of equal.

             ((and (eq fn 'equal)
                   (equal (car expanded-args) (cadr expanded-args)))
              (mv step-limit *t* ttree))
             (t
              (expand-abbreviations-with-lemma
               term geneqv pequiv-info
               fns-to-be-ignored-by-rewrite rdepth step-limit ens
               wrld state ttree))))))))))))

(defun expand-abbreviations-lst (lst alist bkptr rewritten-args-rev
                                     deep-pequiv-lst shallow-pequiv-lst
                                     parent-geneqv parent-fn geneqv-lst
                                     fns-to-be-ignored-by-rewrite rdepth
                                     step-limit ens wrld state ttree)
  (cond
   ((null lst) (mv step-limit (reverse rewritten-args-rev) ttree))
   (t (mv-let
       (child-geneqv child-pequiv-info)
       (geneqv-and-pequiv-info-for-rewrite
        parent-fn bkptr rewritten-args-rev lst alist
        parent-geneqv
        (car geneqv-lst)
        deep-pequiv-lst
        shallow-pequiv-lst
        wrld)
       (sl-let (term1 new-ttree)
               (expand-abbreviations (car lst) alist
                                     child-geneqv child-pequiv-info
                                     fns-to-be-ignored-by-rewrite
                                     rdepth step-limit ens wrld state ttree)
               (expand-abbreviations-lst (cdr lst) alist
                                         (1+ bkptr)
                                         (cons term1 rewritten-args-rev)
                                         deep-pequiv-lst shallow-pequiv-lst
                                         parent-geneqv parent-fn
                                         (cdr geneqv-lst)
                                         fns-to-be-ignored-by-rewrite
                                         rdepth step-limit ens wrld
                                         state new-ttree))))))

)

(defun and-orp (term bool lambda-okp)

; We return t or nil according to whether term is a disjunction (if bool is t)
; or conjunction (if bool is nil).

; After v8-0 we made a change to preserve lambdas on right-hand sides of
; rewrite rules.  At that time we added the clause for lambdas below, to
; preserve the old behavior of find-and-or-lemma.  However, in general it seems
; a good idea to open up lambdas slowly, so we keep the old behavior of and-orp
; -- not diving into lambda bodies -- in other places, which also helps with
; backward compatibility (one example is the proof of lemma
; aignet-marked-copies-in-bounds-of-empty-bitarr in community book
; books/centaur/aignet/rewrite.lisp).  Parameter lambda-okp is true when we
; allow exploration of lambda bodies, else nil.  When we tried on 8/14/2018
; calling and-orp with lambda-okp = t in the case (flambda-applicationp term)
; of expand-and-or -- that is, to dive into lambda-bodies of lambda-bodies --
; we got 19 failures when trying an "everything" regression, which (of course)
; almost surely undercounts failures, since certification wasn't attempted for
; books depending on failed books.

  (case-match term
              (('if & c2 c3)
               (if bool
                   (or (equal c2 *t*) (equal c3 *t*))
                 (or (equal c2 *nil*) (equal c3 *nil*))))
              ((('lambda & body) . &)
               (and lambda-okp
                    (and-orp body bool lambda-okp)))))

(defun find-and-or-lemma (term bool lemmas ens wrld)

; Term is a function application and lemmas is the 'lemmas property of
; the function symbol of term.  We find the first enabled and-or
; (wrt bool) lemma that rewrites term maintaining iff.

; If we win we return t, the :CONGRUENCE rule name, the lemma, and the
; unify-subst.  Otherwise we return four nils.

  (cond ((null lemmas) (mv nil nil nil nil))
        ((and (enabled-numep (access rewrite-rule (car lemmas) :nume) ens)
              (or (eq (access rewrite-rule (car lemmas) :subclass) 'backchain)
                  (eq (access rewrite-rule (car lemmas) :subclass) 'abbreviation))
              (null (access rewrite-rule (car lemmas) :hyps))
              (null (access rewrite-rule (car lemmas) :heuristic-info))
              (geneqv-refinementp (access rewrite-rule (car lemmas) :equiv)
                                 *geneqv-iff*
                                 wrld)
              (and-orp (access rewrite-rule (car lemmas) :rhs) bool t))
         (mv-let
             (wonp unify-subst)
           (one-way-unify (access rewrite-rule (car lemmas) :lhs) term)
           (cond (wonp (mv t
                           (geneqv-refinementp
                            (access rewrite-rule (car lemmas) :equiv)
                            *geneqv-iff*
                            wrld)
                           (car lemmas)
                           unify-subst))
                 (t (find-and-or-lemma term bool (cdr lemmas) ens wrld)))))
        (t (find-and-or-lemma term bool (cdr lemmas) ens wrld))))

(defun expand-and-or (term bool fns-to-be-ignored-by-rewrite ens wrld state
                           ttree step-limit)

; We expand the top-level fn symbol of term provided the expansion produces a
; conjunction -- when bool is nil -- or a disjunction -- when bool is t.  We
; return four values: the new step-limit, wonp, the new term, and a new ttree.
; This fn is a No-Change Loser.

; Note that preprocess-clause calls expand-abbreviations; but also
; preprocess-clause calls clausify-input, which calls expand-and-or, which
; calls expand-abbreviations.  But this is not redundant, as expand-and-or
; calls expand-abbreviations after expanding function definitions and using
; rewrite rules when the result is a conjunction or disjunction (depending on
; bool) -- even when the rule being applied is not an abbreviation rule.  Below
; are event sequences that illustrate this extra work being done.  In both
; cases, evaluation of (getpropc 'foo 'lemmas) shows that we are expanding with
; a rewrite-rule structure that is not of subclass 'abbreviation.

; (defstub bar (x) t)
; (defun foo (x) (and (bar (car x)) (bar (cdr x))))
; (trace$ expand-and-or expand-abbreviations clausify-input preprocess-clause)
; (thm (foo x) :hints (("Goal" :do-not-induct :otf)))

; (defstub bar (x) t)
; (defstub foo (x) t)
; (defaxiom foo-open (equal (foo x) (and (bar (car x)) (bar (cdr x)))))
; (trace$ expand-and-or expand-abbreviations clausify-input preprocess-clause)
; (thm (foo x) :hints (("Goal" :do-not-induct :otf)))

  (cond ((variablep term) (mv step-limit nil term ttree))
        ((fquotep term) (mv step-limit nil term ttree))
        ((member-equal (ffn-symb term) fns-to-be-ignored-by-rewrite)
         (mv step-limit nil term ttree))
        ((flambda-applicationp term)
         (cond ((and-orp (lambda-body (ffn-symb term)) bool nil)
                (sl-let
                 (term ttree)
                 (expand-abbreviations
                  (subcor-var (lambda-formals (ffn-symb term))
                              (fargs term)
                              (lambda-body (ffn-symb term)))
                  nil
                  *geneqv-iff*
                  nil
                  fns-to-be-ignored-by-rewrite
                  (rewrite-stack-limit wrld) step-limit ens wrld state ttree)
                 (mv step-limit t term ttree)))
               (t (mv step-limit nil term ttree))))
        (t
         (let ((def-body (def-body (ffn-symb term) wrld)))
           (cond
            ((and def-body
                  (null (access def-body def-body :recursivep))
                  (null (access def-body def-body :hyp))
                  (member-eq (access def-body def-body :equiv)
                             '(equal iff))
                  (enabled-numep (access def-body def-body :nume)
                                 ens)
                  (and-orp (access def-body def-body :concl) bool nil))
             (sl-let
              (term ttree)
              (with-accumulated-persistence
               (access def-body def-body :rune)
               ((the #.*fixnum-type* step-limit) term ttree)
               t
               (expand-abbreviations
                (subcor-var (access def-body def-body
                                    :formals)
                            (fargs term)
                            (access def-body def-body :concl))
                nil
                *geneqv-iff*
                nil
                fns-to-be-ignored-by-rewrite
                (rewrite-stack-limit wrld)
                step-limit ens wrld state
                (push-lemma? (access def-body def-body :rune)
                             ttree)))
              (mv step-limit t term ttree)))
            (t (mv-let
                (wonp cr-rune lemma unify-subst)
                (find-and-or-lemma
                 term bool
                 (getpropc (ffn-symb term) 'lemmas nil wrld)
                 ens wrld)
                (cond
                 (wonp
                  (sl-let
                   (term ttree)
                   (with-accumulated-persistence
                    (access rewrite-rule lemma :rune)
                    ((the #.*fixnum-type* step-limit) term ttree)
                    t
                    (expand-abbreviations
                     (sublis-var unify-subst
                                 (access rewrite-rule lemma :rhs))
                     nil
                     *geneqv-iff*
                     nil
                     fns-to-be-ignored-by-rewrite
                     (rewrite-stack-limit wrld)
                     step-limit ens wrld state
                     (push-lemma cr-rune
                                 (push-lemma (access rewrite-rule lemma
                                                     :rune)
                                             ttree))))
                   (mv step-limit t term ttree)))
                 (t (mv step-limit nil term ttree))))))))))

(defun clausify-input1 (term bool fns-to-be-ignored-by-rewrite ens wrld state
                             ttree step-limit)

; We return three things: a new step-limit, a clause, and a ttree.  If bool is
; t, the (disjunction of the literals in the) clause is equivalent to term.  If
; bool is nil, the clause is equivalent to the negation of term.  This function
; opens up some nonrec fns and applies some rewrite rules.  The final ttree
; contains the symbols and rules used.

  (cond
   ((equal term (if bool *nil* *t*)) (mv step-limit nil ttree))
   ((ffn-symb-p term 'if)
    (let ((t1 (fargn term 1))
          (t2 (fargn term 2))
          (t3 (fargn term 3)))
      (cond
       (bool
        (cond
         ((equal t3 *t*)
          (sl-let (cl1 ttree)
                  (clausify-input1 t1 nil
                                   fns-to-be-ignored-by-rewrite
                                   ens wrld state ttree step-limit)
                  (sl-let (cl2 ttree)
                          (clausify-input1 t2 t
                                           fns-to-be-ignored-by-rewrite
                                           ens wrld state ttree step-limit)
                          (mv step-limit (disjoin-clauses cl1 cl2) ttree))))
         ((equal t2 *t*)
          (sl-let (cl1 ttree)
                  (clausify-input1 t1 t
                                   fns-to-be-ignored-by-rewrite
                                   ens wrld state ttree step-limit)
                  (sl-let (cl2 ttree)
                          (clausify-input1 t3 t
                                           fns-to-be-ignored-by-rewrite
                                           ens wrld state ttree step-limit)
                          (mv step-limit (disjoin-clauses cl1 cl2) ttree))))
         (t (mv step-limit (list term) ttree))))
       ((equal t3 *nil*)
        (sl-let (cl1 ttree)
                (clausify-input1 t1 nil
                                 fns-to-be-ignored-by-rewrite
                                 ens wrld state ttree step-limit)
                (sl-let (cl2 ttree)
                        (clausify-input1 t2 nil
                                         fns-to-be-ignored-by-rewrite
                                         ens wrld state ttree step-limit)
                        (mv step-limit (disjoin-clauses cl1 cl2) ttree))))
       ((equal t2 *nil*)
        (sl-let (cl1 ttree)
                (clausify-input1 t1 t
                                 fns-to-be-ignored-by-rewrite
                                 ens wrld state ttree step-limit)
                (sl-let (cl2 ttree)
                        (clausify-input1 t3 nil
                                         fns-to-be-ignored-by-rewrite
                                         ens wrld state ttree step-limit)
                        (mv step-limit (disjoin-clauses cl1 cl2) ttree))))
       (t (mv step-limit (list (dumb-negate-lit term)) ttree)))))
   (t (sl-let (wonp term ttree)
              (expand-and-or term bool fns-to-be-ignored-by-rewrite
                             ens wrld state ttree step-limit)
              (cond (wonp
                     (clausify-input1 term bool fns-to-be-ignored-by-rewrite
                                      ens wrld state ttree step-limit))
                    (bool (mv step-limit (list term) ttree))
                    (t (mv step-limit
                           (list (dumb-negate-lit term))
                           ttree)))))))

(defun clausify-input1-lst (lst fns-to-be-ignored-by-rewrite ens wrld state
                                ttree step-limit)

; This function is really a subroutine of clausify-input.  It just
; applies clausify-input1 to every element of lst, accumulating the ttrees.
; It uses bool=t.

  (cond ((null lst) (mv step-limit nil ttree))
        (t (sl-let (clause ttree)
                   (clausify-input1 (car lst) t fns-to-be-ignored-by-rewrite
                                    ens wrld state ttree step-limit)
                   (sl-let (clauses ttree)
                           (clausify-input1-lst (cdr lst)
                                                fns-to-be-ignored-by-rewrite
                                                ens wrld state ttree
                                                step-limit)
                           (mv step-limit
                               (conjoin-clause-to-clause-set clause clauses)
                               ttree))))))

(defun clausify-input (term fns-to-be-ignored-by-rewrite ens wrld state ttree
                            step-limit)

; This function converts term to a set of clauses, expanding some non-rec
; functions when they produce results of the desired parity (i.e., we expand
; AND-like functions in the hypotheses and OR-like functions in the
; conclusion.)  AND and OR themselves are, of course, already expanded into
; IFs, but we will expand other functions when they generate the desired IF
; structure.  We also apply :REWRITE rules deemed appropriate.  We return three
; results: a new step-limit, the set of clauses, and a ttree documenting the
; expansions.

  (sl-let (neg-clause ttree)
          (clausify-input1 term nil fns-to-be-ignored-by-rewrite ens
                           wrld state ttree step-limit)

; Neg-clause is a clause that is equivalent to the negation of term.  That is,
; if the literals of neg-clause are lit1, ..., litn, then (or lit1 ... litn)
; <-> (not term).  Therefore, term is the negation of the clause, i.e., (and
; (not lit1) ... (not litn)).  We will form a clause from each (not lit1) and
; return the set of clauses, implicitly conjoined.

          (clausify-input1-lst (dumb-negate-lit-lst neg-clause)
                               fns-to-be-ignored-by-rewrite
                               ens wrld state ttree step-limit)))

(defun expand-some-non-rec-fns-in-clauses (fns clauses wrld)

; Warning: fns should be a subset of functions that

; This function expands the non-rec fns listed in fns in each of the clauses
; in clauses.  It then throws out of the set any trivial clause, i.e.,
; tautologies.  It does not normalize the expanded terms but just leaves
; the expanded bodies in situ.  See the comment in preprocess-clause.

  (cond
   ((null clauses) nil)
   (t (let ((cl (expand-some-non-rec-fns-lst fns (car clauses) wrld)))
        (cond
         ((trivial-clause-p cl wrld)
          (expand-some-non-rec-fns-in-clauses fns (cdr clauses) wrld))
         (t (cons cl
                  (expand-some-non-rec-fns-in-clauses fns (cdr clauses)
                                                      wrld))))))))

(defun no-op-histp (hist)

; We say a history, hist, is a "no-op history" if it is empty or its most
; recent entry is a to-be-hidden preprocess-clause or apply-top-hints-clause
; (possibly followed by a settled-down-clause).

  (or (null hist)
      (and hist
           (member-eq (access history-entry (car hist) :processor)
                      '(apply-top-hints-clause preprocess-clause))
           (tag-tree-occur 'hidden-clause
                           t
                           (access history-entry (car hist) :ttree)))
      (and hist
           (eq (access history-entry (car hist) :processor)
               'settled-down-clause)
           (cdr hist)
           (member-eq (access history-entry (cadr hist) :processor)
                      '(apply-top-hints-clause preprocess-clause))
           (tag-tree-occur 'hidden-clause
                           t
                           (access history-entry (cadr hist) :ttree)))))

(mutual-recursion

; This pair of functions is copied from expand-abbreviations and
; heavily modified.  The idea implemented by the caller of this
; function is to expand all the IMPLIES terms in the final literal of
; the goal clause.  This pair of functions actually implements that
; expansion.  One might think to use expand-some-non-rec-fns with
; first argument '(IMPLIES).  But this function is different in two
; respects.  First, it respects HIDE.  Second, it expands the IMPLIES
; inside of lambda bodies.  The basic idea is to mimic what
; expand-abbreviations used to do, before we added the
; assume-true-false-if idea.

(defun expand-any-final-implies1 (term wrld)
  (cond
   ((variablep term)
    term)
   ((fquotep term)
    term)
   ((eq (ffn-symb term) 'hide)
    term)
   (t
    (let ((expanded-args (expand-any-final-implies1-lst (fargs term)
                                                        wrld)))
      (let* ((fn (ffn-symb term))
             (term (cons-term fn expanded-args)))
        (cond ((flambdap fn)
               (let ((body (expand-any-final-implies1 (lambda-body fn)
                                                      wrld)))

; Note: We could use a make-lambda-application here, but if the
; original lambda used all of its variables then so does the new one,
; because IMPLIES uses all of its variables and we're not doing any
; simplification.  This remark is not soundness related; there is no
; danger of introducing new variables, only the inefficiency of
; keeping a big actual which is actually not used.

                 (fcons-term (make-lambda (lambda-formals fn) body)
                             expanded-args)))
              ((eq fn 'IMPLIES)
               (subcor-var (formals 'implies wrld)
                           expanded-args
                           (bbody 'implies)))
              (t term)))))))

(defun expand-any-final-implies1-lst (term-lst wrld)
  (cond ((null term-lst)
         nil)
        (t
         (cons (expand-any-final-implies1 (car term-lst) wrld)
               (expand-any-final-implies1-lst (cdr term-lst) wrld)))))

 )

(defun expand-any-final-implies (cl wrld)

; Cl is a clause (a list of ACL2 terms representing a goal) about to
; enter preprocessing.  If the final term contains an 'IMPLIES, we
; expand those IMPLIES here.  This change in the handling of IMPLIES
; (as well as several others) is caused by the introduction of
; assume-true-false-if.  See the mini-essay at assume-true-false-if.

; Note that we fail to report the fact that we used the definition
; of IMPLIES.

; Note also that we do not use expand-some-non-rec-fns here.  We want
; to preserve the meaning of 'HIDE and expand an 'IMPLIES inside of
; a lambda.

  (cond ((null cl)  ; This should not happen.
         nil)
        ((null (cdr cl))
         (list (expand-any-final-implies1 (car cl) wrld)))
        (t
         (cons (car cl)
               (expand-any-final-implies (cdr cl) wrld)))))

(defun rw-cache-state (wrld)
  (let ((pair (assoc-eq t (table-alist 'rw-cache-state-table wrld))))
    (cond (pair (cdr pair))
          (t *default-rw-cache-state*))))

(defmacro make-rcnst (ens wrld state &rest args)

; (Make-rcnst ens w state) will make a rewrite-constant that is the result of
; filling in *empty-rewrite-constant* with a few obviously necessary values,
; such as the global-enabled-structure as the :current-enabled-structure.  Then
; it additionally loads user supplied values specified by alternating
; keyword/value pairs to override what is otherwise created.  E.g.,

; (make-rcnst ens w state :expand-lst lst)

; will make a rewrite-constant that is like the default one except that it will
; have lst as the :expand-lst.

; Note: Wrld and ens are used in the "default" setting of certain fields.

; Warning: wrld could be evaluated several times.  So it should be an
; inexpensive expression, such as a variable or (w state).

  `(change rewrite-constant
           (change rewrite-constant
                   *empty-rewrite-constant*
                   :current-enabled-structure ,ens
                   :oncep-override (match-free-override ,wrld)
                   :case-split-limitations (case-split-limitations ,wrld)
                   :forbidden-fns (forbidden-fns ,wrld ,state)
                   :nonlinearp (non-linearp ,wrld)
                   :backchain-limit-rw (backchain-limit ,wrld :rewrite)
                   :rw-cache-state (rw-cache-state ,wrld)
                   :heavy-linearp (if (heavy-linear-p) :heavy t))
           ,@args))

; We now finish the development of tau-clause...  To recap our story so far: In
; the file tau.lisp we defined everything we need to implement tau-clause
; except for its connection to type-alist and the linear pot-lst.  Now we can
; define tau-clause.

(defun cheap-type-alist-and-pot-lst (cl ens wrld state)

; Given a clause cl, we build a type-alist and linear pot-lst with all of the
; literals in cl assumed false.  The pot-lst is built with the heavy-linearp
; flag onff, which means we do not rewrite terms before turning them into polys
; and we add no linear lemmas.  We ensure that the type-alist has no
; assumptions or forced hypotheses.  FYI: Just to be doubly sure that we are
; not ignoring assumptions and forced hypotheses, you will note that in
; relieve-dependent-hyps, after calling type-set, we check that no such entries
; are in the returned ttree.  We return (mv contradictionp type-alist pot-lst)

  (mv-let (contradictionp type-alist ttree)
          (type-alist-clause cl nil nil nil ens wrld nil nil)
          (cond
           ((or (tagged-objectsp 'assumption ttree)
                (tagged-objectsp 'fc-derivation ttree))
            (mv (er hard 'cheap-type-alist-and-pot-lst
                    "Assumptions and/or fc-derivations were found in the ~
                     ttree constructed by CHEAP-TYPE-ALIST-AND-POT-LST.  This ~
                     is supposedly impossible!")
                nil nil))
           (contradictionp
            (mv t nil nil))
           (t (mv-let (new-step-limit provedp pot-lst)
                      (setup-simplify-clause-pot-lst1
                       cl nil type-alist
                       (make-rcnst ens wrld state
                                   :force-info 'weak
                                   :heavy-linearp nil)
                       wrld state *default-step-limit*)
                      (declare (ignore new-step-limit))
                      (cond
                       (provedp
                        (mv t nil nil))
                       (t (mv nil type-alist pot-lst))))))))

(defconst *tau-ttree*
  (add-to-tag-tree 'lemma
                   '(:executable-counterpart tau-system)
                   nil))

(defun tau-clausep (clause ens wrld state calist)

; This function returns (mv flg ttree), where if flg is t then clause is true.
; The ttree, when non-nil, is just the *tau-ttree*.

; If the executable-counterpart of tau is disabled, this function is a no-op.

  (cond
   ((enabled-numep *tau-system-xnume* ens)
    (mv-let
     (contradictionp type-alist pot-lst)
     (cheap-type-alist-and-pot-lst clause ens wrld state)
     (cond
      (contradictionp
       (mv t *tau-ttree* calist))
      (t
       (let ((triples (merge-sort-car-<
                       (annotate-clause-with-key-numbers clause
                                                         (len clause)
                                                         0 wrld))))
         (mv-let
          (flg calist)
          (tau-clause1p triples nil type-alist pot-lst
                        ens wrld calist)
          (cond
           ((eq flg t)
            (mv t *tau-ttree* calist))
           (t (mv nil nil calist)))))))))
   (t (mv nil nil calist))))

(defun tau-clausep-lst-rec (clauses ens wrld ans ttree state calist)

; We return (mv clauses' ttree) where clauses' are provably equivalent to
; clauses under the tau rules and ttree is either the tau ttree or nil
; depending on whether anything changed.  Note that this function knows that if
; tau-clause returns non-nil ttree it is *tau-ttree*: we just OR the ttrees
; together, not CONS-TAG-TREES them!

  (cond
   ((endp clauses)
    (mv (revappend ans nil) ttree calist))
   (t (mv-let
       (flg1 ttree1 calist)
       (tau-clausep (car clauses) ens wrld state calist)
       (prog2$

; If the time-tracker call below is changed, update :doc time-tracker
; accordingly.

        (time-tracker :tau :print?)
        (tau-clausep-lst-rec (cdr clauses) ens wrld
                             (if flg1
                                 ans
                               (cons (car clauses) ans))
                             (or ttree1 ttree)
                             state calist))))))

(defun tau-clausep-lst (clauses ens wrld ans ttree state calist)

; If the time-tracker calls below are changed, update :doc time-tracker
; accordingly.

  (prog2$ (time-tracker :tau :start!)
          (mv-let
           (clauses ttree calist)
           (tau-clausep-lst-rec clauses ens wrld ans ttree state calist)
           (prog2$ (time-tracker :tau :stop)
                   (mv clauses ttree calist)))))

(defun prettyify-clause-simple (cl)

; This variant of prettyify-clause does not call untranslate.

  (cond ((null cl) nil)
        ((null (cdr cl)) cl)
        ((null (cddr cl))
         (fcons-term* 'implies
                      (dumb-negate-lit (car cl))
                      (cadr cl)))
        (t (fcons-term* 'implies
                        (conjoin (dumb-negate-lit-lst (butlast cl 1)))
                        (car (last cl))))))

(defun preprocess-clause (cl hist pspv wrld state step-limit)

; This is the first "real" clause processor (after a little remembered
; apply-top-hints-clause) in the waterfall.  Its arguments and values are the
; standard ones, except that it takes a step-limit and returns a new step-limit
; in the first position.  We expand abbreviations and clausify the clause cl.
; For mainly historic reasons, expand-abbreviations and clausify-input operate
; on terms.  Thus, our first move is to convert cl into a term.

  (let ((rcnst (access prove-spec-var pspv :rewrite-constant)))
    (mv-let
      (built-in-clausep ttree)
      (cond
       ((or (eq (car (car hist)) 'simplify-clause)
            (eq (car (car hist)) 'settled-down-clause))

; If the hist shows that cl has just come from simplification, there is no
; need to check that it is built in, because the simplifier does that.

        (mv nil nil))
       (t
        (built-in-clausep 'preprocess-clause
                          cl
                          (access rewrite-constant
                                  rcnst
                                  :current-enabled-structure)
                          (access rewrite-constant
                                  rcnst
                                  :oncep-override)
                          wrld
                          state)))

; Ttree is known to be 'assumption free.

      (cond
       (built-in-clausep
        (mv step-limit 'hit nil ttree pspv))
       (t

; Here is where we expand the "original" IMPLIES in the conclusion but
; leave any IMPLIES in the hypotheses.  These IMPLIES are thought to
; have been introduced by :USE hints.

; Historical Note: We used to call possibly-clean-up-dirty-lambda-objects here
; but that was wrong because we don't have hyps to establish warrants and
; preprocess-clause shouldn't be applying conditional rewrite rules or forcing
; things anyway.

        (let ((term (disjoin (expand-any-final-implies cl wrld))))
          (sl-let (term ttree)
                  (expand-abbreviations term nil
                                        *geneqv-iff* nil
                                        (access rewrite-constant
                                                rcnst
                                                :fns-to-be-ignored-by-rewrite)
                                        (rewrite-stack-limit wrld)
                                        step-limit
                                        (access rewrite-constant
                                                rcnst
                                                :current-enabled-structure)
                                        wrld state nil)
                  (sl-let (clauses ttree)
                          (clausify-input term
                                          (access rewrite-constant
                                                  rcnst
                                                  :fns-to-be-ignored-by-rewrite)
                                          (access rewrite-constant
                                                  rcnst
                                                  :current-enabled-structure)
                                          wrld
                                          state
                                          ttree
                                          step-limit)
;;;                         (let ((clauses
;;;                                (expand-some-non-rec-fns-in-clauses
;;;                                 '(iff implies)
;;;                                 clauses
;;;                                 wrld)))

; Previous to Version_2.6 we had written:

; ; Note: Once upon a time (in Version 1.5) we called "clausify-clause-set" here.
; ; That function called clausify on each element of clauses and unioned the
; ; results together, in the process naturally deleting tautologies as does
; ; expand-some-non-rec-fns-in-clauses above.  But Version 1.5 caused Bishop a
; ; lot of pain because many theorems would explode into case analyses, each of
; ; which was then dispatched by simplification.  The reason we used a full-blown
; ; clausify in Version 1.5 was that in was also into that version that we
; ; introduced forcing rounds and the liberal use of force-flg = t.  But if we
; ; are to force that way, we must really get all of our hypotheses out into the
; ; open so that they can contribute to the type-alist stored in each assumption.
; ; For example, in Version 1.4 the concl of (IMPLIES hyps concl) was rewritten
; ; first without the hyps being manifest in the type-alist since IMPLIES is a
; ; function.  Not until the IMPLIES was opened did the hyps become "governors"
; ; in this sense.  In Version 1.5 we decided to throw caution to the wind and
; ; just clausify the clausified input.  Well, it bit us as mentioned above and
; ; we are now backing off to simply expanding the non-rec fns that might
; ; contribute hyps.  But we leave the expansions in place rather than normalize
; ; them out so that simplification has one shot on a small set (usually
; ; singleton set) of clauses.

; But the comment above is now irrelevant to the current situation.
; Before commenting on the current situation, however, we point out that
; in (admittedly light) testing the original call to
; expand-some-non-rec-fns-in-clauses in its original context acted as
; the identity.  This seems reasonable because 'iff and 'implies were
; expanded in expand-abbreviations.

; We now expand the 'implies from the original theorem (but not the
; implies from a :use hint) in the call to expand-any-final-implies.
; This performs the expansion whose motivations are mentioned in the
; old comments above, but does not interfere with the conclusions
; of a :use hint.  See the mini-essay

; Mini-Essay on Assume-true-false-if and Implies
; or
; How Strengthening One Part of a Theorem Prover Can Weaken the Whole.

; in type-set-b for more details on this latter criterion.

                          (let ((tau-completion-alist
                                 (access prove-spec-var pspv :tau-completion-alist)))
                            (mv-let
                              (clauses1 ttree1 new-tau-completion-alist)
                              (if (or (null hist)

; If (null (cdr hist)) and (null (cddr hist)) are tested in this disjunction,
; then tau is tried during the first three simplifications and then again when
; the clause settles down.  Call this the ``more aggressive'' approach.  If
; they are not tested, tau is tried only on the first simplification and upon
; settling down.  Call this ``less aggressive.''  There are, of course, proofs
; where the more aggressive use of tau speeds things up.  But of course it
; slows down many more proofs.  Overall, experiments on the regression suggest
; that the more aggressive approach slows total reported book certification
; time down by about 1.5% compared to the less aggressive approach.  However, we
; think it might be worth it as more tau-based proofs scripts are developed.

                                      (null (cdr hist))
                                      (null (cddr hist))
                                      (eq (car (car hist)) 'settled-down-clause))
                                  (let ((ens (access rewrite-constant
                                                     rcnst
                                                     :current-enabled-structure)))
                                    (if (enabled-numep *tau-system-xnume* ens)
                                        (tau-clausep-lst clauses
                                                         ens
                                                         wrld
                                                         nil
                                                         nil
                                                         state
                                                         tau-completion-alist)
                                        (mv clauses nil tau-completion-alist)))
                                  (mv clauses nil tau-completion-alist))
                              (let ((pspv (if (equal tau-completion-alist
                                                     new-tau-completion-alist)
                                              pspv
                                              (change prove-spec-var pspv
                                                      :tau-completion-alist
                                                      new-tau-completion-alist))))
                                (cond
                                 ((equal clauses1 (list cl))

; In this case, preprocess-clause has made no changes to the clause.

                                  (mv step-limit 'miss nil nil nil))
                                 ((and (consp clauses1)
                                       (null (cdr clauses1))
                                       (no-op-histp hist)
                                       (equal (prettyify-clause-simple
                                               (car clauses1))
                                              (access prove-spec-var pspv
                                                      :user-supplied-term)))

; In this case preprocess-clause has produced a singleton set of clauses whose
; only element is the translated user input.  For example, the user might have
; invoked defthm on (implies p q) and preprocess has managed to to produce the
; singleton set of clauses containing {(not p) q}.  This is a valuable step in
; the proof of course.  However, users complain when we report that (IMPLIES P
; Q) -- the displayed goal -- is reduced to (IMPLIES P Q) -- the
; prettyification of the output.

; We therefore take special steps to hide this transformation from the
; user without changing the flow of control through the waterfall.  In
; particular, we will insert into the ttree the tag
; 'hidden-clause with (irrelevant) value t.  In subsequent places
; where we print explanations and clauses to the user we will look for
; this tag.

; At one point we called prettyify-clause below instead of
; prettyify-clause-simple, and compared the (untranslated) result to the
; (untranslated) displayed-goal of the pspv.  But we have decided to avoid the
; expense of untranslating, especially since often the potentially-confusing
; printing will never take place!  Let's elaborate.  Suppose that the input
; user-level term t1 translates to termp tt1, and suppose that the result of
; preprocessing the clause set (list (list tt1)) is a single clause for which
; prettyify-clause-simple returns the (translated) term tt1.  Then we are in
; this case and we set 'hidden-clause in the returned ttree.  However, suppose
; that instead prettyify-clause-simple returns tt2 not equal to tt1, although
; tt2 nevertheless untranslates (perhaps surprisingly) to t1.  Then we are not
; in this case, and Goal' will print exactly as goal.  This is unfortunate, but
; we have seen (back in 2003!) that kind of invisible transformation happen for
; other than Goal:

;   Subgoal 3
;   (IMPLIES (AND (< I -1)
;                 (ACL2-NUMBERP J)
;                 ...)
;            ...)
;
;   By case analysis we reduce the conjecture to
;
;   Subgoal 3'
;   (IMPLIES (AND (< I -1)
;                 (ACL2-NUMBERP J)
;                 ...)
;            ...)

; As of this writing we do not handle this sort of situation, not even -- after
; Version_7.0, when we started using prettyify-clause-simple to avoid the cost
; of untranslation, instead of prettyify-clause -- for the case considered
; here, transitioning from Goal to Goal' by preprocess-clause.  Perhaps we will
; do such a check for all preprocess-clause transformations, but only when
; actually printing output (so as to avoid the overhead of untranslation).

                                  (mv step-limit
                                      'hit
                                      clauses1
                                      (add-to-tag-tree
                                       'hidden-clause t
                                       (cons-tag-trees ttree1 ttree))
                                      pspv))
                                 (t (mv step-limit
                                        'hit
                                        clauses1
                                        (cons-tag-trees ttree1 ttree)
                                        pspv))))))))))))))

; And here is the function that reports on a successful preprocessing.

(defun tilde-*-preprocess-phrase (ttree)

; This function is like tilde-*-simp-phrase but knows that ttree was
; constructed by preprocess-clause and hence is based on abbreviation
; expansion rather than full-fledged rewriting.

; Warning:  The function apply-top-hints-clause-msg1 knows
; that if the (car (cddddr &)) of the result is nil then nothing but
; case analysis was done!

  (mv-let (message-lst char-alist)
          (tilde-*-simp-phrase1
           (extract-and-classify-lemmas ttree '(implies not iff) nil)

; Note: The third argument to extract-and-classify-lemmas is the list
; of forced runes, which we assume to be nil in preprocessing.  If
; this changes, see the comment in fertilize-clause-msg1.

           t)
          (list* "case analysis"
                 "~@*"
                 "~@* and "
                 "~@*, "
                 message-lst
                 char-alist)))

(defun tilde-*-raw-preprocess-phrase (ttree punct)

; See tilde-*-preprocess-phrase.  Here we print for a non-nil value of state
; global 'raw-proof-format.

  (let ((runes (all-runes-in-ttree ttree nil)))
    (mv-let (message-lst char-alist)
            (tilde-*-raw-simp-phrase1
             runes
             nil ; forced-runes
             punct
             '(implies not iff) ; ignore-lst
             "" ; phrase
             nil)
            (list* (concatenate 'string "case analysis"
                                (case punct
                                  (#\, ",")
                                  (#\. ".")
                                  (otherwise "")))
                   "~@*"
                   "~@* and "
                   "~@*, "
                   message-lst
                   char-alist))))

(defun preprocess-clause-msg1 (signal clauses ttree pspv state)

; This function is one of the waterfall-msg subroutines.  It has the
; standard arguments of all such functions: the signal, clauses, ttree
; and pspv produced by the given processor, in this case
; preprocess-clause.  It produces the report for this step.

  (declare (ignore signal pspv))
  (let ((raw-proof-format (f-get-global 'raw-proof-format state)))
    (cond ((tag-tree-occur 'hidden-clause t ttree)

; If this preprocess clause is to be hidden, e.g., because it transforms
; (IMPLIES P Q) to {(NOT P) Q}, we print no message.  Note that this is
; just part of the hiding.  Later in the waterfall, when some other processor
; has successfully hit our output, that output will be printed and we
; need to stop that printing too.

           state)
          ((and raw-proof-format
                (null clauses))
           (fms "But preprocess reduces the conjecture to T, by ~*0~|"
                (list (cons #\0 (tilde-*-raw-preprocess-phrase ttree #\.)))
                (proofs-co state)
                state
                (term-evisc-tuple nil state)))
          ((null clauses)
           (fms "But we reduce the conjecture to T, by ~*0.~|"
                (list (cons #\0 (tilde-*-preprocess-phrase ttree)))
                (proofs-co state)
                state
                (term-evisc-tuple nil state)))
          (raw-proof-format
           (fms "Preprocess reduces the conjecture to ~#1~[~x2~/the ~
                 following~/the following ~n3 conjectures~], by ~*0~|"
                (list (cons #\0 (tilde-*-raw-preprocess-phrase ttree #\.))
                      (cons #\1 (zero-one-or-more clauses))
                      (cons #\2 t)
                      (cons #\3 (length clauses)))
                (proofs-co state)
                state
                (term-evisc-tuple nil state)))
          (t
           (fms "By ~*0 we reduce the conjecture to~#1~[~x2.~/~/ the ~
                 following ~n3 conjectures.~]~|"
                (list (cons #\0 (tilde-*-preprocess-phrase ttree))
                      (cons #\1 (zero-one-or-more clauses))
                      (cons #\2 t)
                      (cons #\3 (length clauses)))
                (proofs-co state)
                state
                (term-evisc-tuple nil state))))))


; Section: Induction

(defun select-x-cl-set (cl-set induct-hint-val)

; This function produces the clause set we explore to collect
; induction candidates.  The x in this name means "explore."  If
; induct-hint-val is non-nil and non-t, we use the user-supplied
; induction hint value (which, if t means use cl-set); otherwise, we
; use cl-set.

  (cond ((null induct-hint-val) cl-set)
        ((equal induct-hint-val *t*) cl-set)
        (t (list (list induct-hint-val)))))

(defun unchangeables (formals args quick-block-info subset ans)

; We compute the set of all variable names occurring in args in
; unchanging measured formal positions.  We accumulate the answer onto
; ans.

  (cond ((null formals) ans)
        ((and (member-eq (car formals) subset)
              (eq (car quick-block-info) 'unchanging))
         (unchangeables (cdr formals) (cdr args) (cdr quick-block-info) subset
                        (all-vars1 (car args) ans)))
        (t
         (unchangeables (cdr formals) (cdr args) (cdr quick-block-info) subset
                        ans))))

(defun changeables (formals args quick-block-info subset ans)

; We compute the args in changing measured formal positions.  We
; accumulate the answer onto ans.

  (cond ((null formals) ans)
        ((and (member-eq (car formals) subset)
              (not (eq (car quick-block-info) 'unchanging)))
         (changeables (cdr formals) (cdr args) (cdr quick-block-info)
                      subset
                      (cons (car args) ans)))
        (t
         (changeables (cdr formals) (cdr args) (cdr quick-block-info)
                      subset
                      ans))))

(defun sound-induction-principle-mask1 (formals args quick-block-info
                                                subset
                                                unchangeables
                                                changeables)
; See sound-induction-principle-mask.

  (cond
   ((null formals) nil)
   (t (let ((var (car formals))
            (arg (car args))
            (q (car quick-block-info)))
        (mv-let (mask-ele new-unchangeables new-changeables)
          (cond ((member-eq var subset)
                 (cond ((eq q 'unchanging)
                        (mv 'unchangeable unchangeables changeables))
                       (t (mv 'changeable unchangeables changeables))))
                ((and (variablep arg)
                      (eq q 'unchanging))
                 (cond ((member-eq arg changeables)
                        (mv nil unchangeables changeables))
                       (t (mv 'unchangeable
                              (add-to-set-eq arg unchangeables)
                              changeables))))
                ((and (variablep arg)
                      (not (member-eq arg changeables))
                      (not (member-eq arg unchangeables)))
                 (mv 'changeable
                     unchangeables
                     (cons arg changeables)))
                (t (mv nil unchangeables changeables)))
          (cons mask-ele
                (sound-induction-principle-mask1 (cdr formals)
                                                 (cdr args)
                                                 (cdr quick-block-info)
                                                 subset
                                                 new-unchangeables
                                                 new-changeables)))))))

(defun sound-induction-principle-mask (term formals quick-block-info subset)

; Term is a call of some fn on some args.  The formals and
; quick-block-info are those of fn, and subset is one of fn's measured
; subset (a subset of formals).  We wish to determine, in the
; terminology of ACL, whether the induction applies to term.  If so we
; return a mask indicating how to build the substitutions for the
; induction from args and the machine for fn.  Otherwise we return
; nil.

; Let the changeables be those args that are in measured formal
; positions that sometimes change in the recursion.  Let the
; unchangeables be all of the variables occurring in measured actuals
; that never change in recursion.  The induction applies if
; changeables is a sequence of distinct variable names and has an
; empty intersection with unchangeables.

; If the induction is applicable then the substitutions should
; substitute for the changeables just as the recursion would, and hold
; each unchangeable fixed -- i.e., substitute each for itself.  With
; such substitutions it is possible to prove the measure lemmas
; analogous to those proved when justification of subset was stored,
; except that the measure is obtained by instantiating the measure
; term used in the justification by the measured actuals in unchanging
; slots.  Actual variables that are neither among the changeables or
; unchangeables may be substituted for arbitrarily.

; If the induction is applicable we return a mask with as many
; elements as there are args.  For each arg the mask contains either
; 'changeable, 'unchangeable, or nil.  'Changeable means the arg
; should be instantiated as specified in the recursion.  'Unchangeable
; means each var in the actual should be held fixed.  Nil means that
; the corresponding substitution pairs in the machine for the function
; should be ignored.

; Abstractly, this function builds the mask by first putting either
; 'changeable or 'unchangeable in each measured slot.  It then fills
; in the remaining slots from the left so as to permit the actual to
; be instantiated or held fixed as desired by the recursion, provided
; that in so doing it does not permit substitutions for previously
; allocated actuals.

  (let ((unchangeables
         (unchangeables formals (fargs term) quick-block-info subset nil))
        (changeables
         (changeables formals (fargs term) quick-block-info subset nil)))
    (cond ((or (not (no-duplicatesp-equal changeables))
               (not (all-variablep changeables))
               (intersectp-eq changeables unchangeables))
           nil)
          (t (sound-induction-principle-mask1 formals
                                              (fargs term)
                                              quick-block-info
                                              subset
                                              unchangeables
                                              changeables)))))


(defrec candidate
  (score controllers changed-vars unchangeable-vars
         tests-and-alists-lst justification induction-term other-terms
         xinduction-term xother-terms xancestry
         ttree)
  nil)

; This record is used to represent one of the plausible inductions that must be
; considered.  The SCORE represents some fairly artificial estimation of how
; many terms in the conjecture want this induction.  CONTROLLERS is the list of
; the controllers -- including unchanging controllers -- for all the inductions
; merged to form this one.  The CHANGED-VARS is a list of all those variables
; that will be instantiated (non-identically) in some induction hypotheses.
; Thus, CHANGED-VARS include both variables that actually contribute to why
; some measure goes down and variables like accumulators that are just along
; for the ride.  UNCHANGEABLE-VARS is a list of all those vars which may not be
; changed by any substitution if this induction is to be sound for the reasons
; specified.  TESTS-AND-ALISTS-LST is a list of TESTS-AND-ALISTS which
; indicates the case analysis for the induction and how the various induction
; hypotheses are obtained via substitutions.  JUSTIFICATION is the
; JUSTIFICATION that justifies this induction, and INDUCTION-TERM is the term
; that suggested this induction and from which you obtain the actuals to
; substitute into the template.  OTHER-TERMS are the induction-terms of
; candidates that have been merged into this one for heuristic reasons.

; Because of induction rules we can think of some terms being aliases for
; others.  We have to make a distinction between the terms in the conjecture
; that suggested an induction and the actual terms that suggested the
; induction.  For example, if an induction rule maps (fn x y) to (recur x y),
; then (recur x y) will be the INDUCTION-TERM because it suggested the
; induction and we will, perhaps, have to recover its induction machine or
; quick block information to implement various heuristics.  But we do not wish
; to report (recur x y) to the user, preferring instead to report (fn x y).
; Therefore, corresponding to INDUCTION-TERM and OTHER-TERMS we have
; XINDUCTION-TERM and XOTHER-TERMS, which are maintained in exactly the same
; way as their counterparts but which deal completely with the user-level view
; of the induction.  In practice this means that we will initialize the
; XINDUCTION-TERM field of a candidate with the term from the conjecture,
; initialize the INDUCTION-TERM with its alias, and then merge the fields
; completely independently but analogously.  XANCESTRY is a field maintained by
; merging to contain the user-level terms that caused us to change our
; tests-and-alists.  (Some candidates may be flushed or merged into this one
; without changing it.)

; The ttree of a candidate contains 'LEMMA tags listing the :induction rules
; (if any) involved in the suggestion of the candidate.

(defun count-non-nils (lst)
  (cond ((null lst) 0)
        ((car lst) (1+ (count-non-nils (cdr lst))))
        (t (count-non-nils (cdr lst)))))

(defun controllers (formals args subset ans)
  (cond ((null formals) ans)
        ((member (car formals) subset)
         (controllers (cdr formals) (cdr args) subset
                      (all-vars1 (car args) ans)))
        (t (controllers (cdr formals) (cdr args) subset ans))))

(defun changed/unchanged-vars (x args mask ans)
  (cond ((null mask) ans)
        ((eq (car mask) x)
         (changed/unchanged-vars x (cdr args) (cdr mask)
                                 (all-vars1 (car args) ans)))
        (t (changed/unchanged-vars x (cdr args) (cdr mask) ans))))

(defrec tests-and-alists (tests alists) nil)

(defun tests-and-alists/alist (alist args mask call-args)

; Alist is an alist that maps the formals of some fn to its actuals,
; args.  Mask is a sound-induction-principle-mask indicating the args
; for which we will build substitution pairs.  Call-args is the list of
; arguments to some recursive call of fn occurring in the induction
; machine for fn.  We build an alist mapping the masked args to the
; instantiations (under alist) of the values in call-args.

  (cond
   ((null mask) nil)
   ((null (car mask))
    (tests-and-alists/alist alist (cdr args) (cdr mask) (cdr call-args)))
   ((eq (car mask) 'changeable)
    (cons (cons (car args)
                (sublis-var alist (car call-args)))
          (tests-and-alists/alist alist
                                  (cdr args)
                                  (cdr mask)
                                  (cdr call-args))))
   (t (let ((vars (all-vars (car args))))
        (append (pairlis$ vars vars)
                (tests-and-alists/alist alist
                                        (cdr args)
                                        (cdr mask)
                                        (cdr call-args)))))))

(defun tests-and-alists/alists (alist args mask calls)

; Alist is an alist that maps the formals of some fn to its actuals,
; args.  Mask is a sound-induction-principle-mask indicating the args
; for which we will build substitution pairs.  Calls is the list of
; calls for a given case of the induction machine.  We build the alists
; from those calls.

  (cond
   ((null calls) nil)
   (t (cons (tests-and-alists/alist alist args mask (fargs (car calls)))
            (tests-and-alists/alists alist args mask (cdr calls))))))

; The following record contains the tests leading to a collection of
; recursive calls at the end of a branch through a defun.  In general,
; the calls may not be to the function being defuned but rather to
; some other function in the same mutually recursive clique, but in
; the context of induction we know that all the calls are to the same
; fn because we haven't implemented mutually recursive inductions yet.

; A list of these records constitute the induction machine for a function.

(defrec tests-and-calls (tests . calls) nil)

; The justification record contains a subset of the formals of the function
; under which it is stored.  Only the subset, ruler-extenders, and subversive-p
; fields have semantic content!  The other fields are the domain predicate, mp;
; the relation, rel, which is well-founded on mp objects; and the mp-measure
; term which has been proved to decrease in the recursion.  The latter three
; fields are correct at the time the function is admitted, but note that they
; might all be local and hence have disappeared by the time these fields are
; read.  Thus, we include them only for heuristic purposes, for example as used
; in community book books/workshops/2004/legato/support/generic-theories.lisp.

; A list of justification records is stored under each function symbol by the
; defun principle.

(defrec justification
  (subset . ((subversive-p . (mp . rel))
             (measure . ruler-extenders)))
  nil)

(defun tests-and-alists (alist args mask tc)

; Alist is an alist that maps the formals of some fn to its actuals,
; args.  Mask is a sound-induction-principle-mask indicating the args
; for which we will build substitution pairs.  Tc is one of the
; tests-and-calls in the induction machine for the function.  We make
; a tests-and-alists record containing the instantiated tests of tc
; and alists derived from the calls of tc.

  (make tests-and-alists
        :tests (sublis-var-lst alist (access tests-and-calls tc :tests))
        :alists (tests-and-alists/alists alist
                                        args
                                        mask
                                        (access tests-and-calls tc :calls))))

(defun tests-and-alists-lst (alist args mask machine)

; We build a list of tests-and-alists from machine, instantiating it
; with alist, which is a map from the formals of the function to the
; actuals, args.  Mask is the sound-induction-principle-mask that
; indicates the args for which we substitute.

  (cond
   ((null machine) nil)
   (t (cons (tests-and-alists alist args mask (car machine))
            (tests-and-alists-lst alist args mask (cdr machine))))))

(defun flesh-out-induction-principle (term formals justification mask machine
                                           xterm ttree)

; Term is a call of some function the indicated formals and induction machine.
; Justification is its 'justification and mask is a sound-induction-
; principle-mask for the term.  We build the induction candidate suggested by
; term.

  (make candidate
        :score
        (/ (count-non-nils mask) (length mask))

        :controllers
        (controllers formals (fargs term)
                     (access justification justification :subset)
                     nil)

        :changed-vars
        (changed/unchanged-vars 'changeable (fargs term) mask nil)

        :unchangeable-vars
        (changed/unchanged-vars 'unchangeable (fargs term) mask nil)

        :tests-and-alists-lst
        (tests-and-alists-lst (pairlis$ formals (fargs term))
                              (fargs term) mask machine)

        :justification justification

        :induction-term term
        :xinduction-term xterm

        :other-terms nil
        :xother-terms nil
        :xancestry nil
        :ttree ttree))

; Essay on DO$ Induction and the Selection of Q

; Now we define the functions that analyze a ``semi-concrete do$'' to determine
; whether and what induction it suggests and then applies that induction to
; a clause set.

; A semi-concrete do$ is a do whose measure and body lambdas are nice constants
; (nice in the sense that we can parse them as though they came from a do
; loop$) and whose alist is semi-concrete, e.g., (list (cons 'key1 val1)
; ... (cons 'keyn valn)).  Typically we'd expect the vali, or at least some of
; them, to be variables.

; The basic idea is that we ``decompile'' the do body lambda into a pseudo
; function definition, e.g.,

; (defun hint-fn (val1 ... valn)
;   (declare (xargs :measure <measure>))
;   (if <base>
;       <ans>
;       (hint-fn val1' ... valn')))

; and we construct the corresponding ``call,'' (hint-fn init-val1
; ... init-valn).  By the way, throughout this discussion we act like we only
; handle inductions with one base case and one induction hyp, but of course
; we're fully general.

; We don't actually admit this hint-fn.  Then we analyze it as though we had
; admitted it to get an induction machine.  We then construct a candidate (or
; not, according to whether the controllers are distinct variables, etc) from
; the call using this machine.  We toss the candidate into the list of
; suggestions as though it were the intrinsic candidate suggested by the do$
; term.

; Note however that the termination of hint-fn has not been proved.  We will
; add some ``measure conjectures'' to the fleshed out induction scheme if we
; end up choosing a do$ induction.  The reason we wait to add the measure
; conjectures as we apply the suggested scheme to the clause-set is discussed
; next.

; The termination proof done for a do loop$ usually depends on guards and
; guards have been eliminated by the prover as the do$ is rewritten.

; Consider

; (defun foo (i)
;   (declare (xargs :guard (natp i)))
;   (loop$ with i = i
;          do
;          :guard (natp i)
;          (if (equal i 0) (return t) (setq i (- i 1)))))

; This function can be guard verified (proving termination) and can be proved
; to return t when (natp i).

; The result of decompiling the loop$ is

; (defun hint-fn (i)
;   (if (equal i 0)
;       t
;       (hint-fn (- i 1))))

; This is, of course, inadmissible because it can't be proved to terminate.
; But do$ induction uses this to suggest the following scheme:

; [Base] (implies (equal i 0) (p i))
; [Step] (implies (and (not (equal i 0)) (p (- i 1))) (p i))
; [Term] (implies (not (equal i 0)) (l< (lex-fix (- i 1)) (lex-fix i)))

; Applying this scheme to (implies (natp i) (equal (loop$ with i ...) t)) gives
; the obvious Base and Step (and since (natp i) is a hypothesis of (p i) it's
; available in the Base and Step), but we modify [Term] by searching the clause
; (set) being proved, in this case

; ({(not (natp i)) (equal (loop$ with i ...) t)})

; and choosing a ``q'' that is the conjunction of the negations of some
; literals in (all of) the clause(s).  In this case we choose q to be (natp i).

; When then augment [Term] by adding q as a hypothesis:

; [Term'] (implies (and (natp i) (not (equal i 0)))
;                  (l< (lex-fix (- i 1)) (lex-fix i)))

; The soundness of this scheme is demonstrated in books/projects/apply/
; justification-of-do-induction.lisp.  That book shows (in a simple but generic
; setting) that if we can establish

; (defthm [a] (implies (and (q x) (not (basep x)))
;                      (l< (lex-fix (m (stp x)))
;                          (lex-fix (m x)))))
; (defthm [b] (implies (basep x) (p x)))
; (defthm [c] (implies (and (not (basep x)) (p (stp x))) (p x)))
; (defthm [d] (implies (not (q x)) (p x))))

; Then we can prove (p x).  In our case, [a] is [Term'], [b] and [c] are [Base]
; and [Step], and [d] is a new proof obligation requiring us to prove that our
; goal conjecture holds when q is false.  But because of how we choose q -- as
; a conjunction of hypotheses of p -- obligation [d] is always a tautology.

; From a heuristic standpoint, it is important to choose q wisely!  Why not
; just choose q to be the conjunction of the negations of ALL the literals of
; p?  That works for [d], because for that q, (not q) is equivalent to p so [d]
; becomes (implies p p).  (The negation of a conjunction of negations of lits
; in cl is the disjunction of the lits in cl, which is the clause itself.)

; But what about [a]?  If q is equivalent to (not p), then [a] becomes

; (implies (and (not (p x)) (not (basep x)))
;          (l< (lex-fix (m (stp x))) (lex-fix (m x))))

; which is just

; (or (p x)                                                  [i]
;     (implies (not (basep x))                               [ii]
;              (l< (lex-fix (m (stp x))) (lex-fix (m x))))

; And if we know we can't prove the ``bare-bones'' measure conjecture, [ii],
; then we're left with proving (p x).  So we really haven't gotten anywhere.

; Thus, it behooves us, heuristically, to choose q by picking hypotheses of p
; that are helpful in proving the measure conjecture without polluting it with
; too much.

; We've implemented two heuristics in the function select-do$-induction-q.

; (1) choose only literals whose free vars are a subset of the variables of the
;     measure, and

; (2) do not choose a literal that mentions any term that suggested an
;     induction.

; The reason we include (2) is that often the do$ term that suggests the
; induction satisfies (1) and makes [a] impractical (i.e., equivalent to
; proving p).

; Note that q is not chosen unless the winning candidate comes from a do$ (via
; decompilation) and then it is chosen during the application of the do$ scheme
; to the clause set.  So you have to understand the do$ candidates are only
; partially correct schemes, awaiting the choice of q to fully realize.  That
; selection of q occurs in the function induction-formula, where we have cl-set
; and the candidate.

; But there are two additional twists.  First, induction-formula is also used
; in the output msg for induction.  It is used to produce the induction scheme,
; phrased in terms of :P.  To do that we call induction-formula with the
; clause-set (((:P ...))) -- a singleton set containing a unit clause with the
; literal (:P ...).  But of course there's no way to find a q in that!  So we
; provide induction-formula with a list of all the terms suggesting the winning
; induction and we pick q with the original clause-set (not the generic :P
; one).  We allow the ``list of all the terms suggesting'' this induction to be
; :all, meaning all literals are excluded, and that has the effect that q is
; empty (i.e., T).  That option is used when an :induct :hint is provided.  We
; want the hint function to completely control the scheme used and not go
; messing it up with automatic choices of q.

; The second twist is that induct may be given the original (unclausified) term
; in a pathological clause set, ({term}), for example because there was an
; :induct t hint on "Goal" or because the simplifier abandoned its work on the
; clauses and pushed the original goal for induction.  In this case, in order
; to find q, we have to use clausify-input to convert this pathological
; clause-set into a non-trivial one even though we form the instance of the do$
; induction scheme with the unit clause set.

(mutual-recursion

(defun eliminate-cdr-assoc-eq-safe (term)
  (cond ((variablep term) term)
        ((fquotep term) term)
        ((and (eq (ffn-symb term) 'cdr)
              (consp (fargn term 1))
              (eq (ffn-symb (fargn term 1)) 'assoc-eq-safe)
              (quotep (fargn (fargn term 1) 1))
              (equal (fargn (fargn term 1) 2) 'alist))
         (unquote (fargn (fargn term 1) 1)))
        (t (cons (ffn-symb term)
                 (eliminate-cdr-assoc-eq-safe-lst (fargs term))))))

(defun eliminate-cdr-assoc-eq-safe-lst (terms)
  (cond ((endp terms) nil)
        (t (cons (eliminate-cdr-assoc-eq-safe (car terms))
                 (eliminate-cdr-assoc-eq-safe-lst (cdr terms))))))
)

(defun formal-alist-to-alist-on-vars (term)

; If term is a ``formal symbol alist'', the translation of a term like (list
; (cons 'key1 val1) ... (cons 'keyn valn)), where each vali is a term, we
; return (mv t ((key1 . val1') ... (keyn . valn'))), where vali' is vali except
; that each occurrence of (CDR (ASSOC-EQ-SAFE 'x ALIST)) is replaced by x.
; Else we return (mv nil nil).  We actually expect each vali to be a term in
; the single variable ALIST and we expect all the 'x to be quoted variable
; names.  So we convert a term in the single variable ALIST to a term in the
; various x's.  But we do not actually check these expectations!

  (cond
   ((variablep term) (mv nil nil))
   ((equal term *nil*) (mv t nil))
   (t (mv-let (flg pair rest)
        (formal-cons-to-components term)
        (cond
         ((null flg) (mv nil nil))
         (t (mv-let (flg key val)
              (formal-cons-to-components pair)
              (cond
               ((null flg) (mv nil nil))
               ((not (quotep key)) (mv nil nil))
               (t (mv-let (flg alist)
                    (formal-alist-to-alist-on-vars rest)
                    (cond
                     ((null flg) (mv nil nil))
                     (t (mv t (cons (cons (unquote key)
                                          (eliminate-cdr-assoc-eq-safe val))
                                    alist))))))))))))))

; Instead of using the genuine function name hint-fn for the decompiled
; function definition, we use the keyword below.  When we see that the
; induction was suggested by a call of this keyword, we know do$ induction is
; being performed (and thus that measure clauses (augmented by a q) must be
; added).

(defconst *do$-induction-fn* :do$-induction-fn)

(defun decompile-formal-do$-triple (formals term)

; Term is a formal term that is supposed to represent a do$ triple of the form
; (list exit-flg value alist).  We deconstruct it and either return (mv nil
; nil) meaning it is not of the supposed form, or (mv t term') where term' is
; the corresponding induction function body.  We check that every alist we
; recover maps the formals.

  (mv-let (flg formal-exit-flg term1)
    (formal-cons-to-components term)
    (cond
     ((null flg) (mv nil nil))
     (t (mv-let (flg formal-val term2)
          (formal-cons-to-components term1)
          (declare (ignore formal-val))
          (cond
           ((null flg) (mv nil nil))
           (t (mv-let (flg formal-alist term3)
                (formal-cons-to-components term2)
                (cond
                 ((null flg) (mv nil nil))
                 ((not (equal term3 *nil*)) (mv nil nil))
                 (t (mv-let (flg alist)
                      (formal-alist-to-alist-on-vars formal-alist)
                      (cond
                       ((null flg) (mv nil nil))
                       ((not (equal (strip-cars alist) formals))
                        (mv nil nil))
                       (t (cond
                           ((eq (unquote formal-exit-flg) nil)
                            (mv t (sublis-var alist (cons *do$-induction-fn* formals))))
                           (t (mv t (cons 'list formals)))))))))))))))))

(defun decompile-do$-body (formals term)
  (cond
   ((variablep term) (mv nil nil))
   ((fquotep term)
    (decompile-formal-do$-triple formals term))
   ((eq (ffn-symb term) 'if)
    (mv-let (flg tb)
      (decompile-do$-body formals (fargn term 2))
      (cond
       ((null flg) (mv nil nil))
       (t (mv-let (flg fb)
            (decompile-do$-body formals (fargn term 3))
            (cond
             ((null flg) (mv nil nil))
             (t (mv t (list 'if
                            (eliminate-cdr-assoc-eq-safe (fargn term 1))
                            tb fb)))))))))
   (t (decompile-formal-do$-triple formals term))))

(defun quoted-lambda-to-body (x)
  (case-match x
    (('quote ('lambda ('alist) body))
     (mv t body))
    (& (mv nil nil))))

(defun decompile-do$ (term wrld)
  (let ((cleaned-term
         (possibly-clean-up-dirty-lambda-objects
          :all
          (remove-guard-holders-weak term
                                     (remove-guard-holders-lamp))
          wrld
          (remove-guard-holders-lamp))))
    (mv-let (flg formal-mterm)
      (quoted-lambda-to-body (fargn cleaned-term 1))
      (cond
       ((null flg) nil)
       (t (mv-let (flg alist)
            (formal-alist-to-alist-on-vars (fargn cleaned-term 2))
            (let* ((formals (strip-cars alist))
                   (call (cons *do$-induction-fn* (strip-cdrs alist))))
              (cond
               ((null flg) nil)
               (t (mv-let (flg formal-body)
                    (quoted-lambda-to-body (fargn cleaned-term 3))
                    (cond
                     ((null flg) nil)
                     (t (mv-let (flg body)
                          (decompile-do$-body formals formal-body)
                          (cond
                           ((null flg) nil)
                           (t (let ((mterm (eliminate-cdr-assoc-eq-safe formal-mterm)))
                                (list formals
                                      call
                                      mterm
                                      body)))))))))))))))))

(defun intrinsic-suggested-induction-cand1
  (induction-rune term formals quick-block-info justification machine xterm
                  ttree)

; Note: An "intrinsically suggested" induction scheme is an induction scheme
; suggested by a justification of a recursive function.  The rune controlling
; the intrinsic suggestion from the justification of fn is (:induction fn).  We
; distinguish between intrinsically suggested inductions and those suggested
; via records of induction-rule type.

; Term, above, is a call of some fn with the given formals, quick-block-info,
; justification and induction machine.  We return a list of induction
; candidates, said list either being empty or the singleton list containing the
; induction candidate intrinsically suggested by term.  Xterm is logically
; unrelated to term and is the term appearing in the original conjecture from
; which we (somehow) obtained term for consideration.

  (let ((mask (sound-induction-principle-mask term formals
                                              quick-block-info
                                              (access justification
                                                      justification
                                                      :subset))))
    (cond
     (mask
      (list (flesh-out-induction-principle term formals
                                           justification
                                           mask
                                           machine
                                           xterm
                                           (push-lemma induction-rune
                                                       ttree))))
     (t nil))))

; We next extend the notion of intrinsic induction scheme to a scheme suggested
; by a semi-concrete do$ term.  But first we have to introduce the notion of
; ruler-extenders because its needed when we try to create the machines

(defconst *no-ruler-extenders*
  :none)

(defconst *basic-ruler-extenders*

; We ensure that these are sorted, although this may no longer be important.

  (let ((lst '(if mv-list return-last)))
    (sort-symbol-listp lst)))

(defconst *basic-ruler-extenders-plus-lambdas*

; We ensure that these are sorted, although this may no longer be important.

  (let ((lst (cons :lambdas *basic-ruler-extenders*)))
    (sort-symbol-listp lst)))

(defun get-ruler-extenders1 (r edcls default ctx wrld state)

; This function is analogous to get-measures1, but for obtaining the
; :ruler-extenders xarg.

  (cond ((null edcls) (value (if (eq r *no-ruler-extenders*)
                                 default
                               r)))
        ((eq (caar edcls) 'xargs)
         (let ((temp (assoc-keyword :RULER-EXTENDERS (cdar edcls))))
           (cond ((null temp)
                  (get-ruler-extenders1 r (cdr edcls) default ctx wrld state))
                 (t
                  (let ((r0 (cadr temp)))
                    (cond
                     ((eq r *no-ruler-extenders*)
                      (er-let*
                       ((r1

; If keywords other than :ALL, :BASIC, and :LAMBDAS are supported, then also
; change set-ruler-extenders.

                         (cond ((eq r0 :BASIC)
                                (value *basic-ruler-extenders*))
                               ((eq r0 :LAMBDAS)
                                (value *basic-ruler-extenders-plus-lambdas*))
                               ((eq r0 :ALL)
                                (value :ALL))
                               (t (er-progn
                                   (chk-ruler-extenders r0 soft ctx wrld)
                                   (value r0))))))
                       (get-ruler-extenders1 r1 (cdr edcls) default ctx
                                             wrld state)))
                     ((equal r r0)
                      (get-ruler-extenders1 r (cdr edcls) default ctx wrld
                                            state))
                     (t (er soft ctx
                            "It is illegal to declare two different ~
                             ruler-extenders for the admission of a single ~
                             function.  But you have specified ~
                             :RULER-EXTENDERS ~x0 and :RULER-EXTENDERS ~x1."
                            r r0))))))))
        (t (get-ruler-extenders1 r (cdr edcls) default ctx wrld state))))

(defun get-ruler-extenders2 (lst default ctx wrld state)
  (cond ((null lst) (value nil))
        (t (er-let* ((r (get-ruler-extenders1
                         *no-ruler-extenders* (fourth (car lst)) default ctx
                         wrld state))
                     (rst (get-ruler-extenders2 (cdr lst) default ctx wrld
                                                state)))
                    (value (cons r rst))))))

(defmacro default-ruler-extenders-from-table (alist)
  `(let ((pair (assoc-eq :ruler-extenders ,alist)))
     (cond ((null pair)
            *basic-ruler-extenders*)
           (t (cdr pair)))))

(defun default-ruler-extenders (wrld)
  (default-ruler-extenders-from-table (table-alist 'acl2-defaults-table wrld)))

(defun get-ruler-extenders-lst (symbol-class lst ctx wrld state)

; This function returns a list in 1:1 correspondence with lst containing the
; user's specified :RULER-EXTENDERS (or *no-ruler-extenders* if no
; ruler-extenders is specified).  We cause an error if more than one
; :RULER-EXTENDERS is specified within the edcls of a given element of lst.

; If symbol-class is program, we ignore the contents of lst and simply return
; all *no-ruler-extenders*.  See the comment in chk-acceptable-defuns where
; get-ruler-extenders is called.

  (cond
   ((eq symbol-class :program)
    (value (make-list (length lst) :initial-element *no-ruler-extenders*)))
   (t (get-ruler-extenders2 lst (default-ruler-extenders wrld) ctx wrld
                            state))))

(defun member-eq-all (a lst)
  (or (eq lst :all)
      (member-eq a lst)))

(defrec tests-and-call (tests call) nil)

; In Nqthm the record above was called TEST-AND-CASE and the second component
; was the arglist of a recursive call of the function being analyzed.  Because
; of the presence of mutual recursion, we have renamed it tests-and-call and
; the second component is a "recursive" call (possibly mutually recursive).

(defun termination-machine1 (tests calls ans)

; This function makes a tests-and-call with tests tests for every call
; in calls.  It accumulates them onto ans so that if called initially
; with ans=nil the result is a list of tests-and-call in the reverse
; order of the calls.

  (cond ((null calls) ans)
        (t (termination-machine1 tests
                                 (cdr calls)
                                 (cons (make tests-and-call
                                             :tests tests
                                             :call (car calls))
                                       ans)))))

(mutual-recursion

(defun all-calls (names term alist ans)

; Names is a list of defined function symbols.  We accumulate into ans all
; terms u/alist such that for some f in names, u is a subterm of term that is a
; call of f.  The algorithm just explores term looking for calls, and
; instantiate them as they are found.

; Our answer is in reverse print order (displaying lambda-applications
; as LETs).  For example, if a, b and c are all calls of fns in names,
; then if term is (foo a ((lambda (x) c) b)), which would be printed
; as (foo a (let ((x b)) c)), the answer is (c b a).

  (cond ((variablep term) ans)
        ((fquotep term) ans)
        ((flambda-applicationp term)
         (all-calls names
                    (lambda-body (ffn-symb term))
                    (pairlis$ (lambda-formals (ffn-symb term))
                              (sublis-var-lst alist (fargs term)))
                    (all-calls-lst names (fargs term) alist ans)))
        ((and (eq (ffn-symb term) 'return-last)
              (quotep (fargn term 1))
              (eq (unquote (fargn term 1)) 'mbe1-raw))
         (all-calls names (fargn term 3) alist ans))
        (t (all-calls-lst names
                          (fargs term)
                          alist
                          (cond ((member-eq (ffn-symb term) names)
                                 (add-to-set-equal
                                  (sublis-var alist term)
                                  ans))
                                (t ans))))))

(defun all-calls-lst (names lst alist ans)
  (cond ((null lst) ans)
        (t (all-calls-lst names
                          (cdr lst)
                          alist
                          (all-calls names (car lst) alist ans)))))

)

(mutual-recursion

(defun all-loop$-scion-quote-lambdas (term alist)

; We collect every subterm of term/alist that is a call of a loop$ scion on a
; quoted lambda and that is not within another such call.

  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   ((flambda-applicationp term)
    (union-equal
     (all-loop$-scion-quote-lambdas-lst (fargs term) alist)
     (all-loop$-scion-quote-lambdas
      (lambda-body (ffn-symb term))
      (pairlis$ (lambda-formals (ffn-symb term))
                (sublis-var-lst alist
                                 (fargs term))))))
   ((and (loop$-scion-style (ffn-symb term))
         (quotep (fargn term 1))
         (consp (unquote (fargn term 1)))
         (eq (car (unquote (fargn term 1))) 'lambda))

; We pay the price of instantiating the loop$ scion term now with the alist
; even though it might not have any recursions in it.  C'est la vie.

    (list (sublis-var alist term)))
   (t (all-loop$-scion-quote-lambdas-lst (fargs term) alist))))

(defun all-loop$-scion-quote-lambdas-lst (terms alist)
  (cond ((endp terms) nil)
        (t (union-equal
            (all-loop$-scion-quote-lambdas (car terms) alist)
            (all-loop$-scion-quote-lambdas-lst (cdr terms) alist)))))

)

(defconst *equality-aliases*

; This constant should be a subset of *definition-minimal-theory*, since we do
; not track the corresponding runes in simplify-tests and related code below.

  '(eq eql =))

(defun term-equated-to-constant (term)
  (case-match term
    ((rel x y)
     (cond ((or (eq rel 'equal)
                (member-eq rel *equality-aliases*))
            (cond ((quotep x) (mv y x))
                  ((quotep y) (mv x y))
                  (t (mv nil nil))))
           (t (mv nil nil))))
    (& (mv nil nil))))

; We now develop the code for eliminating needless tests in tests-and-calls
; records, leading to function simplify-tests-and-calls-lst.  See the comment
; there.  Term-equated-to-constant appears earlier, because it is used in
; related function simplify-clause-for-term-equal-const-1.

(defun term-equated-to-constant-in-termlist (lst)
  (cond ((endp lst)
         (mv nil nil))
        (t (mv-let
            (var const)
            (term-equated-to-constant (car lst))
            (cond (var (mv var const))
                  (t (term-equated-to-constant-in-termlist (cdr lst))))))))

(defun simplify-tests (var const tests)

; For a related function, see simplify-clause-for-term-equal-const-1.

  (cond ((endp tests)
         (mv nil nil))
        (t (mv-let (changedp rest)
                   (simplify-tests var const (cdr tests))
                   (mv-let (flg term)
                           (strip-not (car tests))
                           (mv-let (var2 const2)
                                   (term-equated-to-constant term)
                                   (cond ((and flg
                                               (equal var var2)
                                               (not (equal const const2)))
                                          (mv t rest))
                                         (changedp
                                          (mv t (cons (car tests) rest)))
                                         (t
                                          (mv nil tests)))))))))

(defun add-test-smart (test tests)
; For a related function, see add-literal-smart.
  (mv-let (term const)
          (term-equated-to-constant test)
          (cons test
                (cond
                 (term
                  (mv-let (changedp new-tests)
                          (simplify-tests term const tests)
                          (if changedp
                              new-tests
                              tests)))
                 (t tests)))))

(mutual-recursion

(defun termination-machine-rec (loop$-recursion
                                names body alist tests
                                ruler-extenders avoid-vars)

; This function is only called if loop$-recursion-checkedp is t, i.e., we have
; run well-formedness checks on body.  The first argument above, the similarly
; named variable loop$-recursion, if t, means that names is a singleton list
; and that body actually exhibits loop$ recursion somewhere.

; It is admittedly odd that `names' is a plural noun (and when loop$-recursion
; is t, is a singleton list of function names) whereas `body' is singular (and
; is the body of the only function listed in names).  The reason is that when
; loop$-recursion is nil names may be a list of all the functions in a
; mutually-recursive clique with the one defined by body and a call of any of
; the functions in names constitutes recursion.

; This function builds a list of tests-and-call records for all calls in body
; of functions in names, but substituting alist into every term in the result.
; At the top level, body is the body of a function in names and alist is nil.
; Note that we don't need to know the function symbol to which the body
; belongs; all the functions in names are considered "recursive" calls.  Names
; is a list of all the mutually recursive fns in the clique.  Alist maps
; variables in body to actuals and is used in the exploration of lambda
; applications.

; For each recursive call in body a tests-and-call is returned whose tests are
; all the tests that "rule" the call and whose call is the call.  If a rules b
; then a governs b but not vice versa.  For example, in (if (g (if a b c)) d e)
; a governs b but does not rule b.  The reason for taking this weaker notion of
; governance is that we can show that the tests-and-calls are together
; sufficient to imply the tests-and-calls generated by induction-machine.  The
; notion of "rules" is extended by ruler-extenders; see :doc
; acl2-defaults-table and see :doc ruler-extenders.

; If loop$-recursion is non-nil and body is a loop$ scion call on a quoted
; lambda (sum$ '(lambda ...) lst) then we know that the lambda is well-formed
; (by the implicit loop$-recursion-checkedp = t mentioned above) and we look
; for recursive calls inside the body of that lambda.  Furthermore, we generate
; a new variable (i.e., not in avoid-vars), add it to avoid-vars, throw away
; alist and replace it with one that binds the locals of the lambda to the new
; variable, and add a ruling test that the value of this new variable is a
; member of the target, lst.

  (cond
   ((or (variablep body)
        (fquotep body))
    nil)
   ((flambda-applicationp body)
    (let ((lambda-body-result
           (termination-machine-rec loop$-recursion
                                    names
                                    (lambda-body (ffn-symb body))
                                    (pairlis$ (lambda-formals (ffn-symb body))
                                              (sublis-var-lst alist
                                                              (fargs body)))
                                    tests
                                    ruler-extenders
                                    avoid-vars)))
      (cond
       ((member-eq-all :lambdas ruler-extenders)
        (union-equal (termination-machine-rec-for-list loop$-recursion
                                                       names
                                                       (fargs body)
                                                       alist
                                                       tests
                                                       ruler-extenders
                                                       avoid-vars)
                     lambda-body-result))
       (t
        (append
         (termination-machine1
          (reverse tests)
          (all-calls-lst names
                         (fargs body)
                         alist
                         nil)
          (termination-machine-rec-for-list
           loop$-recursion
           names
           (all-loop$-scion-quote-lambdas-lst (fargs body) alist)
           alist
           tests
           ruler-extenders
           avoid-vars))
         lambda-body-result)))))
   ((eq (ffn-symb body) 'if)
    (let* ((inst-test (sublis-var alist

; Since (remove-guard-holders-weak x _) is provably equal to x, the machine we
; generate using it below is equivalent to the machine generated without it.
; It might be sound also to call possibly-clean-up-dirty-lambda-objects (i.e.,
; to call remove-guard-holders instead of remove-guard-holders-weak) so that
; guard holders are removed from quoted lambdas in argument positions with ilk
; :fn (or :fn?), but we don't expect to pay much of a price by playing it safe
; here and in induction-machine-for-fn1.

                                  (remove-guard-holders-weak (fargn body 1)

; Rather than pass (remove-guard-holders-lamp) to the following argument
; through all the recursive calls of termination-machine-rec, or passing it
; from the caller, we use nil.  That's simpler and it probably doesn't much
; matter in practice.  We similarly use nil in other calls of
; remove-guard-holders-weak in this function and in induction-machine-for-fn1.

                                                             nil)))
           (branch-result
            (append (termination-machine-rec loop$-recursion
                                             names
                                             (fargn body 2)
                                             alist
                                             (add-test-smart inst-test tests)
                                             ruler-extenders
                                             avoid-vars)
                    (termination-machine-rec loop$-recursion
                                             names
                                             (fargn body 3)
                                             alist
                                             (add-test-smart
                                              (dumb-negate-lit inst-test)
                                              tests)
                                             ruler-extenders
                                             avoid-vars))))
      (cond
       ((member-eq-all 'if ruler-extenders)
        (append (termination-machine-rec loop$-recursion
                                         names
                                         (fargn body 1)
                                         alist
                                         tests
                                         ruler-extenders
                                         avoid-vars)
                branch-result))
       (t
        (append
         (termination-machine1
          (reverse tests)
          (all-calls names (fargn body 1) alist nil)
          (termination-machine-rec-for-list
           loop$-recursion
           names
           (all-loop$-scion-quote-lambdas (fargn body 1) alist)
           alist
           tests
           ruler-extenders
           avoid-vars))
         branch-result)))))
   ((and (eq (ffn-symb body) 'return-last)
         (quotep (fargn body 1))
         (eq (unquote (fargn body 1)) 'mbe1-raw))

; It is sound to treat return-last as a macro for logic purposes.  We do so for
; (return-last 'mbe1-raw exec logic) both for induction and for termination.
; We could probably do this for any return-last call, but for legacy reasons
; (before introduction of return-last after v4-1) we restrict to 'mbe1-raw.

    (termination-machine-rec loop$-recursion
                             names
                             (fargn body 3) ; (return-last 'mbe1-raw exec logic)
                             alist
                             tests
                             ruler-extenders
                             avoid-vars))
   ((member-eq-all (ffn-symb body) ruler-extenders)
    (let ((rec-call (termination-machine-rec-for-list loop$-recursion
                                                      names (fargs body) alist
                                                      tests ruler-extenders
                                                      avoid-vars)))
      (if (member-eq (ffn-symb body) names)
          (cons (make tests-and-call
                      :tests (reverse tests)
                      :call (sublis-var alist body))
                rec-call)
          rec-call)))
   ((loop$-scion-style (ffn-symb body))
    (let ((style (loop$-scion-style (ffn-symb body)))

; Before we get too carried away with the possibility of loop$ recursion here,
; we need to remember to deal with normal recursion in this term!  This
; collects recursions in the globals and target expressions.

          (normal-ans (termination-machine1 (reverse tests)
                                            (all-calls names body alist nil)
                                            nil)))
      (cond
       ((and loop$-recursion
             (quotep (fargn body 1))
             (consp (unquote (fargn body 1)))
             (eq (car (unquote (fargn body 1))) 'lambda))

; Loop$-recursion may be present in this call of a loop$ scion.  (We can't just
; use ffnnamep to ask because it doesn't look inside of lambda objects that
; might be in the body of this one; furthermore, that information alone
; wouldn't help us since if a recursive call is buried several layers deep in
; loop$ scions we need to generate the newvars and ruling member tests on the
; way down.)  The well-formedness checks done by chk-acceptable-defuns1 ensures
; that every quoted lambda is well-formed, and that every loop$ scion call is
; on a quoted lambda of the right arity (1 or 2 depending on whether its a
; :plain or :fancy loop$ scion).  We need give special attention to those loop$
; scion calls whose quoted lambda contains a recursive call of the fn being
; defined.  And this may be one!

        (cond
         ((eq style :plain)
          (let* ((lamb (unquote (fargn body 1)))
                 (v (car (lambda-object-formals lamb)))

; While we generally follow the convention of calling
; possibly-clean-up-dirty-lambda-objects anytime we're removing guard holders
; we do not do so here because we don't want to think about the effect on
; termination machines, at least not until we see it hurt us.

                 (lamb-body (remove-guard-holders-weak
                             (lambda-object-body lamb)
                             nil))
                 (target (sublis-var alist (fargn body 2)))
                 (newvar (genvar v "NV" 0 avoid-vars))
                 (avoid-vars (cons newvar avoid-vars))
                 (inst-test `(MEMBER-EQUAL
                              ,newvar
                              ,(remove-guard-holders-weak target nil))))
            (append normal-ans
                    (termination-machine-rec loop$-recursion
                                             names
                                             lamb-body
; Note: The only free var in lamb-body is v, so we can ignore the substitutions
; in alist!
                                             (list (cons v newvar))
                                             (add-test-smart inst-test tests)
                                             ruler-extenders
                                             avoid-vars)
                    (termination-machine-rec-for-list
                     loop$-recursion
                     names
                     (all-loop$-scion-quote-lambdas target alist)
                     alist
                     tests
                     ruler-extenders
                     avoid-vars))))
         ((eq style :fancy)
          (let* ((lamb (unquote (fargn body 1)))
                 (gvars (car (lambda-object-formals lamb)))
                 (ivars (cadr (lambda-object-formals lamb)))
                 (lamb-body (remove-guard-holders-weak
                             (lambda-object-body lamb)
                             nil))
                 (globals (sublis-var alist (fargn body 2)))
                 (target (sublis-var alist (fargn body 3)))
                 (newvar (genvar ivars "NV" 0 avoid-vars))
                 (avoid-vars (cons newvar avoid-vars))
                 (inst-test `(MEMBER-EQUAL
                              ,newvar
                              ,(remove-guard-holders-weak target nil))))
            (append normal-ans
                    (termination-machine-rec loop$-recursion
                                             names
                                             lamb-body
                                             (list (cons gvars globals)
                                                   (cons ivars newvar))
                                             (add-test-smart inst-test tests)
                                             ruler-extenders
                                             avoid-vars)
                    (termination-machine-rec-for-list
                     loop$-recursion
                     names
; The following collects the top-level loop$-scion calls on quoted lambdas in
; the globals and the target of a fancy loop$.
                     (all-loop$-scion-quote-lambdas-lst (cdr (fargs body)) alist)
                     alist
                     tests
                     ruler-extenders
                     avoid-vars))))
         (t normal-ans)))
       (t

; This is a loop$ scion call but not one that could have loop$ recursion in it,
; (except possibly in the non-:FN arguments) so we just return the normal
; answer.

        normal-ans))))
   (t (termination-machine1
       (reverse tests)
       (all-calls names body alist nil)
       (termination-machine-rec-for-list
        loop$-recursion
        names
        (all-loop$-scion-quote-lambdas body alist)
        alist
        tests
        ruler-extenders
        avoid-vars)))))

(defun termination-machine-rec-for-list
  (loop$-recursion names bodies alist tests ruler-extenders avoid-vars)
  (cond ((endp bodies) nil)
        (t (append (termination-machine-rec loop$-recursion
                                            names (car bodies) alist tests
                                            ruler-extenders avoid-vars)
                   (termination-machine-rec-for-list loop$-recursion
                                                     names
                                                     (cdr bodies)
                                                     alist tests
                                                     ruler-extenders
                                                     avoid-vars)))))
)

; Essay on Choking on Loop$ Recursion

; Several system functions, e.g., termination-machine, termination-machines,
; termination-theorem-clauses, and putprop-recursivep-lst have changed so that
; they anticipate the possibility of recursive calls inside quoted lambda
; objects.  This is necessary to support recursion in loop$ statements.  But
; these system functions are sometimes called directly in user-authored books.
; We do not want to be responsible for correcting those books.  So our
; functions that deal with loop$ recursion -- at least, those of our functions
; that are sometimes used directly by users -- have been modified to check
; whether loop$ recursion is present and to cause a hard error.  We call this
; ``choking on loop$ recursion.''  However, a difficulty is that some of our
; functions do not take world as an argument and so cannot actually implement
; the check properly!  For example, loop$ recursion requires a singly-recursive
; defun with an xargs declaration of loop$-recursion t, but the old definition
; of termination-machine can't see the declarations.  Furthermore, if
; loop$-recursion t is declared, every lambda in the body must be well-formed
; and that is checked by chk-acceptable-defuns1 before termination-machine ever
; sees the definition.  But termination-machine doesn't take the world and so
; can't check well-formedness and thus it can't really explore the body of the
; quoted lambda object looking for recursive calls.  So our choke detector is
; conservative and does a tree-occur-eq looking for the fn symbol in the
; ``body'' of the evg.

; As a final twist, choke detection slows us down.  So functions outfitted with
; the choke detection have been given a new argument, loop$-recursion-checkedp,
; which if T means the choke detection is skipped because, supposedly, the
; caller has done all the necessary well-formedness checks.  This extra
; argument, of course, breaks books that call such system functions.  That's by
; design.  The regression will fail and we'll find them.  But rather than fix
; them properly -- i.e., rather than figuring out how that user's book ought to
; handle loop$ recursion -- we just add the loop$-recursion-checkedp argument
; and set it to NIL, meaning choke detection is run.

; Loop$-recursion, a different but similarly named flag, has the value declared
; in the :loop$-recursion xarg.  If non-nil it means loop$ recursion is
; permitted and present!  If NIL it means loop$ recursion is prohibited and
; doesn't occur.  But it is only valid if loop$ recursion has been checked.

; Note that loop$-recursion-checkedp does not mean that loop$ recursion is
; present!  It just means that the bodies have passed the tests in
; chk-acceptable-defuns1.  What this really means is that the function being,
; e.g., termination-machine, is being called from within our own source code,
; where we know definitions have been checked thoroughly before other
; processing occurs.  But a user might call these system functions and there we
; advise the user to call them with loop$-recursion-checkedp nil.  That forces
; the check.  Meanwhile, back in our own code, the choke check is never done
; and we just proceed.  Note also that if the similarly named flag
; loop$-recursion is t we know not only that loop$ recursion is allowed but
; that it actually happens somewhere in the body.

; Our convention is that any of our functions that involves loop$-recursion and
; is called in a user's book must have a loop$-recursion-checkedp argument that
; if nil means that the function must call the choke detector.  If a user book
; calls one of these functions without the proper number of arguments we will
; get a syntax error if the user's call is in a :program or :logic mode
; function.  But if it is in a raw function, no compile error may be detected.
; The result (at least in ccl) is often a runtime memory error and a print out
; of the call stack.  That print out will show (somewhere) the offending
; function which is called with insufficient arguments.

(mutual-recursion

(defun choke-on-loop$-recursion1 (fn term sysfn)
  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   ((flambdap (ffn-symb term))
    (or (choke-on-loop$-recursion1 fn (lambda-body (ffn-symb term)) sysfn)
        (choke-on-loop$-recursion1-lst fn (fargs term) sysfn)))
   ((and (loop$-scion-style (ffn-symb term))
         (quotep (fargn term 1))
         (consp (unquote (fargn term 1))))
; This is a loop$ scion call on a quoted cons.  So this might be a loop$ scion
; call on a quoted lambda.  But the lambda may not be well-formed and because
; we do not have access to world, we can't check.  So we just see whether fn
; occurs anywhere in the ``body'' of the ``lambda.''

    (cond ((tree-occur-eq fn (lambda-object-body (unquote (fargn term 1))))
           (er hard 'choke-on-loop$-recursion
               "It appears that the ACL2 system function ~x0 has been called ~
                inappropriately on a function body that engages in loop$ ~
                recursion.  In particular, ~x1 in the body of ~x2 looks like ~
                a call of a translated LOOP$ statement that recursively calls ~
                ~x2.  (We can't be sure because we do not have enough ~
                contextual information so we have been conservative in our ~
                defensive check!)  Recursion in quoted LAMBDA constants was ~
                disallowed when LOOP$ was first introduced but has since been ~
                allowed.  We suspect some user-managed book calls ~x0 without ~
                having been updated to anticipate the possibility of ~
                recursion inside quoted LAMBDA objects!"
               sysfn term fn))
          (t (choke-on-loop$-recursion1-lst fn (fargs term) sysfn))))
   (t (choke-on-loop$-recursion1-lst fn (fargs term) sysfn))))

(defun choke-on-loop$-recursion1-lst (fn terms sysfn)
  (cond ((endp terms) nil)
        (t (or (choke-on-loop$-recursion1 fn (car terms) sysfn)
               (choke-on-loop$-recursion1-lst fn (cdr terms) sysfn)))))
)

(defun choke-on-loop$-recursion (loop$-recursion-checkedp names body sysfn)

; See the Essay on Choking on Loop$ Recursion above.  We can skip the choke
; detector if loop$ recursion has already been exposed (i.e., removed) or if
; there is more than one fn in names (meaning this is a mutual-recursion which
; disallows loop$-recursion).  This function either causes a hard error or
; returns nil.

  (cond ((or loop$-recursion-checkedp
             (cdr names))
         nil)
        (t (choke-on-loop$-recursion1
            (car names)
            body
            sysfn))))

(defun termination-machine (loop$-recursion-checkedp
                            loop$-recursion
                            names formals body
                            alist tests ruler-extenders)

; See the Essay on Choking on Loop$ Recursion for an explanation of the first
; argument.  See termination-machine-rec for the spec of what this function
; does otherwise.

; Names is the list of all the functions defined in a mutually recursive
; clique, formals is the list of formals of one of those functions and body is
; the body of one of those functions.  We are only interested in formals when
; loop$-recursion-checkedp and loop$-recursion are t, in which case names is a
; singleton containing the name of single function being defined.  In that
; case, we use formals to initialize the list of all variables to avoid.  Note
; that bound variables (e.g., from LET statements) occurring in body will be
; eliminated by the on-the-fly beta reduction.

; Note: formals is irrelevant (as described above) if loop$-recursion-checkedp
; is nil.

  (prog2$
   (choke-on-loop$-recursion loop$-recursion-checkedp
                             names
                             body
                             'termination-machine)
   (termination-machine-rec loop$-recursion
                            names body alist tests ruler-extenders
                            (if (and loop$-recursion-checkedp
                                     loop$-recursion)

; We know names, formals-lst, and bodies are singleton lists and that loop$
; recursion is present.  In this case, we compute the list of all formals and
; all bound vars in the body of the fn being defined.  This is the initial list
; of variable names to avoid when generating newvars for the member-equal hyps
; implicitly ruling recursions hidden in quoted lambdas.

                                formals
                                nil))))

(defun termination-machines (loop$-recursion-checkedp
                             loop$-recursion
                             names arglists bodies ruler-extenders-lst)

; This function builds the termination machine for each function defined in
; names with the corresponding formals in arglists and body in bodies.  A list
; of machines is returned.

; Note: arglists is irrelevant (as implied by the comment in
; termination-machine) if loop$-recursion-checkedp is nil.  Otherwise, it
; should be in 1:1 correspondence with names and bodies.  This function chokes
; on unchecked loop$ recursion, but inherits the call of
; (choke-on-loop$-recursion loop$-recursion-checkedp ...) from
; termination-machine.

  (cond ((null bodies) nil)
        (t (cons (termination-machine loop$-recursion-checkedp
                                      loop$-recursion
                                      names (car arglists) (car bodies)
                                      nil nil
                                      (car ruler-extenders-lst))
                 (termination-machines loop$-recursion-checkedp
                                       loop$-recursion
                                       names (cdr arglists) (cdr bodies)
                                       (cdr ruler-extenders-lst))))))

(defun quick-block-initial-settings (formals)
  (cond ((null formals) nil)
        (t (cons 'un-initialized
                 (quick-block-initial-settings (cdr formals))))))

(defun quick-block-info1 (var term)
  (cond ((eq var term) 'unchanging)
        ((dumb-occur var term) 'self-reflexive)
        (t 'questionable)))

(defun quick-block-info2 (setting info1)
  (case setting
        (questionable 'questionable)
        (un-initialized info1)
        (otherwise
         (cond ((eq setting info1) setting)
               (t 'questionable)))))

(defun quick-block-settings (settings formals args)
  (cond ((null settings) nil)
        (t (cons (quick-block-info2 (car settings)
                                    (quick-block-info1 (car formals)
                                                       (car args)))
                 (quick-block-settings (cdr settings)
                                       (cdr formals)
                                       (cdr args))))))

(defun quick-block-down-t-machine (name settings formals t-machine)
  (cond ((null t-machine) settings)
        ((not (eq name
                  (ffn-symb (access tests-and-call (car t-machine) :call))))
         (er hard 'quick-block-down-t-machine
             "When you add induction on mutually recursive functions don't ~
              forget about QUICK-BLOCK-INFO!"))
        (t (quick-block-down-t-machine
            name
            (quick-block-settings
             settings
             formals
             (fargs (access tests-and-call (car t-machine) :call)))
            formals
            (cdr t-machine)))))

(defun quick-block-info (name formals t-machine)

; This function should be called a singly recursive function, name, and
; its termination machine.  It should not be called on a function
; in a non-trivial mutually recursive clique because the we don't know
; how to analyze a call to a function other than name in the t-machine.

; We return a list in 1:1 correspondence with the formals of name.
; Each element of the list is either 'unchanging, 'self-reflexive,
; or 'questionable.  The list is used to help quickly decide if a
; blocked formal can be tolerated in induction.

  (quick-block-down-t-machine name
                              (quick-block-initial-settings formals)
                              formals
                              t-machine))

(defun sublis-tests-rev (test-alist acc)

; Each element of test-alist is a pair (test . alist) where test is a term and
; alist is either an alist or the atom :no-calls, which we treat as nil.  Under
; that interpretation, we return the list of all test/alist, in reverse order
; from test-alist.

  (cond ((endp test-alist) acc)
        (t (sublis-tests-rev
            (cdr test-alist)
            (let* ((test (caar test-alist))
                   (alist (cdar test-alist))
                   (inst-test (cond ((or (eq alist :no-calls)
                                         (null alist))
                                     test)
                                    (t (sublis-expr alist test)))))
              (cons inst-test acc))))))

(defun all-calls-test-alist (names test-alist acc)
  (cond ((endp test-alist) acc)
        (t (all-calls-test-alist
            names
            (cdr test-alist)
            (let* ((test (caar test-alist))
                   (alist (cdar test-alist)))
              (cond ((eq alist :no-calls)
                     acc)
                    (t
                     (all-calls names test alist acc))))))))

(defun union-equal-to-end (x y)

; This is like union-equal, but where a common element is removed from the
; second argument instead of the first.

  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (cond ((intersectp-equal x y)
         (append x (set-difference-equal y x)))
        (t (append x y))))

(defun cross-tests-and-calls3 (tacs tacs-lst)
  (cond ((endp tacs-lst) nil)
        (t
         (let ((tests1 (access tests-and-calls tacs :tests))
               (tests2 (access tests-and-calls (car tacs-lst) :tests)))
           (cond ((some-element-member-complement-term tests1 tests2)
                  (cross-tests-and-calls3 tacs (cdr tacs-lst)))
                 (t (cons (make tests-and-calls
                                :tests (union-equal-to-end tests1 tests2)
                                :calls (union-equal
                                        (access tests-and-calls tacs
                                                :calls)
                                        (access tests-and-calls (car tacs-lst)
                                                :calls)))
                          (cross-tests-and-calls3 tacs (cdr tacs-lst)))))))))

(defun cross-tests-and-calls2 (tacs-lst1 tacs-lst2)

; See cross-tests-and-calls.

  (cond ((endp tacs-lst1) nil)
        (t (append (cross-tests-and-calls3 (car tacs-lst1) tacs-lst2)
                   (cross-tests-and-calls2 (cdr tacs-lst1) tacs-lst2)))))

(defun cross-tests-and-calls1 (tacs-lst-lst acc)

; See cross-tests-and-calls.

  (cond ((endp tacs-lst-lst) acc)
        (t (cross-tests-and-calls1 (cdr tacs-lst-lst)
                                   (cross-tests-and-calls2 (car tacs-lst-lst)
                                                           acc)))))

(defun cross-tests-and-calls (names top-test-alist top-calls tacs-lst-lst)

; We are given a list, tacs-lst-lst, of lists of non-empty lists of
; tests-and-calls records.  Each such record represents a list of tests
; together with a corresponding list of calls.  Each way of selecting elements
; <testsi, callsi> in the ith member of tacs-lst-lst can be viewed as a "path"
; through tacs-lst-lst (see also discussion of a matrix, below).  We return a
; list containing a tests-and-calls record formed for each path: the tests, as
; the union of the tests of top-test-alist (viewed as a list of entries
; test/alist; see sublis-tests-rev) and the testsi; and the calls, as the union
; of the top-calls and the callsi.

; We can visualize the above discussion by forming a sort of matrix as follows.
; The columns (which need not all have the same length) are the elements of
; tacs-lst-lst; typically, for some call of a function in names, each column
; contains the tests-and-calls records formed from an argument of that call
; using induction-machine-for-fn1.  A "path", as discussed above, is formed by
; picking one record from each column.  The order of records in the result is
; probably not important, but it seems reasonable to give priority to the
; records from the first argument by starting with all paths containing the
; first record of the first argument; and so on.

; Note that the records are in the desired order for each list in tacs-lst-lst,
; but are in reverse order for top-test-alist, and also tacs-lst-lst is in
; reverse order, i.e., it corresponds to the arguments of some function call
; but in reverse argument order.

; For any tests-and-calls record: we view the tests as their conjunction, we
; view the calls as specifying substitutions, and we view the measure formula
; as the implication specifying that the substitutions cause an implicit
; measure to go down, assuming the tests.  Logically, we want the resulting
; list of tests-and-calls records to have the following properties.

; - Coverage: The disjunction of the tests is provably equivalent to the
;   conjunction of the tests in top-test-alist.

; - Disjointness: The conjunction of any two tests is provably equal to nil.

; - Measure: Each measure formula is provable.

; We assume that each list in tacs-lst-lst has the above three properties, but
; with top-test-alist being the empty list (that is, with conjunction of T).

; It's not clear as of this writing that Disjointness is necessary.  The others
; are critical for justifying the induction schemes that will ultimately be
; generated from the tests-and-calls records.

; (One may imagine an alternate approach that avoids taking this sort of cross
; product, by constructing induction schemes with inductive hypotheses of the
; form (implies (and <conjoined_path_of_tests> <calls_for_that_path>)).  But
; then the current tests-and-calls data structure and corresponding heuristics
; would have to be revisited.)

  (let ((full-tacs-lst-lst
         (append tacs-lst-lst
                 (list
                  (list (make tests-and-calls
                              :tests (sublis-tests-rev top-test-alist nil)
                              :calls (all-calls-test-alist names
                                                           top-test-alist
                                                           top-calls)))))))
    (cross-tests-and-calls1
     (cdr full-tacs-lst-lst)
     (car full-tacs-lst-lst))))

; To generate the body of the inductor function for a loop$ recursive function
; we will generate ``nuggets'' for certain loop$s in the original body and then
; glue those nuggets onto the front of the original body using (return-last
; 'progn <nugget> <orig-body>).  But in induction-machine-for-fn1 we need to
; recognize when a (return-last 'progn ...)  contains a nugget and treat that
; nugget a little differently than we would another term embedded in such a
; (return-last 'progn ...) form.  So here is how we mark a nugget -- which
; involves ANOTHER (return-last 'progn ...) -- and how we extract the nugget
; from its marking.  The generation of nuggets and inductor functions will
; eventually be implemented in a distributed book.  The only reason we're
; defining these functions now is so that induction-machine-for-fn1 can
; recognize when it's been presented with a nugget.

(defun mark-loop$-recursion-nugget (nugget)
  `(return-last 'progn
                'loop$-recursion-nugget
                ,nugget))

(defun marked-loop$-recursion-nuggetp (term)
; If term satisfies this predicate, then (fargn term 3) is the nugget.
  (and (nvariablep term)
       (not (fquotep term))
       (eq (ffn-symb term) 'return-last)
       (quotep (fargn term 1))
       (eq (unquote (fargn term 1)) 'progn)
       (quotep (fargn term 2))
       (eq (unquote (fargn term 2)) 'loop$-recursion-nugget)))

(mutual-recursion

(defun induction-machine-for-fn1 (names body alist test-alist calls
                                        ruler-extenders merge-p)

; At the top level, this function builds a list of tests-and-calls for the
; given body of a function in names, a list of all the mutually recursive fns
; in a clique.  Note that we don't need to know the function symbol to which
; the body belongs; all the functions in names are considered "recursive"
; calls.  As we recur, we are considering body/alist, with accumulated tests
; consisting of test/a for test (test . a) in test-alist (but see :no-calls
; below, treated as the nil alist), and accumulated calls (already
; instantiated).

; To understand this algorithm, let us first consider the case that there are
; no lambda applications in body, which guarantees that alist will be empty on
; every recursive call, and ruler-extenders is nil.  We explore body,
; accumulating into the list of tests (really, test-alist, but we defer
; discussion of the alist aspect) as we dive: for (if x y z), we accumulate x
; as we dive into y, and we accumulate the negation of x as we dive into z.
; When we hit a term u for which we are blocked from diving further (because we
; have encountered other than an if-term, or are diving into the first argument
; of an if-term), we collect up all the tests, reversing them to restore them
; to the order in which they were encountered from the top, and we collect up
; all calls of functions in names that are subterms of u or of any of the
; accumulated tests.  From the termination analysis we know that assuming the
; collected tests, the arguments for each call are suitably smaller than the
; formals of the function symbol of that call, where of course, for a test only
; the tests superior to it are actually necessary.

; There is a subtle aspect to the handling of the tests in the above algorithm.
; To understand it, consider the following example.  Suppose names is (f), p is
; a function symbol, 'if is in ruler-extenders, and body is:
;  (if (consp x)
;      (if (if (consp x)
;              (p x)
;            (p (f (cons x x))))
;          x
;        (f (cdr x)))
;    x)
; Since 'if is in ruler-extenders, termination analysis succeeds because the
; tests leading to (f (cons x x)) are contradictory.  But with the naive
; algorithm described above, when we encounter the term (f (cdr x)) we would
; create a tests-and-calls record that collects up the call (f (cons x x)); yet
; clearly (cons x x) is not smaller than the formal x under the default measure
; (acl2-count x), even assuming (consp x) and (not (p (f (cons x x)))).

; Thus it is unsound in general to collect all the calls of a ruling test when
; 'if is among the ruler-extenders.  But we don't need to do so anyhow, because
; we will collect suitable calls from the first argument of an 'if test as we
; dive into it, relying on cross-tests-and-calls to incorporate those calls, as
; described below.  We still have to note the test as we dive into the true and
; false branches of an IF call, but that test should not contribute any calls
; when the recursion bottoms out under one of those branches.

; A somewhat similar issue arises with lambda applications in the case that
; :lambdas is among the ruler-extenders.  Consider the term ((lambda (x) (if
; <test> <tbr> <fbr>)) <arg>).  With :lambdas among the ruler-extenders, we
; will be diving into <arg>, and not every call in <arg> may be assumed to be
; "smaller" than the formals as we are exploring the body of the lambda.  So we
; need to collect up the combination of <test> and an alist binding lambda
; formals to actuals (in this example, binding x to <arg>, or more generally,
; the instantiation of <arg> under the existing bindings).  That way, when the
; recursion bottoms out we can collect calls explicitly in that test (unless
; 'if is in ruler-extenders, as already described), instantiating them with the
; associated alist.  If we instead had collected up the instantiated test, we
; would also have collected all calls in <arg> above when bottoming out in the
; lambda body, and that would be a mistake (as discussed above, since not every
; call in arg is relevant).

; So when the recursion bottoms out, some tests should not contribute any
; calls, and some should be instantiated with a corresponding alist.  As we
; collect a test when we recur into the true or false branch of an IF call, we
; thus actually collect a pair consisting of the test and a corresponding
; alist, signifying that for every recursive call c in the test, the actual
; parameter list for c/a is known to be "smaller" than the formals.  If
; ruler-extenders is the default, then all calls of the instantiated test are
; known to be "smaller", so we pair the instantiated test with nil.  But if 'if
; is in the ruler-extenders, then we do not want to collect any calls of the
; test -- as discussed above, cross-tests-and-calls will take care of them --
; so we pair the instantiated test with the special indicator :no-calls.

; The merge-p argument concerns the question of whether exploration of a term
; (if test tbr fbr) should create two tests-and-calls records even if there are
; no recursive calls in tbr or fbr.  For backward compatibility, the answer is
; "no" if we are exploring according to the conventional notion of "rulers".
; But now imagine a function body that has many calls of 'if deep under
; different arguments of some function call.  If we create separate records as
; in the conventional case, the induction scheme may explode when we combine
; these cases with cross-tests-and-calls -- it will be as though we clausified
; even before starting the induction proof proper.  But if we avoid such a
; priori case-splitting, then during the induction proof, it is conceivable
; that many of these potential separate cases could be dispatched with
; rewriting, thus avoiding so much case splitting.

; So if merge-p is true, then we avoid creating tests-and-calls records when
; both branches of an IF term have no recursive calls.  We return (mv flag
; tests-and-calls-lst), where if merge-p is true, then flag is true exactly
; when a call of a function in names has been encountered.  For backward
; compatibility, merge-p is false except when we the analysis has taken
; advantage of ruler-extenders.  If merge-p is false, then the first returned
; value is irrelevant.

; Here are some ideas we expressed about merge-p in the "to do" list, which we
; may want to consider at some point:

;   At the end of Oct. 2009 we modified induction-machine-for-fn1 by giving
;   prog2$ and some other ruler-extenders special handling to avoid the
;   merge-p=t heuristic when there is only one argument with recursive calls.
;   It might be good to re-think the merge-p argument entirely -- maybe for
;   example we could eliminate it, and simply do the merge-p on the fly when
;   appropriate -- e.g., if there is only one argument with recursive calls,
;   just throw out the tests-and-cases for the other arguments, and otherwise
;   do the merging (either by recomputing or by merging on-the-fly) for all
;   arguments before cross-tests-and-calls.
;
;   At any rate, maybe we should add a bit of documentation to the end of
;   ruler-extenders about merge-p.

; Note: Perhaps some calls of reverse can be omitted, though that might ruin
; some regressions.  Our main concern for replayability has probably been the
; order of the tests, not so much the order of the calls.

  (cond
   ((or (variablep body)
        (fquotep body)
        (and (not (flambda-applicationp body))
             (not (eq (ffn-symb body) 'if))
             (not (and (eq (ffn-symb body) 'return-last)
                       (quotep (fargn body 1))
                       (eq (unquote (fargn body 1)) 'mbe1-raw)))
             (not (member-eq-all (ffn-symb body) ruler-extenders))))
    (mv (and merge-p ; optimization
             (ffnnamesp names body))
        (list (make tests-and-calls
                    :tests (sublis-tests-rev test-alist nil)
                    :calls (reverse
                            (all-calls names body alist
                                       (all-calls-test-alist
                                        names
                                        (reverse test-alist)
                                        calls)))))))
   ((flambda-applicationp body)
    (cond
     ((member-eq-all :lambdas ruler-extenders) ; other case is easier to follow
      (mv-let (flg1 temp1)
              (induction-machine-for-fn1 names
                                         (lambda-body (ffn-symb body))
                                         (pairlis$
                                          (lambda-formals (ffn-symb body))
                                          (sublis-var-lst alist (fargs body)))
                                         nil ; test-alist
                                         nil ; calls
                                         ruler-extenders

; The following example shows why we use merge-p = t when ruler-extenders
; includes :lambdas.

; (defun app (x y)
;   ((lambda (result)
;      (if (our-test result)
;          result
;        0))
;    (if (endp x)
;        y
;      (cons (car x)
;            (app (cdr x) y)))))

; If we do not use t, then we wind up crossing two base cases from the lambda
; body with two from the arguments, which seems like needless explosion.

                                         t)
              (mv-let (flg2 temp2)
                      (induction-machine-for-fn1-lst names
                                                     (fargs body)
                                                     alist
                                                     ruler-extenders
                                                     nil ; acc
                                                     t   ; merge-p
                                                     nil) ; flg
                      (mv (or flg1 flg2)
                          (cross-tests-and-calls
                           names
                           test-alist
                           calls

; We cons the lambda-body's contribution to the front, since we want its tests
; to occur after those of the arguments to the lambda application (because the
; lambda body occurs lexically last in a LET form, so this will make the most
; sense to the user).  Note that induction-machine-for-fn1-lst returns its
; result in reverse of the order of arguments.  Thus, the following cons will
; be in the reverse order that is expected by cross-tests-and-calls.

                           (cons temp1 temp2))))))
     (t ; (not (member-eq-all :lambdas ruler-extenders))

; We just go straight into the body of the lambda, with the appropriate alist.
; But we modify calls, so that every tests-and-calls we build will contain all
; of the calls occurring in the actuals to the lambda application.

      (mv-let
       (flg temp)
       (induction-machine-for-fn1 names
                                  (lambda-body (ffn-symb body))
                                  (pairlis$
                                   (lambda-formals (ffn-symb body))
                                   (sublis-var-lst alist (fargs body)))
                                  test-alist
                                  (all-calls-lst names (fargs body) alist
                                                 calls)
                                  ruler-extenders
                                  merge-p)
       (mv (and merge-p ; optimization
                (or flg
                    (ffnnamesp-lst names (fargs body))))
           temp)))))
   ((and (eq (ffn-symb body) 'return-last)
         (quotep (fargn body 1))
         (eq (unquote (fargn body 1)) 'mbe1-raw))

; See the comment in termination-machine about it being sound to treat
; return-last as a macro.

    (induction-machine-for-fn1 names
                               (fargn body 3)
                               alist
                               test-alist
                               calls
                               ruler-extenders
                               merge-p))
   ((eq (ffn-symb body) 'if)
    (let ((test

; Since (remove-guard-holders-weak x _) is provably equal to x, the machine we
; generate using it below is equivalent to the machine generated without it.
; It might be sound also to call possibly-clean-up-dirty-lambda-objects (i.e.,
; to call remove-guard-holders instead of remove-guard-holders-weak) so that
; guard holders are removed from quoted lambdas in argument positions with ilk
; :fn (or :fn?), but we don't expect to pay much of a price by playing it safe
; here and in termination-machine.

; For why we pass nil as the second argument of remove-guard-holders-weak,
; below, see a comment about remove-guard-holders-weak in the definition of
; termination-machine-rec.

           (remove-guard-holders-weak (fargn body 1) nil)))
      (cond
       ((member-eq-all 'if ruler-extenders) ; other case is easier to follow
        (mv-let
         (tst-flg tst-result)
         (induction-machine-for-fn1 names
                                    (fargn body 1) ; keep guard-holders
                                    alist
                                    test-alist
                                    calls
                                    ruler-extenders
                                    t)
         (let ((inst-test (sublis-var alist test))
               (merge-p (or merge-p

; If the test contains a recursive call then we prefer to merge when computing
; the induction machines for the true and false branches, to avoid possible
; explosion in cases.

                            tst-flg)))
           (mv-let
            (tbr-flg tbr-result)
            (induction-machine-for-fn1 names
                                       (fargn body 2)
                                       alist
                                       (cons (cons inst-test :no-calls)
                                             nil) ; tst-result has the tests
                                       nil ; calls, already in tst-result
                                       ruler-extenders
                                       merge-p)
            (mv-let
             (fbr-flg fbr-result)
             (induction-machine-for-fn1 names
                                        (fargn body 3)
                                        alist
                                        (cons (cons (dumb-negate-lit inst-test)
                                                    :no-calls)
                                              nil) ; tst-result has the tests
                                        nil ; calls, already in tst-result
                                        ruler-extenders
                                        merge-p)
             (cond ((and merge-p
                         (not (or tbr-flg fbr-flg)))
                    (mv tst-flg tst-result))
                   (t
                    (mv (or tbr-flg fbr-flg tst-flg)
                        (cross-tests-and-calls
                         names
                         nil ; top-test-alist
                         nil ; calls are already in tst-result

; We put the branch contributions on the front, since their tests are to wind
; up at the end, in analogy to putting the lambda body on the front as
; described above.

                         (list (append tbr-result fbr-result)
                               tst-result))))))))))
       (t ; (not (member-eq-all 'if ruler-extenders))
        (mv-let
         (tbr-flg tbr-result)
         (induction-machine-for-fn1 names
                                    (fargn body 2)
                                    alist
                                    (cons (cons test alist)
                                          test-alist)
                                    calls
                                    ruler-extenders
                                    merge-p)
         (mv-let
          (fbr-flg fbr-result)
          (induction-machine-for-fn1 names
                                     (fargn body 3)
                                     alist
                                     (cons (cons (dumb-negate-lit test)
                                                 alist)
                                           test-alist)
                                     calls
                                     ruler-extenders
                                     merge-p)
          (cond ((and merge-p
                      (not (or tbr-flg fbr-flg)))
                 (mv nil
                     (list (make tests-and-calls
                                 :tests
                                 (sublis-tests-rev test-alist nil)
                                 :calls
                                 (all-calls names test alist
                                            (reverse
                                             (all-calls-test-alist
                                              names
                                              (reverse test-alist)
                                              calls)))))))
                (t
                 (mv (or tbr-flg fbr-flg)
                     (append tbr-result fbr-result))))))))))
   (t ; (member-eq-all (ffn-symb body) ruler-extenders) and not lambda etc.
    (mv-let (merge-p args)

; The special cases just below could perhaps be nicely generalized to any call
; in which at most one argument contains calls of any name in names.  We found
; that we needed to avoid merge-p=t on the recursive call in the prog2$ case
; (where no recursive call is in the first argument) when we introduced
; defun-nx after Version_3.6.1, since the resulting prog2$ broke community book
; books/tools/flag.lisp, specifically event (FLAG::make-flag flag-pseudo-termp
; ...), because the :normalize nil kept the prog2$ around and merge-p=t then
; changed the induction scheme.

; Warning: Do not be tempted to skip the call of cross-tests-and-calls in the
; special cases below for mv-list, prog2$ and arity 1.  It is needed in order
; to handle :no-calls (used above).

            (cond ((and (eq (ffn-symb body) 'mv-list)
                        (not (ffnnamesp names (fargn body 1))))
                   (mv merge-p (list (fargn body 2))))
                  ((and (eq (ffn-symb body) 'return-last)
                        (quotep (fargn body 1))
                        (eq (unquote (fargn body 1)) 'progn)
                        (marked-loop$-recursion-nuggetp (fargn body 2)))
                   (mv merge-p (list (fargn (fargn body 2) 3) (fargn body 3))))
                  ((and (eq (ffn-symb body) 'return-last)
                        (quotep (fargn body 1))
                        (eq (unquote (fargn body 1)) 'progn)
                        (not (ffnnamesp names (fargn body 2))))
                     (mv merge-p (list (fargn body 3))))
                  ((null (cdr (fargs body)))
                   (mv merge-p (list (fargn body 1))))
                  (t (mv t (fargs body))))
            (let* ((flg0 (member-eq (ffn-symb body) names))
                   (calls (if flg0
                              (cons (sublis-var alist body) calls)
                            calls)))
              (mv-let
               (flg temp)
               (induction-machine-for-fn1-lst names
                                              args
                                              alist
                                              ruler-extenders
                                              nil ; acc
                                              merge-p
                                              nil) ; flg
               (mv (or flg0 flg)
                   (cross-tests-and-calls
                    names
                    test-alist
                    calls
                    temp))))))))

(defun induction-machine-for-fn1-lst (names bodies alist ruler-extenders acc
                                            merge-p flg)

; The resulting list corresponds to bodies in reverse order.

  (cond ((endp bodies) (mv flg acc))
        (t (mv-let (flg1 ans1)
                   (induction-machine-for-fn1 names (car bodies) alist
                                              nil ; tests
                                              nil ; calls
                                              ruler-extenders
                                              merge-p)
                   (induction-machine-for-fn1-lst
                    names (cdr bodies) alist ruler-extenders
                    (cons ans1 acc)
                    merge-p
                    (or flg1 flg))))))
)

(defun simplify-tests-and-calls (tc)

; For an example of the utility of removing guard holders, note that lemma
; STEP2-PRESERVES-DL->NOT2 in community book
; books/workshops/2011/verbeek-schmaltz/sources/correctness.lisp has failed
; when we did not do so.

; While we generally follow the convention of calling
; possibly-clean-up-dirty-lambda-objects anytime we're removing guard holders
; we do not do so here and just play it safe until we get burned!

; For why we pass nil as the second argument of remove-guard-holders-weak,
; below, see a comment about remove-guard-holders-weak in the definition of
; termination-machine-rec.

  (let* ((tests0 (remove-guard-holders-weak-lst
                  (access tests-and-calls tc :tests)
                  nil)))
    (mv-let
     (var const)
     (term-equated-to-constant-in-termlist tests0)
     (let ((tests
            (cond (var (mv-let (changedp tests)
                               (simplify-tests var const tests0)
                               (declare (ignore changedp))
                               tests))
                  (t tests0))))

; Through Version_7.1 we returned nil when (null tests), with the comment:
; "contradictory case".  However, that caused a bad error when a caller
; expected a tests-and-calls record, as in the following example.

;   (skip-proofs (defun foo (x)
;                  (declare (xargs :measure (acl2-count x)))
;                  (identity
;                   (cond ((zp x) 17)
;                         (t (foo (1- x)))))))

; We now see no particular reason why special handling is necessary in this
; case.  Of course, the ultimate induction scheme may allow a proof of nil; for
; the example above, try (thm nil :hints (("Goal" :induct (foo x)))).  But
; everything we are doing here is presumably sound, so we expect a skip-proofs
; to be to blame for nil tests, as in the example above.

       (make tests-and-calls
             :tests tests
             :calls (remove-guard-holders-weak-lst
                     (access tests-and-calls tc :calls)
                     nil))))))

(defun simplify-tests-and-calls-lst (tc-list)

; We eliminate needless tests (not (equal term (quote const))) that clutter the
; induction machine.  To see this function in action:

; (skip-proofs (defun foo (x)
;                (if (consp x)
;                    (case (car x)
;                      (0 (foo (nth 0 x)))
;                      (1 (foo (nth 1 x)))
;                      (2 (foo (nth 2 x)))
;                      (3 (foo (nth 3 x)))
;                      (otherwise (foo (cdr x))))
;                  x)))

; (thm (equal (foo x) yyy))

  (cond ((endp tc-list)
         nil)
        (t (cons (simplify-tests-and-calls (car tc-list))
                 (simplify-tests-and-calls-lst (cdr tc-list))))))

(mutual-recursion

(defun loop$-recursion-ffnnamep (fn term)

; Like ffnamep, we determine whether the function fn (possibly a
; lambda-expression) is used as a function in term.  However, unlike ffnnamep,
; we check every quoted lambda-like object in term looking for calls of fn.  We
; know that every quoted lambda-like object in term is in fact a
; well-formed-lambda-objectp.

  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term) nil)
        ((fquotep term)
         (cond ((and (consp (unquote term))
                     (eq (car (unquote term)) 'LAMBDA))
                (loop$-recursion-ffnnamep fn (lambda-object-body (unquote term))))
               (t nil)))
        ((flambda-applicationp term)
         (or (equal fn (ffn-symb term))
             (loop$-recursion-ffnnamep fn (lambda-body (ffn-symb term)))
             (loop$-recursion-ffnnamep-lst fn (fargs term))))
        ((eq (ffn-symb term) fn) t)
        (t (loop$-recursion-ffnnamep-lst fn (fargs term)))))

(defun loop$-recursion-ffnnamep-lst (fn l)
  (declare (xargs :guard (pseudo-term-listp l)))
  (if (endp l)
      nil
      (or (loop$-recursion-ffnnamep fn (car l))
          (loop$-recursion-ffnnamep-lst fn (cdr l)))))

 )

(defun induction-machine-for-fn (names body ruler-extenders)

; We build an induction machine for the function in names with the given body.
; We claim the soundness of the induction schema suggested by this machine is
; easily seen from the proof done by prove-termination.  See
; termination-machine.

; Note: The induction machine built for a clique of more than 1
; mutually recursive functions is probably unusable.  We do not know
; how to do inductions on such functions now.

  (mv-let (flg ans)
          (induction-machine-for-fn1 names
                                     body
                                     nil ; alist
                                     nil ; tests
                                     nil ; calls
                                     ruler-extenders
                                     nil); merge-p
          (declare (ignore flg))
          (simplify-tests-and-calls-lst ans)))

(defun intrinsic-suggested-induction-cand-do$ (term wrld)

; This function takes a do$ term and computes three properties that would have
; been stored for the induction hint function, had that function been defined.
; The three properties are QUICK-BLOCK-INFO, JUSTIFICATION, and
; INDUCTION-MACHINE.  We then attempt to create an induction candidate from
; those data structures, returning either a singleton list containing the
; candidate or nil (if no induction is possible, e.g., a controller is occupied
; by a non-variable term).

  (let ((four-tuple (decompile-do$ term wrld)))
    (case-match four-tuple
      ((formals call measure body)

; This and the next paragraph concern the call of termination-machine below.
; We use the default-ruler-extenders for all do$ terms.  Changing this would be
; hard.  Imagine allowing a DO$ term to carry around a :ruler-extenders
; specification, but it would have to be a new argument and it would be awkward
; since it wouldn't affect the value and so would be a good candidate for
; ``nilifying'' to make matches work, but that would defeat the purpose of
; having it there when we are looking for induction suggestions.  So we just
; punt and leave it for some future extension.

; We use loop$-recursion-checkedp = t because DO$ prohibits loop$ recursion.
; Thus, we also know there was no loop$ recursion present, so we set
; loop$-recursion to nil.

       (let* ((ruler-extenders (default-ruler-extenders wrld))
              (t-machine (termination-machine
                          t   ; loop$-recursion-checkedp
                          nil ; loop$-recursion
                          (list *do$-induction-fn*)
                          (list formals)
                          body
                          nil nil
                          ruler-extenders))
              (quick-block-info (quick-block-info *do$-induction-fn*
                                                  formals
                                                  t-machine))
              (formals-to-actuals-alist (pairlis$ formals (fargs call)))

; The justification constructed below will find its way into the candidate
; record constructed by intrinsic-suggested-induction-cand1.  We regard the
; justification record as merely a package carrying the measured variables,
; well-founded domain and relation, and the measure.  This justification is not
; stored on any property list.  Indeed, we don't actually know that the
; termination proof obligations can even be proved.  They will be among the
; clauses to be proved when the derived induction scheme is applied.

              (justification (make justification
                                   :subset
                                   (all-vars
                                    (sublis-var formals-to-actuals-alist
                                                measure))
                                   :subversive-p

; To see why :subversive-p is nil here, we first recall the idea of subversive
; justifications.  A justification is subversive if the corresponding induction
; is not justified.  Generally that happens when the justification depends on
; properties local to an enclosing non-trivial encapsulate.

; In this case, unlike the termination proofs done for defun (where the
; termination proof is done when the defun is admitted and then the induction
; scheme is assumed legitimate in all future extensions), the legitimacy of the
; induction scheme suggested by a do$ is in fact proved every time the scheme
; is used.  Because of that proof, there is no reason to doubt the correctness
; of the generated induction when used in a successful proof, so there is no
; need to mark the justification as subversive.

; The explanation above is sufficient, by itself, to explain why there is
; nothing subversive here.  But here are two additional (though unnecessary)
; reasons to feel secure that this :justification value of nil avoids
; unsoundness.

; First, it's actually really hard to even threaten subversion with a do$!  A
; signature function may only be badged locally, because it is only during pass
; 1 of the encapsulate that a signature function is defined and only defined
; functions may be badged.  (Put another way, if a signature function is
; non-locally badged, an error is caused on pass 2 because the function is not
; defined.)  But any function used in the measure or body of a do$ must be
; badged.  So any do$ statement inside an encapsulate and using a signature
; function must be local.

; Second, this :subversive-p field of a justification is never even consulted!
; If you inspect all the places the :subversive-p field of a justification is
; used you find only two: in termination-theorem and in get-subversives.  In
; both cases, the justification accessed is first recovered from the property
; list of a function symbol.  But no do$ justification record is ever stored
; under a function symbol.  Indeed, the ``name'' of the decompiled do$ function
; is the value of the constant *do$-induction-fn* which is not even a function
; symbol, it is a keyword.  So if the only way the rest of the prover sees
; :subversive-p is in connection with a function symbol, this :subversive-p
; will never be seen.

                                   nil
                                   :mp 'lexp
                                   :rel 'l<
                                   :measure
                                   `(lex-fix ,(sublis-var
                                               formals-to-actuals-alist
                                               measure))
                                   :ruler-extenders ruler-extenders))
              (induction-machine
               (induction-machine-for-fn (list *do$-induction-fn*)
                                         body
                                         ruler-extenders)))
; The call argument below finds its way into the :induction-term field of the
; candidate constructed.  Calls are always function calls and the fn-symb of
; any call produced by a do$ induction is *do$-induction-fn*, which is a
; keyword.  So if you're looking at a candidate and want to know whether it was
; suggested as the intrinsic induction of a particular do$, check to see if
; (ffn-symb (access candidate cand :induction-term)) is *do$-induction-fn*.

         (intrinsic-suggested-induction-cand1
          '(:induction do$)  ; We always use the induction rune for DO$
          call               ; The identifying mark -- see above
          formals
          quick-block-info
          justification
          induction-machine
          term               ; the do$ term suggesting this induction
          nil                ; ttree
          )))
      (& nil))))

(defun intrinsic-suggested-induction-cand
    (induction-rune term formals quick-block-info justification machine xterm
                    ttree wrld)

; Term, above, is a call of some fn with the given formals, quick-block-info,
; justification and induction machine.  We return a list of induction
; candidates, said list either being empty or the singleton list containing the
; induction candidate intrinsically suggested by term.  Xterm is logically
; unrelated to term and is the term appearing in the original conjecture from
; which we (somehow) obtained term for consideration.

; If term is a call of DO$ we first try to derive a do$ induction from it as
; though it might be a semi-concrete do$.  If that fails, we try to get the
; intrinsic induction from do$.  If term is not a call of do$, we just use the
; intrinsic induction.

  (cond
   ((and (nvariablep term)
         (not (fquotep term))
         (eq (ffn-symb term) 'do$))

; Intrinsic-suggested-induction-cand-do$ returns nil if term is not
; a semi-concrete call that suggests an induction.

    (or (intrinsic-suggested-induction-cand-do$ term wrld)
        (intrinsic-suggested-induction-cand1
         induction-rune term formals quick-block-info
         justification machine xterm ttree)))
   (t (intrinsic-suggested-induction-cand1
       induction-rune term formals quick-block-info
       justification machine xterm ttree))))

; The following is now defined in rewrite.lisp.

; (defrec induction-rule (nume (pattern . condition) scheme . rune) nil)

(defun relieve-induction-condition-terms (rune pattern terms alist type-alist
                                               ens wrld)
  (cond
   ((endp terms) t)
   ((or (variablep (car terms))
        (fquotep (car terms))
        (not (eq (ffn-symb (car terms)) 'synp)))
    (mv-let (ts ttree1)
      (type-set (sublis-var alist (car terms))
                t nil type-alist ens wrld nil nil nil)
      (declare (ignore ttree1))
      (cond
       ((ts-intersectp *ts-nil* ts) nil)
       (t (relieve-induction-condition-terms rune pattern
                                             (cdr terms)
                                             alist type-alist ens wrld)))))
   (t

; In this case, (car terms) is (SYNP 'NIL '(SYNTAXP ...) 'term), where term
; is the translated term to be evaluated under alist.

    (mv-let (erp val)
      (ev-w (get-evg (fargn (car terms) 3) 'relieve-induction-condition-terms)
            alist
            wrld
            nil ; user-stobj-alist
            t   ; safe-mode
            nil ; gc-off
            nil ; hard-error-returns-nilp
            nil ; aok
            )
      (cond
       (erp (er hard 'relieve-induction-condition-terms
                "The form ~x0 caused the error, ~@1.  That SYNTAXP form ~
                 occurs as a :condition governing the :induction rule ~x2, ~
                 which we tried to fire after matching the :pattern ~x3 using ~
                 the unifying substitution ~x4."
                (get-evg (fargn (car terms) 2) 'relieve-induction-condition-terms)
                val
                rune
                pattern
                alist))
       (val (relieve-induction-condition-terms rune pattern
                                               (cdr terms)
                                               alist type-alist ens wrld)))))))

(mutual-recursion

(defun apply-induction-rule (rule term type-alist xterm ttree seen ens wrld)

; We apply the induction-rule, rule, to term, and return a possibly empty list
; of suggested inductions.  The basic idea is to check that the rule is enabled
; and that the :pattern of the rule matches term.  If so, we check that the
; :condition of the rule is true under the current type-alist.  This check is
; heuristic only and so we indicate that the guards have been checked and we
; allow forcing.  We ignore the ttree because we are making a heuristic choice
; only.  If type-set says the :condition is non-nil, we fire the rule by
; instantiating the :scheme and recursively getting the suggested inductions
; for that term.  Note that we are not recursively exploring the instantiated
; scheme but just getting the inductions suggested by its top-level function
; symbol.

; Seen is a list of numes of induction-rules already encountered, used in order
; to prevent infinite loops.  The following are two examples that looped before
; the use of this list of numes seen.

; From Daron Vroon:

;  (defun zip1 (xs ys)
;    (declare (xargs :measure (acl2-count xs)))
;    (cond ((endp xs) nil)
;          ((endp ys) nil)
;          (t (cons (cons (car xs) (car ys)) (zip1 (cdr xs) (cdr ys))))))

;  (defun zip2 (xs ys)
;    (declare (xargs :measure (acl2-count ys)))
;    (cond ((endp xs) nil)
;          ((endp ys) nil)
;          (t (cons (cons (car xs) (car ys)) (zip2 (cdr xs) (cdr ys))))))

;  (defthm zip1-zip2-ind
;    t
;    :rule-classes ((:induction :pattern (zip1 xs ys)
;                               :scheme (zip2 xs ys))))

;  (defthm zip2-zip1-ind
;    t
;    :rule-classes ((:induction :pattern (zip2 xs ys)
;                               :scheme (zip1 xs ys))))

;  (defstub foo (*) => *)

;  ;; the following overflows the stack.
;  (thm
;   (= (zip1 (foo xs) ys)
;      (zip2 (foo xs) ys)))

; From Pete Manolios:

;  (defun app (x y)
;    (if (endp x)
;        y
;      (cons (car x) (app (cdr x) y))))

;  (defthm app-ind
;    t
;    :rule-classes ((:induction :pattern (app x y)
;                               :condition (and (true-listp x) (true-listp y))
;                               :scheme (app x y))))

;  (in-theory (disable (:induction app)))

;  (defthm app-associative
;    (implies (and (true-listp a)
;                  (true-listp b)
;                  (true-listp c))
;             (equal (app (app a b) c)
;                    (app a (app b c)))))

  (let ((nume (access induction-rule rule :nume)))
    (cond
     ((and (not (member nume seen))
           (enabled-numep nume ens))
      (mv-let
        (ans alist)
        (one-way-unify (access induction-rule rule :pattern)
                       term)
        (cond
         (ans
          (with-accumulated-persistence
           (access induction-rule rule :rune)
           (suggestions)
           suggestions
           (cond
            ((relieve-induction-condition-terms (access induction-rule rule
                                                        :rune)
                                                (access induction-rule rule
                                                        :pattern)
                                                (access induction-rule rule
                                                        :condition)
                                                alist type-alist ens wrld)
             (let ((term1 (sublis-var alist
                                      (access induction-rule rule :scheme))))
               (cond ((or (variablep term1)
                          (fquotep term1))
                      nil)
                     (t (suggested-induction-cands term1 type-alist
                                                   xterm
                                                   (push-lemma
                                                    (access induction-rule
                                                            rule
                                                            :rune)
                                                    ttree)
                                                   nil ; eflg
                                                   (cons nume seen)
                                                   ens wrld)))))
            (t nil))))
         (t nil))))
     (t nil))))

(defun suggested-induction-cands1
  (induction-rules term type-alist xterm ttree eflg seen ens wrld)

; We map down induction-rules and apply each enabled rule to term, which is
; known to be an application of the function symbol fn to some args.  Each rule
; gives us a possibly empty list of suggested inductions.  We append all these
; suggestions together.  In addition, if fn is recursively defined and is
; enabled (or, even if fn is disabled if we are exploring a user-supplied
; induction hint) we collect the intrinsic suggestion for term as well.

; Seen is a list of numes of induction-rules already encountered, used in order
; to prevent infinite loops.

; Eflg represents an "enable flag".  When true, an induction rune that
; represents the induction scheme of a recursive definition must be enabled in
; order to be applicable.  When false (nil), it may be applied regardless.

  (cond
   ((null induction-rules)
    (let* ((fn (ffn-symb term))
           (machine (getpropc fn 'induction-machine nil wrld)))
      (cond
       ((null machine) nil)
       (t

; Historical note:  Before Version_2.6 we had the following note:

;   Note: The intrinsic suggestion will be non-nil only if (:INDUCTION fn) is
;   enabled and so here we have a case in which two runes have to be enabled
;   (the :DEFINITION and the :INDUCTION runes) to get the desired effect.  It
;   is not clear if this is a good design but at first sight it seems to
;   provide upward compatibility because in Nqthm a disabled function suggests
;   no inductions.

; We no longer make any such requirement:  the test above (t) replaces the
; following.

;       (or (enabled-fnp fn nil ens wrld)
;           (and induct-hint-val
;                (not (equal induct-hint-val *t*))))

        (let ((induction-rune (list :induction (ffn-symb term))))
          (and (or (null eflg)
                   (enabled-runep induction-rune ens wrld))
               (intrinsic-suggested-induction-cand
                induction-rune
                term
                (formals fn wrld)
                (getpropc fn 'quick-block-info
                          '(:error "See SUGGESTED-INDUCTION-CANDS1.")
                          wrld)
                (getpropc fn 'justification
                          '(:error "See SUGGESTED-INDUCTION-CANDS1.")
                          wrld)
                machine
                xterm
                ttree
                wrld)))))))
   (t (append (apply-induction-rule (car induction-rules)
                                    term type-alist
                                    xterm ttree seen ens wrld)
              (suggested-induction-cands1 (cdr induction-rules)
                                          term type-alist
                                          xterm ttree eflg seen ens wrld)))))

(defun suggested-induction-cands
  (term type-alist xterm ttree eflg seen ens wrld)

; Term is some fn applied to args.  Xterm is some term occurring in the
; conjecture we are exploring and is the term upon which this induction
; suggestion will be "blamed" and from which we have obtained term via
; induction-rules.  We return all of the induction candidates suggested by
; term.  Lambda applications suggest no inductions.  Disabled functions suggest
; no inductions -- unless we are applying the user's induct hint value (in
; which case we, quite reasonably, assume every function in the value is worthy
; of analysis since any function could have been omitted).

; Seen is a list of numes of induction-rules already encountered, used in order
; to prevent infinite loops.

  (cond
   ((flambdap (ffn-symb term)) nil)
   (t (suggested-induction-cands1
       (getpropc (ffn-symb term) 'induction-rules nil wrld)
       term type-alist xterm ttree eflg seen ens wrld))))
)

(mutual-recursion

(defun get-induction-cands (term type-alist ens wrld ans)

; We explore term and accumulate onto ans all of the induction
; candidates suggested by it.

  (cond ((variablep term) ans)
        ((fquotep term) ans)
        ((eq (ffn-symb term) 'hide)
         ans)
        (t (get-induction-cands-lst
            (fargs term)
            type-alist ens wrld
            (append (suggested-induction-cands term type-alist
                                               term nil
                                               t ; eflg
                                               nil ens wrld)
                    ans)))))

(defun get-induction-cands-lst (lst type-alist ens wrld ans)

; We explore the list of terms, lst, and accumulate onto ans all of
; the induction candidates.

  (cond ((null lst) ans)
        (t (get-induction-cands
            (car lst)
            type-alist ens wrld
            (get-induction-cands-lst
             (cdr lst)
             type-alist ens wrld ans)))))

)

(defun get-induction-cands-from-cl-set1 (cl-set ens oncep-override wrld state
                                                ans)

; We explore cl-set and accumulate onto ans all of the induction
; candidates.

  (cond
   ((null cl-set) ans)
   (t (mv-let (contradictionp type-alist fc-pairs)
              (forward-chain-top 'induct
                                 (car cl-set) nil t
                                 nil ; do-not-reconsiderp
                                 wrld ens oncep-override state)

; We need a type-alist with which to compute induction aliases.  It is of
; heuristic use only, so we may as well turn the force-flg on.  We assume no
; contradiction is found.  If by chance one is, then type-alist is nil, which
; is an acceptable type-alist.

              (declare (ignore contradictionp fc-pairs))
              (get-induction-cands-lst
               (car cl-set)
               type-alist ens wrld
               (get-induction-cands-from-cl-set1 (cdr cl-set)
                                                 ens oncep-override wrld state
                                                 ans))))))

(defun get-induction-cands-from-cl-set (cl-set pspv wrld state)

; We explore cl-set and collect all induction candidates.

  (let ((rcnst (access prove-spec-var pspv :rewrite-constant)))
    (get-induction-cands-from-cl-set1 cl-set
                                      (access rewrite-constant
                                              rcnst
                                              :current-enabled-structure)
                                      (access rewrite-constant
                                              rcnst
                                              :oncep-override)
                                      wrld
                                      state
                                      nil)))

; That completes the development of the code for exploring a clause set
; and gathering the induction candidates suggested.

; Section:  Pigeon-Holep

; We next develop pigeon-holep, which tries to fit some "pigeons" into
; some "holes" using a function to determine the sense of the word
; "fit".  Since ACL2 is first-order we can't pass arbitrary functions
; and hence we pass symbols and define our own special-purpose "apply"
; that interprets the particular symbols passed to calls of
; pigeon-holep.

; However, it turns out that the applications of pigeon-holep require
; passing functions that themselves call pigeon-holep.  And so
; pigeon-holep-apply is mutually recursive with pigeon-holep (but only
; because the application functions use pigeon-holep).

(mutual-recursion

(defun pigeon-holep-apply (fn pigeon hole)

; See pigeon-holep for the problem and terminology.  This function
; takes a symbol denoting a predicate and two arguments.  It applies
; the predicate to the arguments.  When the predicate holds we say
; the pigeon argument "fits" into the hole argument.

  (case fn
        (pair-fitp

; This predicate is applied to two pairs, each taken from two substitutions.
; We say (v1 . term1) (the "pigeon") fits into (v2 . term2) (the "hole")
; if v1 is v2 and term1 occurs in term2.

         (and (eq (car pigeon) (car hole))
              (occur (cdr pigeon) (cdr hole))))

        (alist-fitp

; This predicate is applied to two substitutions. We say the pigeon
; alist fits into the hole alist if each pair of the pigeon fits into
; a pair of the hole and no pair of the hole is used more than once.

         (pigeon-holep pigeon hole nil 'pair-fitp))

        (tests-and-alists-fitp

; This predicate is applied to two tests-and-alists records.  The
; first fits into the second if the tests of the first are a subset
; of those of the second and either they are both base cases (i.e., have
; no alists) or each substitution of the first fits into a substitution of
; the second, using no substitution of the second more than once.

         (and (subsetp-equal (access tests-and-alists pigeon :tests)
                             (access tests-and-alists hole :tests))
              (or (and (null (access tests-and-alists pigeon :alists))
                       (null (access tests-and-alists hole :alists)))
                  (pigeon-holep (access tests-and-alists pigeon :alists)
                                (access tests-and-alists hole :alists)
                                nil
                                'alist-fitp))))))

(defun pigeon-holep (pigeons holes filled-holes fn)

; Both pigeons and holes are lists of arbitrary objects.  The holes
; are implicitly enumerated left-to-right from 0.  Filled-holes is a
; list of the indices of holes we consider "filled."  Fn is a
; predicate known to pigeon-holep-apply.  If fn applied to a pigeon and
; a hole is non-nil, then we say the pigeon "fits" into the hole.  We
; can only "put" a pigeon into a hole if the hole is unfilled and the
; pigeon fits.  The act of putting the pigeon into the hole causes the
; hole to become filled.  We return t iff it is possible to put each
; pigeon into a hole under these rules.

  (cond
   ((null pigeons) t)
   (t (pigeon-holep1 (car pigeons)
                     (cdr pigeons)
                     holes 0
                     holes filled-holes fn))))

(defun pigeon-holep1 (pigeon pigeons lst n holes filled-holes fn)

; Lst is a terminal sublist of holes, whose first element has index n.
; We map over lst looking for an unfilled hole h such that (a) we can
; put pigeon into h and (b) we can dispose of the rest of the pigeons
; after filling h.

  (cond
   ((null lst) nil)
   ((member n filled-holes)
    (pigeon-holep1 pigeon pigeons (cdr lst) (1+ n) holes filled-holes fn))
   ((and (pigeon-holep-apply fn pigeon (car lst))
         (pigeon-holep pigeons holes
                       (cons n filled-holes)
                       fn))
    t)
   (t (pigeon-holep1 pigeon pigeons (cdr lst) (1+ n)
                     holes filled-holes fn))))

)

(defun flush-cand1-down-cand2 (cand1 cand2)

; This function takes two induction candidates and determines whether
; the first is subsumed by the second.  If so, it constructs a new
; candidate that is logically equivalent (vis a vis the induction
; suggested) to the second but which now carries with it the weight
; and heuristic burdens of the first.

  (cond
   ((and (subsetp-eq (access candidate cand1 :changed-vars)
                     (access candidate cand2 :changed-vars))
         (subsetp-eq (access candidate cand1 :unchangeable-vars)
                     (access candidate cand2 :unchangeable-vars))
         (pigeon-holep (access candidate cand1 :tests-and-alists-lst)
                       (access candidate cand2 :tests-and-alists-lst)
                       nil
                       'tests-and-alists-fitp))
    (change candidate cand2
            :score (+ (access candidate cand1 :score)
                      (access candidate cand2 :score))
            :controllers (union-eq (access candidate cand1 :controllers)
                                   (access candidate cand2 :controllers))
            :other-terms (add-to-set-equal
                          (access candidate cand1 :induction-term)
                          (union-equal
                           (access candidate cand1 :other-terms)
                           (access candidate cand2 :other-terms)))
            :xother-terms (add-to-set-equal
                           (access candidate cand1 :xinduction-term)
                           (union-equal
                            (access candidate cand1 :xother-terms)
                            (access candidate cand2 :xother-terms)))
            :ttree (cons-tag-trees (access candidate cand1 :ttree)
                                   (access candidate cand2 :ttree))))
   (t nil)))

(defun flush-candidates (cand1 cand2)

; This function determines whether one of the two induction candidates
; given flushes down the other and if so returns the appropriate
; new candidate.  This function is a mate and merge function used
; by m&m and is hence known to m&m-apply.

  (or (flush-cand1-down-cand2 cand1 cand2)
      (flush-cand1-down-cand2 cand2 cand1)))

; We now begin the development of the merging of two induction
; candidates.  The basic idea is that if two functions both replace x
; by x', and one of them simultaneously replaces a by a' while the
; other replaces b by b', then we should consider inducting on x, a,
; and b, by x', a', and b'.  Of course, by the time we get here, the
; recursion is coded into substitution alists: ((x . x') (a . a')) and
; ((x . x') (b . b')).  We merge these two alists into ((x . x') (a .
; a') (b . b')).  The merge of two sufficiently compatible alists is
; accomplished by just unioning them together.

; The key ideas are (1) recognizing when two alists are describing the
; "same" recursive step (i.e., they are both replacing x by x', where
; x is somehow a key variable); (2) observing that they do not
; explicitly disagree on what to do with the other variables.

(defun alists-agreep (alist1 alist2 vars)

; Two alists agree on vars iff for each var in vars the image of var under
; the first alist is equal to that under the second.

  (cond ((null vars) t)
        ((equal (let ((temp (assoc-eq (car vars) alist1)))
                  (cond (temp (cdr temp))(t (car vars))))
                (let ((temp (assoc-eq (car vars) alist2)))
                  (cond (temp (cdr temp))(t (car vars)))))
         (alists-agreep alist1 alist2 (cdr vars)))
        (t nil)))

(defun irreconcilable-alistsp (alist1 alist2)

; Two alists are irreconcilable iff there is a var v that they both
; explicitly map to different values.  Put another way, there exists a
; v such that (v . a) is a member of alist1 and (v . b) is a member of
; alist2, where a and b are different.  If two substitutions are
; reconcilable then their union is a substitution.

; We rely on the fact that this function return t or nil.

  (cond ((null alist1) nil)
        (t (let ((temp (assoc-eq (caar alist1) alist2)))
             (cond ((null temp)
                    (irreconcilable-alistsp (cdr alist1) alist2))
                   ((equal (cdar alist1) (cdr temp))
                    (irreconcilable-alistsp (cdr alist1) alist2))
                   (t t))))))

(defun affinity (aff alist1 alist2 vars)

; We say two alists that agree on vars but are irreconcilable are
; "antagonists".  Two alists that agree on vars and are not irreconcilable
; are "mates".

; Aff is either 'antagonists or 'mates and denotes one of the two relations
; above.  We return t iff the other args are in the given relation.

  (and (alists-agreep alist1 alist2 vars)
       (eq (irreconcilable-alistsp alist1 alist2)
           (eq aff 'antagonists))))

(defun member-affinity (aff alist alist-lst vars)

; We determine if some member of alist-lst has the given affinity with alist.

  (cond ((null alist-lst) nil)
        ((affinity aff alist (car alist-lst) vars)
         t)
        (t (member-affinity aff alist (cdr alist-lst) vars))))

(defun occur-affinity (aff alist lst vars)

; Lst is a list of tests-and-alists.  We determine whether alist has
; the given affinity with some alist in lst.  We call this occur
; because we are looking inside the elements of lst.  But it is
; technically a misnomer because we don't look inside recursively; we
; treat lst as though it were a list of lists.

  (cond
   ((null lst) nil)
   ((member-affinity aff alist
                     (access tests-and-alists (car lst) :alists)
                     vars)
    t)
   (t (occur-affinity aff alist (cdr lst) vars))))

(defun some-occur-affinity (aff alists lst vars)

; Lst is a list of tests-and-alists.  We determine whether some alist
; in alists has the given affinity with some alist in lst.

  (cond ((null alists) nil)
        (t (or (occur-affinity aff (car alists) lst vars)
               (some-occur-affinity aff (cdr alists) lst vars)))))

(defun all-occur-affinity (aff alists lst vars)

; Lst is a list of tests-and-alists.  We determine whether every alist
; in alists has the given affinity with some alist in lst.

  (cond ((null alists) t)
        (t (and (occur-affinity aff (car alists) lst vars)
                (all-occur-affinity aff (cdr alists) lst vars)))))

(defun contains-affinity (aff lst vars)

; We determine if two members of lst have the given affinity.

  (cond ((null lst) nil)
        ((member-affinity aff (car lst) (cdr lst) vars) t)
        (t (contains-affinity aff (cdr lst) vars))))

; So much for general-purpose scanners.  We now develop the predicates
; that are used to determine if we can merge lst1 into lst2 on vars.
; See merge-tests-and-alists-lsts for extensive comments on the ideas
; behind the following functions.

(defun antagonistic-tests-and-alists-lstp (lst vars)

; Lst is a list of tests-and-alists.  Consider just the set of all
; alists in lst.  We return t iff that set contains an antagonistic
; pair.

; We operate as follows.  Each element of lst contains some alists.
; We take the first element and ask whether its alists contain an
; antagonistic pair.  If so, we're done.  Otherwise, we ask whether
; any alist in that first element is antagonistic with the alists in
; the rest of lst.  If so, we're done.  Otherwise, we recursively
; look at the rest of lst.

  (cond
   ((null lst) nil)
   (t (or (contains-affinity
           'antagonists
           (access tests-and-alists (car lst) :alists)
           vars)
          (some-occur-affinity
           'antagonists
           (access tests-and-alists (car lst) :alists)
           (cdr lst)
           vars)
          (antagonistic-tests-and-alists-lstp (cdr lst) vars)))))

(defun antagonistic-tests-and-alists-lstsp (lst1 lst2 vars)

; Both lst1 and lst2 are lists of tests-and-alists.  We determine whether
; there exists an alist1 in lst1 and an alist2 in lst2 such that alist1
; and alist2 are antagonists.

  (cond
   ((null lst1) nil)
   (t (or (some-occur-affinity
           'antagonists
           (access tests-and-alists (car lst1) :alists)
           lst2
           vars)
          (antagonistic-tests-and-alists-lstsp (cdr lst1) lst2 vars)))))

(defun every-alist1-matedp (lst1 lst2 vars)

; Both lst1 and lst2 are lists of tests-and-alists.  We determine for every
; alist1 in lst1 there exists an alist2 in lst2 that agrees with alist1 on
; vars and that is not irreconcilable.

  (cond ((null lst1) t)
        (t (and (all-occur-affinity
                 'mates
                 (access tests-and-alists (car lst1) :alists)
                 lst2
                 vars)
                (every-alist1-matedp (cdr lst1) lst2 vars)))))

; The functions above are used to determine that lst1 and lst2 contain
; no antagonistic pairs, that every alist in lst1 has a mate somewhere in
; lst2, and that the process of merging alists from lst1 with their
; mates will not produce alists that are antagonistic with other alists
; in lst1.  We now develop the code for merging non-antagonistic alists
; and work up the structural hierarchy to merging lists of tests and alists.

(defun merge-alist1-into-alist2 (alist1 alist2 vars)

; We assume alist1 and alist2 are not antagonists.  Thus, either they
; agree on vars and have no explicit disagreements, or they simply
; don't agree on vars.  If they agree on vars, we merge alist1 into
; alist2 by just unioning them together.  If they don't agree on vars,
; then we merge alist1 into alist2 by ignoring alist1.

  (cond
   ((alists-agreep alist1 alist2 vars)
    (union-equal alist1 alist2))
   (t alist2)))

; Now we begin working up the structural hierarchy.  Our strategy is
; to focus on a given alist2 and hit it with every alist1 we have.
; Then we'll use that to copy lst2 once, hitting each alist2 in it
; with everything we have.  We could decompose the problem the other
; way: hit lst2 with successive alist1's.  That suffers from forcing
; us to copy lst2 repeatedly, and there are parts of that structure
; (i.e., the :tests) that don't change.

(defun merge-alist1-lst-into-alist2 (alist1-lst alist2 vars)

; Alist1-lst is a list of alists and alist2 is an alist.  We know that
; there is no antagonists between the elements of alist1-lst and in
; alist2.  We merge each alist1 into alist2 and return
; the resulting extension of alist2.

  (cond
   ((null alist1-lst) alist2)
   (t (merge-alist1-lst-into-alist2
       (cdr alist1-lst)
       (merge-alist1-into-alist2 (car alist1-lst) alist2 vars)
       vars))))

(defun merge-lst1-into-alist2 (lst1 alist2 vars)

; Given a list of tests-and-alists, lst1, and an alist2, we hit alist2
; with every alist1 in lst1.

  (cond ((null lst1) alist2)
        (t (merge-lst1-into-alist2
            (cdr lst1)
            (merge-alist1-lst-into-alist2
             (access tests-and-alists (car lst1) :alists)
             alist2
             vars)
            vars))))

; So now we write the code to copy lst2, hitting each alist in it with lst1.

(defun merge-lst1-into-alist2-lst (lst1 alist2-lst vars)
  (cond ((null alist2-lst) nil)
        (t (cons (merge-lst1-into-alist2 lst1 (car alist2-lst) vars)
                 (merge-lst1-into-alist2-lst lst1 (cdr alist2-lst) vars)))))

(defun merge-lst1-into-lst2 (lst1 lst2 vars)
  (cond ((null lst2) nil)
        (t (cons (change tests-and-alists (car lst2)
                         :alists
                         (merge-lst1-into-alist2-lst
                          lst1
                          (access tests-and-alists (car lst2) :alists)
                          vars))
                 (merge-lst1-into-lst2 lst1 (cdr lst2) vars)))))

(defun merge-tests-and-alists-lsts (lst1 lst2 vars)

; Lst1 and lst2 are each tests-and-alists-lsts from some induction
; candidates.  Intuitively, we try to stuff the alists of lst1 into
; those of lst2 to construct a new lst2 that combines the induction
; schemes of both.  If we fail we return nil.  Otherwise we return the
; modified lst2.  The modified lst2 has exactly the same tests as
; before; only its alists are different and they are different only by
; virtue of having been extended with some addition pairs.  So the
; justification of the merged induction is the same as the
; justification of the original lst2.

; Given an alist1 from lst1, which alist2's of lst2 do you extend and
; how?  Suppose alist1 maps x to x' and y to y'.  Then intuitively we
; think "the first candidate is trying to keep x and y in step, so
; that when x goes to x' y goes to y'."  So, if you see an alist in
; lst2 that is replacing x by x', one might be tempted to augment it
; by replacing y by y'.  However, what if x is just an accumulator?
; The role of vars is to specify upon which variables two
; substitutions must agree in order to be merged.  Usually, vars
; consists of the measured variables.

; So now we get a little more technical.  We will try to "merge" each
; alist1 from lst1 into each alist2 from lst2 (preserving the case structure
; of lst2).  If alist1 and alist2 do not agree on vars then their merge
; is just alist2.  If they do agree on vars, then their merge is their
; union, provided that is a substitution.  It may fail to be a substitution
; because the two alists disagree on some other variable.  In that case
; we say the two are irreconcilable.  We now give three simple examples:

; Let vars be {x}.  Let alist2 be {(x . x') (z . z')}.  If alist1 maps
; x to x'', then their merge is just alist2 because alist1 is
; addressing a different case of the induction.  If alist1 maps x to x'
; and y to y', then their merge is {(x . x') (y . y') (z . z')}.  If
; alist1 maps x to x' and z to z'', then the two are irreconcilable.
; Two irreconcilable alists that agree on vars are called "antagonists"
; because they "want" to merge but can't.  We cannot merge lst1 into lst2
; if they have an antagonistic pair between them.  If an antagonistic pair
; is discovered, the entire merge operation fails.

; Now we will successively consider each alist1 in lst1 and merge it
; into lst2, forming successive lst2's.  We insist that each alist1 of
; lst1 have at least one mate in lst2 with which it agrees and is
; reconcilable.  (Otherwise, we could merge completely disjoint
; substitutions.)

; Because we try the alist1's successively, each alist1 is actually
; merged into the lst2 produced by all the previous alist1's.  That
; produces an apparent order dependence.  However, this is avoided by
; the requirement that we never produce antagonistic pairs.

; For example, suppose that in one case of lst1, x is mapped to x' and
; y is mapped to y', but in another case x is mapped to x' and y is
; mapped to y''.  Now imagine trying to merge that lst1 into a lst2 in
; which x is mapped to x' and z is mapped to z'.  The first alist of
; lst1 extends lst2 to (((x . x') (y . y') (z . z'))).  But the second
; alist is then antagonistic.  The same thing happens if we tried the two
; alists of lst1 in the other order.  Thus, the above lst1 cannot be merged
; into lst2.  Note that they can be merged in the other order!  That is,
; lst2 can be merged into lst1, because the case structure of lst1 is
; richer.

; We can detect the situation above without forming the intermediate
; lst2.  In particular, if lst1 contains an antagonistic pair, then it
; cannot be merged with any lst2 and we can quit.

; Note: Once upon a time, indeed, for the first 20 years or so of the
; existence of the merge routine, we took the attitude that if
; irreconcilable but agreeable alists arose, then we just added to
; alist2 those pairs of alist1 that were reconcilable and we left out
; the irreconcilable pairs.  This however resulted in the system often
; merging complicated accumulator using functions (like TAUTOLOGYP)
; into simpler functions (like NORMALIZEDP) by dropping the
; accumulators that got in the way.  This idea of just not doing
; "hostile merges" is being tried out for the first time in ACL2.

  (cond ((antagonistic-tests-and-alists-lstp lst1 vars) nil)
        ((antagonistic-tests-and-alists-lstsp lst1 lst2 vars) nil)
        ((not (every-alist1-matedp lst1 lst2 vars)) nil)
        (t (merge-lst1-into-lst2 lst1 lst2 vars))))

(defun merge-cand1-into-cand2 (cand1 cand2)

; Can induction candidate cand1 be merged into cand2?  If so, return
; their merge.  The guts of this function is merge-tests-and-alists-
; lsts.  The tests preceding it are heuristic only.  If
; merge-tests-and-alists-lsts returns non-nil, then it returns a sound
; induction; indeed, it merely extends some of the substitutions in
; the second candidate.

  (let ((vars (or (intersection-eq
                   (access candidate cand1 :controllers)
                   (intersection-eq
                    (access candidate cand2 :controllers)
                    (intersection-eq
                     (access candidate cand1 :changed-vars)
                     (access candidate cand2 :changed-vars))))
                  (intersection-eq
                   (access candidate cand1 :changed-vars)
                   (access candidate cand2 :changed-vars)))))

; Historical Plaque from Nqthm:

; We once merged only if both cands agreed on the intersection of the
; changed-vars.  But the theorem that, under suitable conditions, (EV
; FLG X VA FA N) = (EV FLG X VA FA K) made us realize it was important
; only to agree on the intersection of the controllers.  Note in fact
; that we mean the changing controllers -- there seems to be no need
; to merge two inductions if they only share unchanging controllers.
; However the theorem that (GET I (SET J VAL MEM)) = ... (GET I MEM)
; ...  illustrates the situation in which the controllers, {I} and {J}
; do not even overlap; but the accumulators {MEM} do and we want a
; merge.  So we want agreement on the intersection of the changing
; controllers (if that is nonempty) or on the accumulators.

; For soundness it does not matter what list of vars we want to agree
; on because no matter what, merge-tests-and-alists-lsts returns
; either nil or an extension of the second candidate's alists.

    (cond
     ((and vars
           (not (intersectp-eq (access candidate cand1 :unchangeable-vars)
                               (access candidate cand2 :changed-vars)))
           (not (intersectp-eq (access candidate cand2 :unchangeable-vars)
                               (access candidate cand1 :changed-vars))))
      (let ((temp (merge-tests-and-alists-lsts
                   (access candidate cand1 :tests-and-alists-lst)
                   (access candidate cand2 :tests-and-alists-lst)
                   vars)))
        (cond (temp
               (make candidate
                     :score (+ (access candidate cand1 :score)
                               (access candidate cand2 :score))
                     :controllers (union-eq
                                   (access candidate cand1 :controllers)
                                   (access candidate cand2 :controllers))
                     :changed-vars (union-eq
                                    (access candidate cand1 :changed-vars)
                                    (access candidate cand2 :changed-vars))
                     :unchangeable-vars (union-eq
                                         (access candidate cand1
                                                 :unchangeable-vars)
                                         (access candidate cand2
                                                 :unchangeable-vars))
                     :tests-and-alists-lst temp
                     :justification (access candidate cand2 :justification)
                     :induction-term (access candidate cand2 :induction-term)
                     :other-terms (add-to-set-equal
                                   (access candidate cand1 :induction-term)
                                   (union-equal
                                    (access candidate cand1 :other-terms)
                                    (access candidate cand2 :other-terms)))
                     :xinduction-term (access candidate cand2 :xinduction-term)
                     :xother-terms (add-to-set-equal
                                    (access candidate cand1 :xinduction-term)
                                    (union-equal
                                     (access candidate cand1 :xother-terms)
                                     (access candidate cand2 :xother-terms)))
                     :xancestry (cond
                                ((equal temp
                                        (access candidate cand2
                                                :tests-and-alists-lst))
                                 (access candidate cand2 :xancestry))
                                (t (add-to-set-equal
                                    (access candidate cand1 :xinduction-term)
                                    (union-equal
                                     (access candidate cand1 :xancestry)
                                     (access candidate cand2 :xancestry)))))

; Note that :xancestry, computed just above, may not reflect cand1, but we
; always include the :ttree of cand1 just below.  This is deliberate, since
; cand1 is contributing to the :score, and hence the eventual induction scheme
; chosen; so we want to report its induction rules in the final proof.

                     :ttree (cons-tag-trees (access candidate cand1 :ttree)
                                            (access candidate cand2 :ttree))))
              (t nil))))
     (t nil))))

(defun merge-candidates (cand1 cand2)

; This function determines whether one of the two induction candidates
; can be merged into the other.  If so, it returns their merge.  This
; function is a mate and merge function used by m&m and is hence known
; to m&m-apply.

  (or (merge-cand1-into-cand2 cand1 cand2)
      (merge-cand1-into-cand2 cand2 cand1)))

; We now move from merging to flawing.  The idea is to determine which
; inductions get in the way of others.



(defun controller-variables1 (args controller-pocket)

; Controller-pocket is a list of t's and nil's in 1:1 correspondence with
; args, indicating which args are controllers.  We collect those controller
; args that are variable symbols.

  (cond ((null controller-pocket) nil)
        ((and (car controller-pocket)
              (variablep (car args)))
         (add-to-set-eq (car args)
                        (controller-variables1 (cdr args)
                                               (cdr controller-pocket))))
        (t (controller-variables1 (cdr args)
                                  (cdr controller-pocket)))))

(defun controller-variables (term controller-alist)

; Controller-alist comes from the def-body of the function symbol, fn, of term.
; Recall that controller-alist is an alist that associates with each function
; in fn's mutually recursive clique the controller pockets used in a given
; justification of the clique.  In induction, as things stand today, we know
; that fn is singly recursive because we don't know how to handle mutual
; recursion yet.  But no use is made of that here.  We collect all the
; variables in controller slots of term.

  (controller-variables1 (fargs term)
                         (cdr (assoc-eq (ffn-symb term)
                                        controller-alist))))

(defun induct-vars1 (lst wrld)

; Lst is a list of terms.  We collect every variable symbol occurring in a
; controller slot of any term in lst.

  (cond ((null lst) nil)
        (t (union-eq
            (controller-variables
             (car lst)
             (access def-body
                     (original-def-body (ffn-symb (car lst)) wrld)
                     :controller-alist))
            (induct-vars1 (cdr lst) wrld)))))

(defun induct-vars (cand wrld)

; Historical Plaque from Nqthm:

;   Get all skos occupying controller slots in any of the terms associated
;   with this candidate.

; The age of that comment is not known, but the fact that we referred
; to the variables as "skos" (Skolem constants) suggests that it may
; date from the Interlisp version.  Meta comment: Perhaps someday some
; enterprising PhD student (in History?) will invent Software
; Archaeology, in which decrepit fragments of archive tapes are pieced
; together and scrutinized for clues as to the way people thought back
; in the early days.

  (induct-vars1 (cons (access candidate cand :induction-term)
                      (access candidate cand :other-terms))
                wrld))

(defun vetoedp (cand vars lst changed-vars-flg)

; Vars is a list of variables.  We return t iff there exists a candidate
; in lst, other than cand, whose unchangeable-vars (or, if changed-vars-flg,
; changed-vars or unchangeable-vars) intersect with vars.

; This function is used both by compute-vetoes1, where flg is t and
; vars is the list of changing induction vars of cand, and by
; compute-vetoes2, where flg is nil and vars is the list of
; changed-vars cand.  We combine these two into one function simply to
; eliminate a definition from the system.

  (cond ((null lst) nil)
        ((equal cand (car lst))
         (vetoedp cand vars (cdr lst) changed-vars-flg))
        ((and changed-vars-flg
              (intersectp-eq vars
                             (access candidate (car lst) :changed-vars)))
         t)
        ((intersectp-eq vars
                        (access candidate (car lst) :unchangeable-vars))
         t)
        (t (vetoedp cand vars (cdr lst) changed-vars-flg))))

(defun compute-vetoes1 (lst cand-lst wrld)

; Lst is a tail of cand-lst.  We throw out from lst any candidate
; whose changing induct-vars intersect the changing or unchanging vars
; of another candidate in cand-lst.  We assume no two elements of
; cand-lst are equal, an invariant assured by the fact that we have
; done merging and flushing before this.

  (cond ((null lst) nil)
        ((vetoedp (car lst)
                  (intersection-eq
                   (access candidate (car lst) :changed-vars)
                   (induct-vars (car lst) wrld))
                  cand-lst
                  t)
         (compute-vetoes1 (cdr lst) cand-lst wrld))
        (t (cons (car lst)
                 (compute-vetoes1 (cdr lst) cand-lst wrld)))))

; If the first veto computation throws out all candidates, we revert to
; another heuristic.

(defun compute-vetoes2 (lst cand-lst)

; Lst is a tail of cand-lst.  We throw out from lst any candidate
; whose changed-vars intersect the unchangeable-vars of another
; candidate in cand-lst.  Again, we assume no two elements of cand-lst
; are equal.

  (cond ((null lst) nil)
        ((vetoedp (car lst)
                  (access candidate (car lst) :changed-vars)
                  cand-lst
                  nil)
         (compute-vetoes2 (cdr lst) cand-lst))
        (t (cons (car lst)
                 (compute-vetoes2 (cdr lst) cand-lst)))))

(defun compute-vetoes (cand-lst wrld)

; We try two different techniques for throwing out candidates.  If the
; first throws out everything, we try the second.  If the second throws
; out everything, we throw out nothing.

; The two are: (1) throw out a candidate if its changing induct-vars
; (the variables in control slots that change) intersect with either
; the changed-vars or the unchangeable-vars of another candidate.  (2)
; throw out a candidate if its changed-vars intersect the
; unchangeable-vars of another candidate.

; Historical Plaque from Nqthm:

;   This function weeds out "unclean" induction candidates.  The
;   intuition behind the notion "clean" is that an induction is clean
;   if nobody is competing with it for instantiation of its variables.
;   What we actually do is throw out any candidate whose changing
;   induction variables -- that is the induction variables as computed
;   by induct-vars intersected with the changed vars of candidate --
;   intersect the changed or unchanged variables of another candidate.
;   The reason we do not care about the first candidates unchanging
;   vars is as follows.  The reason you want a candidate clean is so
;   that the terms riding on that cand will reoccur in both the
;   hypothesis and conclusion of an induction.  There are two ways to
;   assure (or at least make likely) this: change the variables in the
;   terms as specified or leave them constant.  Thus, if the first
;   cand's changing vars are clean but its unchanging vars intersect
;   another cand it means that the first cand is keeping those other
;   terms constant, which is fine. (Note that the first cand would be
;   clean here.  The second might be clean or dirty depending on
;   whether its changed vars or unchanged vars intersected the first
;   cand's vars.)  The reason we check only the induction vars and not
;   all of the changed vars is if cand1's changed vars include some
;   induction vars and some accumulators and the accumulators are
;   claimed by another cand2 we believe that cand1 is still clean.
;   The motivating example was

;   (IMPLIES (MEMBER A C) (MEMBER A (UNION1 B C)))

;   where the induction on C is dirty because the induction on B and C
;   claims C, but the induction on B and C is clean because the B does
;   not occur in the C induction.  We do not even bother to check the
;   C from the (B C) induction because since it is necessarily an
;   accumulator it is probably being constructed and thus, if it
;   occurs in somebody else's ind vars it is probably being eaten so
;   it will be ok.  In formulating this heuristic we did not consider
;   the possibility that the accums of one candidate occur as
;   constants in the other.  Oh well.

;   July 20, 1978.  We have added an additional heuristic, to be
;   applied if the above one eliminates all cands.  We consider a cand
;   flawed if it changes anyone else's constants.  The motivating
;   example was GREATEST-FACTOR-LESSP -- which was previously proved
;   only by virtue of a very ugly use of the no-op fn ID to make a
;   certain induction flawed.

  (or (compute-vetoes1 cand-lst cand-lst wrld)
      (compute-vetoes2 cand-lst cand-lst)
      cand-lst))

; The next heuristic is to select complicated candidates, based on
; support for non-primitive recursive function schemas.

(defun induction-complexity1 (lst wrld)

; The "function" induction-complexity does not exist.  It is a symbol
; passed to maximal-elements-apply which calls this function on the list
; of terms supported by an induction candidate.  We count the number of
; non pr fns supported.

  (cond ((null lst) 0)
        ((getpropc (ffn-symb (car lst)) 'primitive-recursive-defunp nil wrld)
         (induction-complexity1 (cdr lst) wrld))
        (t (1+ (induction-complexity1 (cdr lst) wrld)))))

; We develop a general-purpose function for selecting maximal elements from
; a list under a measure.  That function, maximal-elements, is then used
; with the induction-complexity measure to collect both the most complex
; inductions and then to select those with the highest scores.

(defun maximal-elements-apply (fn x wrld)

; This function must produce an integerp.  This is just the apply function
; for maximal-elements.

  (case fn
        (induction-complexity
         (induction-complexity1 (cons (access candidate x :induction-term)
                                      (access candidate x :other-terms))
                                wrld))
        (score (access candidate x :score))
        (otherwise 0)))

(defun maximal-elements1 (lst winners maximum fn wrld)

; We are scanning down lst collecting into winners all those elements
; with maximal scores as computed by fn.  Maximum is the maximal score seen
; so far and winners is the list of all the elements passed so far with
; that score.

  (cond ((null lst) winners)
        (t (let ((temp (maximal-elements-apply fn (car lst) wrld)))
             (cond ((> temp maximum)
                    (maximal-elements1 (cdr lst)
                                       (list (car lst))
                                       temp fn wrld))
; PETE
; In other versions the = below is, mistakenly, an int=!

                   ((= temp maximum)
                    (maximal-elements1 (cdr lst)
                                       (cons (car lst) winners)
                                       maximum fn wrld))
                   (t
                    (maximal-elements1 (cdr lst)
                                       winners
                                       maximum fn wrld)))))))

(defun maximal-elements (lst fn wrld)

; Return the subset of lst that have the highest score as computed by
; fn.  The functional parameter fn must be known to maximal-elements-apply.
; We reverse the accumulated elements to preserve the order used by
; Nqthm.

  (cond ((null lst) nil)
        ((null (cdr lst)) lst)
        (t (reverse
            (maximal-elements1 (cdr lst)
                               (list (car lst))
                               (maximal-elements-apply fn (car lst) wrld)
                               fn wrld)))))


; All that is left in the heuristic selection of the induction candidate is
; the function m&m that mates and merges arbitrary objects.  We develop that
; now.

; The following three functions are not part of induction but are
; used by other callers of m&m and so have to be introduced now
; so we can define m&m-apply and get on with induct.

(defun intersectp-eq/union-equal (x y)
  (cond ((intersectp-eq (car x) (car y))
         (cons (union-eq (car x) (car y))
               (union-equal (cdr x) (cdr y))))
        (t nil)))

(defun equal/union-equal (x y)
  (cond ((equal (car x) (car y))
         (cons (car x)
               (union-equal (cdr x) (cdr y))))
        (t nil)))

(defun subsetp-equal/smaller (x y)
  (cond ((subsetp-equal x y) x)
        ((subsetp-equal y x) y)
        (t nil)))

(defun m&m-apply (fn x y)

; This is a first-order function that really just applies fn to x and
; y, but does so only for a fixed set of fns.  In fact, this function
; handles exactly those functions that we give to m&m.

  (case fn
        (intersectp-eq/union-equal (intersectp-eq/union-equal x y))
        (equal/union-equal (equal/union-equal x y))
        (flush-candidates (flush-candidates x y))
        (merge-candidates (merge-candidates x y))
        (subsetp-equal/smaller (subsetp-equal/smaller x y))))

(defun count-off (n lst)

; Pair the elements of lst with successive integers starting at n.

  (cond ((null lst) nil)
        (t (cons (cons n (car lst))
                 (count-off (1+ n) (cdr lst))))))

(defun m&m-search (x y-lst del fn)

; Y-lst is a list of pairs, (id . y).  The ids are integers.  If id is
; a member of del, we think of y as "deleted" from y-lst.  That is,
; y-lst and del together characterize a list of precisely those y such
; that (id . y) is in y-lst and id is not in del.

; We search y-lst for the first y that is not deleted and that mates
; with x.  We return two values, the merge of x and y and the integer
; id of y.  If no such y exists, return two nils.

  (cond ((null y-lst) (mv nil nil))
        ((member (caar y-lst) del)
         (m&m-search x (cdr y-lst) del fn))
        (t (let ((z (m&m-apply fn x (cdar y-lst))))
             (cond (z (mv z (caar y-lst)))
                   (t (m&m-search x (cdr y-lst) del fn)))))))

(defun m&m1 (pairs del ans n fn)

; This is workhorse for m&m.  See that fn for a general description of
; the problem and the terminology.  Pairs is a list of pairs.  The car
; of each pair is an integer and the cdr is a possible element of the
; bag we are closing under fn.  Del is a list of the integers
; identifying all the elements of pairs that have already been
; deleted.  Abstractly, pairs and del together represent a bag we call
; the "unprocessed bag".  The elements of the unprocessed bag are
; precisely those ele such that (i . ele) is in pairs and i is not in
; del.

; Without assuming any properties of fn, this function can be
; specified as follows: If the first element, x, of the unprocessed
; bag, mates with some y in the rest of the unprocessed bag, then put
; the merge of x and the first such y in place of x, delete that y,
; and iterate.  If the first element has no such mate, put it in the
; answer accumulator ans.  N, by the way, is the next available unique
; identifier integer.

; If one is willing to make the assumptions that the mate and merge
; fns of fn are associative and commutative and have the distributive
; and non-preclusion properties, then it is possible to say more about
; this function.  The rest of this comment makes those assumptions.

; Ans is a bag with the property that no element of ans mates with any
; other element of ans or with any element of the unprocessed bag.  N
; is the next available unique identifier integer; it is always larger
; than any such integer in pairs or in del.

; Abstractly, this function closes B under fn, where B is the bag
; union of the unprocessed bag and ans.

  (cond
   ((null pairs) ans)
   ((member (caar pairs) del)
    (m&m1 (cdr pairs) del ans n fn))
   (t (mv-let (mrg y-id)
        (m&m-search (cdar pairs) (cdr pairs) del fn)
        (cond
         ((null mrg)
          (m&m1 (cdr pairs)
                del
                (cons (cdar pairs) ans)
                n fn))
         (t (m&m1 (cons (cons n mrg) (cdr pairs))
                  (cons y-id del)
                  ans
                  (1+ n)
                  fn)))))))

(defun m&m (bag fn)

; This function takes a bag and a symbol naming a dyadic function, fn,
; known to m&m-apply and about which we assume certain properties
; described below.  Let z be (m&m-apply fn x y).  Then we say x and y
; "mate" if z is non-nil.  If x and y mate, we say z is the "merge" of
; x and y.  The name of this function abbreviates the phrase "mate and
; merge".

; We consider each element, x, of bag in turn and seek the first
; successive element, y, that mates with it.  If we find one, we throw
; out both, add their merge in place of x and iterate.  If we find no
; mate for x, we deposit it in our answer accumulator.

; The specification above is explicit about the order in which we try
; the elements of the bag.  If we try to loosen the specification so
; that order is unimportant, we must require that fn have certain
; properties.  We discuss this below.

; First, note that we have implicitly assumed that mate and merge are
; commutative because we haven't said in which order we present the
; arguments.

; Second, note that if x doesn't mate with any y, we set it aside in
; our accumulating answer.  We do not even try to mate such an x with
; the offspring of the y's it didn't like.  This makes us order
; dependent.  For example, consider the bag {x y1 y2}.  Suppose x
; won't mate with either y1 or y2, but that y1 mates with y2 to
; produce y3 and x mates with y3 to produce y4.  Then if we seek mates
; for x first we find none and it gets into our final answer.  Then y1
; and y2 mate to form y3.  The final answer is hence {x y3}.  But if
; we seek mates for y1 first we find y2, produce y3, add it to the
; bag, forming {y3 x}, and then mate x with y3 to get the final answer
; {y4}.  This order dependency cannot arise if fn has the property
; that if x mates with the merge of y and z then x mates with either y
; or z.  This is called the "distributive" property of mate over merge.

; Third, note that if x does mate with y to produce z then we throw x
; out in favor of z.  Thus, x is not mated against any but the first
; y.  Thus, if we have {x y1 y2} and x mates with y1 to form z1 and x
; mates with y2 to form z2 and there are no other mates, then we can
; either get {z1 y2} or {z2 y1} as the final bag, depending on whether
; we mate x with y1 or y2.  This order dependency cannot arise if fn
; has the property that if x mates with y1 and x mates with y2, then
; (a) the merge of x and y1 mates with y2, and (b) merge has the
; "commutativity-2" (merge (merge x y1) y2) = (merge (merge x y2) y1).
; We call property (a) "non-preclusion" property of mate and merge,
; i.e., merging doesn't preclude mating.

; The commutativity-2 property is implied by associativity and (the
; already assumed commutativity).  Thus, another way to avoid the
; third order dependency is if legal merges are associative and have
; the non-preclusion property.

; Important Note: The commonly used fn of unioning together two alists
; that agree on the intersection of their domains, does not have the
; non-preclusion property!  Suppose x, y1, and y2 are all alists and
; all map A to 0.  Suppose in addition y1 maps B to 1 but y2 maps B to
; 2.  Finally, suppose x maps C to 3.  Then x mates with both y1 and
; y2.  But merging y1 into x precludes mating with y2 and vice versa.

; We claim, but do not prove, that if the mate and merge functions for
; fn are commutative and associative, and have the distributive and
; non-preclusion properties, then m&m is order independent.

; For efficiency we have chosen to implement deletion by keeping a
; list of the deleted elements.  But we cannot make a list of the
; deleted elements themselves because there may be duplicate elements
; in the bag and we need to be able to delete occurrences.  Thus, the
; workhorse function actually operates on a list of pairs, (i . ele),
; where i is a unique identification integer and ele is an element of
; the bag.  In fact we just assign the position of each occurrence to
; each element of the initial bag and thereafter count up as we
; generate new elements.
;
; See m&m1 for the details.

  (m&m1 (count-off 0 bag) nil nil (length bag) fn))

; We now develop a much more powerful concept, that of mapping m&m over the
; powerset of a set.  This is how we actually merge induction candidates.
; That is, we try to mash together every possible subset of the candidates,
; largest subsets first.  See m&m-over-powerset for some implementation
; commentary before going on.

(defun cons-subset-tree (x y)

; We are representing full binary trees of t's and nil's and
; collapsing trees of all nil's to nil and trees of all t's to t.  See
; the long comment in m&m-over-powerset.  We avoid consing when
; convenient.

  (if (eq x t)
      (if (eq y t)
          t
        (if y (cons x y) '(t)))
    (if x
        (cons x y)
      (if (eq y t)
          '(nil . t)
        (if y (cons x y) nil)))))

(defabbrev car-subset-tree (x)

; See cons-subset-tree.

  (if (eq x t) t (car x)))

(defabbrev cdr-subset-tree (x)

; See cons-subset-tree.

  (if (eq x t) t (cdr x)))

(defun or-subset-trees (tree1 tree2)

; We disjoin the tips of two binary t/nil trees.  See cons-subset-tree.

  (cond ((or (eq tree1 t)(eq tree2 t)) t)
        ((null tree1) tree2)
        ((null tree2) tree1)
        (t (cons-subset-tree (or-subset-trees (car-subset-tree tree1)
                                              (car-subset-tree tree2))
                             (or-subset-trees (cdr-subset-tree tree1)
                                              (cdr-subset-tree tree2))))))

(defun m&m-over-powerset1 (st subset stree ans fn)

; See m&m-over-powerset.

  (cond
   ((eq stree t) (mv t ans))
   ((null st)
    (let ((z (m&m subset fn)))
      (cond ((and z (null (cdr z)))
             (mv t (cons (car z) ans)))
            (t (mv nil ans)))))
   (t
    (mv-let (stree1 ans1)
      (m&m-over-powerset1 (cdr st)
                          (cons (car st) subset)
                          (cdr-subset-tree stree)
                          ans fn)
      (mv-let (stree2 ans2)
        (m&m-over-powerset1 (cdr st)
                            subset
                            (or-subset-trees
                             (car-subset-tree stree)
                             stree1)
                            ans1 fn)
        (mv (cons-subset-tree stree2 stree1) ans2))))))

(defun m&m-over-powerset (st fn)

; Fn is a function known to m&m-apply.  Let (fn* s) be defined to be z,
; if (m&m s fn) = {z} and nil otherwise.  Informally, (fn* s) is the
; result of somehow mating and merging all the elements of s into a single
; object, or nil if you can't.

; This function applies fn* to the powerset of st and collects all those
; non-nil values produced from maximal s's.  I.e., we keep (fn* s) iff it
; is non-nil and no superset of s produces a non-nil value.

; We do this amazing feat (recall that the powerset of a set of n
; things contains 2**n subsets) by generating the powerset in order
; from largest to smallest subsets and don't generate or test any
; subset under a non-nil fn*.  Nevertheless, if the size of set is
; very big, this function will get you.

; An informal specification of this function is that it is like m&m
; except that we permit an element to be merged into more than one
; other element (but an element can be used at most once per final
; element) and we try to maximize the amount of merging we can do.

; For example, if x mates with y1 to form z1, and x mates with y2 to
; form z2, and no other mates occur, then this function would
; transform {x y1 y2} into {z1 z2}.  It searches by generate and test:

;       s            (fn* s)
;    (x y1 y2)         nil
;    (x y1)            z1
;    (x y2)            z2
;    (x)              subsumed
;    (y1 y2)           nil
;    (y1)             subsumed
;    (y2)             subsumed
;    nil              subsumed

; Here, s1 is "subsumed" by s2 means s1 is a subset of s2.  (Just the
; opposite technical definition but exactly the same meaning as in the
; clausal sense.)

; The way we generate the powerset elements is suggested by the
; following trivial von Neumann function, ps, which, when called as in
; (ps set nil), calls PROCESS on each member of the powerset of set,
; in the order in which we generate them:

; (defun ps (set subset)
;  (cond ((null set) (PROCESS subset))
;        (t (ps (cdr set) (cons (car set) subset))   ;rhs
;           (ps (cdr set) subset))))                 ;lhs

; By generating larger subsets first we know that if a subset subsumes
; the set we are considering then that subset has already been
; considered.  Therefore, we need a way to keep track of the subsets
; with non-nil values.  We do this with a "subset tree".  Let U be the
; universe of objects in some order.  Then the full binary tree with
; depth |U| can be thought of as the powerset of U.  In particular,
; any branch through the tree, from top-most node to tip, represents a
; subset of U by labeling the nodes at successive depth by the
; successive elements of U (the topmost node being labeled with the
; first element of U) and adopting the convention that taking a
; right-hand (cdr) branch at a node indicates that the label is in the
; subset and a left-hand (car) branch indicates that the label is not
; in the subset.  At the tip of the tree we store a T indicating that
; the subset had a non-nil value or a NIL indicating that it had a nil
; value.

; For storage efficiency we let nil represent an arbitrarily deep full
; binary tree will nil at every tip and we let t represent the
; analogous trees with t at every tip.  Car-subset-tree,
; cdr-subset-tree and cons-subset-tree implement these abstractions.

; Of course, we don't have the tree when we start and we generate it
; as we go.  That is a really weird idea because generating the tree
; that tells us who was a subset of whom in the past seems to have little
; use as we move forward.  But that is not true.

; Observe that there is a correspondence between these trees and the
; function ps above for generating the power set.  The recursion
; labeled "rhs" above is going down the right-hand side of the tree
; and the "lhs" recursion is going down the left-hand side.  Note that
; we go down the rhs first.

; The neat fact about these trees is that there is a close
; relationship between the right-hand subtree (rhs) and left-hand
; subtree (lhs) of any given node of the tree: lhs can be obtained
; from rhs by turning some nils into ts.  The reason is that the tips
; of the lhs of a node labeled by x denote exactly the same subsets
; as the corresponding tips of the right-hand side, except that on the
; right x was present in the subset and on the left it is not.  So
; when we do the right hand side we come back with a tree and if we
; used that very tree for the left hand side (interpreting nil as
; meaning "compute it and see" and t as meaning "a superset of this
; set has non-nil value") then it is correct.  But we can do a little
; better than that because we might have come into this node with a
; tree (i.e., one to go into the right hand side with and another to go
; into the left hand side with) and so after we have gone into the
; right and come back with its new tree, we can disjoin the output of
; the right side with the input for the left side to form the tree we
; will actually use to explore the left side.

  (mv-let (stree ans)
    (m&m-over-powerset1 st nil nil nil fn)
    (declare (ignore stree))
    ans))

; Now we work on the selection of q for the induction suggested by a
; semi-concrete do$.

(defun select-do$-induction-q-seedp1 (lit xterms)
  (cond
   ((endp xterms) t)
   ((occur (car xterms) lit)
    nil)
   (t (select-do$-induction-q-seedp1 lit (cdr xterms)))))

(defun select-do$-induction-q-seedp (lit xterms mvars)
  (and (subsetp-eq (all-vars lit) mvars)
       (if (eq xterms :DO$)
           (not (ffnnamep 'DO$ lit))
           (select-do$-induction-q-seedp1 lit xterms))))

(defun select-do$-induction-q-seed (cl xterms mvars)
  (cond
   ((endp cl) nil)
   ((select-do$-induction-q-seedp (car cl) xterms mvars)
    (cons (car cl) (select-do$-induction-q-seed (cdr cl) xterms mvars)))
   (t (select-do$-induction-q-seed (cdr cl) xterms mvars))))

(defun select-do$-induction-q-filterp (lit cl-set)
; Return t iff lit is in every element of cl-cset.
  (cond
   ((endp cl-set) t)
   ((member-equal lit (car cl-set))
    (select-do$-induction-q-filterp lit (cdr cl-set)))
   (t nil)))

(defun select-do$-induction-q-filter (seed cl-set)
  (cond
   ((endp seed) nil)
   ((select-do$-induction-q-filterp (car seed) cl-set)
    (cons (car seed)
          (select-do$-induction-q-filter (cdr seed) cl-set)))
   (t (select-do$-induction-q-filter (cdr seed) cl-set))))

(defun select-do$-induction-q (cl-set xterms mterm)

; Cl-set is a set of clauses we're proving by induction, a do$ induction has
; been chosen and it was suggested by the terms in xterms (unless xterms is
; :DO$).  Mterm is the measure term.  We return a list of literals that should
; be unioned into the measure conjecture to be generated.  The :DO$ case is
; explained below.

; The conjunction of the negations of the literals returned is what we call Q
; in our do$ induction scheme.  We describe its use and the choice of Q below.
; But for example, a typical Q might be (AND (NATP I) (NATP J)) which is
; represented here by the list ((NOT (NATP I)) (NOT (NATP J))).  Note that by
; unioning the list of literals to a clause we're really adding the hypothesis
; Q to the clause.

; When we generate the measure clauses for a DO$ induction we augment the
; clauses with a predicate, Q, extracted from the clauses, cl-set, being
; proved.  We can choose any set of literals provided we obey the ``inclusion
; rule:'' every literal is a member of each clause.  The consequences of
; choosing poorly -- as long as we obey the inclusion rule -- is that we won't
; be able to justify the induction (i.e., the proof attempt employing this
; induction will fail).  C'est la vie.  Use a :hint!

; The heuristic behind our choice is to restrict the types of the variables
; mentioned in the measure.  The inclusion rule is necessary for the soundness
; of our implementation: Technically, the induction scheme we're using requires
; us to prove (implies (not q) p), but the inclusion rule guarantees that this
; is a tautology.  So we don't even generate that proof obligation and thus we
; must be careful to obey the rule!

; Our algorithm is to collect from the first clause in cl-set all the literals
; that mention only variables in the measure but that do not contain any of the
; xterms.  If xterms is :DO$ it is interpreted to mean the list of every DO$
; term in the conjecture.  That is, if xterms is :DO$ we exclude from Q any
; term containing any call of DO$.  Note that we'll collect literals that
; mention NO variables, e.g., warrants.  Call the resulting set of literals the
; ``seed.''  Then we'll throw out of the seed any literal that is not mentioned
; in all the other clauses.  We call this ``filtering'' the seed and it
; guarantees the ``inclusion rule.''

  (let* ((mvars (all-vars mterm))
         (seed (select-do$-induction-q-seed (car cl-set) xterms mvars)))
    (select-do$-induction-q-filter seed (cdr cl-set))))

(defun do$-induction-measure-clauses1 (negated-tests alist-lst mterm)
  (cond
   ((endp alist-lst) nil)
   (t (cons (append negated-tests
                    (list (cons-term* 'L<
                                      (sublis-var (car alist-lst) mterm)
                                      mterm)))
            (do$-induction-measure-clauses1 negated-tests (cdr alist-lst) mterm)))))

(defun do$-induction-measure-clauses (ta-lst q-lst mterm)

; Note: We considered using union-equal instead of append but all the tests are
; distinct and so are the alists, so union-equal would find no duplications.

  (cond
   ((endp ta-lst) nil)
   (t (append (do$-induction-measure-clauses1
               (union-equal q-lst
                            (dumb-negate-lit-lst
                             (access tests-and-alists (car ta-lst) :tests)))
               (access tests-and-alists (car ta-lst) :alists)
               mterm)
              (do$-induction-measure-clauses (cdr ta-lst) q-lst mterm)))))

; Ok, so now we have finished the selection process and we begin the
; construction of the induction formula itself.

(defun all-picks2 (pocket pick ans)
; See all-picks.
  (cond ((null pocket) ans)
        (t (cons (cons (car pocket) pick)
                 (all-picks2 (cdr pocket) pick ans)))))

(defun all-picks2r (pocket pick ans)
; See all-picks.
  (cond ((null pocket) ans)
        (t (all-picks2r (cdr pocket) pick
                        (cons (cons (car pocket) pick) ans)))))

(defun all-picks1 (pocket picks ans rflg)
; See all-picks.
  (cond ((null picks) ans)
        (t (all-picks1 pocket (cdr picks)
                       (if rflg
                           (all-picks2r pocket (car picks) ans)
                         (all-picks2 pocket (car picks) ans))
                       rflg))))

(defun all-picks (pockets rflg)

; Pockets is a list of pockets, each pocket containing 0 or more
; objects.  We return a list of all the possible ways you can pick one
; thing from each pocket.  If rflg is nil initially, then the order of
; the resulting list is exactly the same as it was in Nqthm.  There is
; not much else to recommend this particular choice of definition!

; Historical Plaque from Nqthm:

;   (DEFUN ALL-PICKS (POCKET-LIST)
;    (COND ((NULL POCKET-LIST) (LIST NIL))
;          (T (ITERATE FOR PICK IN (ALL-PICKS (CDR POCKET-LIST))
;                      NCONC (ITERATE FOR CHOICE IN (CAR POCKET-LIST)
;                                     COLLECT (CONS CHOICE PICK))))))

; Nqthm's construction is a very natural recursive one, except that it
; used nconc to join together the various segments of the answer.  If
; we tried the analogous construction here we would have to append the
; segments together and copy a very long list.  So we do it via an
; accumulator.  The trouble however is that we reverse the order of
; the little buckets in our answer every time we process a pocket.  We
; could avoid that if we wanted to recurse down the length of our
; answer on recursive calls, but we were afraid of running out of
; stack, and so we have coded this with tail recursion only.  We do
; non-tail recursion only over short things like individual pockets or
; the list of pockets.  And so to (a) avoid unnecessary copying, (b)
; non-tail recursion, and (c) constructing our answer in a different
; order, we introduced rflg.  Rflg causes us either to reverse or not
; reverse a certain intermediate result every other recursion.  It
; would be reassuring to see a mechanically checked proof that this
; definition of all-picks is equivalent to Nqthm's.

  (cond ((null pockets) '(nil))
        (t (all-picks1 (car pockets)
                       (all-picks (cdr pockets) (not rflg))
                       nil
                       rflg))))



(defun dumb-negate-lit-lst-lst (cl-set)

; We apply dumb-negate-lit-lst to every list in cl-set and collect the
; result.  You can think of this as negating a clause set (i.e., an
; implicit conjunction of disjunctions), but you have to then imagine
; that the implicit "and" at the top has been turned into an "or" and
; vice versa at the lower level.

  (cond ((null cl-set) nil)
        (t (cons (dumb-negate-lit-lst (car cl-set))
                 (dumb-negate-lit-lst-lst (cdr cl-set))))))

(defun induction-hyp-clause-segments2 (alists cl ans)
; See induction-hyp-clause-segments1.
  (cond ((null alists) ans)
        (t (cons (sublis-var-lst (car alists) cl)
                 (induction-hyp-clause-segments2 (cdr alists) cl ans)))))

(defun induction-hyp-clause-segments1 (alists cl-set ans)

; This function applies all of the substitutions in alists to all of
; the clauses in cl-set and appends the result to ans to create one
; list of instantiated clauses.

  (cond ((null cl-set) ans)
        (t (induction-hyp-clause-segments2
            alists
            (car cl-set)
            (induction-hyp-clause-segments1 alists (cdr cl-set) ans)))))

(defun induction-hyp-clause-segments (alists cl-set)

; Cl-set is a set of clauses.  We are trying to prove the conjunction
; over that set, i.e., cl1 & cl2 ... & clk, by induction.  We are in a
; case in which we can assume every instance under alists of that
; conjunction.  Thus, we can assume any lit from cl1, any lit from
; cl2, etc., instantiated via all of the alists.  We wish to return a
; list of clause segments.  Each segment will be spliced into the a
; clause we are trying to prove and together the resulting set of
; clauses is supposed to be equivalent to assuming all instances of
; the conjunction over cl-set.

; So one way to create the answer would be to first instantiate each
; of the k clauses with each of the n alists, getting a set of n*k
; clauses.  Then we could run all-picks over that, selecting one
; literal from each of the instantiated clauses to assume.  Then we'd
; negate each literal within each pick to create a clause hypothesis
; segment.  That is nearly what we do, except that we do the negation
; first so as to share structure among the all-picks answers.


; Note: The code below calls (dumb-negate-lit lit) on each lit.  Nqthm
; used (negate-lit lit nil ...) on each lit, employing
; negate-lit-lst-lst, which has since been deleted but was strictly
; analogous to the dumb version called below.  But since the
; type-alist is nil in Nqthm's call, it seems unlikely that the
; literal will be decided by type-set.  We changed to dumb-negate-lit
; to avoid having to deal both with ttrees and the enabled structure
; implicit in type-set.

  (all-picks
   (induction-hyp-clause-segments1 alists
                                   (dumb-negate-lit-lst-lst cl-set)
                                   nil)
   nil))

(defun induction-formula3 (neg-tests hyp-segments cl ans)

; Neg-tests is the list of the negated tests of an induction
; tests-and-alists entry.  hyp-segments is a list of hypothesis clause
; segments (i.e., more negated tests), and cl is a clause.  For each
; hyp segment we create the clause obtained by disjoining the tests,
; the segment, and cl.  We conjoin the resulting clauses to ans.

; See induction-formula for a comment about this iteration.

  (cond
   ((null hyp-segments) ans)
   (t (induction-formula3 neg-tests
                          (cdr hyp-segments)
                          cl
                          (conjoin-clause-to-clause-set

; Historical Plaque from Nqthm:

;   We once implemented the idea of "homographication" in which we combined
;   both induction, opening up of the recursive fns in the conclusion, and
;   generalizing away some recursive calls.  This function did the expansion
;   and generalization.  If the idea is reconsidered the following theorems are
;   worthy of consideration:

;       (ORDERED (SORT X)),
;       (IMPLIES (ORDERED X)
;                (ORDERED (ADDTOLIST I X))),
;       (IMPLIES (AND (NUMBER-LISTP X)
;                     (ORDERED X)
;                     (NUMBERP I)
;                     (NOT (< (CAR X) I)))
;                (EQUAL (ADDTOLIST I X) (CONS I X))), and
;       (IMPLIES (AND (NUMBER-LISTP X) (ORDERED X)) (EQUAL (SORT X) X)).

; Observe that we simply disjoin the negated tests, hyp segments, and clause.
; Homographication further manipulated the clause before adding it to the
; answer.
                           (disjoin-clauses
                            neg-tests
                            (disjoin-clauses (car hyp-segments) cl))
                           ans)))))

(defun induction-formula2 (cl cl-set ta-lst ans)

; Cl is a clause in cl-set, which is a set of clauses we are proving
; by induction.  Ta-lst is the tests-and-alists-lst component of the
; induction candidate we are applying to prove cl-set.  We are now
; focused on the proof of cl, using the induction schema of ta-lst
; but getting to assume all the clauses in cl-set in our induction
; hypothesis.  We will map across ta-lst, getting a set of tests and
; some alists at each stop, and for each stop add a bunch of clauses
; to ans.

  (cond
   ((null ta-lst) ans)
   (t (induction-formula2 cl cl-set (cdr ta-lst)
                          (induction-formula3

; Note:  Nqthm used (negate-lit-lst ... nil ...), but since the
; type-alist supplied was nil, we decided it was probably no buying us
; much -- not as much as passing up the ttrees would cost in terms of
; coding work!

                           (dumb-negate-lit-lst
                            (access tests-and-alists (car ta-lst) :tests))
                           (induction-hyp-clause-segments
                            (access tests-and-alists (car ta-lst) :alists)
                            cl-set)
                           cl
                           ans)))))

(defun induction-formula1 (lst cl-set ta-lst ans)

; Lst is a tail of cl-set.  Cl-set is a set of clauses we are trying to prove.
; Ta-lst is the tests-and-alists-lst component of the induction candidate
; we wish to apply to cl-set.  We map down lst forming a set of clauses
; for each cl in lst.  Basically, the set we form for cl is of the form
; ... -> cl, where ... involves all the case analysis under the tests in
; ta-lst and all the induction hypotheses from cl-set under the alists in
; each test-and-alists.  We add our clauses to ans.

  (cond
   ((null lst) ans)
   (t (induction-formula1 (cdr lst) cl-set ta-lst
                          (induction-formula2 (car lst)
                                              cl-set ta-lst ans)))))

(defun induction-formula (cl-set induction-term xterms measure-term ta-lst)

; Cl-set is a set of clauses we are to try to prove by induction, applying the
; inductive scheme suggested by induction-term, said scheme being described by
; the tests-and-alists-lst, ta-lst.  Measure-term is the measure term for the
; function symbol of induction-term but is only relevant if that function
; symbol is *do$-induction-fn*.  And no formal term has that function symbol!
; So if you're calling induction-formula on a genuine formal term, you may use
; nil for the measure-term.  The value of *do$-induction-fn* is in fact a
; keyword and is used in the induction term when the actual term was a DO$ with
; explicit quoted measures and body lambdas as explored by
; intrinsic-suggested-induction-cand-do$.

; The following historical plaque tells all, except for the fact that when the
; induction-term is in fact a call of *do$-induction-term* we add to the proof
; obligations the measure conjectures stemming from the DO$'s call.

; Historical Plaque from Nqthm:

;   TESTS-AND-ALISTS-LST is a such a list that the disjunction of the
;   conjunctions of the TESTS components of the members is T.  Furthermore,
;   there exists a measure M, a well-founded relation R, and a sequence of
;   variables x1, ..., xn such that for each T&Ai in TESTS-AND-ALISTS-LST, for
;   each alist alst in the ALISTS component of T&Ai, the conjunction of the
;   TESTS component, say qi, implies that (R (M x1 ... xn)/alst (M x1 ... xn)).

;   To prove thm, the conjunction of the disjunctions of the members of CL-SET,
;   it is sufficient, by the principle of induction, to prove instead the
;   conjunction of the terms qi & thm' & thm'' ...  -> thm, where the primed
;   terms are the results of substituting the alists in the ALISTS field of the
;   ith member of TESTS-AND-ALISTS-LST into thm.

;   If thm1, thm2, ..., thmn are the disjunctions of the members of CL-SET,
;   then it is sufficient to prove all of the formulas qi & thm' & thm'' ...
;   -> thmj.  This is a trivial proposition fact, to prove (IMPLIES A (AND B
;   C)) it is sufficient to prove (IMPLIES A B) and (IMPLIES A C).

;   The (ITERATE FOR PICK ...)* expression below returns a list of
;   clauses whose conjunction propositionally implies qi & thm' &
;   thm'' ...  -> thmj, where TA is the ith member of
;   TESTS-AND-ALISTS-LST and CL is the jth member of CL-SET.  Proof:
;   Let THM have the form:
;
;        (AND (OR a1 ...)
;             (OR b1 ...)
;             ...
;             (OR z1 ...)).

;   Then qi & thm' & thm'' ... -> thmj has the form:

;       (IMPLIES (AND qi
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... ))'
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... ))''
;                     ...
;                     (AND (OR a1 ... )
;                          (OR b1 ... )
;                          ...
;                          (OR z1 ... )))'''...'
;                thmj).
;
;   Suppose this formula is false for some values of the free variables.  Then
;   under those values, each disjunction in the hypothesis is true.  Thus there
;   exists a way of choosing one literal from each of the disjunctions, all of
;   which are true.  This choice is one of the PICKs below.  But we prove that
;   (IMPLIES (AND qi PICK) thmj).

; Note: The (ITERATE FOR PICK ...) expression mentioned above is the function
; induction-formula3 above.

  (let* ((ans1 (reverse
                (induction-formula1 cl-set cl-set ta-lst nil)))
         (ans2 (if (and (consp induction-term)
                        (eq (ffn-symb induction-term) *do$-induction-fn*))
                   (append
                    (do$-induction-measure-clauses
                     ta-lst
                     (select-do$-induction-q cl-set xterms measure-term)
                     measure-term)
                    ans1)
                   ans1)))
    (m&m ans2 'subsetp-equal/smaller)))

; Because the preceding computation is potentially explosive we will
; sometimes reduce its complexity by shrinking the given clause set to
; a singleton set containing a unit clause.  To decide whether to do that
; we will use the following rough measures:

(defun all-picks-size (cl-set)

; This returns the size of the all-picks computed by induction-formula3.

  (cond ((null cl-set) 1)
        (t (* (length (car cl-set)) (all-picks-size (cdr cl-set))))))

(defun induction-formula-size1 (hyps-size concl-size ta-lst)

; We determine roughly the number of clauses that ta-lst will generate when
; the number of all-picks through the hypotheses is hyps-size and the
; number of conclusion clauses is concl-size.  The individual cases of
; the tests-and-alists combine additively.  But we must pick our way through
; the hyps for each instantiation.

  (cond ((null ta-lst) 0)
        (t
         (+ (* concl-size (expt hyps-size
                                (length (access tests-and-alists
                                                (car ta-lst)
                                                :alists))))
            (induction-formula-size1 hyps-size concl-size (cdr ta-lst))))))

(defun induction-formula-size (cl-set ta-lst)

; This function returns a rough upper bound on the number of clauses
; that will be generated by induction-formula on the given arguments.
; See the comment in that function.

  (induction-formula-size1 (all-picks-size cl-set)
                           (length cl-set)
                           ta-lst))

; The following constant determines the limit on the estimated number of
; clauses induct, below, will return.  When normal processing would exceed
; this number, we try to cut down the combinatorics by collapsing clauses
; back into terms.

(defconst *maximum-induct-size* 100)

; And here is how we convert a hairy set of clauses into a term when we
; have to.

(defun termify-clause-set (clauses)

; This function is similar to termify-clause except that it converts a
; set of clauses into an equivalent term.  The set of clauses is
; understood to be implicitly conjoined and we therefore produce a
; conjunction expressed as (if cl1 cl2 nil).

  (declare (xargs :guard (pseudo-term-list-listp clauses)))
  (cond ((null clauses) *t*)
        ((null (cdr clauses)) (disjoin (car clauses)))
        (t (mcons-term* 'if
                        (disjoin (car clauses))
                        (termify-clause-set (cdr clauses))
                        *nil*))))

; Once we have created the set of clauses to prove, we inform the
; simplifier of what to look out for during the early processing.

(defun inform-simplify3 (alist terms ans)

; Instantiate every term in terms with alist and add them to ans.

  (cond ((null terms) ans)
        (t (inform-simplify3 alist (cdr terms)
                             (add-to-set-equal (sublis-var alist (car terms))
                                               ans)))))

(defun inform-simplify2 (alists terms ans)

; Using every alist in alists, instantiate every term in terms and add
; them all to ans.

  (cond ((null alists) ans)
        (t (inform-simplify2 (cdr alists) terms
                             (inform-simplify3 (car alists) terms ans)))))


(defun inform-simplify1 (ta-lst terms ans)

; Using every alist mentioned in any tests-and-alists record of ta-lst
; we instantiate every term in terms and add them all to ans.

  (cond ((null ta-lst) ans)
        (t (inform-simplify1 (cdr ta-lst) terms
                             (inform-simplify2 (access tests-and-alists
                                                       (car ta-lst)
                                                       :alists)
                                               terms
                                               ans)))))


(defun inform-simplify (ta-lst terms pspv)

; Historical Plaque from Nqthm:

;   Two of the variables effecting REWRITE are TERMS-TO-BE-IGNORED-BY-REWRITE
;   and EXPAND-LST.  When any term on the former is encountered REWRITE returns
;   it without rewriting it.  Terms on the latter must be calls of defined fns
;   and when encountered are replaced by the rewritten body.

;   We believe that the theorem prover will perform significantly faster on
;   many theorems if, after an induction, it does not waste time (a) trying to
;   simplify the recursive calls introduced in the induction hypotheses and (b)
;   trying to decide whether to expand the terms inducted for in the induction
;   conclusion.  This suspicion is due to some testing done with the idea of
;   "homographication" which was just a jokingly suggested name for the idea of
;   generalizing the recursive calls away at INDUCT time after expanding the
;   induction terms in the conclusion.  Homographication speeded the
;   theorem-prover on many theorems but lost on several others because of the
;   premature generalization.  See the comment in FORM-INDUCTION-CLAUSE.

;   To avoid the generalization at INDUCT time we are going to try using
;   TERMS-TO-BE-IGNORED-BY-REWRITE.  The idea is this, during the initial
;   simplification of a clause produced by INDUCT we will have the recursive
;   terms on TERMS-TO-BE-IGNORED-BY-REWRITE.  When the clause settles down --
;   hopefully it will often be proved first -- we will restore
;   TERMS-TO-BE-IGNORED-BY-REWRITE to its pre-INDUCT value.  Note however that
;   we have to mess with TERMS-TO-BE-IGNORED-BY-REWRITE on a clause by clause
;   basis, not just once in INDUCT.

;   So here is the plan.  INDUCT will set INDUCTION-HYP-TERMS to the list of
;   instances of the induction terms, and will set INDUCTION-CONCL-TERMS to the
;   induction terms themselves.  SIMPLIFY-CLAUSE will look at the history of
;   the clause to determine whether it has settled down since induction.  If
;   not it will bind TERMS-TO-BE-IGNORED-BY-REWRITE to the concatenation of
;   INDUCTION-HYP-TERMS and its old value and will analogously bind EXPAND-LST.
;   A new process, called SETTLED-DOWN-SENT, will be used to mark when in the
;   history the clause settled down.

; In a departure from Nqthm, starting with Version_2.8, we do not wait for
; settled-down before turning off the above special consideration given to
; induction-hyp-terms and induction-concl-terms. See simplify-clause for
; details.

  (change prove-spec-var pspv
          :induction-concl-terms terms
          :induction-hyp-terms (inform-simplify1 ta-lst terms nil)))

; Ok, except for our output and putting it all together, that's induction.
; We now turn to the output.  Induct prints two different messages. One
; reports the successful choice of an induction.  The other reports failure.

(defun all-vars1-lst-lst (lst ans)

; Lst is a list of lists of terms.  For example, it might be a set of
; clauses.  We compute the set of all variables occurring in it.

  (cond ((null lst) ans)
        (t (all-vars1-lst-lst (cdr lst)
                              (all-vars1-lst (car lst) ans)))))

(defun gen-new-name1 (char-lst wrld i)
  (let ((name (intern
               (coerce
                (append char-lst
                        (explode-nonnegative-integer i 10 nil))
                'string)
               "ACL2")))
    (cond ((new-namep name wrld) name)
          (t (gen-new-name1 char-lst wrld (1+ i))))))

(defun gen-new-name (root wrld)

; Create from the symbol root a possibly different symbol that
; is a new-namep in wrld.

  (cond ((new-namep root wrld) root)
        (t (gen-new-name1 (coerce (symbol-name root) 'list) wrld 0))))

(defun unmeasured-variables3 (vars alist)
; See unmeasured-variables.
  (cond ((null alist) nil)
        ((or (member-eq (caar alist) vars)
             (eq (caar alist) (cdar alist)))
         (unmeasured-variables3 vars (cdr alist)))
        (t (cons (caar alist) (unmeasured-variables3 vars (cdr alist))))))

(defun unmeasured-variables2 (vars alists)
; See unmeasured-variables.
  (cond ((null alists) nil)
        (t (union-eq (unmeasured-variables3 vars (car alists))
                     (unmeasured-variables2 vars (cdr alists))))))

(defun unmeasured-variables1 (vars ta-lst)
; See unmeasured-variables.
  (cond ((null ta-lst) nil)
        (t (union-eq (unmeasured-variables2 vars
                                            (access tests-and-alists
                                                    (car ta-lst)
                                                    :alists))
                     (unmeasured-variables1 vars (cdr ta-lst))))))

(defun unmeasured-variables (measured-vars cand)

; Measured-vars is the :subset of measured variables from the measure of term,
; computed above, for cand.  We collect those variables that are changed by
; some substitution but are not measured by our induction measure.  These are
; simply brought to the user's attention because we find it often surprising to
; see them.

  (unmeasured-variables1 measured-vars
                         (access candidate cand :tests-and-alists-lst)))

(defun tilde-@-well-founded-relation-phrase (rel wrld)

; We return a ~@ message that prints as "the relation rel (which, by name, is
; known to be well-founded on the domain recognized by mp)" and variants of
; that obtained when name is nil (meaning the well-foundedness is built in)
; and/or mp is t (meaning the domain is the universe).

  (let* ((temp (assoc-eq rel (global-val 'well-founded-relation-alist wrld)))
         (mp (cadr temp))
         (base-symbol (base-symbol (cddr temp))))
    (msg "the relation ~x0 (which~#1~[ ~/, by ~x2, ~]is known to be ~
          well-founded~#3~[~/ on the domain recognized by ~x4~])"
         rel
         (if (null base-symbol) 0 1)
         base-symbol
         (if (eq mp t) 0 1)
         mp)))

(defun measured-variables (cand wrld)
  (if (eq (ffn-symb (access candidate cand :induction-term))
          *do$-induction-fn*)

; In the case of do$ induction, the measure in the justification is already
; in terms of the ``formals'' of *do$-induction-fn*.  So we just get the vars
; from the measure.

      (all-vars
       (access justification
               (access candidate cand :justification)
               :measure))

; Otherwise, the measure (which was stored on the property list of the fn) is
; in terms of the formals of the fn, but we need to substitute the actuals in
; the call of the the fn in the conjecture.

      (all-vars1-lst
       (subcor-var-lst
        (formals (ffn-symb (access candidate cand :induction-term))
                 wrld)
        (fargs (access candidate cand :induction-term))
        (access justification
                (access candidate cand :justification)
                :subset))
       nil)))

(defun induct-msg/continue (pool-lst
                            forcing-round
                            cl-set
                            induct-hint-val
                            len-candidates
                            len-flushed-candidates
                            len-merged-candidates
                            len-unvetoed-candidates
                            len-complicated-candidates
                            len-high-scoring-candidates
                            winning-candidate
                            estimated-size
                            clauses
                            wrld
                            state)

; Pool-lst is what is passed to form the tilde-@-pool-name-phrase (q.v.) of the
; set of clauses cl-set to which we are applying induction.  Len-candidates is
; the length of the list of induction candidates we found.
; Len-flushed-candidates is the length of the candidates after flushing some
; down others, etc.  Winning-candidate is the final selection.  Clauses is the
; clause set generated by applying winning-candidate to cl-set.  Wrld and state
; are the usual.

; Estimated-size is either nil or a nat.  Nil indicates that induct did not
; termify the cl-set to squeeze down the number of cases.  If it is non-nil, it
; means induct did termify cl-set and estimated-size is just that: the
; estimated size of the induction case analysis had we not squeezed it.

; This function increments timers.  Upon entry, the accumulated time is
; charged to 'prove-time.  The time spent in this function is charged
; to 'print-time.

; Warning: This function should be called under (io? prove ...).

  (declare (xargs

; Avoid blow-up from (skip-proofs (verify-termination ...)), which otherwise
; takes a long time (e.g., when executed on behalf of community books utility
; verify-guards-program).

            :normalize nil))
  (cond
   ((and (gag-mode)
         (or (eq (gag-mode-evisc-tuple state) t)
             (cdr pool-lst)))
    state)
   (t
    (pprogn
     (increment-timer 'prove-time state)
     (let* ((pool-name
             (tilde-@-pool-name-phrase forcing-round pool-lst))
            (p (cons :p
                     (merge-sort-term-order (all-vars1-lst-lst cl-set nil))))
            (measured-variables (measured-variables winning-candidate wrld))
            (unmeasured-variables (unmeasured-variables measured-variables
                                                        winning-candidate))
            (attribution-phrase (tilde-*-simp-phrase
                                 (access candidate winning-candidate :ttree))))
       (fms "~#H~[We have been told to use induction.  ~N0 induction ~
                scheme~#1~[ is~/s are~] suggested by the induction ~
                hint.~/~

                We have been told to use induction.  ~N0 induction ~
                scheme~#1~[ is~/s are~] suggested by this ~
                conjecture.~/~

                Perhaps we can prove ~@n by induction.  ~

                ~N0 induction scheme~#1~[ is~/s are~] suggested by this ~
                conjecture.~]  ~

          ~#a~[~/Subsumption reduces that number to ~n2.  ~]~

          ~#b~[~/These merge into ~n3 derived induction scheme~#4~[~/s~].  ~]~

          ~#c~[~/However, ~n5 of these ~#6~[is~/are~] flawed and so we are ~
           left with ~nq viable ~#r~[~/candidate~/candidates~].  ~]~

          ~#d~[~/By considering those suggested by the largest number of ~
                 non-primitive recursive functions, we narrow the field ~
                 to ~n7.  ~]~

          ~#e~[~/~N8 of these ~
                 ~#9~[has a score higher than the other~#A~[~/s~].  ~/~
                      are tied for the highest score.  ~]~]~

          ~#f~[~/We will choose arbitrarily among these.  ~]~

          ~|~%We will induct according to a scheme suggested by ~
          ~#h~[~xg.~/~xg, while ac~-com~-mo~-dating ~*i~]~

          ~|~%~#w~[~/~#h~[This suggestion was~/These suggestions were~] ~
          produced using ~*x.~]  ~

          If we let ~xp denote ~@n above then the induction scheme ~
          we'll use is~|~

          ~Qsy.~

          ~#J~[Note that one or more measure conjectures included in ~
          the scheme above justify this induction if they are provable.  ~/~
          This induction is justified by the same argument used to ~
          admit ~xj.  ~]~

          ~#l~[~/Note, however, that the unmeasured ~
                 variable~#m~[ ~&m is~/s ~&m are~] being instantiated.  ~]~

          When applied to the goal at hand the above induction scheme ~
          produces ~#v~[no nontautological subgoals~/one nontautological ~
          subgoal~/~no nontautological subgoals~].~

          ~#t~[~/  However, to achieve this relatively small number of ~
          cases we had to termify ~@n (see :DOC termify).  Otherwise, this ~
          induction would have produced approximately ~nu cases!~]~|"
            (list (cons #\H (cond ((null induct-hint-val) 2)
                                  ((equal induct-hint-val *t*) 1)
                                  (t 0)))
                  (cons #\n pool-name)
                  (cons #\0 len-candidates)
                  (cons #\1 (if (int= len-candidates 1) 0 1))
                  (cons #\a (if (< len-flushed-candidates
                                   len-candidates)
                                1 0))
                  (cons #\2 len-flushed-candidates)
                  (cons #\b (if (< len-merged-candidates
                                   len-flushed-candidates)
                                1 0))
                  (cons #\3 len-merged-candidates)
                  (cons #\4 (if (int= len-merged-candidates 1) 0 1))
                  (cons #\c (if (< len-unvetoed-candidates
                                   len-merged-candidates)
                                1 0))
                  (cons #\5 (- len-merged-candidates
                               len-unvetoed-candidates))
                  (cons #\q len-unvetoed-candidates)
                  (cons #\y (gag-mode-evisc-tuple state)) ; is not t
                  (cons #\r (zero-one-or-more len-unvetoed-candidates))
                  (cons #\6 (if (int= (- len-merged-candidates
                                         len-unvetoed-candidates)
                                      1)
                                0 1))
                  (cons #\d (if (< len-complicated-candidates
                                   len-unvetoed-candidates)
                                1 0))
                  (cons #\7 len-complicated-candidates)
                  (cons #\e (if (< len-high-scoring-candidates
                                   len-complicated-candidates)
                                1 0))
                  (cons #\8 len-high-scoring-candidates)
                  (cons #\9 (if (int= len-high-scoring-candidates 1) 0 1))
                  (cons #\A (if (int= (- len-complicated-candidates
                                         len-high-scoring-candidates)
                                      1)
                                0 1))
                  (cons #\f (if (int= len-high-scoring-candidates 1) 0 1))
                  (cons #\p p)
                  (cons #\s (prettyify-clause-set

; We create the induction scheme by using induction-formula on the clause set
; consisting of the singleton clause ((:P x1 x2 ...)).  However, if this is do$
; induction, we have to add the Q literals to the clause so that
; induction-formula finds them and includes them in the termination theorem.

                             (induction-formula
                              (list
                               (cond
                                ((eq (ffn-symb (access candidate winning-candidate
                                                       :induction-term))
                                     *do$-induction-fn*)
                                 (append
                                  (select-do$-induction-q ; compute actual Q
                                   cl-set
                                   (cons (access candidate winning-candidate
                                                 :xinduction-term)
                                         (access candidate winning-candidate
                                                 :xother-terms))
                                   (access justification
                                           (access candidate winning-candidate
                                                   :justification)
                                           :measure))
                                  (list p)))
                                (t (list p))))
                              (access candidate winning-candidate
                                      :induction-term)
                              (list p) ; ignore (:p x1 x2 ...)
                              (access justification
                                      (access candidate winning-candidate
                                              :justification)
                                      :measure)
                              (access candidate winning-candidate
                                      :tests-and-alists-lst))
                             (let*-abstractionp state)
                             wrld))
                  (cons #\g (untranslate (access candidate winning-candidate
                                                 :xinduction-term)
                                         nil
                                         wrld))
                  (cons #\h (if (access candidate winning-candidate :xother-terms)
                                1 0))
                  (cons #\i (tilde-*-untranslate-lst-phrase
                             (access candidate winning-candidate :xother-terms)
                             #\. nil wrld))
                  (cons #\J (if (eq (ffn-symb (access candidate winning-candidate
                                                      :induction-term))
                                    *do$-induction-fn*)
                                0 1))

                  (cons #\j (ffn-symb
                             (access candidate winning-candidate
                                     :xinduction-term)))
                  (cons #\l (if unmeasured-variables 1 0))
                  (cons #\m unmeasured-variables)
                  (cons #\o (length clauses))
                  (cons #\t (if estimated-size 1 0))

; Note: #\t and #\u are coordinated!  If estimated-size is nil, then #\u is
; ignored by the fmt string above.  If estimated-size is non-nil, #\u is
; treated as a natural by the ~nu directive in the fmt string.

                  (cons #\u estimated-size)
                  (cons #\v (if (null clauses) 0 (if (cdr clauses) 2 1)))
                  (cons #\w (if (nth 4 attribution-phrase) 1 0))
                  (cons #\x attribution-phrase))
            (proofs-co state)
            state
            (term-evisc-tuple nil state)))
     (increment-timer 'print-time state)))))

(mutual-recursion

(defun rec-fnnames (term wrld)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (union-eq (rec-fnnames (lambda-body (ffn-symb term)) wrld)
                   (rec-fnnames-lst (fargs term) wrld)))
        ((getpropc (ffn-symb term) 'recursivep nil wrld)
         (add-to-set-eq (ffn-symb term)
                        (rec-fnnames-lst (fargs term) wrld)))
        (t (rec-fnnames-lst (fargs term) wrld))))

(defun rec-fnnames-lst (lst wrld)
  (cond ((null lst) nil)
        (t (union-eq (rec-fnnames (car lst) wrld)
                     (rec-fnnames-lst (cdr lst) wrld)))))

)

(defun induct-msg/lose (pool-name induct-hint-val pspv state)

; We print the message that no induction was suggested.

; This function increments timers.  Upon entry, the accumulated time is
; charged to 'prove-time.  The time spent in this function is charged
; to 'print-time.

; Warning: This function should be called under (io? prove ...).

  (pprogn
   (increment-timer 'prove-time state)
   (fms "No induction schemes are suggested by ~#H~[the induction ~
         hint.~@?~/~@n.~]  Consequently, the proof attempt has failed.~|"
        (list (cons #\H (cond (induct-hint-val 0) (t 1)))
              (cons #\n pool-name)
              (cons #\?
                    (and induct-hint-val ; optimization
                         (let* ((wrld (w state))
                                (all-fns (all-fnnames induct-hint-val))
                                (rec-fns (rec-fnnames induct-hint-val wrld)))
                           (cond
                            ((null all-fns)
                             "  (Note that there is no function symbol ~
                              occurring in that hint.)")
                            ((and (null rec-fns)
                                  (null (cdr all-fns)))
                             (msg "  (Note that ~x0 is not defined ~
                                   recursively, so it cannot suggest an ~
                                   induction scheme.)"
                                  (car all-fns)))
                            ((null rec-fns)
                             "  (Note that none of its function symbols is ~
                              defined recursively, so they cannot suggest ~
                              induction schemes.)")
                            ((and (all-variablep (fargs induct-hint-val))
                                  (let ((ens (ens-from-pspv pspv)))
                                    (and
                                     (not (enabled-runep
                                           (list :induction (car rec-fns))
                                           ens
                                           wrld))
                                     (not (enabled-runep
                                           (list :definition (car rec-fns))
                                           ens
                                           wrld)))))
                             (msg "  (Note that ~x0 (including its :induction ~
                                   rune) is disabled, so it cannot suggest an ~
                                   induction scheme.  Consider providing an ~
                                   :in-theory hint that enables ~x0 or ~x1.)"
                                  (car all-fns)
                                  (list :induction (car all-fns))))
                            (t ""))))))
        (proofs-co state)
        state
        (term-evisc-tuple nil state))
   (increment-timer 'print-time state)))

; When induct is called it is supplied the hint-settings that were
; attached to the clause by the user.  Induct has the job of loading
; the hint settings into the pspv it returns.  Most of the content of
; the hint-settings is loaded into the rewrite-constant of the pspv.

(defun set-difference-augmented-theories (lst1 lst2 ans)

; Lst1 and lst2 are augmented runic theories.  This is similar to
; set-difference-augmented-theories-fn1 and
; set-difference-augmented-theories-fn1+, except here we return an augmented
; runic theory (not a runic theory) when ans is nil.

  (cond ((endp lst1) (reverse ans))
        ((endp lst2) (revappend ans lst1))
        ((= (car (car lst1)) (car (car lst2)))
         (set-difference-augmented-theories (cdr lst1) (cdr lst2) ans))
        ((> (car (car lst1)) (car (car lst2)))
         (set-difference-augmented-theories
          (cdr lst1) lst2 (cons (car lst1) ans)))
        (t (set-difference-augmented-theories lst1 (cdr lst2) ans))))

(defun@par load-hint-settings-into-rcnst (hint-settings rcnst
                                                        incrmt-array-name-info
                                                        wrld ctx state)

; Certain user supplied hint settings find their way into the rewrite-constant.
; They are :expand, :restrict, :hands-off, and :in-theory.  Our convention is
; that if a given hint key/val is provided it replaces what was in the rcnst.
; Otherwise, we leave the corresponding field of rcnst unchanged.

; Incrmt-array-name-info is either a clause-id, a keyword, or nil.  If it is a
; clause-id and we install a new enabled structure, then we will use that
; clause-id to build the array name, rather than simply incrementing a suffix.
; Otherwise incrmt-array-name-info is a keyword.  A keyword value should be
; used for calls made by user applications, for example in community book
; books/tools/easy-simplify.lisp, so that enabled structures maintained by the
; ACL2 system do not lose their associated von Neumann arrays.

  (er-let*@par
   ((new-ens
     (cond
      ((assoc-eq :in-theory hint-settings)
       (let* ((theory0 (cdr (assoc-eq :in-theory hint-settings)))
              (theory1 (augment-runic-theory theory0 wrld))
              (active-useless-runes (active-useless-runes state))
              (old-ens (access rewrite-constant rcnst
                               :current-enabled-structure))
              (theory
               (if (and active-useless-runes

; The following two conditions are just an optimization.  If old-ens is (ens
; state), then presumably active-useless-runes was already subtracted and we
; don't need to subtract that list again.  We check the name first since that
; should be fastest: when the names are EQ, very likely the two
; enabled-structures are EQ.

                        (eq (access enabled-structure old-ens
                                    :array-name)
                            (access enabled-structure (ens state)
                                    :array-name))
                        (equal old-ens (ens state)))
                   (set-difference-augmented-theories theory1
                                                      active-useless-runes
                                                      nil)
                 theory1)))
         (load-theory-into-enabled-structure@par
          :from-hint
          theory
          t
          old-ens
          (or incrmt-array-name-info t)
          nil
          wrld ctx state)))
      (t (value@par (access rewrite-constant rcnst
                            :current-enabled-structure))))))
   (value@par (change rewrite-constant rcnst
                      :rw-cache-state
                      (cond
                       ((assoc-eq :rw-cache-state hint-settings)
                        (cdr (assoc-eq :rw-cache-state hint-settings)))
                       (t (access rewrite-constant rcnst :rw-cache-state)))
                      :expand-lst
                      (cond
                       ((assoc-eq :expand hint-settings)
                        (cdr (assoc-eq :expand hint-settings)))
                       (t (access rewrite-constant rcnst :expand-lst)))
                      :restrictions-alist
                      (cond
                       ((assoc-eq :restrict hint-settings)
                        (cdr (assoc-eq :restrict hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :restrictions-alist)))
                      :fns-to-be-ignored-by-rewrite
                      (cond
                       ((assoc-eq :hands-off hint-settings)
                        (cdr (assoc-eq :hands-off hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :fns-to-be-ignored-by-rewrite)))
                      :current-enabled-structure
                      new-ens
                      :nonlinearp
                      (cond
                       ((assoc-eq :nonlinearp hint-settings)
                        (cdr (assoc-eq :nonlinearp hint-settings)))
                       (t (access rewrite-constant rcnst :nonlinearp)))
                      :backchain-limit-rw
                      (cond
                       ((assoc-eq :backchain-limit-rw hint-settings)
                        (cdr (assoc-eq :backchain-limit-rw hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :backchain-limit-rw)))
                      :case-split-limitations
                      (cond
                       ((assoc-eq :case-split-limitations hint-settings)
                        (cdr (assoc-eq :case-split-limitations
                                       hint-settings)))
                       (t (access rewrite-constant rcnst
                                  :case-split-limitations)))))))

(defun update-hint-settings (new-hint-settings old-hint-settings)
  (cond
   ((endp new-hint-settings) old-hint-settings)
   ((assoc-eq (caar new-hint-settings) old-hint-settings)
    (update-hint-settings
     (cdr new-hint-settings)
     (cons (car new-hint-settings)
           (remove1-assoc-eq (caar new-hint-settings)
                             old-hint-settings))))
   (t (update-hint-settings
       (cdr new-hint-settings)
       (cons (car new-hint-settings) old-hint-settings)))))

; Thus, a given hint-settings causes us to modify the pspv as follows:

(defun@par load-hint-settings-into-pspv (increment-flg hint-settings pspv cl-id
                                                       wrld ctx state)

; We load the hint-settings into the rewrite-constant of pspv, thereby making
; available the :expand, :case-split-limitations, :restrict, :hands-off,
; :in-theory, and :rw-cache-state hint settings.  We also store the
; hint-settings in the hint-settings field of the pspv, making available the
; :induct and :do-not-induct hint settings.

; When increment-flg is non-nil, we want to preserve the input pspv's hint
; settings except when they collide with hint-settings.  Otherwise (for
; example, when induct is called), we completely replace the input pspv's
; :hint-settings with hint-settings.

; Warning: Restore-hint-settings-in-pspv, below, is supposed to undo these
; changes while not affecting the rest of a newly obtained pspv.  Keep these
; two functions in step.

  (er-let*@par
   ((rcnst (load-hint-settings-into-rcnst@par
            hint-settings
            (access prove-spec-var pspv :rewrite-constant)
            cl-id wrld ctx state)))
   (value@par
    (change prove-spec-var pspv
            :rewrite-constant rcnst
            :hint-settings
            (if increment-flg
                (update-hint-settings hint-settings
                                      (access prove-spec-var pspv
                                              :hint-settings))
              hint-settings)))))

(defun restore-hint-settings-in-pspv (new-pspv old-pspv)

; This considers the fields changed by load-hint-settings-into-pspv above
; and restores them in new-pspv to the values they have in old-pspv.  The
; idea is that we start with a pspv1, load hints into it to get pspv2,
; pass that around the prover and obtain pspv3 (which has a new tag-tree
; and pool etc), and then restore the hint settings as they were in pspv1.
; In this example, new-pspv would be pspv3 and old-pspv would be pspv1.

; We would like the garbage collector to free up space from obsolete arrays of
; enabled-structures.  This may be especially important with potentially many
; such arrays associated with different names, due to the new method of
; creating array names after Version_4.1, where the name is typically based on
; the clause-id.  Previously, the enabled-structure array names were created
; based on just a few possible suffixes, so it didn't seem important to make
; garbage -- each time such a name was re-used, the previous array for that
; name became garbage.  If we change how this is done, revisit the sentence
; about this function in the Essay on Enabling, Enabled Structures, and
; Theories.

  (let* ((old-rcnst (access prove-spec-var old-pspv
                            :rewrite-constant))
         (old-ens (access rewrite-constant old-rcnst
                          :current-enabled-structure))
         (old-name (access enabled-structure old-ens
                           :array-name))
         (new-rcnst (access prove-spec-var new-pspv
                            :rewrite-constant))
         (new-ens (access rewrite-constant new-rcnst
                          :current-enabled-structure))
         (new-name (access enabled-structure new-ens
                           :array-name)))
    (prog2$ (cond ((equal old-name new-name) nil)
                  (t (flush-compress new-name)))
            (change prove-spec-var new-pspv
                    :rewrite-constant old-rcnst
                    :hint-settings (access prove-spec-var old-pspv
                                           :hint-settings)))))

(defun remove-trivial-clauses (clauses wrld)
  (cond
   ((null clauses) nil)
   ((trivial-clause-p (car clauses) wrld)
    (remove-trivial-clauses (cdr clauses) wrld))
   (t (cons (car clauses)
            (remove-trivial-clauses (cdr clauses) wrld)))))

#+:non-standard-analysis
(defun non-standard-vector-check (vars accum)
  (if (null vars)
      accum
    (non-standard-vector-check (cdr vars)
                               (cons (mcons-term* 'standardp (car vars))
                                     accum))))

#+:non-standard-analysis
(defun merge-ns-check (checks clause accum)
  (if (null checks)
      accum
    (merge-ns-check (cdr checks) clause (cons (cons (car checks)
                                                    clause)
                                              accum))))

#+:non-standard-analysis
(defun trap-non-standard-vector-aux (cl-set accum-cl checks wrld)
  (cond ((null cl-set) accum-cl)
        ((classical-fn-list-p (all-fnnames-lst (car cl-set)) wrld)
         (trap-non-standard-vector-aux (cdr cl-set) accum-cl checks wrld))
        (t
         (trap-non-standard-vector-aux (cdr cl-set)
                                       (append (merge-ns-check checks
                                                               (car cl-set)
                                                               nil)
                                               accum-cl)
                                       checks
                                       wrld))))

#+:non-standard-analysis
(defun remove-adjacent-duplicates (x)

; We have slightly modified the original definition so as to match the
; definition (quite likely adapted from the original one here) in community
; book books/defsort/remove-dups.lisp.  Sol Swords points out that an
; unconditional rule true-listp-of-remove-adjacent-duplicates in that book
; relies on (list (car x)) in the second case below, rather than x.

  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list (car x))) ; See comment above for why this is not x.
        ((equal (car x) (cadr x))
         (remove-adjacent-duplicates (cdr x)))
        (t
         (cons (car x)
               (remove-adjacent-duplicates (cdr x))))))

(defun remove-adjacent-duplicates-eq (x)

; See remove-adjacent-duplicates.

  (declare (xargs :guard t))
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list (car x)))
        ((eq (car x) (cadr x))
         (remove-adjacent-duplicates-eq (cdr x)))
        (t
         (cons (car x)
               (remove-adjacent-duplicates-eq (cdr x))))))

#+:non-standard-analysis
(defun non-standard-induction-vars (candidate wrld)
  (remove-adjacent-duplicates
   (merge-sort-term-order
    (append (access candidate candidate :changed-vars)

; The following line was changed after Version_3.0.1.  It seems like a correct
; change, but we'll leave this comment here until Ruben Gamboa (ACL2(r) author)
; checks this change.

            (measured-variables candidate wrld)))))

#+:non-standard-analysis
(defun trap-non-standard-vector (cl-set candidate accum-cl wrld)
  (trap-non-standard-vector-aux cl-set accum-cl
                                (non-standard-vector-check
                                 (non-standard-induction-vars
                                  candidate wrld)
                                 nil)
                                wrld))

(defun induct (forcing-round pool-lst cl-set hint-settings pspv wrld ctx state)

; We take a set of clauses, cl-set, and return four values.  The first
; is either the signal 'lose (meaning we could find no induction to do
; and have explained that to the user) or 'continue, meaning we're
; going to use induction.  The second value is a list of clauses,
; representing the induction base cases and steps.  The last two
; things are new values for pspv and state.  We modify pspv to store
; the induction-hyp-terms and induction-concl-terms for the
; simplifier.

; The clause set we explore to collect the induction candidates,
; x-cl-set, is not necessarily cl-set.  If the value, v, of :induct in
; the hint-settings is non-nil and non-*t*, then we explore the clause
; set {{v}} for candidates.

  (let ((cl-set (remove-guard-holders-lst-lst cl-set wrld))
        (pool-name
         (tilde-@-pool-name-phrase forcing-round pool-lst))
        (induct-hint-val
         (let ((induct-hint-val0
                (cdr (assoc-eq :induct hint-settings))))
           (and induct-hint-val0
                (remove-guard-holders induct-hint-val0 wrld)))))
    (mv-let
     (erp new-pspv state)
     (load-hint-settings-into-pspv
      nil
      (if induct-hint-val
          (remove1-assoc-eq :induct hint-settings)
        hint-settings)
      pspv nil wrld ctx state)
     (cond
      (erp (mv 'lose nil pspv state))
      (t
       (let* ((candidates
               (get-induction-cands-from-cl-set
                (select-x-cl-set cl-set induct-hint-val)
                new-pspv wrld state))
              (flushed-candidates
               (m&m candidates 'flush-candidates))

; In Nqthm we flushed and merged at the same time.  However, flushing
; is a mate and merge function that has the distributive and non-preclusion
; properties and hence can be done with a simple m&m.  Merging on the other
; hand is preclusive and so we wait and run m&m-over-powerset to do
; that.  In Nqthm, we did preclusive merging with m&m (then called
; TRANSITIVE-CLOSURE) and just didn't worry about the fact that we
; messed up some potential merges by earlier merges.  Of course, the
; powerset computation is so expensive for large sets that we can't
; just go into it blindly, so we don't use the m&m-over-powerset to do
; flushing and merging at the same time.  Flushing eliminates duplicates
; and subsumed inductions and thus shrinks the set as much as we know how.

              (merged-candidates
               (cond ((< (length flushed-candidates) 10)
                      (m&m-over-powerset flushed-candidates 'merge-candidates))
                     (t (m&m flushed-candidates 'merge-candidates))))

; Note: We really respect powerset.  If the set we're trying to merge
; has more than 10 things in it -- an arbitrary choice at the time of
; this writing -- we just do the m&m instead, which causes us to miss
; some merges because we only use each candidate once and merging
; early merges can prevent later ones.

              (unvetoed-candidates
               (compute-vetoes merged-candidates wrld))

              (complicated-candidates
               (maximal-elements unvetoed-candidates 'induction-complexity
                                 wrld))

              (high-scoring-candidates
               (maximal-elements complicated-candidates 'score wrld))
              (winning-candidate (car high-scoring-candidates)))
         (cond
          (winning-candidate
           (mv-let
            (erp candidate-ttree state)
            (accumulate-ttree-and-step-limit-into-state
             (access candidate winning-candidate :ttree)
             :skip
             state)
            (declare (ignore erp))
            (let (

; First, we estimate the size of the answer if we persist in using cl-set.

                   (estimated-size
                    (induction-formula-size cl-set
                                            (access candidate
                                                    winning-candidate
                                                    :tests-and-alists-lst))))
              (mv-let (step-limit00 clauses00 ttree00)

; Next we create clauses, the set of clauses we wish to prove.
; Observe that if the estimated size is greater than
; *maximum-induct-size* we squeeze the cl-set into the form {{p}},
; where p is a single term.  This eliminates the combinatoric
; explosion at the expense of making the rest of the theorem prover
; suffer through opening things back up.  The idea, however, is that
; it is better to give the user something to look at, so he sees the
; problem blowing up in front of him in rewrite, than to just
; disappear into induction and never come out.  We have seen simple
; cases where failed guard conjectures would have led to inductions
; containing thousands of cases had induct been allowed to compute
; them out.

; Clausify-input, used in one branch below, returns (mv step-limit clauses
; ttree), so we make all branches of this cond return those three.  But we
; ignore step-limit.

                (cond ((and (> estimated-size *maximum-induct-size*)
                            (not (and (equal (len cl-set) 1)
                                      (equal (len (car cl-set)) 1))))
                       (mv nil (list (list (termify-clause-set cl-set))) nil))
                      ((and (eq (ffn-symb (access candidate
                                                  winning-candidate
                                                  :induction-term))
                                *do$-induction-fn*)
                            (equal (len cl-set) 1)
                            (equal (len (car cl-set)) 1))

; We went into a do$ induction and the clause-set is {{term}}.  It's
; possible that term is just the original input, e.g., because there was an
; :induct t hint on Goal or because we reverted back to Goal after some
; pre-induction case splits.  This makes it impossible to identify a q.  So in
; this case we first clausify the term just for the purposes of finding a q.
; (It is, of course, also possible that term is a much-simplified literal that
; won't clausify to anything else.)

                       (clausify-input
                        (car (car cl-set))
                        (access rewrite-constant
                                (access prove-spec-var new-pspv
                                        :rewrite-constant)
                                :fns-to-be-ignored-by-rewrite)
                        (ens-from-pspv new-pspv)
                        wrld
                        state
                        nil
                        (initial-step-limit wrld state)))
                      (t (mv nil cl-set nil)))
                (declare (ignore step-limit00))
                (let* ((termifiedp (and (> estimated-size *maximum-induct-size*)
                                        (not (and (equal (len cl-set) 1)
                                                  (equal (len (car cl-set)) 1)))))
                       (clauses0
                        (induction-formula
                         clauses00
                         (access candidate winning-candidate :induction-term)
                         (if (and induct-hint-val
                                  (not (equal induct-hint-val *t*)))
                             :DO$
                             (cons (access candidate winning-candidate
                                           :xinduction-term)
                                   (access candidate winning-candidate
                                           :xother-terms)))
                         (access justification
                                 (access candidate winning-candidate
                                         :justification)
                                 :measure)
                         (access candidate winning-candidate
                                 :tests-and-alists-lst)))
                       (clauses1
                        #+:non-standard-analysis
                        (trap-non-standard-vector cl-set
                                                  winning-candidate
                                                  clauses0
                                                  wrld)
                        #-:non-standard-analysis
                        clauses0)
                       (clauses
                        (cond ((> estimated-size *maximum-induct-size*)
                               clauses1)
                              (t (remove-trivial-clauses clauses1 wrld))))

; Now we inform the simplifier of this induction and store the ttree of the
; winning candidate (and the ttree produced by our extra clausify-input above)
; into the tag-tree of the pspv.

                       (newer-pspv
                        (inform-simplify
                         (access candidate winning-candidate :tests-and-alists-lst)
                         (add-to-set-equal
                          (access candidate winning-candidate
                                  :xinduction-term)
                          (access candidate winning-candidate :xother-terms))
                         (change prove-spec-var new-pspv
                                 :tag-tree
                                 (cons-tag-trees
                                  ttree00
                                  (cons-tag-trees
                                   candidate-ttree
                                   (access prove-spec-var new-pspv :tag-tree)))))))

; Now we print out the induct message.

              (let ((state
                     (io? prove nil state
                          (wrld clauses termifiedp estimated-size
                                winning-candidate
                                high-scoring-candidates complicated-candidates
                                unvetoed-candidates merged-candidates
                                flushed-candidates candidates induct-hint-val
                                ;cl-set
                                forcing-round pool-lst)

                          (induct-msg/continue
                           pool-lst
                           forcing-round
                           clauses ; cl-set
                           induct-hint-val
                           (length candidates)
                           (length flushed-candidates)
                           (length merged-candidates)
                           (length unvetoed-candidates)
                           (length complicated-candidates)
                           (length high-scoring-candidates)
                           winning-candidate
                           (if termifiedp
                               estimated-size
                               nil)
                           clauses
                           wrld
                           state))))
                (mv 'continue
                    clauses
                    newer-pspv
                    state)))))))
          (t

; Otherwise, we report our failure to find an induction and return the
; 'lose signal.

           (pprogn (io? prove nil state
                        (induct-hint-val pool-name new-pspv)
                        (induct-msg/lose pool-name induct-hint-val new-pspv
                                         state))
                   (mv 'lose nil pspv state))))))))))

; We now define the elimination of irrelevance.  Logically this ought
; to be defined when the other processors are defined.  But to
; partition the literals of the clause by variables we use m&m, which
; is not defined until induction.  We could have moved m&m-apply back
; into the earlier processors, but that would require moving about a
; third of induction back there.  So we have just put all of
; irrelevance elimination here.

(defun pair-vars-with-lits (cl)

; We pair each lit of clause cl with its variables.  The variables are
; in the car of the pair, the singleton set containing the lit is in
; the cdr.

  (cond ((null cl) nil)
        (t (cons (cons (all-vars (car cl)) (list (car cl)))
                 (pair-vars-with-lits (cdr cl))))))


(mutual-recursion

(defun ffnnames-subsetp (term lst)

; Collect the ffnames in term and say whether it is a subset of lst.
; We don't consider fnnames of constants, e.g., the cons of '(a b).

  (cond ((variablep term) t)
        ((fquotep term) t)
        ((flambda-applicationp term)
         (and (ffnnames-subsetp-listp (fargs term) lst)
              (ffnnames-subsetp (lambda-body (ffn-symb term)) lst)))
        ((member-eq (ffn-symb term) lst)
         (ffnnames-subsetp-listp (fargs term) lst))
        (t nil)))

(defun ffnnames-subsetp-listp (terms lst)
  (cond ((null terms) t)
        ((ffnnames-subsetp (car terms) lst)
         (ffnnames-subsetp-listp (cdr terms) lst))
        (t nil)))
)

;; Historical Comment from Ruben Gamboa:
;; I added realp and complexp to the list of function names
;; simplification can decide.

(defun probably-not-validp (cl)

; Cl is a clause that is a subset of some clause, cl2, that has survived
; simplification.  We are considering whether cl seems useless in proving cl2;
; if so, we return t.  In particular, we return t if we think there is an
; instantiation of cl that makes each literal false.

; We have two trivial heuristics.  One is to detect whether the only function
; symbols in cl are ones that we think make up a fragment of the theory that
; simplification can decide.  The other heuristic is to bet that any cl
; consisting of a single literal which is of the form (fn v1 ... vn) or (not
; (fn v1 ... vn)), where the vi are distinct variables, is probably not valid.

; We elaborate a bit.  For eliminating irrelevance, we view a clause as

; (forall x y)(p(x) \/ q(y))

; where p(x) is a possibly irrelevant literal (or set of literals, but we focus
; here on the case of a single literal) and q(y) is the disjunction of the
; other literals.  In general, of course, each of these terms may have several
; free variables; but even in general, in order for p(x) to be a candidate for
; irrelevance, its set of variables must be disjoint from the set of variables
; in q.  In that case the clause is logically equivalent to the following.

; (forall x)p(x) \/ (forall y)q(y)

; We'd like to ignore one of those disjuncts when choosing an induction
; (actually q could itself be a disjunction on which we recur); but which one?
; If p(x) is probably not valid then we consider it reasonable to ignore p(x) in
; the hope that q(y) may be valid, and indeed provable by ACL2.

; See also the Essay on Alternate Heuristics for Eliminate-Irrelevance.

  (or (ffnnames-subsetp-listp cl '(not consp integerp rationalp
                                       #+:non-standard-analysis realp
                                       acl2-numberp
                                       true-listp complex-rationalp
                                       #+:non-standard-analysis complexp
                                       stringp characterp
                                       symbolp cons car cdr equal
                                       binary-+ unary-- < apply))
      (case-match cl
        ((('not (& . args)))

; To understand why we require args to be non-nil, see the Essay on Alternate
; Heuristics for Eliminate-Irrelevance.

         (and args ; do not drop zero-ary call (see above)
              (all-variablep args)
              (no-duplicatesp-eq args)))
        (((& . args))
         (and args  ; do not drop zero-ary call (see above)
              (all-variablep args)
              (no-duplicatesp-eq args)))
        (& nil))))

(defun irrelevant-lits (alist)

; Alist is an alist that associates a set of literals with each key.  The keys
; are irrelevant.  We consider each set of literals and decide if it is
; probably not valid.  If so we consider it irrelevant.  We return the
; concatenation of all the irrelevant literal sets.

  (cond ((null alist) nil)
        ((probably-not-validp (cdar alist))
         (append (cdar alist) (irrelevant-lits (cdr alist))))
        (t (irrelevant-lits (cdr alist)))))

(defun eliminate-irrelevance-clause (cl hist pspv wrld state)

; A standard clause processor of the waterfall.

; We return 4 values.  The first is a signal that is either 'hit, or
; 'miss.  When the signal is 'miss, the other 3 values are irrelevant.
; When the signal is 'hit, the second result is the list of new
; clauses, the third is a ttree that will become that component of the
; history-entry for this elimination, and the fourth is an
; unmodified pspv.  (We return the fourth thing to adhere to the
; convention used by all clause processors in the waterfall (q.v.).)

; Essay on Alternate Heuristics for Eliminate-Irrelevance

; The algorithm for dropping "irrelevant" literals is based on first
; partitioning the literals of a clause into components with respect to the
; symmetric binary relation defined by: two literals are related if and only if
; they share at least one free variable.  We consider two ways for a component
; to be irrelevant: either (A) its function symbols are all from among a small
; fixed set of primitives, or else (B) the component has a single literal whose
; atom is the application of a function symbol to distinct variables.
; Criterion B, however, is somewhat problematic, and below we discuss
; variations of it that we have considered.  (See function probably-not-validp
; for relevant code.)

; Through Version_7.2, Criterion B was exactly as stated above.  However, we
; encountered an unfortunate aspect of that heuristic, which is illustrated by
; the following example (which is simpler than the one actually encountered,
; but is similar in spirit).  The THM below failed to prove in Version_7.2.

;   (encapsulate
;     ((p () t)
;      (my-app (x y) t))
;     (local (defun p () t))
;     (local (defun my-app (x y) (append x y)))
;     (defthm my-app-def
;       (implies (p)
;                (equal (my-app x y)
;                       (if (consp x)
;                           (cons (car x) (my-app (cdr x) y))
;                         y)))
;       :rule-classes ((:definition
;                       :controller-alist ((my-app t nil))))))
;
;   (defun rev (x)
;     (if (consp x)
;         (my-app (rev (cdr x))
;                 (cons (car x) nil))
;       nil))
;
;   (thm (implies (and (p)
;                      (true-listp x))
;                 (equal (rev (rev x)) x)))

; The problem was that before entering a sub-induction, the hypothesis (P) --
; that is, the literal (NOT (P)) -- was dropped.  Here is the relevant portion
; of a log using Version_7.2.

;   Subgoal *1/2'5'
;   (IMPLIES (AND (P) (TRUE-LISTP X2))
;            (EQUAL (REV (MY-APP RV (LIST X1)))
;                   (CONS X1 (REV RV)))).
;
;   We suspect that the terms (TRUE-LISTP X2) and (P) are irrelevant to
;   the truth of this conjecture and throw them out.  We will thus try
;   to prove
;
;   Subgoal *1/2'6'
;   (EQUAL (REV (MY-APP RV (LIST X1)))
;          (CONS X1 (REV RV))).
;
;   Name the formula above *1.1.

; Since the exported defthm above requires (P) in order to expand MY-APP, the
; goal displayed immediately above isn't a theorem.  So we desired a
; modification of the Criterion B above, on components, that would no longer
; drop (P).

; Our initial solution was a bit elaborate.  In essence, it maintained a world
; global whose value is an alist that identifies "never irrelevant" function
; symbols.  For a rewrite rule, if a hypothesis and the left-hand side had
; disjoint sets of free variables, and the hypothesis was the application of
; some function symbol F to distinct variables, then F was identified as "never
; irrelevant".  We actually went a bit further, by associating a "parity" with
; each such function symbol, both because the hypothesis might actually be (NOT
; (F ...)) and because we allowed the left-hand side to contribute.  The
; "parity" could be t or nil, or even :both (to represent both parities).  We
; extended this world global not only for rewrite rules but also for rules of
; class :definition, :forward-chaining, :linear, and :type-prescription.

; That seemed to work well: it solved our original problem without noticeably
; slowing down the regression suite or even the time for the expensive form
; (include-book "doc/top" :dir :system).

; We then presented this change in the UT Austin ACL2 seminar, and a sequence
; of events caused us to change our heuristics again.

;   (1) During that talk, we stressed the importance of dropping irrelevant
;       literals so that an unsuitable induction isn't selected.  Marijn Heule
;       thus made the intriguing suggestion of keeping the literals and simply
;       ignoring them in our induction heuristics.
;
;   (2) We tried such a change.  Our implementation actually caused
;       eliminate-irrelevance-clause to hide the irrelevant literals rather
;       then to delete then; then, induction would unhide them immediately
;       after choosing an induction scheme.
;
;   (3) The regression exhibited failures, however, because subsumption was no
;       longer succeeding in cases where it had previously -- a goal was no
;       longer subsumed by a previous sibling, but was subsumed by the original
;       goal, causing the proof to abort immediately.  (See below for details.)
;
;   (4) So we decided to drop literals once again, rather than merely to hide
;       them.
;
;   (5) But on further reflection, it seemed a bit far-fetched that a
;       hypothesis (P1 X) could be relevant to simplifying (P2 Y Z) in the way
;       shown above that (P) can be relevant to simplifying (P2 Y Z).  We can
;       construct an example; but we think such examples are likely to be rare.
;       The failures due to lack of subsumption led us to be nervous about
;       keeping literals that Criterion B would otherwise delete.  So we
;       decided on a very simple modification of Criterion B: only drop
;       applications of functions to one or more variables.  This very limited
;       case of keeping a literal seems unlikely to interfere with subsumption,
;       since that literal could typically be reasonably expected to occur in
;       all goals that are stable under simplification.

; Returning to (3) above, here is how subsumption failed for lemma perm-del in
; community book books/models/jvm/m5/perm.lisp, when we merely applied HIDE to
; literals rather than deleting them.  In the failed proof, we see the
; following.

;   Subgoal *1.1/4'''
;   (IMPLIES (AND (NOT (HIDE (CONSP X2)))
;                 (NOT (EQUAL A X1))
;                 (MEM X1 Y)
;                 (NOT (HIDE (CONSP DL))))
;            (MEM X1 (DEL A Y))).
;
;   Name the formula above *1.1.1.

; Then later we see:

;   So we now return to *1.1.2, which is
;
;   (IMPLIES (AND (NOT (PERM (DEL X3 X4) (DEL X3 DL0)))
;                 (NOT (EQUAL X3 X1))
;                 (MEM X1 Y)
;                 (MEM X3 DL)
;                 (PERM X4 DL0))
;            (MEM X1 (DEL X3 Y))).

; In Version_7.2 and also currently, the terms with HIDE in the first goal are
; simply gone; so the first goal subsumes the second goal under the
; substitution mapping A to X3.  However, with the first goal as shown above
; (from our experiment in hiding irrelevant literals), subsumption fails
; because the hypothesis (NOT (HIDE (CONSP X2))) -- that is, the literal (HIDE
; (CONSP X2)) -- is not present in the second goal.

  (declare (ignore hist wrld state))
  (cond
   ((not (assoc-eq 'being-proved-by-induction
                   (access prove-spec-var pspv :pool)))
    (mv 'miss nil nil nil))
   (t (let* ((partitioning (m&m (pair-vars-with-lits cl)
                                'intersectp-eq/union-equal))
             (irrelevant-lits (irrelevant-lits partitioning)))
        (cond ((null irrelevant-lits)
               (mv 'miss nil nil nil))
              (t (mv 'hit
                     (list (set-difference-equal cl irrelevant-lits))
                     (add-to-tag-tree!
                      'irrelevant-lits irrelevant-lits
                      (add-to-tag-tree!
                       'clause cl nil))
                     pspv)))))))

(defun eliminate-irrelevance-clause-msg1 (signal clauses ttree pspv state)

; The arguments to this function are the standard ones for an output
; function in the waterfall.  See the discussion of the waterfall.

  (declare (ignore signal pspv clauses))
  (let* ((lits (tagged-object 'irrelevant-lits ttree))
         (clause (tagged-object 'clause ttree))
         (concl (car (last clause))))
    (cond
     ((equal (length lits)
             (length clause))
      (fms "We suspect that this conjecture is not a theorem.  We ~
            might as well be trying to prove~|"
           nil
           (proofs-co state)
           state
           (term-evisc-tuple nil state)))
     (t
      (let ((iterms (cond
                     ((member-equal concl lits)
                      (append
                       (dumb-negate-lit-lst
                        (remove1-equal concl lits))
                       (list concl)))
                     (t (dumb-negate-lit-lst lits)))))
        (fms "We suspect that the term~#0~[ ~*1 is~/s ~*1 are~] irrelevant to ~
              the truth of this conjecture and throw ~#0~[it~/them~] out.  We ~
              will thus try to prove~|"
             (list
              (cons #\0 iterms)
              (cons #\1 (tilde-*-untranslate-lst-phrase iterms
                                                        nil t (w state))))
             (proofs-co state)
             state
             (term-evisc-tuple nil state)))))))


