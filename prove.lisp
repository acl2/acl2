; ACL2 Version 8.0 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2017, Regents of the University of Texas

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
       ((the (signed-byte 30) step-limit) term ttree)
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
                      (erp val latches)
                      (pstk
                       (ev-fncall fn (strip-cadrs expanded-args) state nil t
                                  nil))
                      (declare (ignore latches))
                      (cond
                       (erp

; We following a suggestion from Matt Wilding and attempt to simplify the term
; before applying HIDE.

                        (let ((new-term1 (cons-term fn expanded-args)))
                          (sl-let (new-term2 ttree)
                                  (expand-abbreviations-with-lemma
                                   new-term1 geneqv pequiv-info
                                   fns-to-be-ignored-by-rewrite
                                   rdepth step-limit ens wrld state ttree)
                                  (cond
                                   ((equal new-term2 new-term1)
                                    (mv step-limit
                                        (mcons-term* 'hide new-term1)
                                        (push-lemma (fn-rune-nume 'hide nil nil wrld)
                                                    ttree)))
                                   (t (mv step-limit new-term2 ttree))))))
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
               ((the (signed-byte 30) step-limit) term ttree)
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

(defun and-orp (term bool)

; We return t or nil according to whether term is a disjunction
; (if bool is t) or conjunction (if bool is nil).

  (case-match term
              (('if & c2 c3)
               (if bool
                   (or (equal c2 *t*) (equal c3 *t*))
                 (or (equal c2 *nil*) (equal c3 *nil*))))))

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
              (and-orp (access rewrite-rule (car lemmas) :rhs) bool))
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
         (cond ((and-orp (lambda-body (ffn-symb term)) bool)
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
                  (and-orp (access def-body def-body :concl)
                           bool))
             (sl-let
              (term ttree)
              (with-accumulated-persistence
               (access def-body def-body :rune)
               ((the (signed-byte 30) step-limit) term ttree)
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
                    ((the (signed-byte 30) step-limit) term ttree)
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
                   :rw-cache-state (rw-cache-state ,wrld))
           ,@args))

; We now finish the development of tau-clause...  To recap our story so far: In
; the file tau.lisp we defined everything we need to implement tau-clause
; except for its connection to type-alist and the linear pot-lst.  Now we can
; define tau-clause.

(defun cheap-type-alist-and-pot-lst (cl ens wrld state)

; Given a clause cl, we build a type-alist and linear pot-lst with all of the
; literals in cl assumed false.  The pot-lst is built with the cheap-linearp
; flag on, which means we do not rewrite terms before turning them into polys
; and we add no linear lemmas.  We insure that the type-alist has no
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
                                   :cheap-linearp t)
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


; Section:  PUSH-CLAUSE and The Pool

; At the opposite end of the waterfall from the preprocessor is push-clause,
; where we actually put a clause into the pool.  We develop it now.

(defun more-than-simplifiedp (hist)

; Return t if hist contains a process besides simplify-clause (and its
; mates settled-down-clause and preprocess-clause), where we don't count
; certain top-level hints: :OR, or top-level hints that create hidden clauses.

  (cond ((null hist) nil)
        ((member-eq (caar hist) '(settled-down-clause
                                  simplify-clause
                                  preprocess-clause))
         (more-than-simplifiedp (cdr hist)))
        ((eq (caar hist) 'apply-top-hints-clause)
         (if (or (tagged-objectsp 'hidden-clause
                                  (access history-entry (car hist) :ttree))
                 (tagged-objectsp ':or
                                  (access history-entry (car hist) :ttree)))
             (more-than-simplifiedp (cdr hist))
           t))
        (t t)))

(defun delete-assoc-eq-lst (lst alist)
  (declare (xargs :guard (if (symbol-listp lst)
                             (alistp alist)
                           (symbol-alistp alist))))
  (if (consp lst)
      (delete-assoc-eq-lst (cdr lst)
                           (delete-assoc-eq (car lst) alist))
    alist))

(defun delete-assumptions-1 (recs only-immediatep)

; See comment for delete-assumptions.  This function returns (mv changedp
; new-recs), where if changedp is nil then new-recs equals recs.

  (cond ((endp recs) (mv nil nil))
        (t (mv-let (changedp new-cdr-recs)
                   (delete-assumptions-1 (cdr recs) only-immediatep)
                   (cond ((cond
                           ((eq only-immediatep 'non-nil)
                            (access assumption (car recs) :immediatep))
                           ((eq only-immediatep 'case-split)
                            (eq (access assumption (car recs) :immediatep)
                                'case-split))
                           ((eq only-immediatep t)
                            (eq (access assumption (car recs) :immediatep)
                                t))
                           (t t))
                          (mv t new-cdr-recs))
                         (changedp
                          (mv t
                              (cons (car recs) new-cdr-recs)))
                         (t (mv nil recs)))))))

(defun delete-assumptions (ttree only-immediatep)

; We delete the assumptions in ttree.  We give the same interpretation to
; only-immediatep as in collect-assumptions.

  (let ((objects (tagged-objects 'assumption ttree)))
    (cond (objects
           (mv-let
            (changedp new-objects)
            (delete-assumptions-1 objects only-immediatep)
            (cond ((null changedp) ttree)
                  (new-objects
                   (extend-tag-tree
                    'assumption
                    new-objects
                    (remove-tag-from-tag-tree! 'assumption ttree)))
                  (t (remove-tag-from-tag-tree! 'assumption ttree)))))
          (t ttree))))

#+acl2-par
(defun save-and-print-acl2p-checkpoint (cl-id prettyified-clause
                                              old-pspv-pool-lst forcing-round
                                              state)

; We almost note that we are changing the global state of the program by
; returning a modified state.  However, we manually ensure that this global
; change is thread-safe by calling with-acl2p-checkpoint-saving-lock, and so
; instead, we give ourselves the Okay to call f-put-global@par.

  (declare (ignorable cl-id prettyified-clause state))
  (let* ((new-pair (cons cl-id prettyified-clause))
         (newp
          (with-acl2p-checkpoint-saving-lock
           (cond
            ((member-equal new-pair (f-get-global 'acl2p-checkpoints-for-summary
                                                  state))
             nil)
            (t
             (prog2$
              (f-put-global@par 'acl2p-checkpoints-for-summary
                                (cons new-pair
                                      (f-get-global
                                       'acl2p-checkpoints-for-summary state))
                                state)
              t))))))
    (and
     newp
     (with-output-lock
      (progn$
       (cw "~%~%([ An ACL2(p) key checkpoint:~%~%~s0~%"
           (string-for-tilde-@-clause-id-phrase cl-id))
       (cw "~x0" prettyified-clause)

; Parallelism no-fix: we are encountering a problem that we've known about from
; within the first few months of looking at parallelizing the waterfall.  When
; two sibling subgoals both push for induction, the second push doesn't know
; about the first proof's push in parallel mode.  So, the number of the second
; proof (e.g., *1.2) gets printed as if the first push hasn't happened (e.g.,
; *1.2 gets mistakenly called *1.1).  Rather than fix this (the problem is
; inherent to the naming scheme of ACL2), we punt and say what the name _could_
; be (e.g., we print *1.1 for what's really *1.2).  The following non-theorem
; showcases this problem.  See :doc topic set-waterfall-printing.

; (thm (equal (append (car (cons x x)) y z) (append x x y)))

; The sentence in the following cw call concerning the halting of the proof
; attempt is motivated by the following example -- which is relevant because
; ACL2(p) with :limited waterfall-printing does not print a message that says
; the :do-not-induct hint causes the proof to abort.

; (thm (equal (append x (append y z)) (append (append x y) z))
;      :hints (("Goal" :do-not-induct t)))

       (cw "~%~%The above subgoal may cause a goal to be pushed for proof by ~
            induction.  The pushed goal's new name might be ~@0.  Note that ~
            we may instead decide (either now or later) to prove the original ~
            conjecture by induction.  Also note that if a hint indicates that ~
            this subgoal or the original conjecture should not be proved by ~
            induction, the proof attempt will halt.~%~%])~%~%"
           (tilde-@-pool-name-phrase
            forcing-round
            old-pspv-pool-lst)))))))

#+acl2-par
(defun find-the-first-checkpoint (h checkpoint-processors)

; "H" is the history reversed, which really means h is in the order that the
; entries were added.  E.g. the history entry for subgoal 1.2 is before the
; entry for 1.1.4.  To remind us that this is not the "standard ACL2 history"
; (which is often in the other order), we name the variable "h" instead of
; "hist."

  (cond ((atom h) ; occurs when we are at the top-level goal
         nil)
        ((atom (cdr h))
         (car h)) ; maybe this should also be an error
        ((member (access history-entry (cadr h) :processor)
                 checkpoint-processors)
         (car h))

; Parallelism blemish: we haven't thought through how specious entries affect
; this function.  The following code is left as a hint at what might be needed.

;        ((or (and (consp (access history-entry (cadr h) :processor))
;                  (equal (access history-entry (cadr h) :processor)
;                         'specious))

        (t (find-the-first-checkpoint (cdr h) checkpoint-processors))))

#+acl2-par
(defun acl2p-push-clause-printing (cl hist pspv wrld state)
  (cond
   ((null cl)

; The following non-theorem illustrates the case where we generate the clause
; nil, and instead of printing the associated key checkpoint, we inform the
; user that nil was generated from that checkpoint.

; (thm (equal (append (car (cons x x)) y z) (append x x y)))

    (cw "~%~%A goal of ~x0 has been generated!  Obviously, the proof attempt ~
         has failed.~%"
        cl))
   (t
    (let* ((hist-entry
            (find-the-first-checkpoint
             (reverse hist)
             (f-get-global 'checkpoint-processors state)))

           (checkpoint-clause
            (or (access history-entry hist-entry :clause)

; We should be able to add an assertion that, if the hist-entry is nil (and
; thus, the :clause field of hist-entry is also nil), cl always has the same
; printed representation as the original conjecture.  However, since we do not
; have access to the original conjecture in this function, we avoid such an
; assertion.

                cl))
           (cl-id (access history-entry hist-entry :cl-id))
           (cl-id (if cl-id cl-id *initial-clause-id*))
           (forcing-round (access clause-id cl-id :forcing-round))
           (old-pspv-pool-lst
            (pool-lst (cdr (access prove-spec-var pspv :pool))))
           (prettyified-clause (prettyify-clause checkpoint-clause
                                                 (let*-abstractionp state)
                                                 wrld)))
      (save-and-print-acl2p-checkpoint cl-id prettyified-clause
                                       old-pspv-pool-lst forcing-round
                                       state)))))

(defun@par push-clause (cl hist pspv wrld state)

; Roughly speaking, we drop cl into the pool of pspv and return.
; However, we sometimes cause the waterfall to abort further
; processing (either to go straight to induction or to fail) and we
; also sometimes choose to push a different clause into the pool.  We
; even sometimes miss and let the waterfall fall off the end of the
; ledge!  We make this precise in the code below.

; The pool is actually a list of pool-elements and is treated as a
; stack.  The clause-set is a set of clauses and is almost always a
; singleton set.  The exception is when it contains the clausification
; of the user's initial conjecture.

; The expected tags are:

; 'TO-BE-PROVED-BY-INDUCTION - the clause set is to be given to INDUCT
; 'BEING-PROVED-BY-INDUCTION - the clause set has been given to INDUCT and
;                              we are working on its subgoals now.

; Like all clause processors, we return four values: the signal,
; which is either 'hit, 'miss or 'abort, the new set of clauses, in this
; case nil, the ttree for whatever action we take, and the new
; value of pspv (containing the new pool).

; Warning: Generally speaking, this function either 'HITs or 'ABORTs.
; But it is here that we look out for :DO-NOT-INDUCT name hints.  For
; such hints we want to act like a :BY name-clause-id was present for
; the clause.  But we don't know the clause-id and the :BY handling is
; so complicated we don't want to reproduce it.  So what we do instead
; is 'MISS and let the waterfall fall off the ledge to the nil ledge.
; See waterfall0.  This function should NEVER return a 'MISS unless
; there is a :DO-NOT-INDUCT name hint present in the hint-settings,
; since waterfall0 assumes that it falls off the ledge only in that
; case.

  (declare (ignorable state wrld)) ; actually ignored in #-acl2-par
  (prog2$

; Every branch of the cond below, with the exception of when cl is null,
; results in an ACL2(p) key checkpoint.  As such, it is reasonable to print the
; checkpoint at the very beginning of this function.
; Acl2p-push-clause-printing contains code that handles the case where cl is
; nil.

; Parallelism blemish: create a :doc topic on ACL2(p) checkpoints and reference
; it in the above comment.

   (parallel-only@par (acl2p-push-clause-printing cl hist pspv wrld state))
   (let ((pool (access prove-spec-var pspv :pool))
         (do-not-induct-hint-val
          (cdr (assoc-eq :do-not-induct
                         (access prove-spec-var pspv :hint-settings)))))
     (cond
      ((null cl)

; The empty clause was produced.  Stop the waterfall by aborting.  Produce the
; ttree that explains the abort.  Drop the clause set containing the empty
; clause into the pool so that when we look for the next goal we see it and
; quit.

       (mv 'abort
           nil
           (add-to-tag-tree! 'abort-cause 'empty-clause nil)
           (change prove-spec-var pspv
                   :pool (cons (make pool-element
                                     :tag 'TO-BE-PROVED-BY-INDUCTION
                                     :clause-set '(nil)
                                     :hint-settings nil)
                               pool))))
      ((and (or (and (not (access prove-spec-var pspv :otf-flg))
                     (eq do-not-induct-hint-val t))
                (eq do-not-induct-hint-val :otf-flg-override))
            (not (assoc-eq :induct (access prove-spec-var pspv
                                           :hint-settings))))

; We need induction but can't use it.  Stop the waterfall by aborting.  Produce
; the ttree that explains the abort.  Drop the clause set containing the empty
; clause into the pool so that when we look for the next goal we see it and
; quit.  Note that if :otf-flg is specified, then we skip this case because we
; do not want to quit just yet.  We will see the :do-not-induct value again in
; prove-loop1 when we return to the goal we are pushing.

       (mv 'abort
           nil
           (add-to-tag-tree! 'abort-cause
                             (if (eq do-not-induct-hint-val :otf-flg-override)
                                 'do-not-induct-otf-flg-override
                               'do-not-induct)
                             nil)
           (change prove-spec-var pspv
                   :pool (cons (make pool-element
                                     :tag 'TO-BE-PROVED-BY-INDUCTION
                                     :clause-set '(nil)
                                     :hint-settings nil)
                               pool))))
      ((and do-not-induct-hint-val
            (not (member-eq do-not-induct-hint-val '(t :otf :otf-flg-override)))
            (not (assoc-eq :induct
                           (access prove-spec-var pspv :hint-settings))))

; In this case, we have seen a :DO-NOT-INDUCT name hint (where name isn't t)
; that is not overridden by an :INDUCT hint.  We would like to give this clause
; a :BY.  We can't do it here, as explained above.  So we will 'MISS instead.

       (mv 'miss nil nil nil))
      ((and (not (access prove-spec-var pspv :otf-flg))
            (not (eq do-not-induct-hint-val :otf))
            (or
             (and (null pool) ;(a)
                  (more-than-simplifiedp hist)
                  (not (assoc-eq :induct (access prove-spec-var pspv
                                                 :hint-settings))))
             (and pool ;(b)
                  (not (assoc-eq 'being-proved-by-induction pool))
                  (not (assoc-eq :induct (access prove-spec-var pspv
                                                 :hint-settings))))))

; We have not been told to press Onward Thru the Fog and

; either (a) this is the first time we've ever pushed anything and we have
; applied processes other than simplification to it and we have not been
; explicitly instructed to induct for this formula, or (b) we have already put
; at least one goal into the pool but we have not yet done our first induction
; and we are not being explicitly instructed to induct for this formula.

; Stop the waterfall by aborting.  Produce the ttree explaining the abort.
; Drop the clausification of the user's input into the pool in place of
; everything else in the pool.

; Note: We once reverted to the output of preprocess-clause in prove.  However,
; preprocess (and clausify-input) applies unconditional :REWRITE rules and we
; want users to be able to type exactly what the system should go into
; induction on.  The theorem that preprocess-clause screwed us on was HACK1.
; It screwed us by distributing * and GCD.

       (mv 'abort
           nil
           (add-to-tag-tree! 'abort-cause 'revert nil)
           (change prove-spec-var pspv

; Before Version_2.6 we did not modify the tag-tree here.  The result was that
; assumptions created by forcing before reverting to the original goal still
; generated forcing rounds after the subsequent proof by induction.  When this
; bug was discovered we added code below to use delete-assumptions to remove
; assumptions from the tag-tree.  Note that we are not modifying the
; 'accumulated-ttree in state, so these assumptions still reside there; but
; since that ttree is only used for reporting rules used and is intended to
; reflect the entire proof attempt, this decision seems reasonable.

; Version_2.6 was released on November 29, 2001.  On January 18, 2002, we
; received email from Francisco J. Martin-Mateos reporting a soundness bug,
; with an example that is included after the definition of push-clause.  The
; problem turned out to be that we did not remove :use and :by tagged values
; from the tag-tree here.  The result was that if the early part of a
; successful proof attempt had involved a :use or :by hint but then the early
; part was thrown away and we reverted to the original goal, the :use or :by
; tagged value remained in the tag-tree.  When the proof ultimately succeeded,
; this tagged value was used to update (global-val
; 'proved-functional-instances-alist (w state)), which records proved
; constraints so that subsequent proofs can avoid proving them again.  But
; because the prover reverted to the original goal rather than taking advantage
; of the :use hint, those constraints were not actually proved in this case and
; might not be valid!

; So, we have decided that rather than remove assumptions and :by/:use tags
; from the :tag-tree of pspv, we would just replace that tag-tree by the empty
; tag-tree.  We do not want to get burned by a third such problem!

                   :tag-tree nil
                   :pool (list (make pool-element
                                     :tag 'TO-BE-PROVED-BY-INDUCTION
                                     :clause-set

; At one time we clausified here.  But some experiments suggested that the
; prover can perhaps do better by simply doing its thing on each induction
; goal, starting at the top of the waterfall.  So, now we pass the same clause
; to induction as it would get if there were a hint of the form ("Goal" :induct
; term), where term is the user-supplied-term.

                                     (list (list
                                            (access prove-spec-var pspv
                                                    :user-supplied-term)))

; Below we set the :hint-settings for the input clause, doing exactly what
; find-applicable-hint-settings does.  Unfortunately, we haven't defined that
; function yet.  Fortunately, it's just a simple assoc-equal.  In addition,
; that function goes on to compute a second value we don't need here.  So
; rather than go to the bother of moving its definition up to here we just open
; code the part we need.  We also remove top-level hints that were supposed to
; apply before we got to push-clause.

                                     :hint-settings
                                     (delete-assoc-eq-lst
                                      (cons ':reorder *top-hint-keywords*)

; We could also delete :induct, but we know it's not here!

                                      (cdr
                                       (assoc-equal
                                        *initial-clause-id*
                                        (access prove-spec-var pspv
                                                :orig-hints)))))))))
      #+acl2-par
      ((and (serial-first-form-parallel-second-form@par nil t)
            (not (access prove-spec-var pspv :otf-flg))
            (not (eq do-not-induct-hint-val :otf))
            (null pool)
            ;; (not (more-than-simplifiedp hist)) ; implicit to the cond
            (not (assoc-eq :induct (access prove-spec-var pspv
                                           :hint-settings))))
       (mv 'hit
           nil
           (add-to-tag-tree! 'abort-cause 'maybe-revert nil)
           (change prove-spec-var pspv

; Parallelism blemish: there may be a bug in ACL2(p) related to the comment
; above (in this function's definition) that starts with "Before Version_2.6 we
; did not modify the tag-tree here."  To fix this (likely) bug, don't reset the
; tag-tree here -- just remove the ":tag-tree nil" -- and instead do it when we
; convert a maybe-to-be-proved-by-induction to a to-be-proved-by-induction.

                   :tag-tree nil
                   :pool
                   (append
                    (list
                     (list 'maybe-to-be-proved-by-induction
                           (make pool-element
                                 :tag 'TO-BE-PROVED-BY-INDUCTION
                                 :clause-set (list cl)
                                 :hint-settings (access prove-spec-var pspv
                                                        :hint-settings))
                           (make pool-element
                                 :tag 'TO-BE-PROVED-BY-INDUCTION
                                 :clause-set

; See above comment that starts with "At one time we clausified here."

                                 (list (list
                                        (access prove-spec-var pspv
                                                :user-supplied-term)))

; See above comment that starts with "Below we set the :hint-settings for..."

                                 :hint-settings
                                 (delete-assoc-eq-lst
                                  (cons ':reorder *top-hint-keywords*)

; We could also delete :induct, but we know it's not here!

                                  (cdr
                                   (assoc-equal
                                    *initial-clause-id*
                                    (access prove-spec-var pspv
                                            :orig-hints)))))))
                    pool))))
      (t (mv 'hit
             nil
             nil
             (change prove-spec-var pspv
                     :pool
                     (cons
                      (make pool-element
                            :tag 'TO-BE-PROVED-BY-INDUCTION
                            :clause-set (list cl)
                            :hint-settings (access prove-spec-var pspv
                                                   :hint-settings))
                      pool))))))))

; Below is the soundness bug example reported by Francisco J. Martin-Mateos.

; ;;;============================================================================
;
; ;;;
; ;;; A bug in ACL2 (2.5 and 2.6). Proving "0=1".
; ;;; Francisco J. Martin-Mateos
; ;;; email: Francisco-Jesus.Martin@cs.us.es
; ;;; Dpt. of Computer Science and Artificial Intelligence
; ;;; University of SEVILLE
; ;;;
; ;;;============================================================================
;
; ;;;   I've found a bug in ACL2 (2.5 and 2.6). The following events prove that
; ;;; "0=1".
;
; (in-package "ACL2")
;
; (encapsulate
;  (((g1) => *))
;
;  (local
;   (defun g1 ()
;     0))
;
;  (defthm 0=g1
;    (equal 0 (g1))
;    :rule-classes nil))
;
; (defun g1-lst (lst)
;   (cond ((endp lst) (g1))
;  (t (g1-lst (cdr lst)))))
;
; (defthm g1-lst=g1
;   (equal (g1-lst lst) (g1)))
;
; (encapsulate
;  (((f1) => *))
;
;  (local
;   (defun f1 ()
;     1)))
;
; (defun f1-lst (lst)
;   (cond ((endp lst) (f1))
;  (t (f1-lst (cdr lst)))))
;
; (defthm f1-lst=f1
;   (equal (f1-lst lst) (f1))
;   :hints (("Goal"
;     :use (:functional-instance g1-lst=g1
;           (g1 f1)
;           (g1-lst f1-lst)))))
;
; (defthm 0=f1
;   (equal 0 (f1))
;   :rule-classes nil
;   :hints (("Goal"
;     :use (:functional-instance 0=g1
;           (g1 f1)))))
;
; (defthm 0=1
;   (equal 0 1)
;   :rule-classes nil
;   :hints (("Goal"
;     :use (:functional-instance 0=f1
;           (f1 (lambda () 1))))))
;
; ;;;   The theorem F1-LST=F1 is not proved via functional instantiation but it
; ;;; can be proved via induction. So, the constraints generated by the
; ;;; functional instantiation hint has not been proved. But when the theorem
; ;;; 0=F1 is considered, the constraints generated in the functional
; ;;; instantiation hint are bypassed because they ".. have been proved when
; ;;; processing the event F1-LST=F1", and the theorem is proved !!!. Finally,
; ;;; an instance of 0=F1 can be used to prove 0=1.
;
; ;;;============================================================================

; We now develop the functions for reporting what push-clause did.  Except,
; pool-lst has already been defined, in support of proof-trees.

(defun push-clause-msg1-abort (cl-id ttree pspv state)

; Ttree has exactly one object associated with the tag 'abort-cause.

  (let ((temp (tagged-object 'abort-cause ttree))
        (cl-id-phrase (tilde-@-clause-id-phrase cl-id))
        (gag-mode (gag-mode)))
    (case temp
      (empty-clause
       (if gag-mode
           (msg "A goal of NIL, ~@0, has been generated!  Obviously, the ~
                 proof attempt has failed.~|"
                cl-id-phrase)
         ""))
      ((do-not-induct do-not-induct-otf-flg-override)
       (msg "Normally we would attempt to prove ~@0 by induction.  However, a ~
             :DO-NOT-INDUCT hint was supplied to abort the proof attempt.~|"
            cl-id-phrase
            (if (eq temp 'do-not-induct)
                t
              :otf-flg-override)))
      (otherwise
       (msg "Normally we would attempt to prove ~@0 by induction.  However, ~
             we prefer in this instance to focus on the original input ~
             conjecture rather than this simplified special case.  We ~
             therefore abandon our previous work on this conjecture and ~
             reassign the name ~@1 to the original conjecture.  (See :DOC ~
             otf-flg.)~#2~[~/  [Note:  Thanks again for the hint.]~]~|"
            cl-id-phrase
            (tilde-@-pool-name-phrase
             (access clause-id cl-id :forcing-round)
             (pool-lst
              (cdr (access prove-spec-var pspv
                           :pool))))
            (if (and (not gag-mode)
                     (access prove-spec-var pspv
                             :hint-settings))
                1
              0))))))

(defun push-clause-msg1 (cl-id signal clauses ttree pspv state)

; Push-clause was given a clause and produced a signal and ttree.  We
; are responsible for printing out an explanation of what happened.
; We look at the ttree to determine what happened.  We return state.

  (declare (ignore clauses))
  (cond ((eq signal 'abort)
         (fms "~@0"
              (list (cons #\0 (push-clause-msg1-abort cl-id ttree pspv state)))
              (proofs-co state)
              state
              nil))
        (t
         (fms "Name the formula above ~@0.~|"
              (list (cons #\0 (tilde-@-pool-name-phrase
                               (access clause-id cl-id :forcing-round)
                               (pool-lst
                                (cdr (access prove-spec-var pspv
                                             :pool))))))
              (proofs-co state)
              state
              nil))))

; Section:  Use and By hints

(defun clause-set-subsumes-1 (init-subsumes-count cl-set1 cl-set2 acc)

; We return t if the first set of clauses subsumes the second in the sense that
; for every member of cl-set2 there exists a member of cl-set1 that subsumes
; it.  We return '? if we don't know (but this can only happen if
; init-subsumes-count is non-nil); see the comment in subsumes.

  (cond ((null cl-set2) acc)
        (t (let ((temp (some-member-subsumes init-subsumes-count
                                             cl-set1 (car cl-set2) nil)))
             (and temp ; thus t or maybe, if init-subsumes-count is non-nil, ?
                  (clause-set-subsumes-1 init-subsumes-count
                                         cl-set1 (cdr cl-set2) temp))))))

(defun clause-set-subsumes (init-subsumes-count cl-set1 cl-set2)

; This function is intended to be identical, as a function, to
; clause-set-subsumes-1 (with acc set to t).  The first two disjuncts are
; optimizations that may often apply.

  (or (equal cl-set1 cl-set2)
      (and cl-set1
           cl-set2
           (null (cdr cl-set2))
           (subsetp-equal (car cl-set1) (car cl-set2)))
      (clause-set-subsumes-1 init-subsumes-count cl-set1 cl-set2 t)))

(defun preprocess-clause? (cl hist pspv wrld state step-limit)
  (cond ((member-eq 'preprocess-clause
                    (assoc-eq :do-not (access prove-spec-var pspv
                                              :hint-settings)))
         (mv step-limit 'miss nil nil nil))
        (t (preprocess-clause cl hist pspv wrld state step-limit))))

(defun apply-use-hint-clauses (temp clauses pspv wrld state step-limit)

; Note: There is no apply-use-hint-clause.  We just call this function
; on a singleton list of clauses.

; Temp is the result of assoc-eq :use in a pspv :hint-settings and is
; non-nil.  We discuss its shape below.  But this function applies the
; given :use hint to each clause in clauses and returns (mv 'hit
; new-clauses ttree new-pspv).

; Temp is of the form (:USE lmi-lst (hyp1 ... hypn) constraint-cl k
; event-names new-entries) where each hypi is a theorem and
; constraint-cl is a clause that expresses the conjunction of all k
; constraints.  Lmi-lst is the list of lmis that generated these hyps.
; Constraint-cl is (probably) of the form {(if constr1 (if constr2 ...
; (if constrk t nil)... nil) nil)}.  We add each hypi as a hypothesis
; to each goal clause, cl, and in addition, create one new goal for
; each constraint.  Note that we discard the extended goal clause if
; it is a tautology.  Note too that the constraints generated by the
; production of the hyps are conjoined into a single clause in temp.
; But we hit that constraint-cl with preprocess-clause to pick out its
; (non-tautological) cases and that code will readily unpack the if
; structure of a typical conjunct.  We remove the :use hint from the
; hint-settings so we don't fire the same :use again on the subgoals.

; We return (mv new-step-limit 'hit new-clauses ttree new-pspv).

; The ttree returned has at most two tags.  The first is :use and has
; ((lmi-lst hyps constraint-cl k event-names new-entries)
; . non-tautp-applications) as its value, where non-tautp-applications
; is the number of non-tautologous clauses we got by adding the hypi
; to each clause.  However, it is possible the :use tag is not
; present: if clauses is nil, we don't report a :use.  The optional
; second tag is the ttree produced by preprocess-clause on the
; constraint-cl.  If the preprocess-clause is to be hidden anyway, we
; ignore its tree (but use its clauses).

  (let* ((hyps (caddr temp))
         (constraint-cl (cadddr temp))
         (new-pspv (change prove-spec-var pspv
                           :hint-settings
                           (remove1-equal temp
                                          (access prove-spec-var
                                                  pspv
                                                  :hint-settings))))
         (A (disjoin-clause-segment-to-clause-set (dumb-negate-lit-lst hyps)
                                                  clauses))
         (non-tautp-applications (length A)))

; In this treatment, the final set of goal clauses will the union of
; sets A and C.  A stands for the "application clauses" (obtained by
; adding the use hyps to each clause) and C stands for the "constraint
; clauses."  Non-tautp-applications is |A|.

    (cond
     ((null clauses)

; In this case, there is no point in generating the constraints!  We
; anticipate this happening if the user provides both a :use and a
; :cases hint and the :cases hint (which is applied first) proves the
; goal completely.  If that were to happen, clauses would be output of
; the :cases hint and pspv would be its output pspv, from which the
; :cases had been deleted.  So we just delete the :use hint from that
; pspv and call it quits, without reporting a :use hint at all.

      (mv step-limit 'hit nil nil new-pspv))
     (t
      (sl-let
       (signal C ttree irrel-pspv)
       (preprocess-clause? constraint-cl nil pspv wrld state step-limit)
       (declare (ignore irrel-pspv))
       (cond
        ((eq signal 'miss)
         (mv step-limit
             'hit
             (conjoin-clause-sets
              A
              (conjoin-clause-to-clause-set constraint-cl
                                            nil))
             (add-to-tag-tree! :use
                               (cons (cdr temp)
                                     non-tautp-applications)
                               nil)
             new-pspv))
        ((or (tag-tree-occur 'hidden-clause
                             t
                             ttree)
             (and C
                  (null (cdr C))
                  constraint-cl
                  (null (cdr constraint-cl))
                  (equal (prettyify-clause-simple (car C))
                         (car constraint-cl))))
         (mv step-limit
             'hit
             (conjoin-clause-sets A C)
             (add-to-tag-tree! :use
                               (cons (cdr temp)
                                     non-tautp-applications)
                               nil)
             new-pspv))
        (t (mv step-limit
               'hit
               (conjoin-clause-sets A C)
               (add-to-tag-tree! :use
                                 (cons (cdr temp)
                                       non-tautp-applications)
                                 (add-to-tag-tree! 'preprocess-ttree
                                                   ttree
                                                   nil))
               new-pspv))))))))

(defun apply-cases-hint-clause (temp cl pspv wrld)

; Temp is the value associated with :cases in a pspv :hint-settings
; and is non-nil.  It is thus of the form (:cases term1 ... termn).
; For each termi we create a new clause by adding its negation to the
; goal clause, cl, and in addition, we create a final goal by adding
; all termi.  As with a :use hint, we remove the :cases hint from the
; hint-settings so that the waterfall doesn't loop!

; We return (mv 'hit new-clauses ttree new-pspv).

  (let ((new-clauses
         (remove-trivial-clauses
          (conjoin-clause-to-clause-set
           (disjoin-clauses
            (cdr temp)
            cl)
           (split-on-assumptions

; We reverse the term-list so the user can see goals corresponding to the
; order of the terms supplied.

            (dumb-negate-lit-lst (reverse (cdr temp)))
            cl
            nil))
          wrld)))
    (mv 'hit
        new-clauses
        (add-to-tag-tree! :cases (cons (cdr temp) new-clauses) nil)
        (change prove-spec-var pspv
                :hint-settings
                (remove1-equal temp
                               (access prove-spec-var
                                       pspv
                                       :hint-settings))))))

(defun non-term-listp-msg (x w)

; Perhaps ~Y01 should be ~y below.  If someone complains about a large term
; being printed, consider making that change.

  (declare (xargs :guard t))
  (cond
   ((atom x)
    (assert$
     x
     "that fails to satisfy true-listp."))
   ((not (termp (car x) w))
    (msg "that contains the following non-termp (see :DOC term):~|~%  ~Y01"
         (car x)
         nil))
   (t (non-term-listp-msg (cdr x) w))))

(defun non-term-list-listp-msg (l w)

; Perhaps ~Y01 should be ~y below.  If someone complains about a large term
; being printed, consider making that change.

  (declare (xargs :guard t))
  (cond
   ((atom l)
    (assert$
     l
     "which fails to satisfy true-listp."))
   ((not (term-listp (car l) w))
    (msg "which has a member~|~%  ~Y01~|~%~@2"
         (car l)
         nil
         (non-term-listp-msg (car l) w)))
   (t (non-term-list-listp-msg (cdr l) w))))

(defun all-ffn-symbs-lst-lst (lst ans)
  (cond ((null lst) ans)
        (t (all-ffn-symbs-lst-lst (cdr lst)
                                  (all-ffn-symbs-lst (car lst) ans)))))

(defun eval-clause-processor (clause term stobjs-out verified-p pspv ctx state)

; Verified-p is either nil, t, or a well-formedness-guarantee of the form
; ((name fn thm-name1) . arity-alist).

; Should we do our evaluation in safe-mode?  For a relevant discussion, see the
; comment in protected-eval about safe-mode.

; Keep in sync with eval-clause-processor@par.

  (revert-world-on-error
   (let ((original-wrld (w state))
         (cl-term (subst-var (kwote clause) 'clause term)))
     (protect-system-state-globals
      (pprogn
       (mv-let
        (erp trans-result state)
        (ev-for-trans-eval cl-term (all-vars cl-term) stobjs-out ctx state

; See chk-evaluator-use-in-rule for a discussion of how we restrict the use of
; evaluators in rules of class :meta or :clause-processor, so that we can use
; aok = t here.

; Note that unlike trans-eval, ev-for-trans-eval never prints a warning when a
; user-defined stobj is modified.  Our feeling is that such warnings would be
; very distracting, since they would appear in the middle of proofs as
; clause-processor hints are processed.

                           t
                           (f-get-global 'ld-user-stobjs-modified-warning
                                         state))
        (cond
         (erp (mv (msg "Evaluation failed for the :clause-processor hint.")
                  nil
                  state))
         (t
          (assert$
           (equal (car trans-result) stobjs-out)
           (let* ((result (cdr trans-result))
                  (eval-erp (and (cdr stobjs-out) (car result)))
                  (val (if (cdr stobjs-out) (cadr result) result)))
             (cond ((stringp eval-erp)
                    (mv (msg "~s0" eval-erp) nil state))
                   ((tilde-@p eval-erp) ; a message
                    (mv (msg "Error in clause-processor hint:~|~%  ~@0"
                             eval-erp)
                        nil
                        state))
                   (eval-erp
                    (mv (msg "Error in clause-processor hint:~|~%  ~Y01"
                             term
                             nil)
                        nil
                        state))
                   (t
                    (pprogn
                     (set-w! original-wrld state)
                     (cond
                      ((equal val (list clause)) ; avoid checks below
                       (value val))
                      (t
                       (let* ((user-says-skip-termp-checkp
                               (skip-meta-termp-checks
                                (ffn-symb term) original-wrld))
                              (well-formedness-guarantee
                               (if (consp verified-p)
                                   verified-p
                                   nil))
                              (not-skipped
                               (and (not user-says-skip-termp-checkp)
                                    (not well-formedness-guarantee)))
                              (bad-arity-info
                               (if (and well-formedness-guarantee
                                        (not user-says-skip-termp-checkp))
                                   (collect-bad-fn-arity-info
                                    (cdr well-formedness-guarantee)
                                    original-wrld nil nil)
                                 nil)))
                         (cond
                          (bad-arity-info
                           (let ((name (nth 0 (car well-formedness-guarantee)))
                                 (fn (nth 1 (car well-formedness-guarantee)))
                                 (thm-name1
                                  (nth 2 (car well-formedness-guarantee))))
                             (mv (bad-arities-msg
                                  name
                                  :CLAUSE-PROCESSOR
                                  fn
                                  nil ; hyp-fn
                                  thm-name1
                                  nil ; wf-thm-name2
                                  bad-arity-info)
                                 nil state)))
                          ((and not-skipped
                                (not (logic-term-list-listp val
                                                            original-wrld)))
                           (cond
                            ((not (term-list-listp val original-wrld))
                             (mv (msg
                                  "The :CLAUSE-PROCESSOR hint~|~%  ~Y01~%did ~
                                   not evaluate to a list of clauses, but ~
                                   instead to~|~%  ~Y23~%~@4"
                                  term nil
                                  val nil
                                  (non-term-list-listp-msg
                                   val original-wrld))
                                 nil
                                 state))
                            (t
                             (mv (msg
                                  "The :CLAUSE-PROCESSOR hint~|~%  ~
                                   ~Y01~%evaluated to a list of clauses,~%  ~
                                   ~Y23,~%which however has a call of the ~
                                   following :program mode ~
                                   function~#4~[~/s~]:~|~&4."
                                  term nil
                                  val nil
                                  (collect-programs
                                   (all-ffn-symbs-lst-lst val nil)
                                   original-wrld))
                                 nil
                                 state))))
                          ((and not-skipped
                                (forbidden-fns-in-term-list-list
                                 val
                                 (access rewrite-constant
                                         (access prove-spec-var pspv
                                                 :rewrite-constant)
                                         :forbidden-fns)))
                           (mv (msg
                                "The :CLAUSE-PROCESSOR ~
                                 hint~|~%~Y01~%evaluated to a list of ~
                                 clauses~|~%~y2~%that contains a call of the ~
                                 function symbol~#3~[, ~&3, which is~/s ~&3, ~
                                 which are~] forbidden in that context.  See ~
                                 :DOC clause-processor and :DOC ~
                                 set-skip-meta-termp-checks and :DOC ~
                                 well-formedness-guarantee."
                                term nil val
                                (forbidden-fns-in-term-list-list
                                 val
                                 (access rewrite-constant
                                         (access prove-spec-var pspv
                                                 :rewrite-constant)
                                         :forbidden-fns)))
                               nil
                               state))
                          (t (value val)))))))))))))))))))

#+acl2-par
(defun eval-clause-processor@par (clause term stobjs-out verified-p pspv ctx
                                         state)

; Keep in sync with eval-clause-processor.

  (cond
   ((and

; Note that potential conjunct (f-get-global 'waterfall-parallelism state) is
; not needed, since we are in an @par definition.  Also note that a
; clause-processor returns (as per :doc clause-processor) either a list cl-list
; of clauses, or else (mv erp cl-list st_i1 ... st_in) where erp and cl-list
; are not stobjs and the st_ik are all stobjs.  Since we want to rule out
; stobjs, we therefore check that stobjs-out is (nil) or (nil nil).

     (not (or (equal stobjs-out '(nil))
              (equal stobjs-out '(nil nil))))
     (not (cdr (assoc-eq 'hacks-enabled
                         (table-alist 'waterfall-parallelism-table
                                      (w state))))))
    (mv (msg
         "Clause-processors that do not return exactly one or two values are ~
          not officially supported when waterfall parallelism is enabled.  If ~
          you wish to use such a clause-processor anyway, you can call ~x0. ~
          See :DOC set-waterfall-parallelism-hacks-enabled for more ~
          information.  "
         '(set-waterfall-parallelism-hacks-enabled t))
        nil))
   (t
    (let ((original-wrld (w state))
          (cl-term (subst-var (kwote clause) 'clause term)))
      (mv-let
       (erp trans-result)

; Parallelism blemish: we could consider making an ev@par, which calls ev-w,
; and tests that the appropriate preconditions for ev-w are upheld (like state
; not being in the alist).

       (ev-w-for-trans-eval cl-term (all-vars cl-term) stobjs-out ctx state

; See chk-evaluator-use-in-rule for a discussion of how we restrict the use of
; evaluators in rules of class :meta or :clause-processor, so that we can use
; aok = t here.

                            t
                            (f-get-global 'ld-user-stobjs-modified-warning
                                          state))
       (cond
        (erp (mv (msg "Evaluation failed for the :clause-processor hint.")
                 nil))
        (t
         (assert$
          (equal (car trans-result) stobjs-out)
          (let* ((result (cdr trans-result))
                 (eval-erp (and (cdr stobjs-out) (car result)))
                 (val (if (cdr stobjs-out) (cadr result) result)))
            (cond ((stringp eval-erp)
                   (mv (msg "~s0" eval-erp) nil))
                  ((tilde-@p eval-erp) ; a message
                   (mv (msg "Error in clause-processor hint:~|~%  ~@0"
                            eval-erp)
                       nil))
                  (eval-erp
                   (mv (msg "Error in clause-processor hint:~|~%  ~Y01"
                            term
                            nil)
                       nil))
                  ((equal val (list clause)) ; avoid checks below
                   (value@par val))
                  (t
                   (let* ((user-says-skip-termp-checkp
                           (skip-meta-termp-checks
                            (ffn-symb term) original-wrld))
                          (well-formedness-guarantee
                           (if (consp verified-p)
                               verified-p
                             nil))
                          (not-skipped
                           (and (not user-says-skip-termp-checkp)
                                (not well-formedness-guarantee)))
                          (bad-arity-info
                           (if (and well-formedness-guarantee
                                    (not user-says-skip-termp-checkp))
                               (collect-bad-fn-arity-info
                                (cdr well-formedness-guarantee)
                                original-wrld nil nil)
                             nil)))
                     (cond
                      (bad-arity-info
                       (let ((name (nth 0 (car well-formedness-guarantee)))
                             (fn (nth 1 (car well-formedness-guarantee)))
                             (thm-name1 (nth 2 (car well-formedness-guarantee))))
                         (mv (bad-arities-msg
                              name
                              :CLAUSE-PROCESSOR
                              fn
                              nil ; hyp-fn
                              thm-name1
                              nil ; wf-thm-name2
                              bad-arity-info)
                             nil)))
                      ((and not-skipped
                            (not (logic-term-list-listp val original-wrld)))
                       (cond
                        ((not (term-list-listp val original-wrld))
                         (mv (msg
                              "The :CLAUSE-PROCESSOR hint~|~%  ~Y01~%did not ~
                               evaluate to a list of clauses, but instead ~
                               to~|~%  ~Y23~%~@4"
                              term nil
                              val nil
                              (non-term-list-listp-msg
                               val original-wrld))
                             nil))
                        (t
                         (mv (msg
                              "The :CLAUSE-PROCESSOR hint~|~%  ~
                               ~Y01~%evaluated to a list of clauses,~%  ~
                               ~Y23,~%which however has a call of the ~
                               following :program mode ~
                               function~#4~[~/s~]:~|~&4."
                              term nil
                              val nil
                              (collect-programs
                               (all-ffn-symbs-lst-lst val nil)
                               original-wrld))
                             nil))))
                      ((and not-skipped
                            (forbidden-fns-in-term-list-list
                             val
                             (access rewrite-constant
                                     (access prove-spec-var pspv
                                             :rewrite-constant)
                                     :forbidden-fns)))
                       (mv (msg
                            "The :CLAUSE-PROCESSOR hint~|~%~Y01~%evaluated to ~
                             a list of clauses~|~%~y2~%that contains a call ~
                             of the function symbol~#3~[, ~&3, which is~/s ~
                             ~&3, which are~] forbidden in that context.  See ~
                             :DOC clause-processor and :DOC ~
                             set-skip-meta-termp-checks and :DOC ~
                             well-formedness-guarantee."
                            term nil val
                            (forbidden-fns-in-term-list-list
                             val
                             (access rewrite-constant
                                     (access prove-spec-var pspv
                                             :rewrite-constant)
                                     :forbidden-fns)))
                           nil))
                      (t (value@par val)))))))))))))))

(defun apply-top-hints-clause1 (temp cl-id cl pspv wrld state step-limit)

; See apply-top-hints-clause.  This handles the case that we found a
; hint-setting, temp, for a top hint other than :clause-processor or :or.

  (case (car temp)
    (:use ; temp is a non-nil :use hint.
     (let ((cases-temp
            (assoc-eq :cases
                      (access prove-spec-var pspv :hint-settings))))
       (cond
        ((null cases-temp)
         (apply-use-hint-clauses temp (list cl) pspv wrld state step-limit))
        (t

; In this case, we have both :use and :cases hints.  Our
; interpretation of this is that we split clause cl according to the
; :cases and then apply the :use hint to each case.  By the way, we
; don't have to consider the possibility of our having a :use and :by
; or :bdd.  That is ruled out by translate-hints.

         (mv-let
          (signal cases-clauses cases-ttree cases-pspv)
          (apply-cases-hint-clause cases-temp cl pspv wrld)
          (declare (ignore signal))

; We know the signal is 'HIT.

          (sl-let
           (signal use-clauses use-ttree use-pspv)
           (apply-use-hint-clauses temp
                                   cases-clauses
                                   cases-pspv
                                   wrld state step-limit)
           (declare (ignore signal))

; Despite the names, use-clauses and use-pspv both reflect the work we
; did for cases.  However, use-ttree was built from scratch as was
; cases-ttree and we must combine them.

           (mv step-limit
               'HIT
               use-clauses
               (cons-tag-trees use-ttree cases-ttree)
               use-pspv)))))))
    (:by

; If there is a :by hint then it is of one of the two forms (:by .  name) or
; (:by lmi-lst thm constraint-cl k event-names new-entries).  The first form
; indicates that we are to give this clause a bye and let the proof fail late.
; The second form indicates that the clause is supposed to be subsumed by thm,
; viewed as a set of clauses, but that we have to prove constraint-cl to obtain
; thm and that constraint-cl is really a conjunction of k constraints.  Lmi-lst
; is a singleton list containing the lmi that generated this thm-cl.

     (cond
      ((symbolp (cdr temp))

; So this is of the first form, (:by . name).  We want the proof to fail, but
; not now.  So we act as though we proved cl (we hit, produce no new clauses
; and don't change the pspv) but we return a tag-tree containing the tag
; :bye with the value (name . cl).  At the end of the proof we must search
; the tag-tree and see if there are any :byes in it.  If so, the proof failed
; and we should display the named clauses.

       (mv step-limit
           'hit
           nil
           (add-to-tag-tree! :bye (cons (cdr temp) cl) nil)
           pspv))
      (t
       (let ((lmi-lst (cadr temp)) ; a singleton list
             (thm (remove-guard-holders

; We often remove guard-holders without tracking their use in the tag-tree.
; Other times we record their use (but not here).  This is analogous to our
; reporting of the use of (:DEFINITION NOT) in some cases but not in others
; (e.g., when we use strip-not).

                   (caddr temp)))
             (constraint-cl (cadddr temp))
             (sr-limit (car (access rewrite-constant
                                    (access prove-spec-var pspv
                                            :rewrite-constant)
                                    :case-split-limitations)))
             (new-pspv
              (change prove-spec-var pspv
                      :hint-settings
                      (remove1-equal temp
                                     (access prove-spec-var
                                             pspv
                                             :hint-settings)))))

; We remove the :by from the hint-settings.  Why do we remove the :by?
; If we don't the subgoals we create from constraint-cl will also see
; the :by!

; We insist that thm-cl-set subsume cl -- more precisely, that cl be
; subsumed by some member of thm-cl-set.

; WARNING: See the warning about the processing in translate-by-hint.

         (let* ((cl (remove-guard-holders-lst cl))
                (cl (remove-equal *nil* cl))
                (easy-winp
                 (cond ((null cl) ; very weird case!
                        (equal thm *nil*))
                       ((null (cdr cl))
                        (equal (car cl) thm))
                       (t
                        (equal thm
                               (implicate
                                (conjoin (dumb-negate-lit-lst (butlast cl 1)))
                                (car (last cl)))))))
                (cl1 (if (and (not easy-winp)
                              (ffnnamep-lst 'implies cl))
                         (expand-some-non-rec-fns-lst '(implies) cl wrld)
                       cl))
                (cl-set (if (not easy-winp)

; Before Version_2.7 we only called clausify here when (and (null hist) cl1
; (null (cdr cl1))).  But Robert Krug sent an example in which a :by hint was
; given on a subgoal that had been produced from "Goal" by destructor
; elimination.  That subgoal was identical to the theorem given in the :by
; hint, and hence easy-winp is true; but before Version_2.7 we did not look for
; the easy win.  So, what happened was that thm-cl-set was the result of
; clausifying the theorem given in the :by hint, but cl-set was a singleton
; containing cl1, which still has IF terms.

                            (clausify (disjoin cl1) nil t sr-limit)
                          (list cl1)))
                (thm-cl-set (if easy-winp
                                (list (list thm))


; WARNING: Below we process the thm obtained from the lmi.  In particular, we
; expand certain non-rec fns and we clausify it.  For heuristic sanity, the
; processing done here should exactly duplicate that done above for cl-set.
; The reason is that we want it to be the case that if the user gives a :by
; hint that is identical to the goal theorem, the subsumption is guaranteed to
; succeed.  If the processing of the goal theorem is slightly different than
; the processing of the hint, that guarantee is invalid.

                              (clausify (expand-some-non-rec-fns
                                         '(implies) thm wrld)
                                        nil
                                        t
                                        sr-limit)))
                (val (list* (cadr temp) thm-cl-set (cdddr temp)))
                (subsumes (and (not easy-winp) ; otherwise we don't care
                               (clause-set-subsumes nil

; We supply nil just above, rather than (say) *init-subsumes-count*, because
; the user will be able to see that if the subsumption check goes out to lunch
; then it must be because of the :by hint.  For example, it takes 167,997,825
; calls of one-way-unify1 (more than 2^27, not far from the fixnum limit in
; many Lisps) to do the subsumption check for the following, yet in a feasible
; time (26 seconds on Allegro CL 7.0, on a 2.6GH Pentium 4).  So we prefer not
; to set a limit.

;  (defstub p (x) t)
;  (defstub s (x1 x2 x3 x4 x5 x6 x7 x8) t)
;  (defaxiom ax
;    (implies (and (p x1) (p x2) (p x3) (p x4)
;                  (p x5) (p x6) (p x7) (p x8))
;             (s x1 x2 x3 x4 x5 x6 x7 x8))
;    :rule-classes nil)
;  (defthm prop
;    (implies (and (p x1) (p x2) (p x3) (p x4)
;                  (p x5) (p x6) (p x7) (p x8))
;             (s x8 x7 x3 x4 x5 x6 x1 x2))
;    :hints (("Goal" :by ax)))

                                                    thm-cl-set cl-set)))
                (success (or easy-winp subsumes)))

; Before the full-blown subsumption check we ask if the two sets are identical
; and also if they are each singleton sets and the thm-cl-set's clause is a
; subset of the other clause.  These are fast and commonly successful checks.

           (cond
            (success

; Ok!  We won!  To produce constraint-cl as our goal we first
; preprocess it as though it had come down from the top.  See the
; handling of :use hints below for some comments on this.  This code
; was copied from that historically older code.

             (sl-let (signal clauses ttree irrel-pspv)
                     (preprocess-clause? constraint-cl nil pspv wrld
                                         state step-limit)
                     (declare (ignore irrel-pspv))
                     (cond ((eq signal 'miss)
                            (mv step-limit
                                'hit
                                (conjoin-clause-to-clause-set
                                 constraint-cl nil)
                                (add-to-tag-tree! :by val nil)
                                new-pspv))
                           ((or (tag-tree-occur 'hidden-clause
                                                t
                                                ttree)
                                (and clauses
                                     (null (cdr clauses))
                                     constraint-cl
                                     (null (cdr constraint-cl))
                                     (equal (prettyify-clause-simple
                                             (car clauses))
                                            (car constraint-cl))))

; If preprocessing produced a single clause that prettyifies to the
; clause we had, then act as though it didn't do anything (but use its
; output clause set).  This is akin to the 'hidden-clause
; hack of preprocess-clause, which, however, is intimately tied to the
; displayed-goal input to prove and not to the input to prettyify-
; clause.  We look for the 'hidden-clause tag just in case.

                            (mv step-limit
                                'hit
                                clauses
                                (add-to-tag-tree! :by val nil)
                                new-pspv))
                           (t
                            (mv step-limit
                                'hit
                                clauses
                                (add-to-tag-tree!
                                 :by val
                                 (add-to-tag-tree! 'preprocess-ttree
                                                   ttree
                                                   nil))
                                new-pspv)))))
            (t (mv step-limit
                   'error
                   (msg "When a :by hint is used to supply a lemma-instance ~
                         for a given goal-spec, the formula denoted by the ~
                         lemma-instance must subsume the goal.  This did not ~
                         happen~@1!  The lemma-instance provided was ~x0, ~
                         which denotes the formula ~p2 (when converted to a ~
                         set of clauses and then printed as a formula).  This ~
                         formula was not found to subsume the goal clause, ~
                         ~p3.~|~%Consider a :use hint instead; see :DOC ~
                         hints."
                        (car lmi-lst)

; The following is not possible, because we are not putting a limit on the
; number of one-way-unify1 calls in our subsumption check (see above).  But we
; leave this code here in case we change our minds on that.

                        (if (eq subsumes '?)
                            " because our subsumption heuristics were unable ~
                             to decide the question"
                          "")
                        (untranslate thm t wrld)
                        (prettyify-clause-set cl-set
                                              (let*-abstractionp state)
                                              wrld))
                   nil
                   nil))))))))
    (:cases

; Then there is no :use hint present.  See the comment in *top-hint-keywords*.

     (prepend-step-limit
      4
      (apply-cases-hint-clause temp cl pspv wrld)))
    (:bdd
     (prepend-step-limit
      4
      (bdd-clause (cdr temp) cl-id cl
                  (change prove-spec-var pspv
                          :hint-settings
                          (remove1-equal temp
                                         (access prove-spec-var
                                                 pspv
                                                 :hint-settings)))
                  wrld state)))
    (t (mv step-limit
           (er hard 'apply-top-hints-clause
               "Implementation error: Missing case in apply-top-hints-clause.")
           nil nil nil))))

(defun@par apply-top-hints-clause (cl-id cl hist pspv wrld ctx state step-limit)

; This is a standard clause processor of the waterfall.  It is odd in that it
; is a no-op unless there is a :use, :by, :cases, :bdd, :clause-processor, or
; :or hint in the :hint-settings of pspv.  If there is, we remove it and apply
; it.  By implementing these hints via this special-purpose processor we can
; take advantage of the waterfall's already-provided mechanisms for handling
; multiple clauses and output.

; We return five values.  The first is a new step-limit and the sixth is state.
; The second is a signal that is either 'hit, 'miss, or 'error.  When the
; signal is 'miss, the remaining three values are irrelevant.  When the signal
; is 'error, the third result is a pair of the form (str . alist) which allows
; us to give our caller an error message to print.  In this case, the remaining
; two values are irrelevant.  When the signal is 'hit, the third result is the
; list of new clauses, the fourth is a ttree that will become that component of
; the history-entry for this process, and the fifth is the modified pspv.

; We need cl-id passed in so that we can store it in the bddnote, in the case
; of a :bdd hint.

  (declare (ignore hist))
  (let ((temp (first-assoc-eq *top-hint-keywords*
                              (access prove-spec-var pspv
                                      :hint-settings))))
    (cond
     ((null temp) (mv@par step-limit 'miss nil nil nil state))
     ((eq (car temp) :or)

; If there is an :or hint then it is the only hint present and (in the
; translated form found here) it is of the form (:or . ((user-hint1
; . hint-settings1) ...(user-hintk . hint-settingsk))).  We simply signal an
; or-hit and let the waterfall process the hints.  We remove the :or hint from
; the :hint-settings of the pspv.  (It may be tempting simply to set the
; :hint-settings to nil.  But there may be other :hint-settings, say from a
; :do-not hint on a superior clause id.)

; The value, val, tagged with :or in the ttree is of the form (parent-cl-id NIL
; uhs-lst), where the parent-cl-id is the cl-id of the clause to which this :OR
; hint applies, the uhs-lst is the list of dotted pairs (... (user-hinti
; . hint-settingsi)...) and the NIL signifies that no branches have been
; created.  Eventually we will replace the NIL in the ttree of each branch by
; an integer i indicating which branch.  If that slot is occupied by an integer
; then user-hinti was applied to the corresponding clause.  See
; change-or-hit-history-entry.

      (mv@par step-limit
              'or-hit
              (list cl)
              (add-to-tag-tree! :or
                                (list cl-id nil (cdr temp))
                                nil)
              (change prove-spec-var pspv
                      :hint-settings
                      (delete-assoc-eq :or
                                       (access prove-spec-var pspv
                                               :hint-settings)))
              state))
     ((eq (car temp) :clause-processor) ; special case as state can be returned

; Temp is of the form (clause-processor-hint . stobjs-out), as returned by
; translate-clause-processor-hint.

      (mv-let@par
       (erp new-clauses state)
       (eval-clause-processor@par cl
                                  (access clause-processor-hint (cdr temp)
                                          :term)
                                  (access clause-processor-hint (cdr temp)
                                          :stobjs-out)
                                  (access clause-processor-hint (cdr temp)
                                          :verified-p)
                                  pspv ctx state)
       (cond (erp (mv@par step-limit 'error erp nil nil state))
             (t (mv@par step-limit
                        'hit
                        new-clauses
                        (cond ((and new-clauses
                                    (null (cdr new-clauses))
                                    (equal (car new-clauses) cl))
                               (add-to-tag-tree! 'hidden-clause t nil))
                              (t (add-to-tag-tree!
                                  :clause-processor
                                  (cons (cdr temp) new-clauses)
                                  nil)))
                        (change prove-spec-var pspv
                                :hint-settings
                                (remove1-equal temp
                                               (access prove-spec-var
                                                       pspv
                                                       :hint-settings)))
                        state)))))
     (t (sl-let
         (signal clauses ttree new-pspv)
         (apply-top-hints-clause1 temp cl-id cl pspv wrld state step-limit)
         (mv@par step-limit signal clauses ttree new-pspv state))))))

(defun tilde-@-lmi-phrase (lmi-lst k event-names)

; Lmi-lst is a list of lmis.  K is the number of constraints we have to
; establish.  Event-names is a list of names of events that justify the
; omission of certain proof obligations, because they have already been proved
; on behalf of those events.  We return an object suitable for printing via ~@
; that will print the phrase

; can be derived from ~&0 via instantiation and functional
; instantiation, provided we can establish the ~n1 constraints

; when event-names is nil, or else

; can be derived from ~&0 via instantiation and functional instantiation,
; bypassing constraints that have been proved when processing the events ...,
;    [or:  instead of ``the events,'' use ``events including'' when there
;          is at least one unnamed event involved, such as a verify-guards
;          event]
; provided we can establish the remaining ~n1 constraints

; Of course, the phrase is altered appropriately depending on the lmis
; involved.  There are two uses of this phrase.  When :by reports it
; says "As indicated by the hint, this goal is subsumed by ~x0, which
; CAN BE ...".  When :use reports it says "We now add the hypotheses
; indicated by the hint, which CAN BE ...".

  (let* ((seeds (lmi-seed-lst lmi-lst))
         (lemma-names (lmi-seeds-info 'hint-events seeds))
         (thms (lmi-seeds-info nil seeds))
         (techs (lmi-techs-lst lmi-lst)))
    (cond ((null techs)
           (cond ((null thms)
                  (msg "can be obtained from ~&0"
                       lemma-names))
                 ((null lemma-names)
                  (msg "can be obtained from the ~
                        ~#0~[~/constraint~/~n1 constraints~] generated"
                       (zero-one-or-more k)
                       k))
                 (t (msg "can be obtained from ~&0 and the ~
                          ~#1~[~/constraint~/~n2 constraints~] ~
                          generated"
                         lemma-names
                         (zero-one-or-more k)
                         k))))
          ((null event-names)
           (msg "can be derived from ~&0 via ~*1~#2~[~/, provided we can ~
                 establish the constraint generated~/, provided we can ~
                 establish the ~n3 constraints generated~]"
                seeds
                (list "" "~s*" "~s* and " "~s*, " techs)
                (zero-one-or-more k)
                k))
          (t
           (msg "can be derived from ~&0 via ~*1, bypassing constraints that ~
                 have been proved when processing ~#2~[events ~
                 including ~/previous events~/the event~#3~[~/s~]~ ~
                 ~]~&3~#4~[~/, provided we can establish the constraint ~
                 generated~/, provided we can establish the ~n5 constraints ~
                 generated~]"
                seeds
                (list "" "~s*" "~s* and " "~s*, " techs)

; Recall that an event-name of 0 is really an indication that the event in
; question didn't actually have a name.  See install-event.

                (if (member 0 event-names)
                    (if (cdr event-names)
                        0
                      1)
                  2)
                (if (member 0 event-names)
                    (remove 0 event-names)
                  event-names)
                (zero-one-or-more k)
                k)))))

(defun or-hit-msg (gag-mode-only-p cl-id ttree)

; We print the opening part of the :OR disjunction message, in which we alert
; the reader to the coming disjunctive branches.  If the signal is 'OR-HIT,
; then clauses just the singleton list contain the same clause the :OR was
; attached to.  But ttree contains an :or tag with value (parent-cl-id nil
; ((user-hint1 . hint-settings1)...))  indicating what is to be done to the
; clause.  Eventually the nil we be replaced, on each branch, by the number of
; that branch.  See change-or-hit-history-entry.  The number of branches is the
; length of the third element.  The parent-cl-id in the value is the same as
; the cl-id passed in.

  (let* ((val (tagged-object :or ttree))
         (branch-cnt (length (nth 2 val))))
    (msg "The :OR hint for ~@0 gives rise to ~n1 disjunctive ~
          ~#2~[~/branch~/branches~].  Proving any one of these branches would ~
          suffice to prove ~@0.  We explore them in turn~#3~[~@4~/~].~%"
         (tilde-@-clause-id-phrase cl-id)
         branch-cnt
         (zero-one-or-more branch-cnt)
         (if gag-mode-only-p 1 0)
         ", describing their derivations as we go")))

(defun apply-top-hints-clause-msg1
  (signal cl-id clauses speciousp ttree pspv state)

; This function is one of the waterfall-msg subroutines.  It has the standard
; arguments of all such functions: the signal, clauses, ttree and pspv produced
; by the given processor, in this case preprocess-clause (except that for bdd
; processing, the ttree comes from bdd-clause, which is similar to
; simplify-clause, which explains why we also pass in the argument speciousp).
; It produces the report for this step.

; Note:  signal and pspv are really ignored, but they don't appear to be when
; they are passed to simplify-clause-msg1 below, so we cannot declare them
; ignored here.

  (cond ((tagged-objectsp :bye ttree)

; The object associated with the :bye tag is (name . cl).  We are interested
; only in name here.

         (fms "But we have been asked to pretend that this goal is ~
               subsumed by the yet-to-be-proved ~x0.~|"
              (list (cons #\0 (car (tagged-object :bye ttree))))
              (proofs-co state)
              state
              nil))
        ((tagged-objectsp :by ttree)
         (let* ((obj (tagged-object :by ttree))

; Obj is of the form (lmi-lst thm-cl-set constraint-cl k event-names
; new-entries).

                (lmi-lst (car obj))
                (thm-cl-set (cadr obj))
                (k (car (cdddr obj)))
                (event-names (cadr (cdddr obj)))
                (ttree (tagged-object 'preprocess-ttree ttree)))
           (fms "~#0~[But, as~/As~/As~] indicated by the hint, this goal is ~
                 subsumed by ~x1, which ~@2.~#3~[~/  By ~*4 we reduce the ~
                 ~#5~[constraint~/~n6 constraints~] to ~#0~[T~/the following ~
                 conjecture~/the following ~n7 conjectures~].~]~|"
                (list (cons #\0 (zero-one-or-more clauses))
                      (cons #\1 (prettyify-clause-set
                                 thm-cl-set
                                 (let*-abstractionp state)
                                 (w state)))
                      (cons #\2 (tilde-@-lmi-phrase lmi-lst k event-names))
                      (cons #\3 (if (int= k 0) 0 1))
                      (cons #\4 (tilde-*-preprocess-phrase ttree))
                      (cons #\5 (if (int= k 1) 0 1))
                      (cons #\6 k)
                      (cons #\7 (length clauses)))
                (proofs-co state)
                state
                (term-evisc-tuple nil state))))
        ((tagged-objectsp :use ttree)
         (let* ((use-obj (tagged-object :use ttree))

; The presence of :use indicates that a :use hint was applied to one
; or more clauses to give the output clauses.  If there is also a
; :cases tag in the ttree, then the input clause was split into to 2
; or more cases first and then the :use hint was applied to each.  If
; there is no :cases tag, the :use hint was applied to the input
; clause alone.  Each application of the :use hint adds literals to
; the target clause(s).  This generates a set, A, of ``applications''
; but A need not be the same length as the set of clauses to which we
; applied the :use hint since some of those applications might be
; tautologies.  In addition, the :use hint generated some constraints,
; C.  The set of output clauses, say G, is (C U A).  But C and A are
; not necessarily disjoint, e.g., some constraints might happen to be
; in A.  Once upon a time, we reported on the number of non-A
; constraints, i.e., |C'|, where C' = C\A.  Because of the complexity
; of the grammar, we do not reveal to the user all the numbers: how
; many non-tautological cases, how many hypotheses, how many
; non-tautological applications, how many constraints generated, how
; many after preprocessing the constraints, how many overlaps between
; C and A, etc.  Instead, we give a fairly generic message.  But we
; have left (as comments) the calculation of the key numbers in case
; someday we revisit this.

; The shape of the use-obj, which is the value of the :use tag, is
; ((lmi-lst (hyp1 ...) cl k event-names new-entries)
; . non-tautp-applications) where non-tautp-applications is the number
; of non-tautologies created by the one or more applications of the
; :use hint, i.e., |A|.  (But we do not report this.)

                (lmi-lst (car (car use-obj)))
                (hyps (cadr (car use-obj)))
                (k (car (cdddr (car use-obj))))             ;;; |C|
                (event-names (cadr (cdddr (car use-obj))))
;               (non-tautp-applications (cdr use-obj))      ;;; |A|
                (preprocess-ttree
                 (tagged-object 'preprocess-ttree ttree))
;               (len-A non-tautp-applications)              ;;; |A|
                (len-G (len clauses))                       ;;; |G|
                (len-C k)                                   ;;; |C|
;               (len-C-prime (- len-G len-A))               ;;; |C'|

                (cases-obj (tagged-object :cases ttree))

; If there is a cases-obj it means we had a :cases and a :use; the
; form of cases-obj is (splitting-terms . case-clauses), where
; case-clauses is the result of splitting on the literals in
; splitting-terms.  We know that case-clauses is non-nil.  (Had it
; been nil, no :use would have been reported.)  Note that if cases-obj
; is nil, i.e., there was no :cases hint applied, then these next two
; are just nil.  But we'll want to ignore them if cases-obj is nil.

;               (splitting-terms (car cases-obj))
;               (case-clauses (cdr cases-obj))
                )

           (fms
            "~#0~[But we~/We~] ~#x~[split the goal into the cases specified ~
             by the :CASES hint and augment each case~/augment the goal~] ~
             with the ~#1~[hypothesis~/hypotheses~] provided by the :USE ~
             hint. ~#1~[The hypothesis~/These hypotheses~] ~@2~#3~[~/; the ~
             constraint~#4~[~/s~] can be simplified using ~*5~].  ~#6~[This ~
             reduces the goal to T.~/We are left with the following ~
             subgoal.~/We are left with the following ~n7 subgoals.~]~%"
            (list
             (cons #\x (if cases-obj 0 1))
             (cons #\0 (if (> len-G 0) 1 0))               ;;; |G|>0
             (cons #\1 hyps)
             (cons #\2 (tilde-@-lmi-phrase lmi-lst k event-names))
             (cons #\3 (if (> len-C 0) 1 0))               ;;; |C|>0
             (cons #\4 (if (> len-C 1) 1 0))               ;;; |C|>1
             (cons #\5 (tilde-*-preprocess-phrase preprocess-ttree))
             (cons #\6 (if (equal len-G 0) 0 (if (equal len-G 1) 1 2)))
             (cons #\7 len-G))
            (proofs-co state)
            state
            (term-evisc-tuple nil state))))
        ((tagged-objectsp :cases ttree)
         (let* ((cases-obj (tagged-object :cases ttree))

; The cases-obj here is of the form (term-list . new-clauses), where
; new-clauses is the result of splitting on the literals in term-list.

;               (splitting-terms (car cases-obj))
                (new-clauses (cdr cases-obj)))
           (cond
            (new-clauses
             (fms "We now split the goal into the cases specified by ~
                   the :CASES hint to produce ~n0 new non-trivial ~
                   subgoal~#1~[~/s~].~|"
                  (list (cons #\0 (length new-clauses))
                        (cons #\1 (if (cdr new-clauses) 1 0)))
                  (proofs-co state)
                  state
                  (term-evisc-tuple nil state)))
            (t
             (fms "But the resulting goals are all true by case reasoning."
                  nil
                  (proofs-co state)
                  state
                  nil)))))
        ((eq signal 'OR-HIT)
         (fms "~@0"
              (list (cons #\0 (or-hit-msg nil cl-id ttree)))
              (proofs-co state) state nil))
        ((tagged-objectsp 'hidden-clause ttree)
         state)
        ((tagged-objectsp :clause-processor ttree)
         (let* ((clause-processor-obj (tagged-object :clause-processor ttree))

; The clause-processor-obj here is produced by apply-top-hints-clause, and is
; of the form (clause-processor-hint . new-clauses), where new-clauses is the
; result of splitting on the literals in term-list and hint is the translated
; form of a :clause-processor hint.

                (verified-p-msg (cond ((access clause-processor-hint
                                               (car clause-processor-obj)
                                               :verified-p)
                                       "verified")
                                      (t "trusted")))
                (new-clauses (cdr clause-processor-obj))
                (cl-proc-fn (ffn-symb (access clause-processor-hint
                                              (car clause-processor-obj)
                                              :term))))
           (cond
            (new-clauses
             (fms "We now apply the ~@0 :CLAUSE-PROCESSOR function ~x1 to ~
                   produce ~n2 new subgoal~#3~[~/s~].~|"
                  (list (cons #\0 verified-p-msg)
                        (cons #\1 cl-proc-fn)
                        (cons #\2 (length new-clauses))
                        (cons #\3 (if (cdr new-clauses) 1 0)))
                  (proofs-co state)
                  state
                  (term-evisc-tuple nil state)))
            (t
             (fms "But the ~@0 :CLAUSE-PROCESSOR function ~x1 replaces this goal ~
                   by T.~|"
                  (list (cons #\0 verified-p-msg)
                        (cons #\1 cl-proc-fn))
                  (proofs-co state)
                  state
                  nil)))))
        (t

; Normally we expect (tagged-object 'bddnote ttree) in this case, but it is
; possible that forward-chaining after trivial equivalence removal proved
; the clause, without actually resorting to bdd processing.

         (simplify-clause-msg1 signal cl-id clauses speciousp ttree pspv
                               state))))

(defun previous-process-was-speciousp (hist)

; NOTE: This function has not been called since Version_2.5.  However,
; we reference the comment below in a comment in settled-down-clause,
; so for now we keep this comment, if for no other other reason than
; historical.

; Context: We are about to print cl-id and clause in waterfall-msg.
; Then we will print the message associated with the first entry in
; hist, which is the entry for the processor which just hit clause and
; for whom we are reporting.  However, if the previous entry in the
; history was specious, then the cl-id and clause were printed when
; the specious hit occurred and we should not reprint them.  Thus, our
; job here is to decide whether the previous process in the history
; was specious.

; There are complications though, introduced by the existence of
; settled-down-clause.  In the first place, settled-down-clause ALWAYS
; produces a set of clauses containing the input clause and so ought
; to be considered specious every time it hits!  We avoid that in
; waterfall-step and never mark a settled-down-clause as specious, so
; we can assoc for them.  More problematically, consider the
; possibility that the first simplification -- the one before the
; clause settled down -- was specious.  Recall that the
; pre-settled-down-clause simplifications are weak.  Thus, it is
; imaginable that after settling down, other simplifications may
; happen and allow a non-specious simplification.  Thus,
; settled-down-clause actually does report its "hit" (and thus add its
; mark to the history so as to enable the subsequent simplify-clause
; to pull out the stops) following even specious simplifications.
; Thus, we must be prepared here to see a non-specious
; settled-down-clause which followed a specious simplification.

; Note: It is possible that the first entry on hist is specious.  That
; is, if the process on behalf of which we are about to print is in
; fact specious, it is so marked right now in the history.  But that
; is irrelevant to our question.  We don't care if the current guy
; specious, we want to know if his "predecessor" was.  For what it is
; worth, as of this writing, it is thought to be impossible for two
; adjacent history entries to be marked 'SPECIOUS.  Only
; simplify-clause, we think, can produce specious hits.  Whenever a
; specious simplify-clause occurs, it is treated as a 'miss and we go
; on to the next process, which is not simplify-clause.  Note that if
; elim could produce specious 'hits, then we might get two in a row.
; Observe also that it is possible for two successive simplifies to be
; specious, but that they are separated by a non-specious
; settled-down-clause.  (Our code doesn't rely on any of this, but it
; is sometimes helpful to be able to read such thoughts later as a
; hint of what we were thinking when we made some terrible coding
; mistake and so this might illuminate some error we're making today.)

  (cond ((null hist) nil)
        ((null (cdr hist)) nil)
        ((consp (access history-entry (cadr hist) :processor)) t)
        ((and (eq (access history-entry (cadr hist) :processor)
                  'settled-down-clause)
              (consp (cddr hist))
              (consp (access history-entry (caddr hist) :processor)))
         t)
        (t nil)))

; Section:  WATERFALL

; The waterfall is a simple finite state machine (whose individual
; state transitions are very complicated).  Abstractly, each state
; contains a "processor" and two neighbor states, the "hit" state and
; the "miss" state.  Roughly speaking, when we are in a state we apply
; its processor to the input clause and obtain either a "hit" signal
; (and some new clauses) or "miss" signal.  We then transit to the
; appropriate state and continue.

; However, the "hit" state for every state is that point in the falls,
; where 'apply-top-hints-clause is the processor.

; apply-top-hints-clause <------------------+
;  |                                        |
; preprocess-clause ----------------------->|
;  |                                        |
; simplify-clause ------------------------->|
;  |                                        |
; settled-down-clause---------------------->|
;  |                                        |
; ...                                       |
;  |                                        |
; push-clause ----------------------------->+

; WARNING: Waterfall1-lst knows that 'preprocess-clause follows
; 'apply-top-hints-clause!

; We therefore represent a state s of the waterfall as a pair whose car
; is the processor for s and whose cdr is the miss state for s.  The hit
; state for every state is the constant state below, which includes, by
; successive cdrs, every state below it in the falls.

; Because the word "STATE" has a very different meaning in ACL2 than we have
; been using thus far in this discussion, we refer to the "states" of the
; waterfall as "ledges" and basically name them by the processors on each.

(defconst *preprocess-clause-ledge*
  '(apply-top-hints-clause
    preprocess-clause
    simplify-clause
    settled-down-clause
    eliminate-destructors-clause
    fertilize-clause
    generalize-clause
    eliminate-irrelevance-clause
    push-clause))

; Observe that the cdr of the 'simplify-clause ledge, for example, is the
; 'settled-down-clause ledge, etc.  That is, each ledge contains the
; ones below it.

; Note: To add a new processor to the waterfall you must add the
; appropriate entry to the *preprocess-clause-ledge* and redefine
; waterfall-step and waterfall-msg, below.

; If we are on ledge p with input cl and pspv, we apply processor p to
; our input and obtain signal, some cli, and pspv'.  If signal is
; 'abort, we stop and return pspv'.  If signal indicates a hit, we
; successively process each cli, starting each at the top ledge, and
; accumulating the successive pspvs starting from pspv'.  If any cli
; aborts, we abort; otherwise, we return the final pspv.  If signal is
; 'miss, we fall to the next lower ledge with cl and pspv.  If signal
; is 'error, we return abort and propagate the error message upwards.

; Before we resume development of the waterfall, we introduce functions in
; support of gag-mode.

(defmacro initialize-pspv-for-gag-mode (pspv)
  `(if (gag-mode)
       (change prove-spec-var ,pspv
               :gag-state
               *initial-gag-state*)
     ,pspv))

; For debug only:
; (progn
;
; (defun show-gag-info-pushed (pushed state)
;   (if (endp pushed)
;       state
;     (pprogn (let ((cl-id (caar pushed)))
;               (fms "~@0 (~@1) pushed for induction.~|"
;                    (list (cons #\0 (tilde-@-pool-name-phrase
;                                     (access clause-id cl-id :forcing-round)
;                                     (cdar pushed)))
;                          (cons #\1 (tilde-@-clause-id-phrase cl-id)))
;                    *standard-co* state nil))
;             (show-gag-info-pushed (cdr pushed) state))))
;
; (defun show-gag-info (info state)
;   (pprogn (fms "~@0:~%~Q12~|~%"
;                (list (cons #\0 (tilde-@-clause-id-phrase
;                                 (access gag-info info :clause-id)))
;                      (cons #\1 (access gag-info info :clause))
;                      (cons #\2 nil))
;                *standard-co* state nil)
;           (show-gag-info-pushed (access gag-info info :pushed)
;                                 state)))
;
; (defun show-gag-stack (stack state)
;   (if (endp stack)
;       state
;     (pprogn (show-gag-info (car stack) state)
;             (show-gag-stack (cdr stack) state))))
;
; (defun show-gag-state (cl-id gag-state state)
;   (let* ((top-stack (access gag-state gag-state :top-stack))
;          (sub-stack (access gag-state gag-state :sub-stack))
;          (clause-id (access gag-state gag-state :active-cl-id))
;          (printed-p (access gag-state gag-state
;                             :active-printed-p)))
;     (pprogn (fms "********** Gag state from handling ~@0 (active ~
;                   clause id: ~#1~[<none>~/~@2~])~%"
;                  (list (cons #\0 (tilde-@-clause-id-phrase cl-id))
;                        (cons #\1 (if clause-id 1 0))
;                        (cons #\2 (and clause-id (tilde-@-clause-id-phrase
;                                                  clause-id))))
;                  *standard-co* state nil)
;             (fms "****** Top-stack:~%" nil *standard-co* state nil)
;             (show-gag-stack top-stack state)
;             (fms "****** Sub-stack:~%" nil *standard-co* state nil)
;             (show-gag-stack sub-stack state)
;             (fms "****** Active-printed-p: ~x0"
;                  (list (cons #\0 (access gag-state gag-state
;                                          :active-printed-p)))
;                  *standard-co* state nil)
;             (fms "****** Forcep: ~x0"
;                  (list (cons #\0 (access gag-state gag-state
;                                          :forcep)))
;                  *standard-co* state nil)
;             (fms "******************************~|" nil *standard-co* state
;                  nil))))
;
; (defun maybe-show-gag-state (cl-id pspv state)
;   (if (and (f-boundp-global 'gag-debug state)
;            (f-get-global 'gag-debug state))
;       (show-gag-state cl-id
;                       (access prove-spec-var pspv :gag-state)
;                       state)
;     state))
; )

(defun waterfall-update-gag-state (cl-id clause proc signal ttree pspv
                                         state)

; We are given a clause-id, cl-id, and a corresponding clause.  Processor proc
; has operated on this clause and returned the given signal (either 'abort or a
; hit indicator), ttree, and pspv.  We suitably extend the gag-state of
; the pspv and produce a message to print before any normal prover output that
; is allowed under gag-mode.

; Thus, we return (mv gagst msg), where gagst is either nil or a new gag-state
; obtained by updating the :gag-state field of pspv, and msg is a message to be
; printed or else nil.  If msg is not nil, then its printer is expected to
; insert a newline before printing msg.

  (let* ((msg-p (not (output-ignored-p 'prove state)))
         (gagst0 (access prove-spec-var pspv :gag-state))
         (pool-lst (access clause-id cl-id :pool-lst))
         (forcing-round (access clause-id cl-id :forcing-round))
         (stack (cond (pool-lst (access gag-state gagst0 :sub-stack))
                      (t        (access gag-state gagst0 :top-stack))))
         (active-cl-id (access gag-state gagst0 :active-cl-id))
         (abort-p (eq signal 'abort))
         (push-or-bye-p (or (eq proc 'push-clause)
                            (and (eq proc 'apply-top-hints-clause)
                                 (eq signal 'hit)
                                 (tagged-objectsp :bye ttree))))
         (new-active-p ; true if we are to push a new gag-info frame
          (and (null active-cl-id)
               (null (cdr pool-lst)) ; not in a sub-induction
               (or push-or-bye-p ; even if the next test fails
                   (member-eq proc (f-get-global 'checkpoint-processors
                                                 state)))))
         (new-frame (and new-active-p
                         (make gag-info
                               :clause-id cl-id
                               :clause clause
                               :pushed nil)))
         (new-stack (cond (new-active-p (cons new-frame stack))
                          (t stack)))
         (gagst (cond (new-active-p (cond (pool-lst
                                           (change gag-state gagst0
                                                   :sub-stack new-stack
                                                   :active-cl-id cl-id))
                                          (t
                                           (change gag-state gagst0
                                                   :top-stack new-stack
                                                   :active-cl-id cl-id))))
                      (t gagst0)))
         (new-forcep (and (not abort-p)
                          (not (access gag-state gagst :forcep))
                          (tagged-objectsp 'assumption ttree)))
         (gagst (cond (new-forcep (change gag-state gagst :forcep t))
                      (t gagst)))
         (forcep-msg (and new-forcep
                          msg-p
                          (msg "Forcing Round ~x0 is pending (caused first by ~
                                ~@1)."
                               (1+ (access clause-id cl-id :forcing-round))
                               (tilde-@-clause-id-phrase cl-id)))))
    (cond
     (push-or-bye-p
      (let* ((top-ci (assert$ (consp new-stack)
                              (car new-stack)))
             (old-pushed (access gag-info top-ci :pushed))
             (top-goal-p (equal cl-id *initial-clause-id*))
             (print-p

; We avoid gag's key checkpoint message if we are in a sub-induction or if we
; are pushing the initial goal for proof by induction.  The latter case is
; handled similarly in the call of waterfall1-lst under waterfall.

              (not (or (access gag-state gagst :active-printed-p)
                       (cdr pool-lst)
                       top-goal-p)))
             (gagst (cond (print-p (change gag-state gagst
                                           :active-printed-p t))
                          (t gagst)))
             (top-stack (access gag-state gagst0 :top-stack))
             (msg0 (cond
                    ((and print-p msg-p)
                     (assert$
                      (null old-pushed)
                      (msg "~@0~|~%~@1~|~Q23~|~%"
                           (gag-start-msg
                            (and pool-lst
                                 (assert$
                                  (consp top-stack)
                                  (access gag-info (car top-stack)
                                          :clause-id)))
                            (and pool-lst
                                 (tilde-@-pool-name-phrase
                                  forcing-round
                                  pool-lst)))
                           (tilde-@-clause-id-phrase
                            (access gag-info top-ci :clause-id))
                           (prettyify-clause
                            (access gag-info top-ci :clause)
                            (let*-abstractionp state)
                            (w state))
                           (term-evisc-tuple nil state))))
                    (t nil))))
        (cond
         (abort-p
          (mv (cond ((equal (tagged-objects 'abort-cause ttree)
                            '(revert))
                     (change gag-state gagst :abort-stack new-stack))
                    ((equal (tagged-objects 'abort-cause ttree)
                            '(empty-clause))
                     (change gag-state gagst :abort-stack 'empty-clause))
                    ((member-equal (tagged-objects 'abort-cause ttree)
                                   '((do-not-induct)
                                     (do-not-induct-otf-flg-override)))
                     (change gag-state gagst :abort-stack 'do-not-induct))
                    (t gagst))
              (and msg-p
                   (msg "~@0~@1"
                        (or msg0 "")
                        (push-clause-msg1-abort cl-id ttree pspv state)))))
         (t (let* ((old-pspv-pool-lst
                    (pool-lst (cdr (access prove-spec-var pspv :pool))))
                   (newer-stack
                    (and (assert$
                          (or (cdr pool-lst) ;sub-induction; no active chkpt
                              (equal (access gag-state gagst
                                             :active-cl-id)
                                     (access gag-info top-ci
                                             :clause-id)))
                          (if (eq proc 'push-clause)
                              (cons (change gag-info top-ci
                                            :pushed
                                            (cons (cons cl-id old-pspv-pool-lst)
                                                  old-pushed))
                                    (cdr new-stack))
                            new-stack)))))
              (mv (cond (pool-lst
                         (change gag-state gagst :sub-stack
                                 newer-stack))
                        (t
                         (change gag-state gagst :top-stack
                                 newer-stack)))
                  (and
                   msg-p
                   (or msg0 forcep-msg (gag-mode))
                   (msg "~@0~#1~[~@2~|~%~/~]~@3"
                        (or msg0 "")
                        (if forcep-msg 0 1)
                        forcep-msg
                        (cond
                         ((null (gag-mode))
                          "")
                         (t
                          (let ((msg-finish
                                 (cond ((or pool-lst ; pushed for sub-induction
                                            (null active-cl-id))
                                        ".")
                                       (t (msg ":~|~Q01."
                                               (prettyify-clause
                                                clause
                                                (let*-abstractionp state)
                                                (w state))
                                               (term-evisc-tuple nil state))))))
                            (cond
                             ((eq proc 'push-clause)
                              (msg "~@0 (~@1) is pushed for proof by ~
                                    induction~@2"
                                   (tilde-@-pool-name-phrase
                                    forcing-round
                                    old-pspv-pool-lst)
                                   (if top-goal-p
                                       "the initial Goal, a key checkpoint"
                                     (tilde-@-clause-id-phrase cl-id))
                                   msg-finish))
                             (t
                              (msg "~@0 is subsumed by a goal yet to be ~
                                    proved~@1"
                                   (tilde-@-clause-id-phrase cl-id)
                                   msg-finish))))))))))))))
     (t (assert$ (not abort-p) ; we assume 'abort is handled above
                 (mv (cond ((or new-active-p new-forcep)
                            gagst)
                           (t nil))
                     forcep-msg))))))

#+acl2-par
(defun waterfall-update-gag-state@par (cl-id clause proc signal ttree pspv state)
  (declare (ignore cl-id clause proc signal ttree pspv state))

; Parallelism blemish: consider causing an error when the user tries to enable
; gag mode.  At the moment I'm unsure of the effects of returning two nils in
; this case.

  (mv nil nil))

(defun@par record-gag-state (gag-state state)
  (declare (ignorable gag-state state))
  (serial-first-form-parallel-second-form@par
   (f-put-global 'gag-state gag-state state)
   nil))

(defun@par gag-state-exiting-cl-id (signal cl-id pspv state)

; If cl-id is the active clause-id for the current gag-state, then we
; deactivate it.  We also eliminate the corresponding stack frame, if any,
; provided no goals were pushed for proof by induction.

  (declare (ignorable signal cl-id pspv state))
  (serial-first-form-parallel-second-form@par
   (let* ((gagst0 (access prove-spec-var pspv :gag-state))
          (active-cl-id (access gag-state gagst0 :active-cl-id)))
     (cond ((equal cl-id active-cl-id)
            (let* ((pool-lst (access clause-id cl-id :pool-lst))
                   (stack (cond (pool-lst
                                 (access gag-state gagst0 :sub-stack))
                                (t
                                 (access gag-state gagst0 :top-stack))))
                   (ci (assert$ (consp stack)
                                (car stack)))
                   (current-cl-id (access gag-info ci :clause-id))
                   (printed-p (access gag-state gagst0 :active-printed-p))
                   (gagst1 (cond (printed-p (change gag-state gagst0
                                                    :active-cl-id nil
                                                    :active-printed-p nil))
                                 (t         (change gag-state gagst0
                                                    :active-cl-id nil))))
                   (gagst2 (cond
                            ((eq signal 'abort)
                             (cond
                              ((equal (tagged-objects
                                       'abort-cause
                                       (access prove-spec-var pspv :tag-tree))
                                      '(revert))
                               (change gag-state gagst1 ; save abort info
                                       :active-cl-id nil
                                       :active-printed-p nil
                                       :forcep nil
                                       :sub-stack nil
                                       :top-stack
                                       (list
                                        (make gag-info
                                              :clause-id *initial-clause-id*
                                              :clause (list '<Goal>)
                                              :pushed
                                              (list (cons *initial-clause-id*
                                                          '(1)))))))
                              (t gagst1)))
                            ((and (equal cl-id current-cl-id)
                                  (null (access gag-info ci
                                                :pushed)))
                             (cond (pool-lst
                                    (change gag-state gagst1
                                            :sub-stack (cdr stack)))
                                   (t
                                    (change gag-state gagst1
                                            :top-stack (cdr stack)))))
                            (t gagst1))))
              (pprogn
               (record-gag-state gagst2 state)
               (cond (printed-p
                      (io? prove nil state nil
                           (pprogn
                            (increment-timer 'prove-time state)
                            (cond ((gag-mode)
                                   (fms "~@0"
                                        (list (cons #\0 *gag-suffix*))
                                        (proofs-co state) state nil))
                                  (t state))
                            (increment-timer 'print-time state))))
                     (t state))
               (mv (change prove-spec-var pspv
                           :gag-state gagst2)
                   state))))
           (t (mv pspv state))))
   (mv@par pspv state)))

(defun remove-pool-lst-from-gag-state (pool-lst gag-state state)
  #-acl2-par
  (declare (ignore state))
  (cond
   #+acl2-par
   ((f-get-global 'waterfall-parallelism state)

; This function contains an assertion that fails when executing the waterfall
; in parallel.  The assertion fails because parallelism mode doesn't save the
; data required to make gag-mode work, and the assertion tests the gag-mode
; state for being in a reasonable condition.

; Based upon a simple test using :mini-proveall, it appears that switching
; gag-mode on and off, and switching between different waterfall parallelism
; modes does not result in a system breakage.

    (mv nil nil))
   (t

; The proof attempt for the induction goal represented by pool-lst has been
; completed.  We return two values, (mv gagst cl-id), as follows.  Gagst is the
; result of removing pool-lst from the given gag-state.  Cl-id is nil unless
; pool-lst represents the final induction goal considered that was generated
; under a key checkpoint, in which case cl-id is the clause-id of that key
; checkpoint.

    (let* ((sub-stack (access gag-state gag-state :sub-stack))
           (stack (or sub-stack (access gag-state gag-state
                                        :top-stack))))
      (assert$ (consp stack)
               (let* ((ci (car stack))
                      (pushed (access gag-info ci :pushed))
                      (pop-car-p (null (cdr pushed))))
                 (assert$
                  (and (consp pushed)
                       (equal (cdar pushed) pool-lst)
                       (not (access gag-state gag-state
                                    :active-cl-id)))
                  (let ((new-stack
                         (if pop-car-p
                             (cdr stack)
                           (cons (change gag-info ci
                                         :pushed
                                         (cdr pushed))
                                 (cdr stack)))))
                    (mv (cond (sub-stack
                               (change gag-state gag-state
                                       :sub-stack new-stack))
                              (t
                               (change gag-state gag-state
                                       :top-stack new-stack)))
                        (and pop-car-p
                             (access gag-info ci :clause-id)))))))))))

(defun pop-clause-update-gag-state-pop (pool-lsts gag-state msgs msg-p state)

; Pool-lsts is in reverse chronological order.

  (cond
   ((endp pool-lsts)
    (mv gag-state msgs))
   (t
    (mv-let
     (gag-state msgs)
     (pop-clause-update-gag-state-pop (cdr pool-lsts) gag-state msgs msg-p
                                      state)
     (mv-let (gagst cl-id)
             (remove-pool-lst-from-gag-state (car pool-lsts) gag-state state)
             (mv gagst
                 (if (and msg-p cl-id)
                     (cons (msg "~@0"
                                (tilde-@-clause-id-phrase cl-id))
                           msgs)
                   msgs)))))))

(defun gag-mode-jppl-flg (gag-state)
  (let ((stack (or (access gag-state gag-state :sub-stack)
                   (access gag-state gag-state :top-stack))))
    (cond (stack
           (let* ((pushed (access gag-info (car stack) :pushed))
                  (pool-lst (and pushed (cdar pushed))))

; Notice that pool-lst is nil if pushed is nil, as can happen when we abort due
; to encountering an empty clause.

             (and (null (cdr pool-lst)) ; sub-induction goal was not printed
                  pool-lst)))
          (t nil))))

; That completes basic support for gag-mode.  We now resume mainline
; development of the waterfall.

; The waterfall also manages the output, by case switching on the processor.
; The function waterfall-msg1 handles the printing of the formula and the
; output for those processes that hit.

(defmacro splitter-output ()
  `(and (f-get-global 'splitter-output state)
        (not (member-eq 'prove
                        (f-get-global 'inhibit-output-lst state)))))

(defmacro set-splitter-output (val)
  `(f-put-global 'splitter-output ,val state))

(defun waterfall-msg1 (processor cl-id signal clauses new-hist msg ttree pspv
                                 state)
  (with-output-lock
   (let ((gag-mode (gag-mode)))
     (pprogn

;  (maybe-show-gag-state cl-id pspv state) ; debug

      (cond

; Suppress printing for :OR splits; see also other comments with this header.

;      ((and (eq signal 'OR-HIT)
;            gag-mode)
;       (fms "~@0~|~%~@1~|"
;            (list (cons #\0 (or msg ""))
;                  (cons #\1 (or-hit-msg t cl-id ttree)))
;            (proofs-co state) state nil))

       ((and msg (gag-mode))
        (fms "~@0~|" (list (cons #\0 msg)) (proofs-co state) state nil))
       (t state))
      (cond
       ((or (gag-mode)
            (f-get-global 'raw-proof-format state))
        (print-splitter-rules-summary cl-id clauses ttree state))
       (t state))
      (cond
       (gag-mode state)
       (t
        (case
          processor
          (apply-top-hints-clause

; Note that the args passed to apply-top-hints-clause, and to
; simplify-clause-msg1 below, are nonstandard.  This is what allows the
; simplify message to detect and report if the just performed simplification
; was specious.

           (apply-top-hints-clause-msg1
            signal cl-id clauses
            (consp (access history-entry (car new-hist)
                           :processor))
            ttree pspv state))
          (preprocess-clause
           (preprocess-clause-msg1 signal clauses ttree pspv state))
          (simplify-clause
           (simplify-clause-msg1 signal cl-id clauses
                                 (consp (access history-entry (car new-hist)
                                                :processor))
                                 ttree pspv state))
          (settled-down-clause
           (settled-down-clause-msg1 signal clauses ttree pspv state))
          (eliminate-destructors-clause
           (eliminate-destructors-clause-msg1 signal clauses ttree
                                              pspv state))
          (fertilize-clause
           (fertilize-clause-msg1 signal clauses ttree pspv state))
          (generalize-clause
           (generalize-clause-msg1 signal clauses ttree pspv state))
          (eliminate-irrelevance-clause
           (eliminate-irrelevance-clause-msg1 signal clauses ttree
                                              pspv state))
          (otherwise
           (push-clause-msg1 cl-id signal clauses ttree pspv state)))))))))

(defmacro io?-prove-cw (vars body &rest keyword-args)

; This macro is a version of io?-prove that prints to the comment window using
; wormholes.

; Keep in sync with io?-prove.

  `(io? prove t state ,vars
        (if (gag-mode) state ,body)
        ,@keyword-args))

#+acl2-par
(defmacro io?-prove@par (&rest rst)

; This macro is the approved way to produce proof output with
; waterfall-parallelism enabled.

  `(io?-prove-cw ,@rst))

(defun waterfall-print-clause-body (cl-id clause state)
  (with-output-lock
   (pprogn
    (increment-timer 'prove-time state)
    (fms "~@0~|~q1.~|"
         (list (cons #\0 (tilde-@-clause-id-phrase cl-id))
               (cons #\1 (prettyify-clause
                          clause
                          (let*-abstractionp state)
                          (w state))))
         (proofs-co state)
         state
         (term-evisc-tuple nil state))
    (increment-timer 'print-time state))))

(defmacro waterfall-print-clause-id-fmt1-call (cl-id)

; Keep in sync with waterfall-print-clause-id-fmt1-call@par.

  `(mv-let (col state)
           (fmt1 "~@0~|"
                 (list (cons #\0
                             (tilde-@-clause-id-phrase ,cl-id)))
                 0 (proofs-co state) state nil)
           (declare (ignore col))
           state))

#+acl2-par
(defmacro waterfall-print-clause-id-fmt1-call@par (cl-id)

; Keep in sync with waterfall-print-clause-id-fmt1-call.

  `(with-output-lock
    (mv-let (col state)
            (fmt1 "~@0~|"
                  (list (cons #\0
                              (tilde-@-clause-id-phrase ,cl-id)))
                  0 (proofs-co state) state nil)
            (declare (ignore col state))
            nil)))

(defmacro waterfall-print-clause-id (cl-id)
  `(pprogn
    (increment-timer 'prove-time state)
    (waterfall-print-clause-id-fmt1-call ,cl-id)
    (increment-timer 'print-time state)))

#+acl2-par
(defmacro waterfall-print-clause-id@par (cl-id)

; Parallelism wart: wormhole printing isn't reliable.  (When this wart is
; removed, then remove the references to it in
; unsupported-waterfall-parallelism-features and
; waterfall1-wrapper@par-before.)  We lock wormholes at a very high level, so
; we thought they might be thread safe.  However, in practice, when we enable
; printing through wormholes, there are problems symptomatic of race
; conditions.  We think these problems are related to the ld-special variables.
; Specifically, a thread tries to read from the prompt upon entering the
; wormhole, even if there isn't supposed to be any interaction with the prompt.
; A possible solution to this problem might involve implementing all of the
; ld-specials with global variables (as opposed to propsets), and then
; rebinding those global variables in each worker thread.  Long story short:
; wormholes might be thread-safe, but we have lots of reasons to believe they
; aren't.

; Therefore, we have different versions of the present macro for the
; #+acl2-loop-only and #-acl2-loop-only cases.  To see why, first note that
; waterfall-print-clause-id-fmt1-call does printing, hence returns state.  As
; such, the #+acl2-loop-only code (where state is not available) performs the
; printing inside a wormhole.  However, because of the parallelism wart above,
; we avoid the wormhole call in the #-acl2-loop-only case, which is the
; actually executed inside the prover.

  #+acl2-loop-only
  `(wormhole 'comment-window-io
             '(lambda (whs)
                (set-wormhole-entry-code whs :ENTER))
             (list ,cl-id)
             '(mv-let (col state)
                      (waterfall-print-clause-id-fmt1-call ,cl-id)
                      (declare (ignore col))
                      (value :q))
             :ld-error-action :return! ; might cause problems
             :ld-verbose nil
             :ld-pre-eval-print nil
             :ld-prompt nil)
  #-acl2-loop-only
  `(waterfall-print-clause-id-fmt1-call@par ,cl-id))

(defproxy print-clause-id-okp (*) => *)

(defun print-clause-id-okp-builtin (cl-id)
  (declare (ignore cl-id)
           (xargs :guard (clause-id-p cl-id)))
  t)

(defattach (print-clause-id-okp print-clause-id-okp-builtin)
  :skip-checks t)

(defun@par waterfall-print-clause (suppress-print cl-id clause state)
  (cond ((or suppress-print (equal cl-id *initial-clause-id*))
         (state-mac@par))
        ((serial-first-form-parallel-second-form@par
          nil
          (member-equal (f-get-global 'waterfall-printing state)
                        '(:limited :very-limited)))
         (state-mac@par))
        (t (pprogn@par
            (if (and (or (gag-mode)
                         (member-eq 'prove
                                    (f-get-global 'inhibit-output-lst state)))
                     (f-get-global 'print-clause-ids state)
                     (print-clause-id-okp cl-id))
                (waterfall-print-clause-id@par cl-id)
              (state-mac@par))
            (io?-prove@par
             (cl-id clause)
             (waterfall-print-clause-body cl-id clause state)
             :io-marker cl-id)))))

#+acl2-par
(defun some-parent-is-checkpointp (hist state)
  (cond ((endp hist)
         nil)
        ((member (access history-entry (car hist) :processor)
                 (f-get-global 'checkpoint-processors state))
         t)
        (t (some-parent-is-checkpointp (cdr hist) state))))

(defun@par waterfall-msg
  (processor cl-id clause signal clauses new-hist ttree pspv state)

; This function prints the report associated with the given processor on some
; input clause, clause, with output signal, clauses, ttree, and pspv.  The code
; below consists of two distinct parts.  First we print the message associated
; with the particular processor.  Then we return three results: a "jppl-flg", a
; new pspv with the gag-state updated, and the state.

; The jppl-flg is either nil or a pool-lst.  When non-nil, the jppl-flg means
; we just pushed a clause into the pool and assigned it the name that is the
; value of the flag.  "Jppl" stands for "just pushed pool list".  This flag is
; passed through the waterfall and eventually finds its way to the pop-clause
; after the waterfall, where it is used to control the optional printing of the
; popped clause.  If the jppl-flg is non-nil when we pop, it means we need not
; re-display the clause because it was just pushed and we can refer to it by
; name.

; This function increments timers.  Upon entry, the accumulated time is charged
; to 'prove-time.  The time spent in this function is charged to 'print-time.

  (declare (ignorable new-hist clauses))
  (pprogn@par
   (increment-timer@par 'prove-time state)
   (serial-only@par
    (io? proof-tree nil state
         (pspv signal new-hist clauses processor ttree cl-id)
         (pprogn
          (increment-proof-tree
           cl-id ttree processor (length clauses) new-hist signal pspv state)
          (increment-timer 'proof-tree-time state))))
   (mv-let
    (gagst msg)
    (waterfall-update-gag-state@par cl-id clause processor signal ttree pspv
                                    state)
    (declare (ignorable msg))
    (mv-let@par
     (pspv state)
     (cond (gagst (pprogn@par (record-gag-state@par gagst state)
                              (mv@par (change prove-spec-var pspv :gag-state
                                              gagst)
                                      state)))
           (t (mv@par pspv state)))
     (pprogn@par
      (serial-first-form-parallel-second-form@par
       (io? prove nil state
            (pspv ttree new-hist clauses signal cl-id processor msg)
            (waterfall-msg1 processor cl-id signal clauses new-hist msg ttree
                            pspv state)
            :io-marker cl-id)

; Parallelism wart: consider replacing print-splitter-rules-summary below.  A
; version of printing that does not involve wormholes will be required.  See
; book parallel/proofs/stress-waterfall-parallelism.lsp.  Note that it is
; unclear to Rager whether the :limited (or nil) version of waterfall-printing
; should print splitter-rules.  :Limited waterfall-printing should probably
; follow whatever gag-mode does.

; We could similarly comment out the :full case just below, since it also uses
; wormholes.  But we prefer to leave it, noting that :full is primarily used by
; developers.

       (cond ((equal (f-get-global 'waterfall-printing state) :full)
              (io? prove t
                   state
                   (pspv ttree new-hist clauses signal cl-id processor msg)
                   (waterfall-msg1 processor cl-id signal clauses new-hist msg
                                   ttree pspv state)
                   :io-marker cl-id))
             (t 'nothing-to-print
;               (io? prove t
;                    state
;                    (cl-id ttree clauses)
;                    (print-splitter-rules-summary
;                     cl-id clauses ttree state)
;                    :io-marker cl-id)
                )))
      (increment-timer@par 'print-time state)
      (mv@par (cond ((eq processor 'push-clause)

; Keep the following in sync with the corresponding call of pool-lst in
; waterfall0-or-hit.  See the comment there.

                     (pool-lst (cdr (access prove-spec-var pspv :pool))))
                    (t nil))
              pspv
              state))))))

; The waterfall is responsible for storing the ttree produced by each
; processor in the pspv.  That is done with:

(defun put-ttree-into-pspv (ttree pspv)
  (change prove-spec-var pspv
          :tag-tree (cons-tag-trees ttree
                                   (access prove-spec-var pspv :tag-tree))))

(defun set-cl-ids-of-assumptions1 (recs cl-id)
  (cond ((endp recs) nil)
        (t (cons (change assumption (car recs)
                         :assumnotes
                         (list (change assumnote
                                       (car (access assumption (car recs)
                                                    :assumnotes))
                                       :cl-id cl-id)))
                 (set-cl-ids-of-assumptions1 (cdr recs) cl-id)))))

(defun set-cl-ids-of-assumptions (ttree cl-id)

; We scan the tag-tree ttree, looking for 'assumptions.  Recall that each has a
; :assumnotes field containing exactly one assumnote record, which contains a
; :cl-id field.  We assume that :cl-id field is empty.  We put cl-id into it.
; We return a copy of ttree.

  (let ((recs (tagged-objects 'assumption ttree)))
    (cond (recs (extend-tag-tree
                 'assumption
                 (set-cl-ids-of-assumptions1 recs cl-id)
                 (remove-tag-from-tag-tree! 'assumption ttree)))
          (t ttree))))

; We now develop the code for proving the assumptions that are forced during
; the first part of the proof.  These assumptions are all carried in the ttree
; on 'assumption tags.  (Delete-assumptions was originally defined just below
; collect-assumptions, but has been moved up since it is used in push-clause.)

(defun collect-assumptions1 (recs only-immediatep ans)
  (cond ((endp recs) ans)
        (t (collect-assumptions1
            (cdr recs)
            only-immediatep
            (cond ((cond
                    ((eq only-immediatep 'non-nil)
                     (access assumption (car recs) :immediatep))
                    ((eq only-immediatep 'case-split)
                     (eq (access assumption (car recs) :immediatep)
                         'case-split))
                    ((eq only-immediatep t)
                     (eq (access assumption (car recs) :immediatep)
                         t))
                    (t t))
                   (add-to-set-equal (car recs) ans))
                  (t ans))))))

(defun collect-assumptions (ttree only-immediatep)

; We collect the assumptions in ttree and accumulate them onto ans.
; Only-immediatep determines exactly which assumptions we collect:
; * 'non-nil    -- only collect those with :immediatep /= nil
; * 'case-split -- only collect those with :immediatep = 'case-split
; * t           -- only collect those with :immediatep = t
; * nil         -- collect ALL assumptions

  (collect-assumptions1 (tagged-objects 'assumption ttree) only-immediatep
                        nil))

; We are now concerned with trying to shorten the type-alists used to
; govern assumptions.  We have two mechanisms.  One is
; ``disguarding,'' the throwing out of any binding whose term
; requires, among its guard clauses, the truth of the term we are
; trying to prove.  The second is ``disvaring,'' the throwing out of
; any binding that does not mention any variable linked to term.

; First, disguarding...  We must first define the fundamental process
; of generating the guard clauses for a term.  This "ought" to be in
; the vicinity of our definition of defun and verify-guards.  But we
; need it now.

; NOTE: Conjoin-clause-sets+ and some other relevant functions were once
; defined here, but have been moved to history-management.lisp in order to
; support the definition of termination-theorem-clauses and
; guard-clauses-for-clique.

; And now disvaring...

(defun linked-variables1 (vars direct-links changedp direct-links0)

; We union into vars those elements of direct-links that overlap its
; current value.  When we have done them all we ask if anything
; changed and if so, start over at the beginning of direct-links.

  (cond
   ((null direct-links)
    (cond (changedp (linked-variables1 vars direct-links0 nil direct-links0))
          (t vars)))
   ((and (intersectp-eq (car direct-links) vars)
         (not (subsetp-eq (car direct-links) vars)))
    (linked-variables1 (union-eq (car direct-links) vars)
                       (cdr direct-links)
                       t direct-links0))
   (t (linked-variables1 vars (cdr direct-links) changedp direct-links0))))

(defun linked-variables (vars direct-links)

; Vars is a list of variables.  Direct-links is a list of lists of
; variables, e.g., '((X Y) (Y Z) (A B) (M)).  Let's say that one
; variable is "directly linked" to another if they both appear in one
; of the lists in direct-links.  Thus, above, X and Y are directly
; linked, as are Y and Z, and A and B.  This function returns the list
; of all variables that are linked (directly or transitively) to those
; in vars.  Thus, in our example, if vars is '(X) the answer is '(X Y
; Z), up to order of appearance.

; Note on Higher Order Definitions and the Inconvenience of ACL2:
; Later in these sources we will define the "mate and merge" function,
; m&m, which computes certain kinds of transitive closures.  We really
; wish we had that function now, because this function could use it
; for the bulk of this computation.  But we can't define it here
; without moving up some of the data structures associated with
; induction.  Rather than rip our code apart, we define a simple
; version of m&m that does the job.

; This suggests that we really ought to support the idea of defining a
; function before all of its subroutines are defined -- a feature that
; ultimately involves the possibility of implicit mutual recursion.

; It should also be noted that the problem with moving m&m is not so
; much with the code for the mate and merge process as it is with the
; pseudo functional argument it takes.  M&m naturally is a higher
; order function that compute the transitive closure of an operation
; supplied to it.  Because ACL2 is first order, our m&m doesn't really
; take a function but rather a symbol and has a finite table mapping
; symbols to functions (m&m-apply).  It is only that table that we
; can't move up to here!  So if ACL2 were higher order, we could
; define m&m now and everything would be neat.  Of course, if ACL2
; were higher order, we suspect some other aspects of our coding
; (perhaps efficiency and almost certainly theorem proving power)
; would be degraded.

  (linked-variables1 vars direct-links nil direct-links))

; Part of disvaring a type-alist to is keep type-alist entries about
; constrained constants.  This goes to a problem that Eric Smith noted.
; He had constrained (thebit) to be 0 or 1 and had a type-alist entry
; stating that (thebit) was not 0.  In a forcing round he needed that
; (thebit) was 1.  But disvaring had thrown out of the type-alist the
; entry for (thebit) because it did not mention any of the relevant
; variables.  So, in a change for Version_2.7 we now keep entries that
; mention constrained constants.  We considered the idea of keeping
; entries that mention any constrained function, regardless of arity.
; But that seems like overkill.  Had Eric constrained (thebit x) to
; be 0 or 1 and then had a hypothesis that it was not 0, it seems
; unlikely that the forcing round would need to know (thebit x) is 1
; if x is not among the relevant vars.  That is, one assumes that if a
; constrained function has arguments then the function's behavior on
; those arguments does not determine the function's behavior on other
; arguments.  This need not be the case.  One can constrain (thebit x)
; so that if it is 0 on some x then it is 0 on all x.
; (implies (equal (thebit x) 0) (equal (thebit y) 0))
; But this seems unlikely.

(mutual-recursion

(defun contains-constrained-constantp (term wrld)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (contains-constrained-constantp-lst (fargs term) wrld)
             (contains-constrained-constantp (lambda-body (ffn-symb term))
                                             wrld)))
        ((and (getpropc (ffn-symb term) 'constrainedp nil wrld)
              (null (getpropc (ffn-symb term) 'formals t wrld)))
         t)
        (t (contains-constrained-constantp-lst (fargs term) wrld))))

(defun contains-constrained-constantp-lst (lst wrld)
  (cond ((null lst) nil)
        (t (or (contains-constrained-constantp (car lst) wrld)
               (contains-constrained-constantp-lst (cdr lst) wrld))))))


; So now we can define the notion of ``disvaring'' a type-alist.

(defun disvar-type-alist1 (vars type-alist wrld)
  (cond ((null type-alist) nil)
        ((or (intersectp-eq vars (all-vars (caar type-alist)))
             (contains-constrained-constantp (caar type-alist) wrld))
         (cons (car type-alist)
               (disvar-type-alist1 vars (cdr type-alist) wrld)))
        (t (disvar-type-alist1 vars (cdr type-alist) wrld))))

(defun collect-all-vars (lst)
  (cond ((null lst) nil)
        (t (cons (all-vars (car lst)) (collect-all-vars (cdr lst))))))

(defun disvar-type-alist (type-alist term wrld)

; We throw out of type-alist any binding that does not involve a
; variable linked by type-alist to those in term.  Thus, if term
; involves only the variables X and Y and type-alist binds a term that
; links Y to Z (and nothing else is linked to X, Y, or Z), then the
; resulting type-alist only binds terms containing X, Y, and/or Z.
; We actually keep entries about constrained constants.

; As we did for ``disguard'' we apologize for (but stand by) the
; non-word ``disvar.''

  (let* ((vars (all-vars term))
         (direct-links (collect-all-vars (strip-cars type-alist)))
         (vars* (linked-variables vars direct-links)))
    (disvar-type-alist1 vars* type-alist wrld)))

; Finally we can define the notion of ``unencumbering'' a type-alist.
; But as pointed out below, we no longer use this notion.

(defun unencumber-type-alist (type-alist term rewrittenp wrld)

; We wish to prove term under type-alist.  If rewrittenp is non-nil,
; it is also a term, namely the unrewritten term from which we
; obtained term.  Generally, term (actually its unrewritten version)
; is some conjunct from a guard.  In many cases we expect term to be
; something very simple like (RATIONALP X).  But chances are high that
; type- alist talks about many other variables and many irrelevant
; terms.  We wish to throw out irrelevant bindings from type-alist and
; return a new type-alist that is weaker but, we believe, as
; sufficient as the original for proving term.  We call this
; ``unencumbering'' the type-alist.

; The following paragraph is inaccurate because we no longer use
; disguarding.

; Historical Comment:
; We apply two different techniques.  The first is ``disguarding.''
; Roughly, the idea is to throw out the binding of any term that
; requires the truth of term in its guard.  Since we are trying to
; prove term true we will assume it false.  If a hypothesis in the
; type-alist requires term to get past the guard, we'll never do it.
; This is not unlikely since term is (probably) a forced guard from
; the very clause from which type-alist was created.
; End of Historical Comment

; The second technique, applied after disguarding, is to throw out any
; binding of a term that is not linked to the variables used by term.
; For example, if term is (RATIONALP X) then we won't keep a
; hypothesis about (PRIMEP Y) unless some kept hypothesis links X and
; Y.  This is called ``disvaring'' and is applied after disguarding
; because the terms thrown out by disguarding are likely to link
; variables in a bogus way.  For example, (< X Y) would link X and Y,
; but is thrown out by disguarding since it requires (RATIONALP X).
; While disvaring, we actually keep type-alist entries about constrained
; constants.

  (declare (ignore rewrittenp))
  (disvar-type-alist
   type-alist
   term
   wrld))

(defun unencumber-assumption (assn wrld)

; We no longer unencumber assumptions.  An example from Jared Davis prompted
; this change, in which he had contradictory hypotheses for which the
; contradiction was not yet evident after a round of simplification, leading to
; premature forcing -- and the contradiction was in hypotheses about variables
; irrelevant to what was forced, and hence was lost in the forcing round!  Here
; is a much simpler example of that phenomenon.

;  (defstub p1 (x) t)
;  (defstub p2 (x) t)
;  (defstub p3 (x) t)
;  (defstub p4 (x) t)
;
;  (defaxiom p1->p2
;    (implies (p1 x)
;             (p2 x)))
;
;  (defun foo (x y)
;    (implies x y))
;
;  (defaxiom p3->p4{forced}
;    (implies (force (p3 x))
;             (p4 x)))
;
;  ; When we unencumber the type-alist upon forcing, the following THM fails with
;  ; the following forcing round.  The problem is that the hypothesis about x is
;  ; dropped because it is deemed (by unencumber-type-alist) to be irrelevant to
;  ; the sole variable y of the forced hypothesis.
;
;  ; We now undertake Forcing Round 1.
;  ;
;  ; [1]Goal
;  ; (P3 Y).
;
;  (thm (if (not (foo (p1 x) (p2 x)))
;           (p4 y)
;         t)
;       :hints (("Goal" :do-not '(preprocess)
;                :in-theory (disable foo))))
;
;  ; But with unencumber-assumption defined to return its first argument, the THM
;  ; produces a forced goal that includes the contradictory hypotheses:
;
;  ; [1]Goal
;  ; (IMPLIES (NOT (FOO (P1 X) (P2 X)))
;  ;          (P3 Y)).
;
;  (thm (if (not (foo (p1 x) (p2 x)))
;           (p4 y)
;         t)
;       :hints (("Goal" :do-not '(preprocess)
;                :in-theory (disable foo))))

; Old comment and code:

; Given an assumption we try to unencumber (i.e., shorten) its
; :type-alist.  We return an assumption that may be proved in place of
; assn and is supposedly simpler to prove.

;   (change assumption assn
;           :type-alist
;           (unencumber-type-alist (access assumption assn :type-alist)
;                                  (access assumption assn :term)
;                                  (access assumption assn :rewrittenp)
;                                  wrld))

  (declare (ignore wrld))
  assn)

(defun unencumber-assumptions (assumptions wrld ans)

; This is just a glorified list reverse function!  At one time we actually did
; unencumber assumptions, but now, unencumber-assumption is defined simply to
; return nil, as explained in a comment in its definition.  A more elegant fix
; is to redefine the present function to return assumptions unchanged, to avoid
; consing up a reversed list.  However, we continue to reverse the input
; assumptions, for backward compatibility (otherwise forcing round goal names
; will change).  Reversing a small list is cheap, so this is not a big deal.

; Old comments:

; We unencumber every assumption in assumptions and return the
; modified list, accumulated onto ans.

; Note: This process is mentioned in :DOC forcing-round.  So if we change it,
; update the documentation.

  (cond
   ((null assumptions) ans)
   (t (unencumber-assumptions
       (cdr assumptions) wrld
       (cons (unencumber-assumption (car assumptions) wrld)
             ans)))))

; We are now concerned, for a while, with the idea of deleting from a
; set of assumptions those implied by others.  We call this
; assumption-subsumption.  Each assumption can be thought of as a goal
; of the form type-alist -> term.  Observe that if you have two
; assumptions with the same term, then the first implies the second if
; the type-alist of the second implies the type-alist of the first.
; That is,
; (thm (implies (implies ta2 ta1)
;               (implies (implies ta1 term) (implies ta2 term))))

; First we develop the idea that one type-alist implies another.

(defun dumb-type-alist-implicationp1 (type-alist1 type-alist2 seen)
  (cond ((null type-alist1) t)
        ((member-equal (caar type-alist1) seen)
         (dumb-type-alist-implicationp1 (cdr type-alist1) type-alist2 seen))
        (t (let ((ts1 (cadar type-alist1))
                 (ts2 (or (cadr (assoc-equal (caar type-alist1) type-alist2))
                          *ts-unknown*)))
             (and (ts-subsetp ts1 ts2)
                  (dumb-type-alist-implicationp1 (cdr type-alist1)
                                            type-alist2
                                            (cons (caar type-alist1) seen)))))))

(defun dumb-type-alist-implicationp2 (type-alist1 type-alist2)
  (cond ((null type-alist2) t)
        (t (and (assoc-equal (caar type-alist2) type-alist1)
                (dumb-type-alist-implicationp2 type-alist1
                                          (cdr type-alist2))))))

(defun dumb-type-alist-implicationp (type-alist1 type-alist2)

; NOTE: This function is intended to be dumb but fast.  One can
; imagine that we should be concerned with the types deduced by
; type-set under these type-alists.  For example, instead of asking
; whether every term bound in type-alist1 is bound to a bigger type
; set in type-alist2, we should perhaps ask whether the term has a
; bigger type-set under type-alist2.  Similarly, if we find a term
; bound in type-alist2 we should make sure that its type-set under
; type-alist1 is smaller.  If we need the smarter function we'll write
; it.  That's why we call this one "dumb."

; We say type-alist1 implies type-alist2 if (1) for every
; "significant" entry in type-alist1, (term ts1 . ttree1) it is the
; case that either term is not bound in type-alist2 or term is bound
; to some ts2 in type-alist2 and (ts-subsetp ts1 ts2), and (2) every
; term bound in type-alist2 is bound in type-alist1.  The case where
; term is not bound in type-alist2 can be seen as the natural
; treatment of the equivalent situation in which term is bound to
; *ts-unknown* in type-set2.  An entry (term ts . ttree) is
; "significant" if it is the first binding of term in the alist.

; We can treat a type-alist as a conjunction of assumptions about the
; terms it binds.  Each relevant entry gives rise to an assumption
; about its term.  Call the conjunction the "assumptions" encoded in
; the type-alist.  If type-alist1 implies type-alist2 then the
; assumptions of the first imply those of the second.  Consider an
; assumption of the first.  It restricts its term to some type.  But
; the corresponding assumption about term in the second type-alist
; restricts term to a larger type.  Thus, each assumption of the first
; type-alist implies the corresponding assumption of the second.

; The end result of all of this is that if you need to prove some
; condition, say g, under type-alist1 and also under type-alist2, and
; you can determine that type-alist1 implies type-alist2, then it is
; sufficient to prove g under type-alist2.

; Here is an example.  Let type-alist1 be
;   ((x *ts-t*)      (y *ts-integer*) (z *ts-symbol*))
; and type-alist2 be
;   ((x *ts-boolean*)(y *ts-rational*)).

; Observe that type-alist1 implies type-alist2: *ts-t* is a subset of
; *ts- boolean*, *ts-integer* is a subset of *ts-rational*, and
; *ts-symbol* is a subset of *ts-unknown*, and there are no terms
; bound in type-alist2 that aren't bound in type-alist1.  If we needed
; to prove g under both of these type-alists, it would suffice to
; prove it under type-alist2 (the weaker) because we must ultimately
; prove g under type-alist2 and the proof of g under type-alist1
; follows from that for free.

; Observe also that if we added to type-alist2 the binding (u
; *ts-cons*) then condition (1) of our definition still holds but (2)
; does not.  Further, if we mistakenly regarded type-alist2 as the
; weaker then proving (consp u) under type-alist2 would not ensure a
; proof of (consp u) under type-alist1.

  (and (dumb-type-alist-implicationp1 type-alist1 type-alist2 nil)
       (dumb-type-alist-implicationp2 type-alist1 type-alist2)))

; Now we arrange to partition a bunch of assumptions into pots
; according to their :terms, so we can do the type-alist implication
; work just on those assumptions that share a :term.

(defun partition-according-to-assumption-term (assumptions alist)

; We partition assumptions into pots, where the assumptions in a
; single pot all share the same :term.  The result is an alist whose
; keys are the :terms and whose values are the assumptions which have
; those terms.

  (cond ((null assumptions) alist)
        (t (partition-according-to-assumption-term
            (cdr assumptions)
            (put-assoc-equal
             (access assumption (car assumptions) :term)
             (cons (car assumptions)
                   (cdr (assoc-equal
                         (access assumption (car assumptions) :term)
                         alist)))
             alist)))))

; So now imagine we have a bunch of assumptions that share a term.  We
; want to delete from the set any whose type-alist implies any one
; kept.  See dumb-keep-assumptions-with-weakest-type-alists.

(defun exists-assumption-with-weaker-type-alist (assumption assumptions i)

; If there is an assumption, assn, in assumptions whose type-alist is
; implied by that of the given assumption, we return (mv pos assn),
; where pos is the position in assumptions of the first such assn.  We
; assume i is the position of the first assumption in assumptions.
; Otherwise we return (mv nil nil).

  (cond
   ((null assumptions) (mv nil nil))
   ((dumb-type-alist-implicationp
     (access assumption assumption :type-alist)
     (access assumption (car assumptions) :type-alist))
    (mv i (car assumptions)))
   (t (exists-assumption-with-weaker-type-alist assumption
                                                (cdr assumptions)
                                                (1+ i)))))

(defun add-assumption-with-weak-type-alist (assumption assumptions ans)

; We add assumption to assumptions, deleting any member of assumptions
; whose type-alist implies that of the given assumption.  When we
; delete an assumption we union its :assumnotes field into that of the
; assumption we are adding.  We accumulate our answer onto ans to keep
; this tail recursive; we presume that there will be a bunch of
; assumptions when this stuff gets going.

  (cond
   ((null assumptions) (cons assumption ans))
   ((dumb-type-alist-implicationp
     (access assumption (car assumptions) :type-alist)
     (access assumption assumption :type-alist))
    (add-assumption-with-weak-type-alist
     (change assumption assumption
             :assumnotes
             (union-equal (access assumption assumption :assumnotes)
                          (access assumption (car assumptions) :assumnotes)))
     (cdr assumptions)
     ans))
   (t (add-assumption-with-weak-type-alist assumption
                                           (cdr assumptions)
                                           (cons (car assumptions) ans)))))

(defun dumb-keep-assumptions-with-weakest-type-alists (assumptions kept)

; We return that subset of assumptions with the property that for
; every member, a, of assumptions there is one, b, among those
; returned such that (dumb-type-alist-implicationp a b).  Thus, we keep
; all the ones with the weakest hypotheses.  If we can prove all the
; ones kept, then we can prove them all, because each one thrown away
; has even stronger hypotheses than one of the ones we'll prove.
; (These comments assume that kept is initially nil and that all of
; the assumptions have the same :term.)  Whenever we throw out a in
; favor of b, we union into b's :assumnotes those of a.

  (cond
   ((null assumptions) kept)
   (t (mv-let
       (i assn)
       (exists-assumption-with-weaker-type-alist (car assumptions) kept 0)
       (cond
        (i (dumb-keep-assumptions-with-weakest-type-alists
            (cdr assumptions)
            (update-nth
             i
             (change assumption assn
                     :assumnotes
                     (union-equal
                      (access assumption (car assumptions) :assumnotes)
                      (access assumption assn :assumnotes)))
             kept)))
        (t (dumb-keep-assumptions-with-weakest-type-alists
            (cdr assumptions)
            (add-assumption-with-weak-type-alist (car assumptions)
                                                 kept nil))))))))

; And now we can write the top-level function for dumb-assumption-subsumption.

(defun dumb-assumption-subsumption1 (partitions ans)

; Having partitioned the original assumptions into pots by :term, we
; now simply clean up the cdr of each pot -- which is the list of all
; assumptions with the given :term -- and append the results of all
; the pots together.

  (cond
   ((null partitions) ans)
   (t (dumb-assumption-subsumption1
       (cdr partitions)
       (append (dumb-keep-assumptions-with-weakest-type-alists
                (cdr (car partitions))
                nil)
               ans)))))

(defun dumb-assumption-subsumption (assumptions)

; We throw out of assumptions any assumption implied by any of the others.  Our
; notion of "implies" here is quite weak, being a simple comparison of
; type-alists.  Briefly, we partition the set of assumptions into pots by :term
; and then, within each pot throw out any assumption whose type-alist is
; stronger than some other in the pot.  When we throw some assumption out in
; favor of another we combine its :assumnotes into that of the one we keep, so
; we can report the cases for which each final assumption accounts.

  (dumb-assumption-subsumption1
   (partition-according-to-assumption-term assumptions nil)
   nil))

; Now we move on to the problem of converting an unencumbered and subsumption
; cleansed assumption into a clause to prove.

(defun clausify-type-alist (type-alist cl ens w seen ttree)

; Consider a type-alist such as

; `((x ,*ts-cons*) (y ,*ts-integer*) (z ,(ts-union *ts-rational* *ts-symbol*)))

; and some term, such as (p x y z).  We wish to construct a clause
; that represents the goal of proving the term under the assumption of
; the type-alist.  A suitable clause in this instance is
; (implies (and (consp x)
;               (integerp y)
;               (or (rationalp z) (symbolp z)))
;          (p x y z))
; We return (mv clause ttree), where clause is the clause constructed.

; Note that we convert each pair in the type-alist to a provably equivalent
; term (i.e., we use convert-type-set-to-term1 with flg = t), since we are
; trying to prove the resulting clause.  See also the comment about tau in
; convert-type-set-to-term1.

  (cond ((null type-alist) (mv cl ttree))
        ((member-equal (caar type-alist) seen)
         (clausify-type-alist (cdr type-alist) cl ens w seen ttree))
        (t (mv-let (term ttree)
                   (convert-type-set-to-term1 (caar type-alist)
                                              (cadar type-alist)
                                              t ; flg; see above
                                              ens w ttree)
                   (clausify-type-alist (cdr type-alist)
                                        (cons (dumb-negate-lit term) cl)
                                        ens w
                                        (cons (caar type-alist) seen)
                                        ttree)))))

(defun clausify-assumption (assumption ens wrld)

; We convert the assumption assumption into a clause.

; Note: If you ever change this so that the assumption :term is not the last
; literal of the clause, change the printer process-assumptions-msg1.

  (clausify-type-alist
   (access assumption assumption :type-alist)
   (list (access assumption assumption :term))
   ens
   wrld
   nil
   nil))

(defun clausify-assumptions (assumptions ens wrld pairs ttree)

; We clausify every assumption in assumptions.  We return (mv pairs ttree),
; where pairs is a list of pairs, each of the form (assumnotes . clause) where
; the assumnotes are the corresponding field of the clausified assumption.

  (cond
   ((null assumptions) (mv pairs ttree))
   (t (mv-let (clause ttree1)
              (clausify-assumption (car assumptions) ens wrld)
              (clausify-assumptions
               (cdr assumptions)
               ens wrld
               (cons (cons (access assumption (car assumptions) :assumnotes)
                           clause)
                     pairs)
               (cons-tag-trees ttree1 ttree))))))

(defun strip-assumption-terms (lst)

; Given a list of assumptions, return the set of their terms.

  (cond ((endp lst) nil)
        (t (add-to-set-equal (access assumption (car lst) :term)
                             (strip-assumption-terms (cdr lst))))))

(defun add-splitters-to-ttree1 (assumnotes tag ttree)
  (cond ((endp assumnotes) ttree)
        (t (add-splitters-to-ttree1
            (cdr assumnotes)
            tag
            (add-to-tag-tree tag
                             (access assumnote (car assumnotes) :rune)
                             ttree)))))

(defun add-splitters-to-ttree (immediatep tag assumptions ttree)
  (cond ((endp assumptions) ttree)
        (t (add-splitters-to-ttree
            immediatep
            tag
            (cdr assumptions)
            (cond
             ((eq immediatep
                  (access assumption (car assumptions) :immediatep))
              (add-splitters-to-ttree1
               (access assumption (car assumptions) :assumnotes)
               tag ttree))
             (t ttree))))))

(defun maybe-add-splitters-to-ttree (splitter-output immediatep tag
                                                     assumptions ttree)
  (cond (splitter-output
         (add-splitters-to-ttree immediatep tag assumptions ttree))
        (t ttree)))

(defun extract-and-clausify-assumptions (cl ttree only-immediatep ens wrld
                                            splitter-output)

; WARNING: This function is overloaded.  Only-immediatep can take only only two
; values in this function: 'non-nil or nil.  The interpretation is as in
; collect-assumptions.  Cl is irrelevant if only-immediatep is nil.  We always
; return four results.  But when only-immediatep = 'non-nil, the first and part
; of the third result are irrelevant.  We know that only-immediatep = 'non-nil
; is used only in waterfall-step to do CASE-SPLITs and immediate FORCEs.  We
; know that only-immediatep = nil is used for forcing-round applications and in
; the proof-builder.  When CASE-SPLIT type assumptions are collected with
; only-immediatep = nil, then they are given the semantics of FORCE rather
; than CASE-SPLIT.  This could happen in the proof-builder, but it is thought
; not to happen otherwise.

; In the case that only-immediatep is nil: we strip all assumptions out of
; ttree, obtaining an assumption-free ttree, ttree'.  We then cleanup the
; assumptions, by removing subsumed ones.  (Formerly we also unencumbered their
; type-alists of presumed irrelevant bindings first, but we no longer do so;
; see unencumber-assumption.)  We then convert each kept assumption into a
; clause encoding the implication from the cleaned up type-alist to the
; assumed term.  We pair each clause with the :assumnotes of the assumptions
; for which it accounts, to produce a list of pairs, which is among the things
; we return.  Each pair is of the form (assumnotes . clause).  We return four
; results, (mv n a pairs ttree'), where n is the number of assumptions in the
; tree, a is the cleaned up assumptions we have to prove, whose length is the
; same as the length of pairs.

; In the case that only-immediatep is 'non-nil: we strip out of ttree only
; those assumptions with non-nil :immediatep flags.  As before, we generate a
; clause for each, but those with :immediatep = 'case-split we handle
; differently now: the clause for such an assumption is the one that encodes
; the implication from the negation of cl to the assumed term, rather than the
; one involving the type-alist of the assumption.  The assumnotes paired with
; such a clause is nil.  We do not really care about the assumnotes in
; case-splits or immediatep = t cases (e.g., they are ignored by the
; waterfall-step processing).  The final ttree, ttree', may still contain
; non-immediatep assumptions.

; To keep the definition simpler, we split into just the two cases outlined
; above.

  (cond
   ((eq only-immediatep nil)
    (let* ((raw-assumptions (collect-assumptions ttree only-immediatep))
           (cleaned-assumptions (dumb-assumption-subsumption
                                 (unencumber-assumptions raw-assumptions
                                                         wrld nil))))
      (mv-let
       (pairs ttree1)
       (clausify-assumptions cleaned-assumptions ens wrld nil nil)

; We check below that ttree1 is 'assumption free, so that when we add it to the
; result of cleansing 'assumptions from ttree we get an assumption-free ttree.
; If ttree1 contains assumptions we believe it must be because the bottom-most
; generator of those ttrees, namely convert-type-set-to-term, was changed to
; force assumptions.  But if that happens, we will have to rethink a lot here.
; How can we ensure that we get rid of all assumptions if we make assumptions
; while trying to express our assumptions as clauses?

       (mv (length raw-assumptions)
           cleaned-assumptions
           pairs
           (cons-tag-trees
            (cond
             ((tagged-objectsp 'assumption ttree1)
              (er hard 'extract-and-clausify-assumptions
                  "Convert-type-set-to-term apparently returned a ttree that ~
                    contained an 'assumption tag.  This violates the ~
                    assumption in this function."))
             (t ttree1))
            (delete-assumptions ttree only-immediatep))))))
   ((eq only-immediatep 'non-nil)
    (let* ((case-split-assumptions (collect-assumptions ttree 'case-split))
           (assumed-terms (strip-assumption-terms case-split-assumptions))
           (case-split-clauses (split-on-assumptions assumed-terms cl nil))
           (case-split-pairs (pairlis2 nil case-split-clauses))
           (raw-assumptions (collect-assumptions ttree t))
           (cleaned-assumptions (dumb-assumption-subsumption
                                 (unencumber-assumptions raw-assumptions
                                                         wrld nil))))
      (mv-let
       (pairs ttree1)
       (clausify-assumptions cleaned-assumptions ens wrld nil nil)

; We check below that ttree1 is 'assumption free, so that when we add it to the
; result of cleansing 'assumptions from ttree we get an assumption-free ttree.
; If ttree1 contains assumptions we believe it must be because the bottom-most
; generator of those ttrees, namely convert-type-set-to-term, was changed to
; force assumptions.  But if that happens, we will have to rethink a lot here.
; How can we ensure that we get rid of all assumptions if we make assumptions
; while trying to express our assumptions as clauses?

       (mv 'ignored
           assumed-terms
           (append case-split-pairs pairs)
           (maybe-add-splitters-to-ttree
            splitter-output
            'case-split
            'splitter-case-split
            case-split-assumptions
            (maybe-add-splitters-to-ttree
             splitter-output
             t
             'splitter-immed-forced
             raw-assumptions
             (cons-tag-trees
              (cond
               ((tagged-objectsp 'assumption ttree1)
                (er hard 'extract-and-clausify-assumptions
                    "Convert-type-set-to-term apparently returned a ttree ~
                     that contained an 'assumption tag.  This violates the ~
                     assumption in this function."))
               (t ttree1))
              (delete-assumptions ttree 'non-nil))))))))
   (t (mv 0 nil
          (er hard 'extract-and-clausify-assumptions
              "We only implemented two cases for only-immediatep:  'non-nil ~
               and nil.  But you now call it on ~p0."
              only-immediatep)
          nil))))

; Finally, we put it all together in the primitive function that
; applies a processor to a clause.

(defun@par waterfall-step1 (processor cl-id clause hist pspv wrld state
                                      step-limit)

; Note that apply-top-hints-clause is handled in waterfall-step.

  (case processor
    (simplify-clause
     (pstk
      (simplify-clause clause hist pspv wrld state step-limit)))
    (preprocess-clause
     (pstk
      (preprocess-clause clause hist pspv wrld state step-limit)))
    (otherwise
     (prepend-step-limit
      4
      (case processor
        (settled-down-clause
         (pstk
          (settled-down-clause clause hist pspv wrld state)))
        (eliminate-destructors-clause
         (pstk
          (eliminate-destructors-clause clause hist pspv wrld state)))
        (fertilize-clause
         (pstk
          (fertilize-clause cl-id clause hist pspv wrld state)))
        (generalize-clause
         (pstk
          (generalize-clause clause hist pspv wrld state)))
        (eliminate-irrelevance-clause
         (pstk
          (eliminate-irrelevance-clause clause hist pspv wrld state)))
        (otherwise
         (pstk
          (push-clause@par clause hist pspv wrld state))))))))

(defun@par process-backtrack-hint (cl-id clause clauses processor new-hist
                                         new-pspv ctx wrld state)

; A step of the indicated clause with cl-id through the waterfall, via
; waterfall-step, has tentatively returned the indicated clauses, new-hist, and
; new-pspv.  If the original pspv contains a :backtrack hint-setting, we replace
; the hint-settings with the computed hint that it specifies.

  (let ((backtrack-hint (cdr (assoc-eq :backtrack
                                       (access prove-spec-var new-pspv
                                               :hint-settings)))))
    (cond
     (backtrack-hint
      (assert$
       (eq (car backtrack-hint) 'eval-and-translate-hint-expression)
       (mv-let@par
        (erp val state)
        (eval-and-translate-hint-expression@par
         (cdr backtrack-hint) ; tuple of the form (name-tree flg term)
         cl-id clause wrld
         :OMITTED ; stable-under-simplificationp, unused in :backtrack hints
         new-hist new-pspv clauses processor
         :OMITTED ; keyword-alist, unused in :backtrack hints
         'backtrack (override-hints wrld) ctx state)
        (cond (erp (mv@par t nil nil state))
              ((assert$ (listp val)
                        (eq (car val) :computed-hint-replacement))
               (mv@par nil
                       (cddr val)
                       (assert$ (consp (cdr val))
                                (case (cadr val)
                                  ((t) (list backtrack-hint))
                                  ((nil) nil)
                                  (otherwise (cadr val))))
                       state))
              (t (mv@par nil val nil state))))))
     (t (mv@par nil nil nil state)))))

; Before we can can complete the definition of waterfall-step, we need support
; for rw-cache operations (see the Essay on Rw-cache) at the pspv level.

(defun set-rw-cache-state-in-pspv (pspv val)
  (declare (xargs :guard (member-eq val *legal-rw-cache-states*)))
  (change prove-spec-var pspv
          :rewrite-constant
          (change rewrite-constant
                  (access prove-spec-var pspv :rewrite-constant)
                  :rw-cache-state val)))

(defun maybe-set-rw-cache-state-disabled (pspv)
  (cond ((eq (access rewrite-constant
                     (access prove-spec-var pspv :rewrite-constant)
                     :rw-cache-state)
             t)
         (set-rw-cache-state-in-pspv pspv :disabled))
        (t pspv)))

(defun maybe-set-rw-cache-state-enabled (pspv)
  (cond ((eq (access rewrite-constant
                     (access prove-spec-var pspv :rewrite-constant)
                     :rw-cache-state)
             :disabled)
         (set-rw-cache-state-in-pspv pspv t))
        (t pspv)))

(defun accumulate-rw-cache-into-pspv (processor ttree pspv)

; This function is called during waterfall-step before modifying the pspv, in
; order to accumulate the rw-cache of ttree into the ttree of pspv.  This need
; only happen when the processor can put significant entries into the rw-cache,
; so this function is a no-op unless the processor is simplify-clause.  This
; need not happen when simplify-clause produces a hit, since the ttree will
; accumulated into the pspv elsewhere (so that runes are reported, forcing
; takes place, etc.); so it should suffice to call this function when there is
; a miss.  If the ttree is empty or if the rw-cache is not active, there is
; nothing to accumulate.  Also, as we clear the rw-cache for every call of
; rewrite-atm, there is no need to accumulate when the rw-cache-state is
; :atom.

  (cond ((and (eq processor 'simplify-clause)
              ttree
              (eq (access rewrite-constant
                          (access prove-spec-var pspv :rewrite-constant)
                          :rw-cache-state)
                  t))
         (let ((new-ttree-or-nil
                (accumulate-rw-cache? nil ttree (access prove-spec-var pspv
                                                        :tag-tree))))
           (cond (new-ttree-or-nil
                  (change prove-spec-var pspv
                          :tag-tree
                          new-ttree-or-nil))
                 (t pspv))))
        (t pspv)))

(defun erase-rw-cache-from-pspv (pspv)

; Erase all rw-cache tagged objects from the ttree of pspv.  We could call
; erase-rw-cache, but since we have the opportunity to call
; remove-tag-from-tag-tree! to save assoc-eq calls, we do so.

  (let ((ttree (access prove-spec-var pspv :tag-tree)))
    (cond ((tagged-objectsp 'rw-cache-any-tag ttree)
           (change prove-spec-var pspv
                   :tag-tree (remove-tag-from-tag-tree
                              'rw-cache-nil-tag
                              (remove-tag-from-tag-tree!
                               'rw-cache-any-tag
                               ttree))))
          ((tagged-objectsp 'rw-cache-nil-tag ttree)
           (change prove-spec-var pspv
                   :tag-tree (remove-tag-from-tag-tree!
                              'rw-cache-nil-tag
                              ttree)))
          (t pspv))))

(defconst *simplify-clause-ledge*
  (member-eq 'simplify-clause *preprocess-clause-ledge*))

(defconst *simplify-clause-ledge-complement*
  (set-difference-eq *preprocess-clause-ledge*
                     *simplify-clause-ledge*))

(defun@par waterfall-step-cleanup (processor cl-id clause hist wrld state
                                             signal clauses ttree pspv new-pspv
                                             step-limit)

; Signal here can be either some form of HIT (hit, hit-rewrite,
; hit-rewrite2, or-hit) or ABORT.

; Imagine that the indicated waterfall processor produced some form of
; hit and returned signal, clauses, ttree, and new-pspv.  We have to
; do certain cleanup on these things (e.g., add cl-id to all the
; assumnotes) and we do all that cleanup here.

; The actual cleanup is
; (1) add the cl-id to each assumnote in ttree
; (2) accumulate the modified ttree into state
; (3) extract the assumptions we are to handle immediately
; (4) compute the resulting case splits and modify clauses appropriately
; (5) make a new history entry
; (6) adjust signal to account for a specious application

; The result is (mv signal' clauses' ttree' hist' pspv' state) where
; each of the primed things are (possibly) modifications of their
; input counterparts.

; Here is blow-by-blow description of the cleanup.

; We update the :cl-id field (in the :assumnote) of every 'assumption.
; We accumulate the modified ttree into state.

  (declare (ignorable cl-id step-limit state))
  (let ((ttree (set-cl-ids-of-assumptions ttree cl-id)))

; We extract the assumptions we are to handle immediately.

    (mv-let
     (n assumed-terms pairs ttree)
     (extract-and-clausify-assumptions
      clause
      ttree
      'non-nil ; collect CASE-SPLIT and immediate FORCE assumptions
      (ens-from-pspv new-pspv)
      wrld
      (access rewrite-constant
              (access prove-spec-var new-pspv :rewrite-constant)
              :splitter-output))
     (declare (ignore n))

; Note below that we throw away the cars of the pairs, which are
; typically assumnotes.  We keep only the clauses themselves.
; We perform the required splitting, augmenting the previously
; generated clauses with the assumed terms.

     (let* ((split-clauses (strip-cdrs pairs))
            (clauses
             (if (and (null split-clauses)
                      (null assumed-terms)
                      (member-eq processor
                                 '(preprocess-clause
                                   apply-top-hints-clause)))
                 clauses
               (remove-trivial-clauses
                (union-equal split-clauses
                             (disjoin-clause-segment-to-clause-set
                              (dumb-negate-lit-lst assumed-terms)
                              clauses))
                wrld)))
            (ttree (cond ((cdr clauses) ttree)
                         (t (remove-tag-from-tag-tree 'splitter-if-intro
                                                      ttree))))

; We create the history entry for this step.  We have to be careful about
; specious hits to prevent a loop described below.

            (new-hist
             (cons (make history-entry
                         :signal signal ; indicating the type of "hit"
                         :processor

; We here detect specious behavior.  The basic idea is that a hit
; is specious if the input clause is among the output clauses.  But
; there are two exceptions: when the process is settled-down-clause or
; apply-top-hints-clause, such apparently specious output is ok.
; We mark a specious hit by setting the :processor of the history-entry
; to the cons (SPECIOUS . processor).

                         (if (and (not (member-eq
                                        processor
                                        '(settled-down-clause

; The obvious example of apparently specious behavior by
; apply-top-hints-clause that is not really specious is when it signals
; an OR-HIT and returns the input clause (to be processed by further hints).
; But the inclusion of apply-top-hints-clause in this list of exceptions
; was originally made in Version_2.7 because of :by hints.  Consider
; what happens when a :by hint produces a subgoal that is identical to the
; current goal.  If the subgoal is labeled as 'SPECIOUS, then we will 'MISS
; below.  This was causing the waterfall to apply the :by hint a second time,
; resulting in output such as the following:

;  As indicated by the hint, this goal is subsumed by (EQUAL (F1 X) (F0 X)),
;  which can be derived from LEMMA1 via functional instantiation, provided
;  we can establish the constraint generated.
;
;  As indicated by the hint, this goal is subsumed by (EQUAL (F1 X) (F0 X)),
;  which can be derived from LEMMA1 via functional instantiation, provided
;  we can establish the constraint generated.

; The following example reproduces the above output.  The top-level hints
; (i.e., *top-hint-keywords*) should never be 'SPECIOUS anyhow, because the
; user will more than likely prefer to see the output before the proof
; (probably) fails.

; (defstub f0 (x) t)
; (defstub f1 (x) t)
; (defstub f2 (x) t)
;
; (defaxiom lemma1
;   (equal (f2 x) (f1 x)))
;
; (defthm main
;   (equal (f1 x) (f0 x))
;   :hints (("Goal" :by (:functional-instance lemma1 (f2 f1) (f1 f0)))))

                                          apply-top-hints-clause)))
                                  (member-equal clause clauses))
                             (cons 'SPECIOUS processor)
                           processor)
                         :clause clause
                         :ttree ttree
                         :cl-id ; only needed for #+acl2-par, but harmless
                         cl-id)
                   hist)))
       (mv-let@par
        (erp ttree state)
        (accumulate-ttree-and-step-limit-into-state@par ttree step-limit state)
        (declare (ignore erp))

        (cond
         ((consp (access history-entry ; (SPECIOUS . processor)
                         (car new-hist) :processor))
          (mv@par 'MISS nil ttree new-hist
                  (accumulate-rw-cache-into-pspv processor ttree pspv)
                  state))
         (t (mv@par signal clauses ttree new-hist
                    (cond
                     ((or (member-eq processor *simplify-clause-ledge-complement*)
                          (eq processor 'settled-down-clause))
                      (put-ttree-into-pspv ttree new-pspv))
                     ((eq processor 'simplify-clause)
                      (put-ttree-into-pspv ttree
                                           (maybe-set-rw-cache-state-enabled
                                            new-pspv)))
                     (t
                      (put-ttree-into-pspv (erase-rw-cache ttree)
                                           (maybe-set-rw-cache-state-disabled
                                            (erase-rw-cache-from-pspv new-pspv)))))
                    state))))))))

#-acl2-loop-only
(defvar *iprint-read-state*

; Possible values are:

; nil      - no requirement on current iprint index
; t        - either all indices must exceed iprint-last-index, or none does
; (n . <=) - n, already read, is <= iprint-last-index; index must be too
; (n .  >) - n, already read, is  > iprint-last-index; index must be too

; The value is initially nil.  At a top-level read, it is set to nil if
; iprint-fal is nil, else to t.  For the first index i that is read when the
; value is t, we set the value to <= if (<= i iprint-last-index) and to >
; otherwise.

  nil)

#-acl2-loop-only
(defun iprint-oracle-updates-raw (state)

; Warning: Keep in sync with iprint-oracle-updates.

  (let* ((ar *wormhole-iprint-ar*))
    (when ar
      (f-put-global 'iprint-ar (compress1 'iprint-ar ar) state)
      (f-put-global 'iprint-fal *wormhole-iprint-fal* state)
      (f-put-global 'iprint-hard-bound *wormhole-iprint-hard-bound* state)
      (f-put-global 'iprint-soft-bound *wormhole-iprint-soft-bound* state)
      (setq *wormhole-iprint-ar* nil))
    (setq *iprint-read-state*
          (if (f-get-global 'iprint-fal state)
              t
            nil)))
  state)

(defun iprint-oracle-updates (state)

; Warning: Keep in sync with iprint-oracle-updates-raw.

  #+acl2-loop-only
  (mv-let (erp val state)
    (read-acl2-oracle state)
    (declare (ignore erp))

; If we intend to reason about this function, then we might want to check that
; val is a reasonable value.  But that seems not to be important, since very
; little reasoning would be possible anyhow for this function.

    (let ((val (fix-true-list val)))
      (pprogn (f-put-global 'iprint-ar
                            (nth 0 val)
                            state)
              (f-put-global 'iprint-hard-bound
                            (nfix (nth 1 val))
                            state)
              (f-put-global 'iprint-soft-bound
                            (nfix (nth 2 val))
                            state)
              (f-put-global 'iprint-fal
                            (nth 3 val)
                            state)
              state)))
  #-acl2-loop-only
  (iprint-oracle-updates-raw state))

(defun iprint-oracle-updates@par ()
  #-acl2-loop-only
  (iprint-oracle-updates-raw *the-live-state*)
  nil)

(defun@par waterfall-step (processor cl-id clause hist pspv wrld ctx state
                                     step-limit)

; Processor is one of the known waterfall processors.  This function applies
; processor and returns seven results: step-limit, signal, clauses, new-hist,
; new-pspv, jppl-flg, and state.

; All processor functions take as input a clause, its hist, a pspv, wrld, and
; state.  They all deliver four values (but apply-top-hints-clause,
; preprocess-clause, and simplify-clause also take a step-limit input and
; deliver a new step-limit as an additional value, in the first position): a
; signal, some clauses, a ttree, and a new pspv.  The signal delivered by such
; processors is one of 'error, 'miss, 'abort, or else indicates a "hit" via the
; signals 'hit, 'hit-rewrite, 'hit-rewrite2 and 'or-hit.  We identify the first
; three kinds of hits.  'Or-hits indicate that a set of disjunctive branches
; has been produced.

; If the returned signal is 'error or 'miss, we immediately return with that
; signal.  But if the signal is a "hit" or 'abort (which in this context means
; "the processor did something but it has demanded the cessation of the
; waterfall process"), we add a new history entry to hist, store the ttree into
; the new pspv, print the message associated with this processor, and then
; return.

; When a processor "hit"s, we check whether it is a specious hit, i.e., whether
; the input is a member of the output.  If so, the history entry for the hit is
; marked specious by having the :processor field '(SPECIOUS . processor).
; However, we report the step as a 'miss, passing back the extended history to
; be passed.  Specious processors have to be recorded in the history so that
; waterfall-msg can detect that they have occurred and not reprint the formula.
; Mild Retraction: Actually, settled-down-clause always produces
; specious-appearing output but we never mark it as 'SPECIOUS because we want
; to be able to assoc for settled-down-clause and we know it's specious anyway.

; We typically return (mv step-limit signal clauses new-hist new-pspv jppl-flg
; state).

; Signal             Meaning

; 'error         Halt the entire proof attempt with an error.  We
;                print out the error message to the returned state.
;                In this case, clauses, new-hist, new-pspv, and jppl-flg
;                are all irrelevant (and nil).

; 'miss          The processor did not apply or was specious.  Clauses,
;                and jppl-flg are irrelevant and nil, but new-hist has the
;                specious processor recorded in it, and new-pspv records
;                rw-cache modifications to the :tag-tree of the input pspv.
;                State is unchanged.

; 'abort         Like a "hit", except that we are not to continue with
;                the waterfall.  We are to use the new pspv as the
;                final pspv produced by the waterfall.

; 'hit           The processor applied and produced the new set of
; 'hit-rewrite   clauses returned.  The appropriate new history and
; 'hit-rewrite2  new pspv are returned.  Jppl-flg is either nil
;                (indicating that the processor was not push-clause)
;                or is a pool lst (indicating that a clause was pushed
;                and assigned that lst).  The jppl-flg of the last executed
;                processor should find its way out of the waterfall so
;                that when we get out and pop a clause we know if we
;                just pushed it.  Finally, the message describing the
;                transformation has been printed to state.

; 'or-hit        The processor applied and has requested a disjunctive
;                split determined by hints.  The results are actually
;                the same as for 'hit.  The processor did not actually
;                produce the case split because some of the hints
;                (e.g., :in-theory) are related to the environment
;                in which we are to process the clause rather than the
;                clause itself.

; 'top-of-waterfall-hint
;                A :backtrack hint was applicable, and suitable results are
;                returned for handling it.

  (sl-let@par
   (erp signal clauses ttree new-pspv state)
   (catch-time-limit5@par
    (cond ((eq processor 'apply-top-hints-clause) ; this case returns state
           (apply-top-hints-clause@par cl-id clause hist pspv wrld ctx state
                                       step-limit))
          (t
           (sl-let
            (signal clauses ttree new-pspv)
            (waterfall-step1@par processor cl-id clause hist pspv wrld state
                                 step-limit)
            (mv@par step-limit signal clauses ttree new-pspv state)))))
   (pprogn@par

; Since wormholes (in particular, brr wormholes) don't change the global values
; of the iprint structures, we make such changes here so that iprinting done
; in brr is reflected in the global state.

    (serial-first-form-parallel-second-form@par
     (iprint-oracle-updates state)
     (iprint-oracle-updates@par))
    (cond
     (erp ; from out-of-time or clause-processor failure; treat as 'error signal
      (mv-let@par (erp2 val state)
                  (er@par soft ctx "~@0" erp)
                  (declare (ignore erp2 val))
                  (pprogn@par
                   (assert$
                    (null ttree)
                    (mv-let@par
                     (erp3 val state)
                     (accumulate-ttree-and-step-limit-into-state@par
                      (add-to-tag-tree! 'abort-cause
                                        (if (equal erp *interrupt-string*)
                                            'interrupt
                                          'time-limit-reached)
                                        nil)
                      step-limit
                      state)
                     (declare (ignore val))
                     (assert$ (null erp3)
                              (state-mac@par))))
                   (mv@par step-limit 'error nil nil nil nil state))))
     (t
      (pprogn@par ; account for bddnote in case we do not have a hit
       (cond ((and (eq processor 'apply-top-hints-clause)
                   (member-eq signal '(error miss))
                   ttree) ; a bddnote; see bdd-clause
              (error-in-parallelism-mode@par

; Parallelism blemish: we disable the following addition of BDD notes to the
; state.  Until a user requests it, we don't see a need to implement this.

               (state-mac@par)
               (f-put-global 'bddnotes
                             (cons ttree
                                   (f-get-global 'bddnotes state))
                             state)))
             (t (state-mac@par)))
       (mv-let@par
        (signal clauses new-hist new-pspv jppl-flg state)
        (cond ((eq signal 'error)

; As of this writing, the only processor which might cause an error is
; apply-top-hints-clause.  But processors can't actually cause errors in the
; error/value/state sense because they don't return state and so can't print
; their own error messages.  We therefore make the convention that if they
; signal error then the "clauses" value they return is in fact a pair
; (fmt-string . alist) suitable for giving error1.  Moreover, in this case
; ttree is an alist assigning state global variables to values.

               (mv-let@par (erp val state)
                           (error1@par ctx (car clauses) (cdr clauses) state)
                           (declare (ignore erp val))
                           (mv@par 'error nil nil nil nil state)))
              ((eq signal 'miss)
               (mv@par 'miss nil hist
                       (accumulate-rw-cache-into-pspv processor ttree pspv)
                       nil state))
              (t
               (mv-let@par
                (signal clauses ttree new-hist new-pspv state)
                (waterfall-step-cleanup@par processor cl-id clause hist wrld
                                            state signal clauses ttree pspv
                                            new-pspv step-limit)
                (mv-let@par
                 (erp new-hint-settings new-hints state)
                 (cond
                  ((or (eq signal 'miss) ; presumably specious
                       (eq processor 'settled-down-clause)) ; not user-visible
                   (mv@par nil nil nil state))
                  (t (process-backtrack-hint@par cl-id clause clauses processor
                                                 new-hist new-pspv ctx wrld
                                                 state)))
                 (cond
                  (erp
                   (mv@par 'error nil nil nil nil state))
                  (new-hint-settings
                   (mv@par 'top-of-waterfall-hint
                           new-hint-settings
                           processor
                           :pspv-for-backtrack
                           new-hints
                           state))
                  (t
                   (mv-let@par
                    (jppl-flg new-pspv state)
                    (waterfall-msg@par processor cl-id clause signal clauses
                                       new-hist ttree new-pspv state)
                    (mv@par signal clauses new-hist new-pspv jppl-flg
                            state))))))))
        (mv@par step-limit signal clauses new-hist new-pspv jppl-flg
                state))))))))

; Section:  FIND-APPLICABLE-HINT-SETTINGS

; Here we develop the code that recognizes that some user-supplied
; hint settings are applicable and we develop the routine to use
; hints.  It all comes together in waterfall1.

(defun@par find-applicable-hint-settings1
  (cl-id clause hist pspv ctx hints hints0 wrld stable-under-simplificationp
         override-hints state)

; See translate-hints1 for "A note on the taxonomy of translated hints", which
; explains hint settings.  Relevant background is also provided by :doc topic
; hints-and-the-waterfall, which links to :doc override-hints (also providing
; relevant background).

; We scan down hints looking for the first one that matches cl-id and clause.
; If we find none, we return nil.  Otherwise, we return a pair consisting of
; the corresponding hint-settings and hints0 modified as directed by the hint
; that was applied.  By "match" here, of course, we mean either

; (a) the hint is of the form (cl-id . hint-settings), or

; (b) the hint is of the form (eval-and-translate-hint-expression name-tree flg
; term) where term evaluates to a non-erroneous non-nil value when ID is bound
; to cl-id, CLAUSE to clause, WORLD to wrld, STABLE-UNDER-SIMPLIFICATIONP to
; stable-under-simplificationp, HIST to hist, PSPV to pspv, CTX to ctx, and
; STATE to state.  In this case the corresponding hint-settings is the
; translated version of what the term produced.  We know that term is
; single-threaded in state and returns an error triple.

; This function is responsible for interpreting computed hints, including the
; meaning of the :computed-hint-replacement keyword.  It also deals
; appropriately with override-hints.  Note that override-hints is
; (override-hints wrld).

; Stable-under-simplificationp is t when the clause has been found not to
; change when simplified.  In particular, it is t if we are about to transition
; to destructor elimination.

; Optimization: By convention, when this function is called with
; stable-under-simplificationp = t, we know that the function returned nil when
; called earlier with the change: stable-under-simplificationp = nil.  That is,
; if we know the clause is stable under simplification, then we have already
; tried and failed to find an applicable hint for it before we knew it was
; stable.  So when stable-under-simplificationp is t, we avoid some work and
; just eval those hints that might be sensitive to
; stable-under-simplificationp.  The flg component of (b)-style hints indicates
; whether the term contains the free variable stable-under-simplificationp.

  (cond ((null hints)
         (cond ((or (null override-hints) ; optimization for common case
                    stable-under-simplificationp) ; avoid loop
                (value@par nil))
               (t ; no applicable hint-settings, so apply override-hints to nil
                (er-let*@par
                 ((new-keyword-alist
                   (apply-override-hints@par
                    override-hints cl-id clause hist pspv ctx wrld
                    stable-under-simplificationp
                    :OMITTED ; clause-list
                    :OMITTED ; processor
                    nil      ; keyword-alist
                    state))
                  (pair (cond (new-keyword-alist
                               (translate-hint@par
                                'override-hints ; name-tree
                                (cons (string-for-tilde-@-clause-id-phrase
                                       cl-id)
                                      new-keyword-alist)
                                nil ; hint-type
                                ctx wrld state))
                              (t (value@par nil)))))
                 (value@par (cond (pair (cons (cdr pair) hints0))
                                  (t nil)))))))
        ((eq (car (car hints)) 'eval-and-translate-hint-expression)
         (cond
          ((and stable-under-simplificationp
                (not (caddr (car hints)))) ; flg
           (find-applicable-hint-settings1@par
            cl-id clause hist pspv ctx (cdr hints) hints0 wrld
            stable-under-simplificationp override-hints state))
          (t
           (er-let*@par
            ((hint-settings

; The following call applies the override-hints to the computed hint.

              (eval-and-translate-hint-expression@par
               (cdr (car hints))
               cl-id clause wrld
               stable-under-simplificationp hist pspv
               :OMITTED ; clause-list
               :OMITTED ; processor
               :OMITTED ; keyword-alist
               nil
               override-hints
               ctx state)))
            (cond
             ((null hint-settings)
              (find-applicable-hint-settings1@par
               cl-id clause hist pspv ctx (cdr hints) hints0 wrld
               stable-under-simplificationp override-hints state))
             ((eq (car hint-settings) :COMPUTED-HINT-REPLACEMENT)
              (value@par
               (cond
                ((eq (cadr hint-settings) nil)
                 (cons (cddr hint-settings)
                       (remove1-equal (car hints) hints0)))
                ((eq (cadr hint-settings) t)
                 (cons (cddr hint-settings)
                       hints0))
                (t (cons (cddr hint-settings)
                         (append (cadr hint-settings)
                                 (remove1-equal (car hints) hints0)))))))
             (t (value@par (cons hint-settings
                                 (remove1-equal (car hints) hints0)))))))))
        ((and (not stable-under-simplificationp)
              (consp (car hints))
              (equal (caar hints) cl-id))
         (cond ((null override-hints)
                (value@par (cons (cdar hints)
                                 (remove1-equal (car hints) hints0))))

; Override-hints is (override-hints wrld).  If override-hints is non-nil, then
; we originally translated the hint as (list* cl-id (:KEYWORD-ALIST
; . keyword-alist) (:NAME-TREE . name-tree) . hint-settings.  We apply the
; override-hints to get a new keyword-alist.  If the keyword-alist has not
; changed, then hint-settings is still the correct translation.  Otherwise, we
; need to translate the new keyword-alist.  The result could be a computed
; hint, in which case we simply replace the hint with that computed hint and
; call this function recursively.  But if the result is not a computed hint,
; then it is a fully-translated hint with the same clause-id, and we have our
; result.

               ((not (let ((hint-settings (cdar hints)))
                       (and (consp hint-settings)
                            (consp (car hint-settings))
                            (eq (car (car hint-settings))
                                :KEYWORD-ALIST)
                            (consp (cdr hint-settings))
                            (consp (cadr hint-settings))
                            (eq (car (cadr hint-settings))
                                :NAME-TREE))))
                (er@par soft ctx
                  "Implementation error: With override-hints present, we ~
                   expected an ordinary translated hint-settings to start ~
                   with ((:KEYWORD-ALIST . keyword-alist) (:NAME-TREE . ~
                   name-tree)) but instead the translated hint-settings was ~
                   ~x0.  Please contact the ACL2 implementors."
                  (cdar hints)))
               (t
                (let* ((full-hint-settings (cdar hints))
                       (keyword-alist (cdr (car full-hint-settings)))
                       (name-tree (cdr (cadr full-hint-settings)))
                       (hint-settings (cddr full-hint-settings)))
                  (er-let*@par
                   ((new-keyword-alist
                     (apply-override-hints@par
                      override-hints cl-id clause hist pspv ctx wrld
                      stable-under-simplificationp
                      :OMITTED ; clause-list
                      :OMITTED ; processor
                      keyword-alist
                      state))
                    (hint-settings
                     (cond
                      ((equal new-keyword-alist keyword-alist)
                       (value@par hint-settings))
                      ((null new-keyword-alist) ; optimization
                       (value@par nil))
                      (t (er-let*@par
                          ((pair (translate-hint@par
                                  name-tree
                                  (cons (string-for-tilde-@-clause-id-phrase
                                         cl-id)
                                        new-keyword-alist)
                                  nil ; hint-type
                                  ctx wrld state)))
                          (assert$ (equal (car pair) cl-id)
                                   (value@par (cdr pair))))))))
                   (value@par (cond ((null new-keyword-alist)
                                     nil)
                                    (t (cons hint-settings
                                             (remove1-equal (car hints)
                                                            hints0))))))))))
        (t (find-applicable-hint-settings1@par
            cl-id clause hist pspv ctx (cdr hints) hints0 wrld
            stable-under-simplificationp override-hints state))))

(defun@par find-applicable-hint-settings (cl-id clause hist pspv ctx hints wrld
                                                stable-under-simplificationp
                                                state)

; First, we find the applicable hint-settings (with
; find-applicable-hint-settings1) from the explicit and computed hints.  Then,
; we modify those hint-settings by using the override-hints; see :DOC
; override-hints.

  (find-applicable-hint-settings1@par cl-id clause hist pspv ctx hints hints
                                      wrld stable-under-simplificationp
                                      (override-hints wrld)
                                      state))

(defun@par thanks-for-the-hint (goal-already-printed-p hint-settings cl-id
                                                       state)

; This function prints the note that we have noticed the hint.  We have to
; decide whether the clause to which this hint was attached was printed out
; above or below us.  We return state.  Goal-already-printed-p is either t,
; nil, or a pair (cons :backtrack processor) where processor is a member of
; *preprocess-clause-ledge*.  Cl-id may be a clause-id, but any value (in
; particular, nil) is legal, as it is only used in construction of the
; :io-marker of a io-record.

  (declare (ignorable state cl-id))
  (cond ((cdr (assoc-eq :no-thanks hint-settings))
         (mv@par (delete-assoc-eq :no-thanks hint-settings) state))
        ((alist-keys-subsetp hint-settings '(:backtrack))
         (mv@par hint-settings state))
        (t
         (pprogn@par
          (cond
           ((serial-first-form-parallel-second-form@par
             nil
             (member-equal (f-get-global 'waterfall-printing state)
                           '(:limited :very-limited)))
            (state-mac@par))
           (t
            (io?-prove@par
             (goal-already-printed-p)
             (fms "[Note:  A hint was supplied for our processing of the goal ~
                   ~#0~[above~/below~/above, provided by a :backtrack hint ~
                   superseding ~@1~].  Thanks!]~%"
                  (list
                   (cons
                    #\0
                    (case goal-already-printed-p
                      ((t) 0)
                      ((nil) 1)
                      (otherwise 2)))
                   (cons
                    #\1
                    (and (consp goal-already-printed-p)
                         (case (cdr goal-already-printed-p)
                           (apply-top-hints-clause
                            "the use of a :use, :by, :cases, :bdd, ~
                             :clause-processor, or :or hint")
                           (preprocess-clause
                            "preprocessing (the use of simple rules)")
                           (simplify-clause
                            "simplification")
                           (eliminate-destructors-clause
                            "destructor elimination")
                           (fertilize-clause
                            "the heuristic use of equalities")
                           (generalize-clause
                            "generalization")
                           (eliminate-irrelevance-clause
                            "elimination of irrelevance")
                           (push-clause
                            "the use of induction")
                           (otherwise
                            (er hard 'thanks-for-the-hint
                                "Implementation error: Unrecognized ~
                                 processor, ~x0."
                                (cdr goal-already-printed-p)))))))
                  (proofs-co state)
                  state
                  nil)
             :io-marker cl-id)))
          (mv@par hint-settings state)))))

; We now develop the code for warning users about :USEing enabled
; :REWRITE and :DEFINITION rules.

(defun lmi-name-or-rune (lmi)

; See also lmi-seed, which is similar except that it returns a base symbol
; where we are happy to return a rune, and when it returns a term we return
; nil.  The symbols returned by this function are those for which we want to
; provide a warning about using an enabled rule; see enabled-lmi-names.

  (cond ((atom lmi) lmi)
        ((member-eq (car lmi) '(:theorem

; There is no reason to warn about using a termination or guard theorem.  (See
; comment above about the purpose being to provide a warning.)

                                :termination-theorem
                                :termination-theorem!
                                :guard-theorem

; Through Version_7.1 we warned when using a functional instance of an enabled
; rule.  As Eric Smith has pointed out, this is rarely appropriate.

                                :functional-instance))
         nil)
        ((eq (car lmi) :instance)
         (lmi-name-or-rune (cadr lmi)))
        (t lmi)))

(defun enabled-lmi-names1 (ens pairs)

; Pairs is the runic-mapping-pairs for some symbol, and hence each of
; its elements looks like (nume . rune).  We collect the enabled
; :definition and :rewrite runes from pairs.

  (cond
   ((null pairs) nil)
   ((and (or (eq (cadr (car pairs)) :definition)
             (eq (cadr (car pairs)) :rewrite))
         (enabled-numep (car (car pairs)) ens))
    (add-to-set-equal (cdr (car pairs))
                      (enabled-lmi-names1 ens (cdr pairs))))
   (t (enabled-lmi-names1 ens (cdr pairs)))))

(defun enabled-lmi-names (ens lmi-lst wrld)

  (cond
   ((null lmi-lst) nil)
   (t (let ((x (lmi-name-or-rune (car lmi-lst))))

; x is either nil, a name, or a rune

        (cond
         ((null x)
          (enabled-lmi-names ens (cdr lmi-lst) wrld))
         ((symbolp x)
          (union-equal (enabled-lmi-names1
                        ens
                        (getpropc x 'runic-mapping-pairs nil wrld))
                       (enabled-lmi-names ens (cdr lmi-lst) wrld)))
         ((enabled-runep x ens wrld)
          (add-to-set-equal x (enabled-lmi-names ens (cdr lmi-lst) wrld)))
         (t (enabled-lmi-names ens (cdr lmi-lst) wrld)))))))

(defun@par maybe-warn-for-use-hint (pspv cl-id ctx wrld state)
  (cond
   ((warning-disabled-p "Use")
    (state-mac@par))
   (t
    (let ((enabled-lmi-names
           (enabled-lmi-names
            (ens-from-pspv pspv)
            (cadr (assoc-eq :use
                            (access prove-spec-var pspv :hint-settings)))
            wrld)))
      (cond
       (enabled-lmi-names
        (warning$@par ctx ("Use")
          "It is unusual to :USE an enabled :REWRITE or :DEFINITION rule, so ~
           you may want to consider disabling ~&0 in the hint provided for ~
           ~@1.  See :DOC using-enabled-rules."
          enabled-lmi-names
          (tilde-@-clause-id-phrase cl-id)))
       (t (state-mac@par)))))))

(defun@par maybe-warn-about-theory-simple (ens1 ens2 ctx wrld state)

; We may use this function instead of maybe-warn-about-theory when we know that
; ens1 contains a compressed theory array (and so does ens2, but that should
; always be the case).

  (let ((force-xnume-en1 (enabled-numep *force-xnume* ens1))
        (imm-xnume-en1 (enabled-numep *immediate-force-modep-xnume* ens1)))
    (maybe-warn-about-theory@par ens1 force-xnume-en1 imm-xnume-en1 ens2
                                 ctx wrld state)))

(defun@par maybe-warn-about-theory-from-rcnsts (rcnst1 rcnst2 ctx ens wrld
                                                       state)
  (declare (ignore ens))
  (let ((ens1 (access rewrite-constant rcnst1 :current-enabled-structure))
        (ens2 (access rewrite-constant rcnst2 :current-enabled-structure)))
    (cond
     ((equal (access enabled-structure ens1 :array-name)
             (access enabled-structure ens2 :array-name))

; We want to avoid printing a warning in those cases where we have not really
; created a new enabled structure.  In this case, the enabled structures could
; still in principle be different, in which case we are missing some possible
; warnings.  In practice, this function is only called when ens2 is either
; identical to ens1 or is created from ens1 by a call of
; load-theory-into-enabled-structure that creates a new array name, in which
; case the eql test above will fail.

; Warning: Through Version_4.1 we compared :array-name-suffix fields.  But now
; that the waterfall can be parallelized, the suffix might not change when we
; install a new theory array; consider load-theory-into-enabled-structure in
; the case that its incrmt-array-name-info argument is a clause-id.

      (state-mac@par))
     (t

; The new theory is being constructed from the user's hint and the ACL2 world.
; The most coherent thing to do is construct the warning in an analogous manner,
; which is why we use ens below rather than ens1.

      (maybe-warn-about-theory-simple@par ens1 ens2 ctx wrld state)))))

; Essay on OR-HIT Messages

; When we generate an OR-HIT, we print a message saying it has
; happened and that we will sweep across the disjuncts and consider
; each in turn.  That message is printed in
; apply-top-hints-clause-msg1.

; As we sweep, we print three kinds of messages:
; a:  ``here is the next disjunct to consider''
; b:  ``this disjunct has succeeded and we won't consider the others''
; c:  ``we've finished the sweep and now we choose the best result''

; Each is printed by a waterfall-or-hit-msg- function, labeled a, b,
; or c.

(defun waterfall-or-hit-msg-a (cl-id user-hinti d-cl-id i branch-cnt state)

; We print out the message associated with one disjunctive branch.  The special
; case of when there is exactly one branch is handled by
; apply-top-hints-clause-msg1.

  (cond
   ((gag-mode)

; Suppress printing for :OR splits; see also other comments with this header.

; In the case where we are only printing for gag-mode, we want to keep the
; message short.  Our message relies on the disjunctive goal name starting with
; the word "Subgoal" so that the English is sensible.

;   (fms "---~|Considering disjunctive ~@0 of ~@1.~|"
;        (list (cons #\0 (tilde-@-clause-id-phrase d-cl-id))
;              (cons #\1 (tilde-@-clause-id-phrase cl-id)))
;        (proofs-co state)
;        state
;        nil)

    state)
   (t
    (fms "---~%~@0~%( same formula as ~@1 ).~%~%The ~n2 disjunctive branch ~
          (of ~x3) for ~@1 can be created by applying the hint:~%~y4.~%"
         (list (cons #\0 (tilde-@-clause-id-phrase d-cl-id))
               (cons #\1 (tilde-@-clause-id-phrase cl-id))
               (cons #\2 (list i))
               (cons #\3 branch-cnt)
               (cons #\4 (cons (string-for-tilde-@-clause-id-phrase d-cl-id)
                               user-hinti)))
         (proofs-co state)
         state
         nil))))

(defun waterfall-or-hit-msg-b (cl-id d-cl-id branch-cnt state)

; We print out the message that d-cl-id (and thus cl-id) has succeeded
; and that we will cut off the search through the remaining branches.

  (cond ((gag-mode)
; Suppress printing for :OR splits; see also other comments with this header.
         state)
        (t
         (fms "---~%~@0 has succeeded!  All of its subgoals have been proved ~
               (modulo any forced assumptions).  Recall that it was one of ~
               ~n1 disjunctive branches generated by the :OR hint to prove ~
               ~@2.   We therefore abandon work on the other branches.~%"
              (list (cons #\0 (tilde-@-clause-id-phrase d-cl-id))
                    (cons #\1 branch-cnt)
                    (cons #\2 (tilde-@-clause-id-phrase cl-id)))
              (proofs-co state)
              state
              nil))))

(defun tilde-*-or-hit-summary-phrase1 (summary)
  (cond
   ((endp summary) nil)
   (t (let ((cl-id (car (car summary)))
            (subgoals (cadr (car summary)))
            (difficulty (caddr (car summary))))
        (cons (msg "~@0~t1   ~c2   ~c3~%"
                   (tilde-@-clause-id-phrase cl-id)
                   20
                   (cons subgoals 5)
                   (cons difficulty 10))
              (tilde-*-or-hit-summary-phrase1 (cdr summary)))))))

(defun tilde-*-or-hit-summary-phrase (summary)

; Each element of summary is of the form (cl-id n d), where n is the
; number of subgoals pushed by the processing of cl-id and d is their
; combined difficulty.  We prepare a ~* message that will print as
; a series of lines:

; disjunct  subgoals  estimated difficulty
; cl-id1       n              d

  (list "" "~@*" "~@*" "~@*"
        (tilde-*-or-hit-summary-phrase1 summary)))

(defun waterfall-or-hit-msg-c (parent-cl-id results revert-d-cl-id cl-id summary
                                            state)

; This message is printed when we have swept all the disjunctive
; branches and have chosen cl-id as the one to pursue.  If results is
; empty, then cl-id and summary are all irrelevant (and probably nil).

  (cond
   ((null results)
    (cond
     (revert-d-cl-id
      (fms "---~%None of the branches we tried for ~@0 led to a plausible set ~
            of subgoals, and at least one, ~@1, led to the suggestion that we ~
            focus on the original conjecture.  We therefore abandon our ~
            previous work on this conjecture and reassign the name *1 to the ~
            original conjecture.  (See :DOC otf-flg.)~%"
           (list (cons #\0 (tilde-@-clause-id-phrase parent-cl-id))
                 (cons #\1 (tilde-@-clause-id-phrase revert-d-cl-id)))
           (proofs-co state)
           state
           nil))
     (t
      (fms "---~%None of the branches we tried for ~@0 led to a plausible set ~
            of subgoals.  The proof attempt has failed.~|"
           (list (cons #\0 (tilde-@-clause-id-phrase parent-cl-id)))
           (proofs-co state)
           state
           nil))))
   ((endp (cdr results))
    (fms "---~%Even though we saw a disjunctive split for ~@0, it ~
          turns out there is only one viable branch to pursue, the ~
          one named ~@1.~%"
         (list (cons #\0 (tilde-@-clause-id-phrase parent-cl-id))
               (cons #\1 (tilde-@-clause-id-phrase cl-id)))
         (proofs-co state)
         state
         nil))
   (t (let* ((temp (assoc-equal cl-id summary))
             (n (cadr temp))
             (d (caddr temp)))

        (fms "---~%After simplifying every branch of the disjunctive ~
              split for ~@0 we choose to pursue the branch named ~@1, ~
              which gave rise to ~x2 *-named formula~#3~[s~/~/s~] ~
              with total estimated difficulty of ~x4.  The complete ~
              list of branches considered is shown below.~%~%~
              clause id              subgoals    estimated~%~
              ~                        pushed     difficulty~%~*5"
             (list (cons #\0 (tilde-@-clause-id-phrase parent-cl-id))
                   (cons #\1 (tilde-@-clause-id-phrase cl-id))
                   (cons #\2 n)
                   (cons #\3 (zero-one-or-more n))
                   (cons #\4 d)
                   (cons #\5 (tilde-*-or-hit-summary-phrase summary)))
             (proofs-co state)
             state
             nil)))))

; Next we define a notion of the difficulty of a term and then grow it
; to define the difficulty of a clause and of a clause set.  The
; difficulty of a term is (almost) the sum of all the level numbers of
; the functions in the term, plus the number of function applications.
; That is, suppose f and g have level-nos of i and j.  Then the
; difficulty of (f (g x)) is i+j+2.  However, the difficulty of (NOT
; (g x)) is just i+1 because we pretend the NOT (and its function
; application) is invisible.

(mutual-recursion

(defun term-difficulty1 (term wrld n)
  (cond ((variablep term) n)
        ((fquotep term) n)
        ((flambda-applicationp term)
         (term-difficulty1-lst (fargs term) wrld
                               (term-difficulty1 (lambda-body term)
                                                 wrld (1+ n))))
        ((eq (ffn-symb term) 'not)
         (term-difficulty1 (fargn term 1) wrld n))
        (t (term-difficulty1-lst (fargs term) wrld
                                 (+ 1
                                    (get-level-no (ffn-symb term) wrld)
                                    n)))))

(defun term-difficulty1-lst (lst wrld n)
  (cond ((null lst) n)
        (t (term-difficulty1-lst (cdr lst) wrld
                                 (term-difficulty1 (car lst) wrld n)))))
)

(defun term-difficulty (term wrld)
  (term-difficulty1 term wrld 0))

; The difficulty of a clause is the sum of the complexities of the
; literals.  Note that we cannot have literals of difficulty 0 (except
; for something trivial like (NOT P)), so this measure will assign
; lower difficulty to shorter clauses, all other things being equal.

(defun clause-difficulty (cl wrld)
  (term-difficulty1-lst cl wrld 0))

; The difficulty of a clause set is similar.

(defun clause-set-difficulty (cl-set wrld)
  (cond ((null cl-set) 0)
        (t (+ (clause-difficulty (car cl-set) wrld)
              (clause-set-difficulty (cdr cl-set) wrld)))))

; The difficulty of a pspv is the sum of the difficulties of the
; TO-BE-PROVED-BY-INDUCTION clause-sets in the pool of the pspv down
; (and not counting) the element element0.

(defun pool-difficulty (element0 pool wrld)
  (cond ((endp pool) 0)
        ((equal (car pool) element0) 0)
        ((not (eq (access pool-element (car pool) :tag)
                  'TO-BE-PROVED-BY-INDUCTION))
         0)
        (t (+ (clause-set-difficulty
               (access pool-element (car pool) :clause-set)
               wrld)
              (pool-difficulty element0 (cdr pool) wrld)))))

(defun how-many-to-be-proved (element0 pool)

; We count the number of elements tagged TO-BE-PROVED-BY-INDUCTION in
; pool until we get to element0.

  (cond ((endp pool) 0)
        ((equal (car pool) element0) 0)
        ((not (eq (access pool-element (car pool) :tag)
                  'TO-BE-PROVED-BY-INDUCTION))
         0)
        (t (+ 1 (how-many-to-be-proved element0 (cdr pool))))))

(defun pick-best-pspv-for-waterfall0-or-hit1
  (results element0 wrld ans ans-difficulty summary)

; Results is a non-empty list of elements, each of which is of the
; form (cl-id . pspv) where pspv is a pspv corresponding to the
; complete waterfall processing of a single disjunct (of conjuncts).
; Inside the :pool of the pspv are a bunch of
; TO-BE-PROVED-BY-INDUCTION pool-elements.  We have to decide which of
; the pspv's is the "best" one, i.e., the one to which we will commit
; to pursue by inductions.  We choose the one that has the least
; difficulty.  We measure the difficulty of the pool-elements until we
; get to element0.

; Ans is the least difficult result so far, or nil if we have not seen
; any yet.  Ans-difficulty is the difficulty of ans (or nil).  Note
; that ans is of the form (cl-id . pspv).

; We accumulate into summary some information that is used to report
; what we find.  For each element of results we collect (cl-id n d),
; where n is the number of subgoals pushed by the cl-id processing and
; d is their combined difficulty.  We return (mv choice summary),
; where choice is the final ans (cl-id . pspv).

  (cond
   ((endp results)
    (mv ans summary))
   (t (let* ((cl-id (car (car results)))
             (pspv (cdr (car results)))
             (new-difficulty (pool-difficulty
                              element0
                              (access prove-spec-var pspv :pool)
                              wrld))
             (new-summary (cons (list cl-id
                                      (how-many-to-be-proved
                                       element0
                                       (access prove-spec-var pspv :pool))
                                      new-difficulty)
                                summary)))
        (if (or (null ans)
                (< new-difficulty ans-difficulty))
            (pick-best-pspv-for-waterfall0-or-hit1 (cdr results)
                                                   element0
                                                   wrld
                                                   (car results)
                                                   new-difficulty
                                                   new-summary)
          (pick-best-pspv-for-waterfall0-or-hit1 (cdr results)
                                                 element0
                                                 wrld
                                                 ans
                                                 ans-difficulty
                                                 new-summary))))))

(defun pick-best-pspv-for-waterfall0-or-hit (results pspv0 wrld)

; Results is a non-empty list of elements, each of which is of the
; form (cl-id . pspv) where pspv is a pspv corresponding to the
; complete waterfall processing of a single disjunct (of conjuncts).
; Inside the :pool of the pspv are a bunch of
; TO-BE-PROVED-BY-INDUCTION pool-elements.  We have to decide which of
; the pspv's is the "best" one, i.e., the one to which we will commit
; to pursue by inductions.  We choose the one that has the least
; difficulty.

; We return (mv (cl-id . pspv) summary) where cl-id and pspv are the
; clause id and pspv of the least difficult result in results and
; summary is a list that summarizes all the results, namely a list of
; the form (cl-id n difficulty), where cl-id is the clause id of a
; disjunct, n is the number of subgoals the processing of that
; disjunct pushed into the pool, and difficulty is the difficulty of
; those subgoals.

  (pick-best-pspv-for-waterfall0-or-hit1
   results

; We pass in the first element of the original pool as element0.  This
; may be a BEING-PROVED-BY-INDUCTION element but is typically a
; TO-BE-PROVED-BY-INDUCTION element.  In any case, we don't consider
; it or anything after it as we compute the difficulty.

   (car (access prove-spec-var pspv0 :pool))
   wrld
   nil   ; ans - none yet
   nil   ; ans-difficulty - none yet
   nil   ; summary
   ))

(defun change-or-hit-history-entry (i hist cl-id)

; The first entry in hist is a history-entry of the form

; (make history-entry
;       :signal 'OR-HIT
;       :processor 'APPLY-TOP-HINTS-CLAUSE
;       :clause clause
;       :ttree ttree)

; where ttree contains an :OR tag with the value, val,

; (parent-cl-id NIL ((user-hint1 . hint-settings1) ...))

; We smash the NIL to i.  This indicates that along this branch of the
; history, we are dealing with user-hinti.  Note that numbering starts
; at 1.

; While apply-top-hints-clause generates a ttree with a :or tagged
; object containing a nil, this function is used to replace that nil
; in the history of every branch by the particular i generating the
; branch.

; In the histories maintained by uninterrupted runs, you should never
; see an :OR tag with a nil in that slot.  (Note carefully the use of
; the word "HISTORIES" above!  It is possible to see ttrees with :OR
; tagged objects containing nil instead of a branch number.  They get
; collected into the ttree inside the pspv that is following a clause
; around.  But it is silly to inspect that ttree to find out the
; history of the clause, since you need the history for that.)

; The basic rule is that in a history recovered from an uninterrupted
; proof attempt the entries with :signal OR-HIT will have a ttree with
; a tag :OR on an object (parent-cl-id i uhs-lst).

  (let* ((val (tagged-object :or
                             (access history-entry (car hist) :ttree)))
         (parent-cl-id (nth 0 val))
         (uhs-lst (nth 2 val)))
    (cons (make history-entry
                :signal 'OR-HIT
                :processor 'apply-top-hints-clause
                :clause (access history-entry (car hist) :clause)
                :ttree (add-to-tag-tree! :or
                                         (list parent-cl-id
                                               i
                                               uhs-lst)
                                         nil)
                :cl-id ; only needed for #+acl2-par, but harmless
                cl-id)
          (cdr hist))))

(defun@par pair-cl-id-with-hint-setting (cl-id hint-settings)

; Background: An :OR hint takes a list of n translated hint settings,
; at a clause with a clause id.  It essentially copies the clause n
; times, gives it a new clause id (with a "Dk" suffix), and arranges
; for the waterfall to apply each hint settings to one such copy of
; the clause.  The way it arranges that is to change the hints in the
; pspv so that the newly generated "Dk" clause ids are paired with
; their respective hints.  But computed hints are different!  A
; computed hint isn't paired with a clause id.  It has it built into
; the form somewhere.  Now generally the user created the form and we
; assume the user saw the subgoal with the "Dk" id of interest and
; entered it into his form.  But we generate some computed hint forms
; -- namely custom keyword hints.  And we're responsible for tracking
; the new clause ids to which they apply.

; Hint-settings is a translated hint-settings.  That is, it is either
; a dotted alist pairing common hint keywords to their translated
; values or it is a computed hint form starting with
; eval-and-translate-hint-expression.  In the former case, we produce
; (cl-id . hint-settings).  In the latter case, we look for the
; possibility that the term we are to eval is a call of the
; custom-keyword-hint-interpreter and if so smash its cl-id field.

  (cond
   ((eq (car hint-settings) 'eval-and-translate-hint-expression)
    (cond
     ((custom-keyword-hint-in-computed-hint-form hint-settings)
      (put-cl-id-of-custom-keyword-hint-in-computed-hint-form@par
       hint-settings cl-id))
     (t hint-settings)))
   (t (cons cl-id hint-settings))))

(defun apply-reorder-hint-front (indices len clauses acc)
  (cond ((endp indices) acc)
        (t (apply-reorder-hint-front
            (cdr indices) len clauses
            (cons (nth (- len (car indices)) clauses)
                  acc)))))

(defun apply-reorder-hint-back (indices current-index clauses acc)
  (cond ((endp clauses) acc)
        (t (apply-reorder-hint-back indices (1- current-index) (cdr clauses)
                                    (if (member current-index indices)
                                        acc
                                      (cons (car clauses) acc))))))

(defun filter-> (lst max)
  (cond ((endp lst) nil)
        ((> (car lst) max)
         (cons (car lst)
               (filter-> (cdr lst) max)))
        (t (filter-> (cdr lst) max))))

(defun@par apply-reorder-hint (pspv clauses ctx state)
  (let* ((hint-settings (access prove-spec-var pspv :hint-settings))
         (hint-setting (assoc-eq :reorder hint-settings))
         (indices (cdr hint-setting))
         (len (length clauses)))
    (cond (indices
           (cond
            ((filter-> indices len)
             (mv-let@par (erp val state)
                         (er@par soft ctx
                           "The following subgoal indices given by a :reorder ~
                            hint exceed the number of subgoals, which is ~x0: ~
                            ~ ~&1."
                           len (filter-> indices len))
                         (declare (ignore val))
                         (mv@par erp nil nil state)))
            (t
             (mv@par nil
                     hint-setting
                     (reverse (apply-reorder-hint-back
                               indices len clauses
                               (apply-reorder-hint-front indices len clauses
                                                         nil)))
                     state))))
          (t (mv@par nil nil clauses state)))))

; This completes the preliminaries for hints and we can get on with the
; waterfall itself soon.  But first we provide additional rw-cache support (see
; the Essay on Rw-cache).

#+acl2-par
(defun pspv-equal-except-for-tag-tree-and-pool (x y)

; Warning: Keep this in sync with prove-spec-var.  The only fields not
; addressed here should be the :tag-tree and :pool fields.

  (and (equal (access prove-spec-var x :rewrite-constant)
              (access prove-spec-var y :rewrite-constant))
       (equal (access prove-spec-var x :induction-hyp-terms)
              (access prove-spec-var y :induction-hyp-terms))
       (equal (access prove-spec-var x :induction-concl-terms)
              (access prove-spec-var y :induction-concl-terms))
       (equal (access prove-spec-var x :hint-settings)
              (access prove-spec-var y :hint-settings))
       (equal (access prove-spec-var x :gag-state)
              (access prove-spec-var y :gag-state))
       (equal (access prove-spec-var x :user-supplied-term)
              (access prove-spec-var y :user-supplied-term))
       (equal (access prove-spec-var x :displayed-goal)
              (access prove-spec-var y :displayed-goal))
       (equal (access prove-spec-var x :orig-hints)
              (access prove-spec-var y :orig-hints))
       (equal (access prove-spec-var x :otf-flg)
              (access prove-spec-var y :otf-flg))

; One can uncomment the following equal test to witness that the comparison is
; indeed actually occurring and causing a hard error upon failure.
;       (equal (access prove-spec-var x :tag-tree)
;              (access prove-spec-var y :tag-tree))

       ))

#+acl2-par
(defun list-extensionp-aux (rev-base rev-extension)
  (assert$
   (<= (length rev-base) (length rev-extension))
   (if (atom rev-base)
       t
     (and (equal (car rev-base)
                 (car rev-extension))
          (list-extensionp-aux (cdr rev-base)
                               (cdr rev-extension))))))

#+acl2-par
(defun list-extensionp (base extension)

  (cond ((> (length base) (length extension))
         nil)
        (t
         (list-extensionp-aux (reverse base)
                              (reverse extension)))))

#+acl2-par
(defun find-list-extensions (base extension acc)
  (if (or (endp extension)
          (equal extension base))
      (reverse acc)
    (find-list-extensions base (cdr extension) (cons (car extension) acc))))

#+acl2-par
(defun combine-pspv-pools (base x y debug-pspv)
  (prog2$
   (if debug-pspv
       (with-output-lock
        (cw "Combining base: ~x0 with x: ~%~x1 and with y: ~%~x2~%" base x y))
     nil)
   (append (find-list-extensions base y nil)
           (find-list-extensions base x nil)
           base)))

#+acl2-par
(defun combine-pspv-tag-trees (x y)

; We reverse the arguments, because y was generated after x in time (in the
; serial case).  And since accumulating into a tag-tree is akin to pushing onto
; the front of a list, y is the first argument to the "cons".

  (cons-tag-trees-rw-cache y x))

#+acl2-par
(defun print-pspvs (base x y debug-pspv)
  (if debug-pspv
      (progn$
       (cw "Base is:~% ~x0~%" base)
       (cw "X is:~% ~x0~%" X)
       (cw "Y is:~% ~x0~%" Y))
    nil))

#+acl2-par
(defun combine-prove-spec-vars (base x y ctx debug-pspv signal1 signal2)

; X and Y should be extensions of the base.  That is, every member of base
; should be in both x and y.  Also, note that switching the order of x and y
; returns a result that means something different.  The order with which we
; combine pspv's matters.

  (assert$

; We check that the signals aren't abort.  This way we know that we are in case
; (1), as described in "Essay on prove-spec-var pool modifications".  We also
; know that this assertion is always true from just examining the code.

   (and (not (equal signal1 'abort))
        (not (equal signal2 'abort)))
   (cond

; We first test to make sure that the pspv's were only changed in the two
; fields that we know how to combine.

    ((not (pspv-equal-except-for-tag-tree-and-pool x y))
     (prog2$
      (print-pspvs base x y debug-pspv)
      (er hard ctx
          "Implementation error: waterfall1 returns the pspv changed in a way ~
           other than the :tag-tree and :pool fields.")))
    (t
     (change prove-spec-var x
             :tag-tree
             (combine-pspv-tag-trees
              (access prove-spec-var x :tag-tree)
              (access prove-spec-var y :tag-tree))
             :pool
             (combine-pspv-pools
              (access prove-spec-var base :pool)
              (access prove-spec-var x :pool)
              (access prove-spec-var y :pool)
              debug-pspv))))))

; The following form may be helpful for tracing waterfall1-lst in an effort to
; understand how the pspv's :pool is modified.

; (trace$
;  (waterfall1-lst
;   :entry (list 'waterfall1-lst
;                'clauses=
;                clauses
;                'pspv-pool=
;                (access prove-spec-var pspv :pool))
;   :exit (list 'waterfall1-lst
;               'signal=
;               (cadr values)
;               'pspv-pool=
;               (access prove-spec-var (caddr values) :pool))))

#+acl2-par
(defun speculative-execution-valid (x y)

; This function aids in determining whether a speculative evaluation of the
; waterfall is valid.  Typically, X is the pspv given to the current call of
; waterfall1-lst, and Y is the pspv returned from calling waterfall1 on the
; first clause.

; For now, if anything but the tag-tree or pool is different, we want to
; immediately return nil, because we don't know how to handle the combining of
; such pspv's.

  (assert$ (pspv-equal-except-for-tag-tree-and-pool x y)
           t))

#+acl2-par
(defun abort-will-occur-in-pool (pool)

; Returns t if the given pool requires that we abort the current set of subgoal
; proof attempts and revert to prove the original conjecture by induction.  The
; function must only consider the case where 'maybe-to-be-proved-by-induction
; tags are present, because push-clause[@par] handles all other cases.

; If you change this function, evaluate the following form.  If the result is
; an error, then either modify the form below or fix the change.

; (assert$
;  (and
;   (not (abort-will-occur-in-pool '((maybe-to-be-proved-by-induction sub orig))))
;   (abort-will-occur-in-pool '((maybe-to-be-proved-by-induction sub orig)
;                               (to-be-proved-by-induction)
;                               (to-be-proved-by-induction)))
;   (not (abort-will-occur-in-pool '((to-be-proved-by-induction))))
;   (not (abort-will-occur-in-pool '((to-be-proved-by-induction)
;                                    (maybe-to-be-proved-by-induction sub orig))))
;   (not (abort-will-occur-in-pool '((maybe-to-be-proved-by-induction sub orig))))
;   (not (abort-will-occur-in-pool '((to-be-proved-by-induction)
;                                    (to-be-proved-by-induction)
;                                    (to-be-proved-by-induction))))
;   (abort-will-occur-in-pool '((maybe-to-be-proved-by-induction sub orig)
;                               (to-be-proved-by-induction)
;                               (to-be-proved-by-induction)
;                               (maybe-to-be-proved-by-induction sub2 orig2)))
;   (abort-will-occur-in-pool '((to-be-proved-by-induction a)
;                               (maybe-to-be-proved-by-induction sub orig)
;                               (to-be-proved-by-induction b)
;                               (to-be-proved-by-induction c)
;                               (maybe-to-be-proved-by-induction sub2 orig2))))
;  "abort-will-occur-in-pool tests passed")

  (cond ((atom pool)
         nil)
        ((and (equal (caar pool) 'maybe-to-be-proved-by-induction)
              (consp (cdr pool)))
         t)
        (t (abort-will-occur-in-pool (cdr pool)))))

#+acl2-par
(defrec maybe-to-be-proved-by-induction

; Important Note: This record is laid out this way so that we can use assoc-eq
; on the pspv pool to detect the presence of a maybe-to-be-proved-by-induction
; tag.  Do not move the key field!

  (key subgoal original)
  t)

#+acl2-par
(defun convert-maybes-to-tobe-subgoals (pool)

; This function converts all 'maybe-to-be-proved-by-induction records to
; 'to-be-proved-by-induction pool-elements.  Since this function is only called
; in the non-abort case, it uses the :subgoal field of the record.

  (cond ((atom pool)
         nil)
        ((equal (caar pool) 'maybe-to-be-proved-by-induction)
         (cons (access maybe-to-be-proved-by-induction (car pool) :subgoal)
               (convert-maybes-to-tobe-subgoals (cdr pool))))
        (t (cons (car pool)
                 (convert-maybes-to-tobe-subgoals (cdr pool))))))

#+acl2-par
(defun convert-maybes-to-tobes (pool)

; This function converts a pool that contains 'maybe-to-be-proved-by-induction
; records to a pool that either (1) aborts and proves the :original conjecture
; or (2) replaces all such clauses with their :subgoal
; 'to-be-proved-by-induction pool-element.  This function outsources all
; thinking about whether we are in an abort case to the function
; abort-will-occur-in-pool.

; If you change this function, evaluate the following form.  If the result is
; an error, then either modify the form below or fix the change.

; (assert$
;  (and
;   (equal (convert-maybes-to-tobes '((maybe-to-be-proved-by-induction sub orig)))
;          '(sub))
;   (equal
;    (convert-maybes-to-tobes '((maybe-to-be-proved-by-induction sub orig)
;                               (to-be-proved-by-induction)
;                               (to-be-proved-by-induction)))
;    '(orig))
;   (equal
;    (convert-maybes-to-tobes '((to-be-proved-by-induction)))
;    '((to-be-proved-by-induction)))
;   (equal (convert-maybes-to-tobes '((to-be-proved-by-induction)
;                                     (maybe-to-be-proved-by-induction sub orig)))
;          '((to-be-proved-by-induction)
;            sub))
;   (equal (convert-maybes-to-tobes '((maybe-to-be-proved-by-induction sub orig)))
;          '(sub))
;   (equal (convert-maybes-to-tobes '((maybe-to-be-proved-by-induction sub orig)
;                                     (to-be-proved-by-induction)
;                                     (to-be-proved-by-induction)
;                                     (maybe-to-be-proved-by-induction sub2 orig2)))
;          '(orig))
;   (equal (convert-maybes-to-tobes '((to-be-proved-by-induction a)
;                                     (maybe-to-be-proved-by-induction sub orig)
;                                     (to-be-proved-by-induction b)
;                                     (to-be-proved-by-induction c)
;                                     (maybe-to-be-proved-by-induction sub2
;                                                                      orig2)))
;          '(orig))
;   (equal (convert-maybes-to-tobes
;           '((maybe-to-be-proved-by-induction sub1 orig)
;             (to-be-proved-by-induction a)
;             (maybe-to-be-proved-by-induction sub2 orig)
;             (to-be-proved-by-induction b)
;             (to-be-proved-by-induction c)
;             (maybe-to-be-proved-by-induction sub3 orig)))
;          '(orig))
;  )
;  "convert-maybes-to-tobes tests worked."
; )

  (cond ((atom pool)
         nil)
        ((abort-will-occur-in-pool pool)
         (list (access maybe-to-be-proved-by-induction

; It doesn't matter whether we use the first 'maybe-to-be-proved-by-induction
; tag to cause an abort, because the :original field will be the same for all
; of them.

                       (assoc-eq 'maybe-to-be-proved-by-induction pool)
                       :original)))
        (t (convert-maybes-to-tobe-subgoals pool))))

#+acl2-par
(defun convert-maybes-to-tobes-in-pspv (pspv)
  (change prove-spec-var pspv
          :pool
          (convert-maybes-to-tobes (access prove-spec-var pspv :pool))))

; This completes the preliminaries for hints and we can get on with the
; waterfall itself soon.  But first we provide additional rw-cache support (see
; the Essay on Rw-cache).

(defun erase-rw-cache-any-tag-from-pspv (pspv)

; We maintain the invariant that the "nil" cache is contained in the "any"
; cache.

  (let ((ttree (access prove-spec-var pspv :tag-tree)))
    (cond ((tagged-objectsp 'rw-cache-any-tag ttree)
           (change prove-spec-var pspv
                   :tag-tree (rw-cache-enter-context ttree)))
          (t pspv))))

(defun restore-rw-cache-state-in-pspv (new-pspv old-pspv)
  (let* ((old-rcnst (access prove-spec-var old-pspv :rewrite-constant))
         (old-rw-cache-state (access rewrite-constant old-rcnst
                                     :rw-cache-state))
         (new-rcnst (access prove-spec-var new-pspv :rewrite-constant))
         (new-rw-cache-state (access rewrite-constant new-rcnst
                                     :rw-cache-state)))
    (cond ((eq old-rw-cache-state new-rw-cache-state) new-pspv)
          (t (change prove-spec-var new-pspv
                     :rewrite-constant
                     (change rewrite-constant new-rcnst
                             :rw-cache-state old-rw-cache-state))))))

#+(and acl2-par (not acl2-loop-only))
(defvar *waterfall-parallelism-timings-ht-alist* nil
  "Association list of hashtables, where the key is the name of a theorem
   attempted with a defthm, and the value is a hashtable mapping from
   clause-ids to the time it took to prove that clause.")

#+(and acl2-par (not acl2-loop-only))
(defvar *waterfall-parallelism-timings-ht* nil
  "This variable supports the :resource-and-timing-based mode for waterfall
   parallelism.  It can contain the hashtable that associates
   waterfall-parallelism timings with each clause-id.  This variable should
   always be nil unless ACL2(p) is in the middle of attempting a proof
   initiated by the user with a defthm.")

#+acl2-par
(defun setup-waterfall-parallelism-ht-for-name (name)
  #-acl2-loop-only
  (let ((curr-ht (assoc-eq name *waterfall-parallelism-timings-ht-alist*)))
    (cond ((null curr-ht)
           (let ((new-ht (make-hash-table :test 'equal :size (expt 2 13)

; Parallelism blemish: CCL locks these hashtable operations automatically
; because of the argument :shared t below.  However in SBCL and LispWorks, we
; should really lock these hashtable operations ourselves.  Note that the SBCL
; documentation at http://www.sbcl.org/manual/Hash-Table-Extensions.html
; describes a keyword, :synchronized, that is like CCL's :shared but is labeled
; as "experimental".  At any rate, we are willing to take our chances for now
; with SBCL and Lispworks.

                                          #+ccl :shared #+ccl t)))
             (setf *waterfall-parallelism-timings-ht-alist*
                   (acons name
                          new-ht
                          (take 4 *waterfall-parallelism-timings-ht-alist*)))
             (setf *waterfall-parallelism-timings-ht* new-ht)))
          (t (setf *waterfall-parallelism-timings-ht* (cdr curr-ht)))))
  name)

#+acl2-par
(defun clear-current-waterfall-parallelism-ht ()
  #-acl2-loop-only
  (setf *waterfall-parallelism-timings-ht* nil)
  t)

#+acl2-par
(defun flush-waterfall-parallelism-hashtables ()
  #-acl2-loop-only
  (progn
    (setf *waterfall-parallelism-timings-ht-alist* nil)
    (setf *waterfall-parallelism-timings-ht* nil))
  t)

#+(and acl2-par (not acl2-loop-only))
(defun save-waterfall-timings-for-cl-id (key value)
  (when *waterfall-parallelism-timings-ht*
    (setf (gethash key *waterfall-parallelism-timings-ht*)
          value))
  value)

#+(and acl2-par (not acl2-loop-only))
(defun lookup-waterfall-timings-for-cl-id (key)
  (mv-let (val found)
          (cond (*waterfall-parallelism-timings-ht*
                 (gethash key *waterfall-parallelism-timings-ht*))
                (t (mv nil nil)))
          (declare (ignore found))
          (or val 0)))

(defmacro waterfall1-wrapper (form)

; We create a non-@par version of waterfall1-wrapper that is the identity, so
; we can later have an @par version that does something important for the
; parallel case.  In the #-acl2-par case, or the serial case,
; waterfall1-wrapper will have no effect, returning its argument unchanged.
; For a discussion about such matters, see the long comment in *@par-mappings*.

  form)

#+(and acl2-par (not acl2-loop-only))
(defparameter *acl2p-starting-proof-time* 0.0d0)

#+acl2-par
(defun waterfall1-wrapper@par-before (cl-id state)
  (case (f-get-global 'waterfall-printing state)
    (:limited
     (and (print-clause-id-okp cl-id)
          (with-output-lock

; Parallelism blemish: Kaufmann suggests that we need to skip printing
; clause-ids that have already been printed.  Note that using the printing of
; clause-ids to show that the prover is still making progress is no longer the
; default setting (see :doc set-waterfall-printing).  This is a low-priority
; blemish, because as of 2012-07, the main ACL2 users use the :very-limited
; setting for waterfall-printing -- this setting only prints periods, not
; clause-ids.  Example:

;   (set-waterfall-parallelism :pseudo-parallel)
;   (set-waterfall-printing :limited)
;   (thm (implies (equal x y) (equal u v)))

; Parallelism blemish: here, and at many other ACL2(p)-specific places, consider
; using observation-cw or printing that can be inhibited, instead of cw.  We
; have not tried this so far because observation-cw calls wormhole, which is
; problematic (see the comment in waterfall-print-clause-id@par).

           #+acl2-loop-only
           nil
           #-acl2-loop-only
           (format t "At time ~,6f sec, starting: ~a~%"
                   (/ (- (get-internal-real-time)
                         *acl2p-starting-proof-time*)
                      internal-time-units-per-second)
                   (string-for-tilde-@-clause-id-phrase cl-id)))))
    (:very-limited
     (with-output-lock
      (cw ".")))
    (otherwise nil)))

#+acl2-par
(defun waterfall1-wrapper@par-after (cl-id start-time state)
  #+acl2-loop-only
  (declare (ignore start-time cl-id))
  #-acl2-loop-only
  (save-waterfall-timings-for-cl-id
   cl-id
   (- (get-internal-real-time) ; end time
      start-time))
  (cond ((f-get-global 'waterfall-printing-when-finished state)
         (cond ((equal (f-get-global 'waterfall-printing state) :very-limited)
                (with-output-lock (cw ",")))
               ((equal (f-get-global 'waterfall-printing state) :limited)
                (with-output-lock
                 #+acl2-loop-only
                 nil
                 #-acl2-loop-only
                 (format t "At time ~,6f sec, finished: ~a~%"
                         (/ (- (get-internal-real-time)
                               *acl2p-starting-proof-time*)
                            internal-time-units-per-second)
                         (string-for-tilde-@-clause-id-phrase cl-id))))
               (t nil)))
         (t nil)))

#+acl2-par
(defmacro waterfall1-wrapper@par (&rest form)
  `(let ((start-time
          #+acl2-loop-only 'ignored-value
          #-acl2-loop-only (get-internal-real-time)))
     (prog2$
      (waterfall1-wrapper@par-before cl-id state)
      (mv-let@par
       (step-limit signal pspv jppl-flg state)
       ,@form
       (prog2$ (waterfall1-wrapper@par-after cl-id start-time state)
               (mv@par step-limit signal pspv jppl-flg state))))))

#+acl2-par
(defun increment-waterfall-parallelism-counter (abbreviated-symbol)
  (case abbreviated-symbol
    ((resource-and-timing-parallel)
     #-acl2-loop-only
     (incf *resource-and-timing-based-parallelizations*)
     'parallel)
    ((resource-and-timing-serial)
     #-acl2-loop-only
     (incf *resource-and-timing-based-serializations*)
     'serial)
    ((resource-parallel)
     #-acl2-loop-only
     (incf *resource-based-parallelizations*)
     'parallel)
    ((resource-serial)
     #-acl2-loop-only
     (incf *resource-based-serializations*)
     'serial)
    (otherwise
     (er hard 'increment-waterfall-parallelism-counter
         "Illegal value ~x0 was given to ~
          increment-waterfall-parallelism-counter"
         abbreviated-symbol))))

#+acl2-par
(defun halves-with-length (clauses)

; Returns (mv first-half second-half len), where clauses is split into the
; indicated halves (maintaining the order of the input list), and len is the
; length of the first half.

  (declare (xargs :guard (true-listp clauses)))
  (let* ((len (length clauses))
         (split-point (ceiling (/ len 2) 1))
         (first-half (take split-point clauses))
         (second-half (nthcdr split-point clauses)))
    (mv first-half second-half split-point)))

(mutual-recursion@par

(defun@par waterfall1
  (ledge cl-id clause hist pspv hints suppress-print ens wrld ctx state
         step-limit)

; ledge      - In general in this mutually recursive definition, the
;              formal "ledge" is any one of the waterfall ledges.  But
;              by convention, in this function, waterfall1, it is
;              always either the 'apply-top-hints-clause ledge or
;              the next one, 'preprocess-clause.  Waterfall1 is the
;              place in the waterfall that hints are applied.
;              Waterfall0 is the straightforward encoding of the
;              waterfall, except that every time it sends clauses back
;              to the top, it send them to waterfall1 so that hints get
;              used again.

; cl-id      - the clause id for clause.
; clause     - the clause to process
; hist       - the history of clause
; pspv       - an assortment of special vars that any clause processor might
;              change
; hints      - an alist mapping clause-ids to hint-settings.
; wrld       - the current world
; state      - the usual state
; step-limit - the new step-limit.

; We return 5 values.  The first is a new step-limit.  The second is a "signal"
; and is one of 'abort, 'error, or 'continue.  The last three returned values
; are the final values of pspv, the jppl-flg for this trip through the falls,
; and state.  The 'abort signal is used by our recursive processing to
; implement aborts from below.  When an abort occurs, the clause processor that
; caused the abort sets the pspv and state as it wishes the top to see them.
; When the signal is 'error, the error message has been printed.  The returned
; pspv is irrelevant (and typically nil).

  (mv-let@par
   (erp pair state)
   (find-applicable-hint-settings@par cl-id clause hist pspv ctx hints
                                      wrld nil state)

; If no error occurs and pair is non-nil, then pair is of the form
; (hint-settings . hints') where hint-settings is the hint-settings
; corresponding to cl-id and clause and hints' is hints with the appropriate
; element removed.

   (cond
    (erp

; This only happens if some hint function caused an error, e.g., by
; generating a hint that would not translate.  The error message has been
; printed and pspv is irrelevant.  We pass the error up.

     (mv@par step-limit 'error nil nil state))
    (t (sl-let@par
        (signal new-pspv jppl-flg state)
        (cond
         ((null pair) ; There was no hint.
          (pprogn@par

; In the #+acl2-par version of the waterfall, with global waterfall-printing
; set to :limited, the need to print the clause on a checkpoint is taken care
; of inside waterfall-msg@par.

           (waterfall-print-clause@par suppress-print cl-id clause
                                       state)
           (waterfall0@par ledge cl-id clause hist pspv hints ens wrld ctx
                           state step-limit)))
         (t (waterfall0-with-hint-settings@par
             (car pair)
             ledge cl-id clause hist pspv (cdr pair) suppress-print ens wrld
             ctx state step-limit)))
        (let ((pspv (cond ((null pair)
                           (restore-rw-cache-state-in-pspv new-pspv pspv))
                          (t new-pspv))))
          (mv-let@par
           (pspv state)
           (cond ((or (eq signal 'miss)
                      (eq signal 'error))
                  (mv@par pspv state))
                 (t (gag-state-exiting-cl-id@par signal cl-id pspv state)))
           (mv@par step-limit signal pspv jppl-flg state))))))))

(defun@par waterfall0-with-hint-settings
  (hint-settings ledge cl-id clause hist pspv hints goal-already-printedp
                 ens wrld ctx state step-limit)

; We ``install'' the hint-settings given and call waterfall0 on the
; rest of the arguments.

  (mv-let@par
   (hint-settings state)
   (thanks-for-the-hint@par goal-already-printedp hint-settings cl-id state)
   (pprogn@par
    (waterfall-print-clause@par goal-already-printedp cl-id clause state)
    (mv-let@par
     (erp new-pspv-1 state)
     (load-hint-settings-into-pspv@par t hint-settings pspv cl-id wrld ctx
                                       state)
     (cond
      (erp (mv@par step-limit 'error pspv nil state))
      (t
       (pprogn@par
        (maybe-warn-for-use-hint@par new-pspv-1 cl-id ctx wrld state)
        (maybe-warn-about-theory-from-rcnsts@par
         (access prove-spec-var pspv :rewrite-constant)
         (access prove-spec-var new-pspv-1 :rewrite-constant)
         ctx ens wrld state)

; If there is no :INDUCT hint, then the hint-settings can be handled by
; modifying the clause and the pspv we use subsequently in the falls.

        (sl-let@par (signal new-pspv new-jppl-flg state)
                    (waterfall0@par (cond ((assoc-eq :induct hint-settings)
                                           '(push-clause))
                                          (t ledge))
                                    cl-id
                                    clause
                                    hist
                                    new-pspv-1
                                    hints ens wrld ctx state step-limit)
                    (mv@par step-limit
                            signal
                            (restore-hint-settings-in-pspv new-pspv pspv)
                            new-jppl-flg state)))))))))

(defun@par waterfall0 (ledge cl-id clause hist pspv hints ens wrld ctx state
                             step-limit)
  (sl-let@par
   (signal clauses new-hist new-pspv new-jppl-flg state)
   (cond
    ((null ledge)

; The only way that the ledge can be nil is if the push-clause at the
; bottom of the waterfall signal led 'MISS.  This only happens if
; push-clause found a :DO-NOT-INDUCT name hint.  That being the case,
; we want to act like a :BY name' hint was attached to that clause,
; where name' is the result of extending the supplied name with the
; clause id.  This fancy call of waterfall-step is just a cheap way to
; get the standard :BY name' processing to happen.  All it will do is
; add a :BYE (name' . clause) to the tag-tree of the new-pspv.  We
; know that the signal returned will be a "hit".  Because we had to smash
; the hint-settings to get this to happen, we'll have to restore them
; in the new-pspv.

     (waterfall-step@par
      'apply-top-hints-clause
      cl-id clause hist
      (change prove-spec-var pspv
              :hint-settings
              (list
               (cons :by
                     (convert-name-tree-to-new-name
                      (cons (cdr (assoc-eq
                                  :do-not-induct
                                  (access prove-spec-var pspv :hint-settings)))
                            (string-for-tilde-@-clause-id-phrase cl-id))
                      wrld))))
      wrld ctx state step-limit))
    ((eq (car ledge) 'eliminate-destructors-clause)
     (mv-let@par (erp pair state)
                 (find-applicable-hint-settings@par ; stable-under-simplificationp=t
                  cl-id clause hist pspv ctx hints wrld t state)
                 (cond
                  (erp

; A hint generated an error.  The error message has been printed and
; we pass the error up.  The other values are all irrelevant.

                   #+acl2-par
                   (assert$

; At one time, the waterfall returned Context Message Pairs.  This assertion
; was subsequently added to check that we no longer do so.  Since it's an
; inexpensive check, we leave it here.

                    (not pair)
                    (mv@par step-limit 'error nil nil nil nil state))
                   #-acl2-par
                   (mv@par step-limit 'error nil nil nil nil state))
                  (pair

; A hint was found.  The car of pair is the new hint-settings and the
; cdr of pair is the new value of hints.  We need to arrange for
; waterfall0-with-hint-settings to be called.  But we are inside
; mv-let binding signal, etc., above.  We generate a fake ``signal''
; to get out of here and handle it below.

                   (mv@par step-limit
                           'top-of-waterfall-hint
                           (car pair) hist (cdr pair) nil state))

; Otherwise no hint was applicable.  We do exactly the same thing we would have
; done had (car ledge) not been 'eliminate-destructors-clause, after checking
; whether we should make a desperate final attempt to simplify, with caching
; turned off.  Keep these two calls of waterfall-step in sync!

                  ((eq (access rewrite-constant
                               (access prove-spec-var pspv
                                       :rewrite-constant)
                               :rw-cache-state)
                       t)

; We return an updated pspv, together with a bogus signal indicating that we
; are to make a "desperation" run through the simplifier with the rw-cache
; disabled.  The nil values returned below will be ignored.

                   (mv@par step-limit
                           'top-of-waterfall-avoid-rw-cache
                           nil nil
                           (set-rw-cache-state-in-pspv
                            (erase-rw-cache-from-pspv pspv)
                            :disabled)
                           nil state))
                  ((member-eq (car ledge)
                              (assoc-eq :do-not
                                        (access prove-spec-var pspv
                                                :hint-settings)))
                   (mv@par step-limit 'miss nil hist pspv nil state))
                  (t (waterfall-step@par (car ledge) cl-id clause hist pspv
                                         wrld ctx state step-limit)))))
    ((member-eq (car ledge)
                (assoc-eq :do-not (access prove-spec-var pspv :hint-settings)))
     (mv@par step-limit 'miss nil hist pspv nil state))
    (t (waterfall-step@par (car ledge) cl-id clause hist pspv wrld ctx state
                           step-limit)))
   (cond
    ((eq signal 'OR-HIT)

; A disjunctive, hint-driven split has been requested by an :OR hint.
; Clauses is a singleton containing the clause to which we are to
; apply all of the hints.  The hints themselves are recorded in the
; first entry of the new-hist, which necessarily has the form

; (make history-entry
;       :signal 'OR-HIT
;       :processor 'APPLY-TOP-HINTS-CLAUSE
;       :clause clause
;       :ttree ttree)

; where ttree contains an :OR tag with the value, val,

; (parent-cl-id NIL ((user-hint1 . hint-settings1) ...))

; Note that we are guaranteed here that (nth 1 val) is NIL.  That is
; because that's what apply-top-hints-clause puts into its ttree.
; It will be replaced along every history by the appropriate i.

; We recover this crucial data first.

     (let* ((val (tagged-object :or
                                (access history-entry
                                        (car new-hist)
                                        :ttree)))
;           (parent-cl-id (nth 0 val))        ;;; same as our cl-id!
            (uhs-lst (nth 2 val))
            (branch-cnt (length uhs-lst)))

; Note that user-hinti is what the user wrote and hint-settingsi is
; the corresponding translation.  For each i we are going to act just
; like the user supplied the given hint for the parent.  Thus the
; waterfall will act like it saw parent n times, once for each
; user-hinti.

; For example, if the original :or hint was

; ("Subgoal 3" :OR ((:use lemma1 :in-theory (disable lemma1))
;                   (:use lemma2 :in-theory (disable lemma2))))
;
; then we will act just as though we saw "Subgoal 3" twice,
; once with the hint
; ("Subgoal 3" :use lemma1 :in-theory (disable lemma1))
; and then again with the hint
; ("Subgoal 3" :use lemma2 :in-theory (disable lemma2)).
; except that we give the two occurrences of "Subgoal 3" different
; names for sanity.

       (waterfall0-or-hit@par
        ledge cl-id
        (assert$ (and (consp clauses) (null (cdr clauses)))
                 (car clauses))
        new-hist new-pspv hints ens wrld ctx state
        uhs-lst 1 branch-cnt nil nil step-limit)))
    (t
     (let ((new-pspv
            (if (and (null ledge)
                     (not (eq signal 'error)))

; If signal is 'error, then new-pspv is nil (e.g., see the error
; behavior of waterfall step) and we wish to avoid manipulating a
; bogus pspv.

                (restore-hint-settings-in-pspv new-pspv pspv)
              new-pspv)))
       (cond
        ((eq signal 'top-of-waterfall-hint)

; This fake signal just means that either we have found an applicable hint for
; a clause that was stable under simplification (stable-under-simplificationp =
; t), or that we have found an applicable :backtrack hint.

         (mv-let
          (hint-settings hints pspv goal-already-printedp)
          (cond ((eq new-pspv :pspv-for-backtrack)

; The variable named clauses is holding the hint-settings.

                 (mv clauses
                     (append new-jppl-flg ; new-hints
                             hints)

; We will act as though we have just discovered the hint-settings and leave it
; up to waterfall0-with-hint-settings to restore the pspv if necessary after
; trying those hint-settings.  Note that the rw-cache is restored (as part of
; the tag-tree, which is part of the rewrite-constant of the pspv).

                     (change prove-spec-var pspv :hint-settings
                             (delete-assoc-eq :backtrack
                                              (access prove-spec-var pspv
                                                      :hint-settings)))
                     (cons :backtrack new-hist) ; see thanks-for-the-hint
                     ))
                (t

; The variables named clauses and new-pspv are holding the hint-settings and
; hints in this case.  We reenter the top of the falls with the new hint
; setting and hints.

                 (mv clauses
                     new-pspv
                     pspv
                     t)))
          (waterfall0-with-hint-settings@par
           hint-settings
           *preprocess-clause-ledge*
           cl-id clause

; Through Version_6.4, simplify-clause contained an optimization that avoided
; resimplifying the clause if the most recent history entry is for
; settled-down-clause and (approximately) the induction hyp and concl terms
; don't occur in it.  Here, we short-circuited that short-circuited by removing
; the settled-down-clause entry if it is the most recent.  We no longer have
; that reason for removing the settled-down-clause entry, but it still seems
; reasonable to do so, i.e., to consider the clause not to have settled down
; when popping back to the top of the waterfall because of a hint.  Moreover,
; we tried removing this modification to hist and found several regression
; failures.

           (cond ((and (consp hist)
                       (eq (access history-entry (car hist) :processor)
                           'settled-down-clause))
                  (cdr hist))
                 (t hist))
           pspv hints goal-already-printedp ens wrld ctx state step-limit)))
        ((eq signal 'top-of-waterfall-avoid-rw-cache)

; New-pspv already has the rw-cache disabled.  Pop up to simplify-clause.  The
; next waterfall-step, which will be a simplify-clause step unless a :do-not
; hint prohibits that, will re-enable the rw-cache.

         (waterfall0@par *simplify-clause-ledge*
                         cl-id clause hist new-pspv hints ens wrld ctx state
                         step-limit))
        ((eq signal 'error)
         (mv@par step-limit 'error nil nil state))
        ((eq signal 'abort)
         (mv@par step-limit 'abort new-pspv new-jppl-flg state))
        ((eq signal 'miss)
         (if ledge
             (waterfall0@par (cdr ledge)
                             cl-id
                             clause
                             new-hist ; used because of specious entries
                             new-pspv
                             hints
                             ens
                             wrld
                             ctx
                             state
                             step-limit)
           (mv@par step-limit
                   (er hard 'waterfall0
                       "The empty ledge signaled 'MISS!  This can only ~
                        happen if we changed APPLY-TOP-HINTS-CLAUSE so that ~
                        when given a single :BY name hint it fails to hit.")
                   nil nil state)))
        (t

; Signal is one of the flavors of 'hit, 'hit-rewrite, or 'hit-rewrite2.

         (mv-let@par
          (erp hint-setting clauses state)
          (apply-reorder-hint@par pspv clauses ctx state)
          (cond
           (erp
            (mv@par step-limit 'error nil nil state))
           (t
            (let ((new-pspv
                   (if (cddr clauses)

; We erase the "any" cache if there are at least two children, much as we erase
; it (more accurately, replace it by the smaller "nil" cache) when diving into
; a branch of an IF term.  Actually, we needn't erase the "any" cache if the
; rw-cache is inactive.  But rather than consider carefully when the cache
; becomes active and inactive due to hints, we simply go ahead and do the cheap
; erase operation here.

                       (erase-rw-cache-any-tag-from-pspv new-pspv)
                     new-pspv)))
              (waterfall1-lst@par
               (cond ((eq (car ledge) 'settled-down-clause)
                      'settled-down-clause)
                     ((null clauses) 0)
                     ((null (cdr clauses)) nil)
                     (t (length clauses)))
               cl-id
               clauses
               new-hist
               (if hint-setting
                   (change
                    prove-spec-var new-pspv
                    :hint-settings
                    (remove1-equal hint-setting
                                   (access prove-spec-var
                                           new-pspv
                                           :hint-settings)))
                 new-pspv)
               new-jppl-flg
               hints
               (eq (car ledge) 'settled-down-clause)
               ens
               wrld
               ctx
               state
               step-limit))))))))))))

(defun@par waterfall0-or-hit (ledge cl-id clause hist pspv hints ens wrld ctx
                                    state uhs-lst i branch-cnt revert-info
                                    results step-limit)

; Cl-id is the clause id of clause, of course, and we are to disjunctively
; apply each of the hints in uhs-lst to it.  Uhs-lst is of the form
; (...(user-hinti . hint-settingsi)...) and branch-cnt is the length of that
; list initially, i.e., the maximum value of i.

; We map over uhs-lst and pursue each branch, giving each its own "D" clause id
; and changing the ttree in its history entry to indicate that it is branch i.
; We collect the results as we go into results.  The results are each of the
; form (d-cl-id . new-pspv), where new-pspv is the pspv that results from
; processing the branch.  If the :pool in any one of these new-pspv's is equal
; to that in pspv, then we have succeeded (nothing was pushed) and we stop.
; Otherwise, when we have considered all the hints in uhs-lst, we inspect
; results and choose the best (least difficult looking) one to pursue further.

; Revert-info is nil unless we have seen a disjunctive subgoal that generated a
; signal to abort and revert to the original goal.  In that case, revert-info
; is a pair (revert-d-cl-id . pspv) where revert-d-cl-id identifies that
; disjunctive subgoal (the first one, in fact) and pspv is the corresponding
; pspv returned for that subgoal.

  #+acl2-par
  (declare (ignorable branch-cnt)) ; irrelevant in @par definition
  (cond
   ((endp uhs-lst)

; Results is the result of doing all the elements of uhs-lst.  If it is empty,
; all branches aborted.  Otherwise, we have to choose between the results.

    (cond
     ((endp results)

; In this case, every single disjunct aborted.  That means each failed in one
; of three ways: (a) it set the goal to nil, (b) it needed induction but found
; a hint prohibiting it, or (c) it chose to revert to the original input.  We
; will cause the whole proof to abort.  We choose to revert if revert-d-cl-id
; is non-nil, indicating that (c) occurred for at least one disjunctive branch,
; namely one with a clause-id of revert-d-cl-id.

      (pprogn@par
       (serial-only@par
        (io? prove nil state
             (cl-id revert-info)
             (waterfall-or-hit-msg-c cl-id nil (car revert-info) nil nil
                                     state)
             :io-marker cl-id))

       (mv@par step-limit
               'abort
               (cond (revert-info (cdr revert-info))
                     (t
                      (change prove-spec-var pspv
                              :pool (cons (make pool-element
                                                :tag 'TO-BE-PROVED-BY-INDUCTION
                                                :clause-set '(nil)
                                                :hint-settings nil)
                                          (access prove-spec-var pspv :pool))
                              :tag-tree
                              (add-to-tag-tree 'abort-cause
                                               'empty-clause
                                               (access prove-spec-var pspv
                                                       :tag-tree)))))
               (and revert-info

; Keep the following in sync with the corresponding call of pool-lst in
; waterfall-msg.  That call assumes that the pspv was returned by push-clause,
; which is also the case here.

                    (pool-lst (cdr (access prove-spec-var (cdr revert-info)
                                           :pool))))
               state)))
     (t (mv-let (choice summary)
                (pick-best-pspv-for-waterfall0-or-hit results pspv wrld)
                #+acl2-par
                (declare (ignorable summary))
                (pprogn@par
                 (serial-only@par
                  (io? proof-tree nil state
                       (choice cl-id)
                       (pprogn
                        (increment-timer 'prove-time state)
                        (install-disjunct-into-proof-tree cl-id (car choice) state)
                        (increment-timer 'proof-tree-time state))))
                 (serial-only@par
                  (io? prove nil state
                       (cl-id results choice summary)
                       (waterfall-or-hit-msg-c cl-id ; parent-cl-id
                                               results
                                               nil
                                               (car choice) ; new goal cl-id
                                               summary
                                               state)
                       :io-marker cl-id))
                 (mv@par step-limit
                         'continue
                         (cdr choice) ; chosen pspv

; Through Version_3.3 we used a jppl-flg here instead of nil.  But to the
; extent that this value controls whether we print the goal before starting
; induction, we prefer to print it: for the corresponding goal pushed for
; induction under one of the disjunctive subgoals, the connection might not be
; obvious to the user.

                         nil
                         state))))))
   (t
    (let* ((user-hinti (car (car uhs-lst)))
           (hint-settingsi (cdr (car uhs-lst)))
           (d-cl-id (make-disjunctive-clause-id cl-id (length uhs-lst)
                                                (current-package state))))
      #+acl2-par
      (declare (ignorable user-hinti))
      (pprogn@par
       (serial-only@par

; Wormholes are known to be a problem in the @par version of the waterfall.  As
; such, we skip the following call of waterfall-or-hit-msg-a (also for some
; similar calls further down), which we have determined through runs of the
; regression suite (specifically with community book
; arithmetic-5/lib/floor-mod/floor-mod-basic.lisp) to cause problems.

        (io? prove nil state
             (cl-id user-hinti d-cl-id i branch-cnt)
             (pprogn
              (increment-timer 'prove-time state)
              (waterfall-or-hit-msg-a cl-id user-hinti d-cl-id i branch-cnt
                                      state)
              (increment-timer 'print-time state))
             :io-marker cl-id))
       (sl-let@par
        (d-signal d-new-pspv d-new-jppl-flg state)
        (waterfall1-wrapper@par
         (waterfall1@par ledge
                         d-cl-id
                         clause
                         (change-or-hit-history-entry i hist cl-id)
                         pspv
                         (cons (pair-cl-id-with-hint-setting@par d-cl-id
                                                                 hint-settingsi)
                               hints)
                         t ;;; suppress-print
                         ens
                         wrld ctx state step-limit))
        (declare (ignore d-new-jppl-flg))

; Here, d-signal is one of 'error, 'abort or 'continue.  We pass 'error up
; immediately and we filter 'abort out.

        (cond
         ((eq d-signal 'error)

; Errors shouldn't happen and we stop with an error if one does.

          (mv@par step-limit 'error nil nil state))
         ((eq d-signal 'abort)

; Aborts are normal -- the proof failed somehow; we just skip it and continue
; with its peers.

          (waterfall0-or-hit@par
           ledge cl-id clause hist pspv hints ens wrld ctx state
           (cdr uhs-lst) (+ 1 i) branch-cnt
           (or revert-info
               (and (equal (tagged-objects 'abort-cause
                                           (access prove-spec-var d-new-pspv
                                                   :tag-tree))
                           '(revert))
                    (cons d-cl-id d-new-pspv)))
           results step-limit))
         ((equal (access prove-spec-var pspv :pool)
                 (access prove-spec-var d-new-pspv :pool))

; We won!  The pool in the new pspv is the same as the pool in the old, which
; means all the subgoals generated in the branch were proved (modulo any forced
; assumptions, etc., in the :tag-tree).  In this case we terminate the sweep
; across the disjuncts.

; Parallelism wart: you'll get a runtime error if pprogn@par forms are
; evaluated that have state returned by other than the last form, such as the
; call below of waterfall-or-hit-msg-b.  Example: (WORMHOLE1 'COMMENT-WINDOW-IO
; 'NIL '(PPROGN (PRINC$ 17 *STANDARD-CO* STATE) 17) 'NIL)

          (pprogn@par
           (serial-only@par
            (io? proof-tree nil state
                 (d-cl-id cl-id)
                 (pprogn
                  (increment-timer 'prove-time state)
                  (install-disjunct-into-proof-tree cl-id d-cl-id state)
                  (increment-timer 'proof-tree-time state))))
           (serial-only@par
            (io? prove nil state
                 (cl-id d-cl-id branch-cnt)
                 (pprogn
                  (increment-timer 'prove-time state)
                  (waterfall-or-hit-msg-b cl-id d-cl-id branch-cnt state)
                  (increment-timer 'print-time state))
                 :io-marker cl-id))
           (mv@par step-limit
                   'continue
                   d-new-pspv
                   nil ; could probably use jppl-flg, but nil is always OK
                   state)))
         (t

; Otherwise, we collect the result into results and continue with the others.

          (waterfall0-or-hit@par
           ledge cl-id clause hist pspv hints ens wrld ctx state
           (cdr uhs-lst) (+ 1 i) branch-cnt
           revert-info
           (cons (cons d-cl-id d-new-pspv) results)
           step-limit)))))))))

(defun waterfall1-lst (n parent-cl-id clauses hist pspv jppl-flg
                         hints suppress-print ens wrld ctx state step-limit)

; N is either 'settled-down-clause, nil, or an integer.  'Settled-
; down-clause means that we just executed settled-down-clause and so
; should pass the parent's clause id through as though nothing
; happened.  Nil means we produced one child and so its clause-id is
; that of the parent with the primes field incremented by 1.  An
; integer means we produced n children and they each get a clause-id
; derived by extending the parent's case-lst.

; Keep the main body of waterfall1-lst in sync with waterfall1-lst@par-serial
; and waterfall1-tree@par-parallel.

  (cond
   ((null clauses) (mv step-limit 'continue pspv jppl-flg state))
   (t (let ((cl-id

; Keep this binding in sync with the binding of cl-id in waterfall1-lst@par.

             (cond
              ((and (equal parent-cl-id *initial-clause-id*)
                    (no-op-histp hist))
               parent-cl-id)
              ((eq n 'settled-down-clause) parent-cl-id)
              ((null n)
               (change clause-id parent-cl-id
                       :primes
                       (1+ (access clause-id
                                   parent-cl-id
                                   :primes))))
              (t (change clause-id parent-cl-id
                         :case-lst
                         (append (access clause-id
                                         parent-cl-id
                                         :case-lst)
                                 (list n))
                         :primes 0)))))
        (sl-let
         (signal new-pspv new-jppl-flg state)
         (waterfall1 *preprocess-clause-ledge*
                     cl-id
                     (car clauses)
                     hist
                     pspv
                     hints
                     suppress-print
                     ens
                     wrld
                     ctx
                     state
                     step-limit)
         (cond
          ((eq signal 'error)
           (mv step-limit 'error nil nil state))
          ((eq signal 'abort)
           (mv step-limit 'abort new-pspv new-jppl-flg state))
          (t
           (waterfall1-lst (cond ((eq n 'settled-down-clause) n)
                                 ((null n) nil)
                                 (t (1- n)))
                           parent-cl-id
                           (cdr clauses)
                           hist
                           new-pspv
                           new-jppl-flg
                           hints
                           nil
                           ens
                           wrld
                           ctx
                           state
                           step-limit))))))))

#+acl2-par
(defun waterfall1-lst@par-serial (n parent-cl-id clauses hist pspv jppl-flg
                                    hints suppress-print ens wrld ctx state
                                    step-limit)

; Keep the main body of waterfall1-lst in sync with waterfall1-lst@par-serial,
; waterfall1-tree@par-parallel, and waterfall1-tree@par-pseudo-parallel.  Keep
; the calculation of cl-id in sync with waterfall1-lst@par.

  (cond
   ((null clauses) (mv@par step-limit 'continue pspv jppl-flg state))
   (t (let ((cl-id (cond
                    ((and (equal parent-cl-id *initial-clause-id*)
                          (no-op-histp hist))
                     parent-cl-id)
                    ((eq n 'settled-down-clause) parent-cl-id)
                    ((null n)
                     (change clause-id parent-cl-id
                             :primes
                             (1+ (access clause-id
                                         parent-cl-id
                                         :primes))))
                    (t (change clause-id parent-cl-id
                               :case-lst
                               (append (access clause-id
                                               parent-cl-id
                                               :case-lst)
                                       (list n))
                               :primes 0)))))
        (sl-let@par
         (signal new-pspv new-jppl-flg state)
         (waterfall1-wrapper@par
          (waterfall1@par *preprocess-clause-ledge*
                          cl-id
                          (car clauses)
                          hist
                          pspv
                          hints
                          suppress-print
                          ens
                          wrld
                          ctx
                          state
                          step-limit))
         (cond
          ((eq signal 'error) (mv@par step-limit 'error nil nil state))
          ((eq signal 'abort) (mv@par step-limit 'abort new-pspv new-jppl-flg state))
          (t
           (waterfall1-lst@par (cond ((eq n 'settled-down-clause) n)
                                     ((null n) nil)
                                     (t (1- n)))
                               parent-cl-id
                               (cdr clauses)
                               hist
                               new-pspv
                               new-jppl-flg
                               hints
                               nil
                               ens
                               wrld
                               ctx
                               state
                               step-limit))))))))

#+acl2-par
(defun waterfall1-tree@par-pseudo-parallel (n parent-cl-id clauses hist pspv
                                              jppl-flg hints suppress-print ens
                                              wrld ctx state step-limit)

; Keep the main body of waterfall1-lst in sync with waterfall1-lst@par-serial,
; waterfall1-tree@par-parallel, and waterfall1-tree@par-pseudo-parallel.  Keep
; the calculation of cl-id in sync with waterfall1-lst@par.

; Since waterfall1-tree@par-pseudo-parallel is just a refactoring of
; waterfall1-tree@par-parallel, I remove many comments from this definition.  So,
; see waterfall1-tree@par-parallel for a more complete set of comments.

  (declare (ignorable ens))
  (cond
   ((null clauses) (mv@par step-limit 'continue pspv jppl-flg state))
   (t (let ((cl-id (cond
                    ((and (equal parent-cl-id *initial-clause-id*)
                          (no-op-histp hist))
                     parent-cl-id)
                    ((eq n 'settled-down-clause) parent-cl-id)
                    ((null n)
                     (change clause-id parent-cl-id
                             :primes
                             (1+ (access clause-id
                                         parent-cl-id
                                         :primes))))
                    (t (change clause-id parent-cl-id
                               :case-lst
                               (append (access clause-id
                                               parent-cl-id
                                               :case-lst)
                                       (list n))
                               :primes 0)))))
        (mv-let
         (first-half-clauses second-half-clauses len-first-half)
         (halves-with-length clauses)
         (mv-let@par
          (step-limit1 signal1 pspv1 jppl-flg1 state)
          (cond ((assert$ (consp clauses)
                          (null (cdr clauses))) ; just one clause, call waterfall1
                 (waterfall1-wrapper@par
                  (waterfall1@par *preprocess-clause-ledge*
                                  cl-id
                                  (car clauses)
                                  hist
                                  pspv
                                  hints
                                  suppress-print
                                  ens
                                  wrld
                                  ctx
                                  state
                                  step-limit)))
                (t
                 (waterfall1-lst@par (cond ((eq n 'settled-down-clause) n)
                                           ((null n) nil)
                                           (t n)) ;(1- n)))
                                     parent-cl-id
                                     first-half-clauses
                                     hist
                                     pspv
                                     jppl-flg
                                     hints
                                     nil
                                     ens
                                     wrld
                                     ctx
                                     state
                                     step-limit)))
          (if

; Conditions that must be true for the speculative call to be valid:

              (and (not (eq signal1 'error))
                   (not (eq signal1 'abort))
                   (speculative-execution-valid pspv pspv1))
              (mv-let

; Here, we perform the speculative call of waterfall1-lst@par, which is the
; recursion on the cdr of clauses.  As such, this code matches the code at the
; end of waterfall1-lst.

               (step-limit2 signal2 pspv2 jppl-flg2)
               (waterfall1-lst@par (cond ((eq n 'settled-down-clause) n)
                                         ((null n) nil)
                                         (t (- n len-first-half)))
                                   parent-cl-id
                                   second-half-clauses
                                   hist
                                   pspv
                                   jppl-flg
                                   hints
                                   nil
                                   ens
                                   wrld
                                   ctx
                                   state
                                   step-limit)

               (cond ((eq signal2 'error)
                      (mv@par step-limit2 'error nil nil state))
                     ((eq signal2 'abort)
                      (mv@par step-limit2 'abort pspv2 jppl-flg2
                              state))
                     (t
                      (let ((combined-step-limit (- (- step-limit
                                                       (- step-limit step-limit1))
                                                    (- step-limit step-limit2)))
                            (combined-prove-spec-vars
                             (combine-prove-spec-vars
                              pspv pspv1 pspv2 ctx
                              (f-get-global 'debug-pspv state)
                              signal1 signal2)))

                        (if (abort-will-occur-in-pool
                             (access prove-spec-var combined-prove-spec-vars :pool))
                            (prog2$
                             (with-output-lock
                              (cw "Normally we would attempt to prove two or ~
                                   more of the previously printed subgoals by ~
                                   induction.  However, we prefer in this ~
                                   instance to focus on the original input ~
                                   conjecture rather than those simplified ~
                                   special cases.  We therefore abandon our ~
                                   previous work on these conjectures and ~
                                   reassign the name *1 to the original ~
                                   conjecture."))
                             (mv@par combined-step-limit
                                     'abort
                                     combined-prove-spec-vars
                                     jppl-flg2
                                     state))
                          (mv@par combined-step-limit
                                  signal2
                                  combined-prove-spec-vars
                                  jppl-flg2 state))))))
            (cond
             ((eq signal1 'error) (mv@par step-limit1 'error nil nil state))
             ((eq signal1 'abort) (mv@par step-limit1 'abort pspv1 jppl-flg1
                                          state))
             (t ; we need to recompute the recursive call
              (prog2$
               (cond ((member-eq 'prove
                                 (f-get-global 'inhibit-output-lst state))
                      nil)
                     (t (with-output-lock
                         (cw "Invalid speculation for children of subgoal ~
                              ~x0~%"
                             (string-for-tilde-@-clause-id-phrase cl-id)))))
               (waterfall1-lst@par (cond ((eq n 'settled-down-clause) n)
                                         ((null n) nil)
                                         (t (- n len-first-half)))
                                   parent-cl-id
                                   second-half-clauses
                                   hist
                                   pspv1
                                   jppl-flg1
                                   hints
                                   nil
                                   ens
                                   wrld
                                   ctx
                                   state step-limit1)))))))))))

#+acl2-par
(defun waterfall1-tree@par-parallel (n parent-cl-id clauses hist pspv jppl-flg
                                       hints suppress-print ens wrld ctx state
                                       step-limit)

; Keep the main body of waterfall1-lst in sync with waterfall1-lst@par-serial,
; waterfall1-tree@par-parallel, and waterfall1-tree@par-pseudo-parallel.  Keep
; the calculation of cl-id in sync with waterfall1-lst@par.

; Once upon a time, we took a "list-based" approach to parallelizing the proofs
; of clauses.  We now take a "tree-based" approach.

; Originally waterfall1-tree@par-parallel would "cdr" down the list of clauses
; and spawn a thread for each of those recursive calls.  However, that approach
; required too many threads (we attempted to mitigate this problem with
; set-total-parallelism-work-limit, but it was just a bandage on a more glaring
; problem).  As of April, 2012, we now take a "tree-based" approach and split
; the list of clauses into halves, and then call waterfall1-lst@par again,
; twice, each with its own half.  We eventually call waterfall1-lst@par with a
; clause list of length 1, and then that clause is proven.

; Note that splitting the list like this is a reasonable thing to do -- we do
; not reorder any subgoals, and we increment the variable that keeps track of
; the current subgoal number (n) by the length of the first half of clauses.

  (declare (ignorable ens))
  (cond
   ((null clauses) (mv@par step-limit 'continue pspv jppl-flg state))
   (t (let ((cl-id (cond
                    ((and (equal parent-cl-id *initial-clause-id*)
                          (no-op-histp hist))
                     parent-cl-id)
                    ((eq n 'settled-down-clause) parent-cl-id)
                    ((null n)
                     (change clause-id parent-cl-id
                             :primes
                             (1+ (access clause-id
                                         parent-cl-id
                                         :primes))))
                    (t (change clause-id parent-cl-id
                               :case-lst
                               (append (access clause-id
                                               parent-cl-id
                                               :case-lst)
                                       (list n))
                               :primes 0)))))
        (mv-let
         (first-half-clauses second-half-clauses len-first-half)
         (halves-with-length clauses)
         (spec-mv-let

; Here, we perform the speculative call of waterfall1-lst@par, which is the
; recursion on the cdr of clauses.  As such, this code matches the code at the
; end of waterfall1-lst.

; Variable names that end with "1" (as in signal1) store results from proving
; the first half of the clauses (the part of the spec-mv-let that is always
; performed), and variable names that end with "2" (as in signal2) store results
; from speculatively proving the second half of the clauses.

          (step-limit2 signal2 pspv2 jppl-flg2)
          (waterfall1-lst@par (cond ((eq n 'settled-down-clause) n)
                                    ((null n) nil)
                                    (t (- n len-first-half)))
                              parent-cl-id
                              second-half-clauses
                              hist
                              pspv
                              jppl-flg
                              hints
                              nil
                              ens
                              wrld
                              ctx
                              state
                              step-limit)
          (mv-let@par
           (step-limit1 signal1 pspv1 jppl-flg1 state)
           (cond ((assert$ (consp clauses)
                           (null (cdr clauses))) ; just one clause, call waterfall1
                  (waterfall1-wrapper@par
                   (waterfall1@par *preprocess-clause-ledge*
                                   cl-id
                                   (car clauses)
                                   hist
                                   pspv
                                   hints
                                   suppress-print
                                   ens
                                   wrld
                                   ctx
                                   state
                                   step-limit)))
                 (t
                  (waterfall1-lst@par (cond ((eq n 'settled-down-clause) n)
                                            ((null n) nil)
                                            (t n))
                                      parent-cl-id
                                      first-half-clauses
                                      hist
                                      pspv
                                      jppl-flg
                                      hints
                                      nil
                                      ens
                                      wrld
                                      ctx
                                      state
                                      step-limit)))
           (if

; Conditions that must be true for the speculative call to be valid:

               (and (not (eq signal1 'error))
                    (not (eq signal1 'abort))
                    (speculative-execution-valid pspv pspv1))
               (cond ((eq signal2 'error)
                      (mv@par step-limit2 'error nil nil state))
                     ((eq signal2 'abort)

; It is okay to just return pspv2, because if there is an abort, any clauses
; pushed for induction into pspv1 would be discarded anyway.  See Essay on
; prove-spec-var pool modifications for further discussion.

                      (mv@par step-limit2 'abort pspv2 jppl-flg2 state))
                     (t
                      (let ((combined-step-limit (- (- step-limit
                                                       (- step-limit step-limit1))
                                                    (- step-limit step-limit2)))
                            (combined-prove-spec-vars
                             (combine-prove-spec-vars
                              pspv pspv1 pspv2 ctx
                              (f-get-global 'debug-pspv state)
                              signal1 signal2)))
                        (if (abort-will-occur-in-pool
                             (access prove-spec-var combined-prove-spec-vars :pool))
                            (prog2$

; Parallelism wart: maybe this call to cw should be inside waterfall instead of
; here.  The potential problem with printing the message here is that printing
; can still occur after we say that we are "focus[sing] on the original
; conjecture".

; For example, suppose we are Subgoal 3.2.4, and we know we need to abort.
; Subgoal 3.3.4 could still be proving and print a checkpoint, even though this
; call of Subgoal 3.2.4 knows we need to abort.  It is not until control
; returns to the waterfall1-lst@par call on Subgoal 3.3 that the 'abort from
; Subgoal 3.2.4 will be seen, and that we will then know that all such calls
; that might print have already returned (because Subgoal 3.3.4 must be
; finished before the call of waterfall1 on Subgoal 3.3 returns).

                             (with-output-lock
                              (cw "Normally we would attempt to prove two or ~
                                   more of the previously printed subgoals by ~
                                   induction.  However, we prefer in this ~
                                   instance to focus on the original input ~
                                   conjecture rather than those simplified ~
                                   special cases.  We therefore abandon our ~
                                   previous work on these conjectures and ~
                                   reassign the name *1 to the original ~
                                   conjecture."))
                             (mv@par combined-step-limit
                                     'abort

; We do not adjust the pspv's pool here.  Instead, we rely upon waterfall to
; correctly convert the 'maybe-to-be-proved-by-induction tag to a
; 'to-be-proved-by-induction and discard the other clauses.

                                     combined-prove-spec-vars
                                     jppl-flg2
                                     state))
                          (mv@par combined-step-limit
                                  signal2
                                  combined-prove-spec-vars
                                  jppl-flg2 state)))))
             (cond
              ((eq signal1 'error) (mv@par step-limit1 'error nil nil state))
              ((eq signal1 'abort) (mv@par step-limit1 'abort pspv1
                                           jppl-flg1 state))
              (t ; we need to recompute the recursive call
               (prog2$

; Parallelism wart: improve message just below (maybe even eliminate it?).
; Also, consider avoiding this direct use of inhibit-output-lst (it seemed that
; io? didn't work because we don't use state, as it requires).
; And finally, deal the same way with all cw printing done on behalf of the
; prover; consider searching for with-output-lock to find those.

; Parallelism wart: due to the definition of speculative-execution-valid, this
; code should no longer be reachable.  We leave it for now because it is an
; example use of 'inhibit-output-lst (also see parallelism wart immediately
; above).

                (cond ((member-eq 'prove
                                  (f-get-global 'inhibit-output-lst state))
                       nil)
                      (t (with-output-lock
                          (cw "Invalid speculation for children of subgoal ~
                               ~x0~%"
                              (string-for-tilde-@-clause-id-phrase cl-id)))))
                (waterfall1-lst@par (cond ((eq n 'settled-down-clause) n)
                                          ((null n) nil)
                                          (t (- n len-first-half)))
                                    parent-cl-id
                                    second-half-clauses
                                    hist
                                    pspv1
                                    jppl-flg1
                                    hints
                                    nil
                                    ens
                                    wrld
                                    ctx
                                    state step-limit1))))))))))))

#+acl2-par
(defun waterfall1-lst@par (n parent-cl-id clauses hist pspv jppl-flg
                             hints suppress-print ens wrld ctx state step-limit)

; Keep the main body of waterfall1-lst in sync with waterfall1-lst@par-serial
; and waterfall1-tree@par-parallel.  Keep the calculation of cl-id in sync with
; waterfall1-lst@par.

  (let ((primes-subproof
         (cond ((and (equal parent-cl-id *initial-clause-id*)
                     (no-op-histp hist))
                nil)
               ((eq n 'settled-down-clause) nil)
               ((null n) t)
               (t nil)))
        (cl-id

; Keep this binding in sync with the binding of cl-id in waterfall1-lst.

         (cond
          ((and (equal parent-cl-id *initial-clause-id*)
                (no-op-histp hist))
           parent-cl-id)
          ((eq n 'settled-down-clause) parent-cl-id)
          ((null n)
           (change clause-id parent-cl-id
                   :primes
                   (1+ (access clause-id
                               parent-cl-id
                               :primes))))
          (t (change clause-id parent-cl-id
                     :case-lst
                     (append (access clause-id
                                     parent-cl-id
                                     :case-lst)
                             (list n))
                     :primes 0)))))
    (declare (ignorable primes-subproof cl-id))
    (let ((call-type
           (cond
            (primes-subproof
             'serial)
            (t
             (case (f-get-global 'waterfall-parallelism state)
               ((nil)
                'serial)
               ((:full)
                (cond #-acl2-loop-only
                      ((not-too-many-futures-already-in-existence)
                       'parallel)
                      (t 'serial)))
               ((:pseudo-parallel)
                'pseudo-parallel)
               ((:top-level)
                (cond ((equal parent-cl-id '((0) NIL . 0))
                       'parallel)
                      (t 'serial)))
               ((:resource-and-timing-based)

; Here, and in the :resource-based branch below, we have an unusual functional
; discrepancy between code in the #+acl2-loop-only and #-acl2-loop-only cases.
; But the alternative we have considered would involve some complicated use of
; the acl2-oracle, which seems unjustified for this #+acl2-par code.

                (cond #-acl2-loop-only
                      ((and

; We could test to see whether doing the lookup or testing for resource
; availability is faster.  It probably doesn't matter since they're both
; supposed to be "lock free."  Since we control the lock-freeness for the
; resource availability test in the definition of futures-resources-available
; (as opposed to relying upon the underlying CCL implementation), we call that
; first.

                        (futures-resources-available)
                        (> (or (lookup-waterfall-timings-for-cl-id cl-id) 0)
                           (f-get-global 'waterfall-parallelism-timing-threshold
                                         state)))
                       (increment-waterfall-parallelism-counter
                        'resource-and-timing-parallel))
                      (t
                       (increment-waterfall-parallelism-counter
                        'resource-and-timing-serial))))
               ((:resource-based)

; See comment above about discrepancy between #+acl2-loop-only and
; #-acl2-loop-only code.

                (cond #-acl2-loop-only
                      ((futures-resources-available)
                       (increment-waterfall-parallelism-counter
                        'resource-parallel))
                      (t (increment-waterfall-parallelism-counter
                          'resource-serial))))
               (otherwise
                (er hard 'waterfall1-lst@par
                    "Waterfall-parallelism type is not what it's supposed to ~
                     be.  Please contact the ACL2 authors.")))))))
      (case call-type

; There are three modes of execution available to the waterfall in ACL2(p).  We
; describe each mode inline, below.

        ((serial)

; The serial mode cdrs down the list of clauses, just like waterfall1-lst.

         (waterfall1-lst@par-serial n parent-cl-id clauses hist pspv jppl-flg
                                    hints suppress-print ens wrld ctx state
                                    step-limit))
        ((parallel)

; The parallel mode will call waterfall1-lst@par on the first half of clauses
; in the current thread and call waterfall1-lst@par on the second half of
; clauses in another thread.  Once upon a time, we took a "list-based" approach
; to proving the list of clauses -- where we would prove the (car clauses) in
; the current thread and call (waterfall1-lst@par (cdr clauses)) in another
; thread.  We now take a "tree-based" approach, hence the difference in name
; ("tree" vs. "lst").

         (waterfall1-tree@par-parallel n parent-cl-id clauses hist pspv
                                       jppl-flg hints suppress-print ens
                                       wrld ctx state step-limit))
        ((pseudo-parallel)

; The pseudo-parallel mode is just like parallel mode, except both calls occur
; in the current thread.

         (waterfall1-tree@par-pseudo-parallel n parent-cl-id clauses hist pspv
                                              jppl-flg hints suppress-print ens
                                              wrld ctx state step-limit))
        (otherwise
         (prog2$ (er hard 'waterfall1-lst@par
                     "Implementation error in waterfall1-lst@par.  Please ~
                      contact the ACL2 authors.")
                 (mv@par nil nil nil nil state)))))))
)

; And here is the waterfall:

(defun waterfall (forcing-round pool-lst x pspv hints ens wrld ctx state
                                step-limit)

; Here x is a list of clauses, except that when we are beginning a forcing
; round other than the first, x is really a list of pairs (assumnotes .
; clause).

; Pool-lst is the pool-lst of the clauses and will be used as the first field
; in the clause-id's we generate for them.  We return the five values: a new
; step-limit, an error flag, the final value of pspv, the jppl-flg, and the
; final state.

  (let ((parent-clause-id
         (cond ((and (= forcing-round 0)
                     (null pool-lst))

; Note:  This cond is not necessary.  We could just do the make clause-id
; below.  We recognize this case just to avoid the consing.

                *initial-clause-id*)
               (t (make clause-id
                        :forcing-round forcing-round
                        :pool-lst pool-lst
                        :case-lst nil
                        :primes 0))))
        (clauses
         (cond ((and (not (= forcing-round 0))
                     (null pool-lst))
                (strip-cdrs x))
               (t x)))
        (pspv (maybe-set-rw-cache-state-disabled (erase-rw-cache-from-pspv
                                                  pspv))))
    (pprogn
     (cond ((output-ignored-p 'proof-tree state)
            state)
           (t (initialize-proof-tree parent-clause-id x ctx state)))
     (sl-let (signal new-pspv new-jppl-flg state)
             #+acl2-par
             (if (f-get-global 'waterfall-parallelism state)
                 (with-ensured-parallelism-finishing
                  (with-parallelism-hazard-warnings
                   (mv-let (step-limit signal new-pspv new-jppl-flg)
                           (waterfall1-lst@par (cond ((null clauses) 0)
                                                     ((null (cdr clauses))
                                                      'settled-down-clause)
                                                     (t (length clauses)))
                                               parent-clause-id
                                               clauses nil
                                               pspv nil hints
                                               (and (eql forcing-round 0)
                                                    (null pool-lst)) ; suppress-print
                                               ens wrld ctx state step-limit)
                           (mv step-limit
                               signal
                               (convert-maybes-to-tobes-in-pspv new-pspv)
                               new-jppl-flg
                               state))))
               (sl-let (signal new-pspv new-jppl-flg state)
                       (waterfall1-lst (cond ((null clauses) 0)
                                             ((null (cdr clauses))
                                              'settled-down-clause)
                                             (t (length clauses)))
                                       parent-clause-id
                                       clauses nil
                                       pspv nil hints
                                       (and (eql forcing-round 0)
                                            (null pool-lst)) ; suppress-print
                                       ens wrld ctx state step-limit)
                       (mv step-limit signal new-pspv new-jppl-flg state)))
             #-acl2-par
             (waterfall1-lst (cond ((null clauses) 0)
                                   ((null (cdr clauses))
                                    'settled-down-clause)
                                   (t (length clauses)))
                             parent-clause-id
                             clauses nil
                             pspv nil hints
                             (and (eql forcing-round 0)
                                  (null pool-lst)) ; suppress-print
                             ens wrld ctx state step-limit)
             (cond ((eq signal 'error)

; If the waterfall signaled an error then it printed the message and we
; just pass the error up.

                    (mv step-limit t nil nil state))
                   (t

; Otherwise, the signal is either 'abort or 'continue.  But 'abort here
; was meant as an internal signal only, used to get out of the recursion
; in waterfall1.  We now simply fold those two signals together into the
; non-erroneous return of the new-pspv and final flg.

                    (mv step-limit nil new-pspv new-jppl-flg state)))))))

; After the waterfall has finished we have a pool of goals.  We
; now develop the functions to extract a goal from the pool for
; induction.  It is in this process that we check for subsumption
; among the goals in the pool.

(defun some-pool-member-subsumes (pool clause-set)

; We attempt to determine if there is a clause set in the pool that subsumes
; every member of the given clause-set.  If we make that determination, we
; return the tail of pool that begins with that member.  Otherwise, no such
; subsumption was found, perhaps because of the limitation in our subsumption
; check (see subsumes), and we return nil.

  (cond ((null pool) nil)
        ((eq (clause-set-subsumes *init-subsumes-count*
                                  (access pool-element (car pool) :clause-set)
                                  clause-set)
             t)
         pool)
        (t (some-pool-member-subsumes (cdr pool) clause-set))))

(defun add-to-pop-history
  (action cl-set pool-lst subsumer-pool-lst pop-history)

; Extracting a clause-set from the pool is called "popping".  It is
; complicated by the fact that we do subsumption checking and other
; things.  To report what happened when we popped, we maintain a "pop-history"
; which is used by the pop-clause-msg fn below.  This function maintains
; pop-histories.

; A pop-history is a list that records the sequence of events that
; occurred when we popped a clause set from the pool.  The pop-history
; is used only by the output routine pop-clause-msg.

; The pop-history is built from nil by repeated calls of this
; function.  Thus, this function completely specifies the format.  The
; elements in a pop-history are each of one of the following forms.
; All the "lst"s below are pool-lsts.

; (pop lst1 ... lstk)             finished the proofs of the lstd goals
; (consider cl-set lst)           induct on cl-set
; (subsumed-by-parent cl-set lst subsumer-lst)
;                                 cl-set is subsumed by lstd parent
; (subsumed-below cl-set lst subsumer-lst)
;                                 cl-set is subsumed by lstd peer
; (qed)                           pool is empty -- but there might be
;                                 assumptions or :byes yet to deal with.
; and has the property that no two pop entries are adjacent.  When
; this function is called with an action that does not require all of
; the arguments, nils may be provided.

; The entries are in reverse chronological order and the lsts in each
; pop entry are in reverse chronological order.

  (cond ((eq action 'pop)
         (cond ((and pop-history
                     (eq (caar pop-history) 'pop))
                (cons (cons 'pop (cons pool-lst (cdar pop-history)))
                      (cdr pop-history)))
               (t (cons (list 'pop pool-lst) pop-history))))
        ((eq action 'consider)
         (cons (list 'consider cl-set pool-lst) pop-history))
        ((eq action 'qed)
         (cons '(qed) pop-history))
        (t (cons (list action cl-set pool-lst subsumer-pool-lst)
                 pop-history))))

(defun pop-clause1 (pool pop-history)

; We scan down pool looking for the next 'to-be-proved-by-induction
; clause-set.  We mark it 'being-proved-by-induction and return six
; things: one of the signals 'continue, 'win, or 'lose, the pool-lst
; for the popped clause-set, the clause-set, its hint-settings, a
; pop-history explaining what we did, and a new pool.

  (cond ((null pool)

; It looks like we won this one!  But don't be fooled.  There may be
; 'assumptions or :byes in the ttree associated with this proof and
; that will cause the proof to fail.  But for now we continue to just
; act happy.  This is called denial.

         (mv 'win nil nil nil
             (add-to-pop-history 'qed nil nil nil pop-history)
             nil))
        ((eq (access pool-element (car pool) :tag) 'being-proved-by-induction)
         (pop-clause1 (cdr pool)
                      (add-to-pop-history 'pop
                                          nil
                                          (pool-lst (cdr pool))
                                          nil
                                          pop-history)))
        ((equal (access pool-element (car pool) :clause-set)
                '(nil))

; The empty set was put into the pool!  We lose.  We report the empty name
; and clause set, and an empty pop-history (so no output occurs).  We leave
; the pool as is.  So we'll go right out of pop-clause and up to the prover
; with the 'lose signal.

         (mv 'lose nil nil nil nil pool))
        (t
         (let ((pool-lst (pool-lst (cdr pool)))
               (sub-pool
                (some-pool-member-subsumes (cdr pool)
                                           (access pool-element (car pool)
                                                   :clause-set))))
           (cond
            ((null sub-pool)
             (mv 'continue
                 pool-lst
                 (access pool-element (car pool) :clause-set)
                 (access pool-element (car pool) :hint-settings)
                 (add-to-pop-history 'consider
                                     (access pool-element (car pool)
                                             :clause-set)
                                     pool-lst
                                     nil
                                     pop-history)
                 (cons (change pool-element (car pool)
                               :tag 'being-proved-by-induction)
                       (cdr pool))))
            ((eq (access pool-element (car sub-pool) :tag)
                 'being-proved-by-induction)
             (mv 'lose nil nil nil
                 (add-to-pop-history 'subsumed-by-parent
                                     (access pool-element (car pool)
                                             :clause-set)
                                     pool-lst
                                     (pool-lst (cdr sub-pool))
                                     pop-history)
                 pool))
            (t
             (pop-clause1 (cdr pool)
                          (add-to-pop-history 'subsumed-below
                                              (access pool-element (car pool)
                                                      :clause-set)
                                              pool-lst
                                              (pool-lst (cdr sub-pool))
                                              pop-history))))))))

; Here we develop the functions for reporting on a pop.

(defun make-defthm-forms-for-byes (byes wrld)

; Each element of byes is of the form (name . clause) and we create
; a list of the corresponding defthm events.

  (cond ((null byes) nil)
        (t (cons (list 'defthm (caar byes)
                       (prettyify-clause (cdar byes) nil wrld)
                       :rule-classes nil)
                 (make-defthm-forms-for-byes (cdr byes) wrld)))))

(defun pop-clause-msg1 (forcing-round lst jppl-flg prev-action gag-state msg-p
                                      state)

; Lst is a reversed pop-history.  Since pop-histories are in reverse
; chronological order, lst is in chronological order.  We scan down
; lst, printing out an explanation of each action.  Prev-action is the
; most recently explained action in this scan, or else nil if we are
; just beginning.  Jppl-flg, if non-nil, means that the last executed
; waterfall process was 'push-clause; the pool-lst of the clause pushed is
; in the value of jppl-flg.

  (cond
   ((null lst)
    (pprogn (increment-timer 'print-time state)
            (mv gag-state state)))
   (t
    (let ((entry (car lst)))
      (mv-let
       (gag-state state)
       (case-match
         entry
         (('pop . pool-lsts)
          (mv-let
           (gagst msgs)
           (pop-clause-update-gag-state-pop pool-lsts gag-state nil msg-p
                                            state)
           (pprogn
            (io? prove nil state
                 (prev-action pool-lsts forcing-round msgs)
                 (pprogn
                  (fms
                   (cond ((gag-mode)
                          (assert$ pool-lsts
                                   "~*1 ~#0~[is~/are~] COMPLETED!~|"))
                         ((null prev-action)
                          "That completes the proof~#0~[~/s~] of ~*1.~|")
                         (t "That, in turn, completes the proof~#0~[~/s~] of ~
                             ~*1.~|"))
                   (list (cons #\0 pool-lsts)
                         (cons #\1
                               (list "" "~@*" "~@* and " "~@*, "
                                     (tilde-@-pool-name-phrase-lst
                                      forcing-round
                                      (reverse pool-lsts)))))
                   (proofs-co state) state nil)
                  (cond
                   ((and msgs (gag-mode))
                    (mv-let
                     (col state)
                     (fmt1 "Thus key checkpoint~#1~[~ ~*0 is~/s ~*0 are~] ~
                            COMPLETED!~|"
                           (list (cons #\0
                                       (list "" "~@*" "~@* and " "~@*, "
                                             (reverse msgs)))
                                 (cons #\1 msgs))
                           0 (proofs-co state) state nil)
                     (declare (ignore col))
                     state))
                   (t state))))
            (mv gagst state))))
         (('qed)

; We used to print Q.E.D. here, but that is premature now that we know
; there might be assumptions or :byes in the pspv.  We let
; process-assumptions announce the definitive completion of the proof.

          (mv gag-state state))
         (&

; Entry is either a 'consider or one of the two 'subsumed... actions.  For all
; three we print out the clause we are working on.  Then we print out the
; action specific stuff.

          (let ((pool-lst (caddr entry)))
            (mv-let
             (gagst cl-id)
             (cond ((eq (car entry) 'consider)
                    (mv gag-state nil))
                   (t (remove-pool-lst-from-gag-state pool-lst gag-state
                                                      state)))
             (pprogn
              (io? prove nil state
                   (prev-action forcing-round pool-lst entry cl-id jppl-flg
                                gag-state)
                   (let* ((cl-set (cadr entry))
                          (jppl-flg (if (gag-mode)
                                        (gag-mode-jppl-flg gag-state)
                                      jppl-flg))
                          (push-pop-flg
                           (and jppl-flg
                                (equal jppl-flg pool-lst))))

; The push-pop-flg is set if the clause just popped is the same as the one we
; just pushed.  It and its name have just been printed.  There's no need to
; identify it here unless we are in gag-mode and we are in a sub-induction,
; since in that case we never printed the formula.  (We could take the attitude
; that the user doesn't deserve to see any sub-induction formulas in gag-mode;
; but we expect there to be very few of these anyhow, since probably they'll
; generally fail.)

                     (pprogn
                      (cond
                       (push-pop-flg state)
                       (t (fms (cond
                                ((eq prev-action 'pop)
                                 "We therefore turn our attention to ~@1, ~
                                  which is~|~%~q0.~|")
                                ((null prev-action)
                                 "So we now return to ~@1, which is~|~%~q0.~|")
                                (t
                                 "We next consider ~@1, which is~|~%~q0.~|"))
                               (list (cons #\0 (prettyify-clause-set
                                                cl-set
                                                (let*-abstractionp state)
                                                (w state)))
                                     (cons #\1 (tilde-@-pool-name-phrase
                                                forcing-round pool-lst)))
                               (proofs-co state)
                               state
                               (term-evisc-tuple nil state))))
                      (case-match
                        entry
                        (('subsumed-below & & subsumer-pool-lst)
                         (pprogn
                          (fms "But the formula above is subsumed by ~@1, ~
                                which we'll try to prove later.  We therefore ~
                                regard ~@0 as proved (pending the proof of ~
                                the more general ~@1).~|"
                               (list
                                (cons #\0
                                      (tilde-@-pool-name-phrase
                                       forcing-round pool-lst))
                                (cons #\1
                                      (tilde-@-pool-name-phrase
                                       forcing-round subsumer-pool-lst)))
                               (proofs-co state)
                               state nil)
                          (cond
                           ((and cl-id (gag-mode))
                            (fms "~@0 COMPLETED!~|"
                                 (list (cons #\0 (tilde-@-clause-id-phrase
                                                  cl-id)))
                                 (proofs-co state) state nil))
                           (t state))))
                        (('subsumed-by-parent & & subsumer-pool-lst)
                         (fms "The formula above is subsumed by one of its ~
                               parents, ~@0, which we're in the process of ~
                               trying to prove by induction.  When an ~
                               inductive proof pushes a subgoal for induction ~
                               that is less general than the original goal, ~
                               it may be a sign that either an inappropriate ~
                               induction was chosen or that the original goal ~
                               is insufficiently general.  In any case, our ~
                               proof attempt has failed.~|"
                              (list
                               (cons #\0
                                     (tilde-@-pool-name-phrase
                                      forcing-round subsumer-pool-lst)))
                              (proofs-co state)
                              state nil))
                        (& ; (consider cl-set pool-lst)
                         state)))))
              (mv gagst state))))))
       (pop-clause-msg1 forcing-round (cdr lst) jppl-flg (caar lst) gag-state
                        msg-p state))))))

(defun pop-clause-msg (forcing-round pop-history jppl-flg pspv state)

; We print the messages explaining the pops we did.

; This function increments timers.  Upon entry, the accumulated time is
; charged to 'prove-time.  The time spent in this function is charged
; to 'print-time.

  (pprogn
   (increment-timer 'prove-time state)
   (mv-let
    (gag-state state)
    (let ((gag-state0 (access prove-spec-var pspv :gag-state)))
      (pop-clause-msg1 forcing-round
                       (reverse pop-history)
                       jppl-flg
                       nil
                       gag-state0
                       (not (output-ignored-p 'prove state))
                       state))
    (pprogn (record-gag-state gag-state state)
            (increment-timer 'print-time state)
            (mv (change prove-spec-var pspv :gag-state gag-state)
                state)))))

(defun subsumed-clause-ids-from-pop-history (forcing-round pop-history)
  (cond
   ((endp pop-history)
    nil)
   ((eq (car (car pop-history)) 'subsumed-below)
    (cons (make clause-id
                :forcing-round forcing-round
                :pool-lst (caddr (car pop-history)) ; see add-to-pop-history
                :case-lst nil
                :primes 0)
          (subsumed-clause-ids-from-pop-history forcing-round
                                                (cdr pop-history))))
   (t (subsumed-clause-ids-from-pop-history forcing-round (cdr pop-history)))))

(defun increment-proof-tree-pop-clause (forcing-round pop-history state)
  (let ((old-proof-tree (f-get-global 'proof-tree state))
        (dead-clause-ids
         (subsumed-clause-ids-from-pop-history forcing-round pop-history)))
    (if dead-clause-ids
        (pprogn (f-put-global 'proof-tree
                              (prune-proof-tree forcing-round
                                                dead-clause-ids
                                                old-proof-tree)
                              state)
                (print-proof-tree state))
      state)))

(defun pop-clause (forcing-round pspv jppl-flg state)

; We pop the first available clause from the pool in pspv.  We print
; out an explanation of what we do.  If jppl-flg is non-nil
; then it means the last executed waterfall processor was 'push-clause
; and the pool-lst of the clause pushed is the value of jppl-flg.

; We return 7 results.  The first is a signal: 'win, 'lose, or
; 'continue and indicates that we have finished successfully (modulo,
; perhaps, some assumptions and :byes in the tag-tree), arrived at a
; definite failure, or should continue.  If the first result is
; 'continue, the second, third and fourth are the pool name phrase,
; the set of clauses to induct upon, and the hint-settings, if any.
; The remaining results are the new values of pspv and state.

  (mv-let (signal pool-lst cl-set hint-settings pop-history new-pool)
          (pop-clause1 (access prove-spec-var pspv :pool)
                       nil)
          (mv-let
           (new-pspv state)
           (pop-clause-msg forcing-round pop-history jppl-flg pspv state)
           (pprogn
            (io? proof-tree nil state
                 (forcing-round pop-history)
                 (pprogn
                  (increment-timer 'prove-time state)
                  (increment-proof-tree-pop-clause forcing-round pop-history
                                                   state)
                  (increment-timer 'proof-tree-time state)))
            (mv signal
                pool-lst
                cl-set
                hint-settings
                (change prove-spec-var new-pspv :pool new-pool)
                state)))))

(defun tilde-@-assumnotes-phrase-lst (lst wrld)

; Warning :If you change this function, consider also changing
; tilde-@-assumnotes-phrase-lst-gag-mode.

; WARNING: Note that the phrase is encoded twelve times below, to put
; in the appropriate noise words and punctuation!

; Note: As of this writing it is believed that the only time the :rune of an
; assumnote is a fake rune, as in cases 1, 5, and 9 below, is when the
; assumnote is in the impossible assumption.  However, we haven't coded this
; specially because such an assumption will be brought immediately to our
; attention in the forcing round by its *nil* :term.

  (cond
   ((null lst) nil)
   (t (cons
       (cons
        (cond ((null (cdr lst))
               (cond ((and (consp (access assumnote (car lst) :rune))
                           (null (base-symbol (access assumnote (car lst) :rune))))
                      " ~@0~%  by primitive type reasoning about~%  ~q2.~|")
                     ((eq (access assumnote (car lst) :rune) 'equal)
                      " ~@0~%  by the linearization of~%  ~q2.~|")
                     ((symbolp (access assumnote (car lst) :rune))
                      " ~@0~%  by assuming the guard for ~x1 in~%  ~q2.~|")
                     (t " ~@0~%  by applying ~x1 to~%  ~q2.~|")))
              ((null (cddr lst))
               (cond ((and (consp (access assumnote (car lst) :rune))
                           (null (base-symbol (access assumnote (car lst) :rune))))
                      " ~@0~%  by primitive type reasoning about~%  ~q2,~| and~|")
                     ((eq (access assumnote (car lst) :rune) 'equal)
                      " ~@0~%  by the linearization of~%  ~q2,~| and~|")
                     ((symbolp (access assumnote (car lst) :rune))
                      " ~@0~%  by assuming the guard for ~x1 in~%  ~q2,~| and~|")
                     (t " ~@0~%  by applying ~x1 to~%  ~q2,~| and~|")))
              (t
               (cond ((and (consp (access assumnote (car lst) :rune))
                           (null (base-symbol (access assumnote (car lst) :rune))))
                      " ~@0~%  by primitive type reasoning about~%  ~q2,~|")
                     ((eq (access assumnote (car lst) :rune) 'equal)
                      " ~@0~%  by the linearization of~%  ~q2,~|")
                     ((symbolp (access assumnote (car lst) :rune))
                      " ~@0~%  by assuming the guard for ~x1 in~%  ~q2,~|")
                     (t " ~@0~%  by applying ~x1 to~%  ~q2,~|"))))
        (list
         (cons #\0 (tilde-@-clause-id-phrase
                    (access assumnote (car lst) :cl-id)))
         (cons #\1 (access assumnote (car lst) :rune))
         (cons #\2 (untranslate (access assumnote (car lst) :target) nil wrld))))
       (tilde-@-assumnotes-phrase-lst (cdr lst) wrld)))))

(defun tilde-*-assumnotes-column-phrase (assumnotes wrld)

; We create a tilde-* phrase that will print a column of assumnotes.

  (list "" "~@*" "~@*" "~@*"
        (tilde-@-assumnotes-phrase-lst assumnotes wrld)))

(defun tilde-@-assumnotes-phrase-lst-gag-mode (lst acc)

; Warning: If you change this function, consider also changing
; tilde-@-assumnotes-phrase-lst.  See also that function definition.

  (cond
   ((null lst)
    (cond ((null acc) acc)
          ((null (cdr acc))
           (list (msg "in~@0.~|" (car acc))))
          (t (reverse (list* (msg "in~@0.~|" (car acc))
                             (msg "in~@0, and " (cadr acc))
                             (pairlis-x1 "in~@0, ~|"
                                         (pairlis$ (pairlis-x1 #\0 (cddr acc))
                                                   nil)))))))
   (t (tilde-@-assumnotes-phrase-lst-gag-mode
       (cdr lst)
       (let* ((cl-id-phrase
               (tilde-@-clause-id-phrase
                (access assumnote (car lst) :cl-id)))
              (x
               (cond ((and (consp (access assumnote (car lst) :rune))
                           (null (base-symbol (access assumnote (car lst)
                                                      :rune))))
                      (list " ~@0 by primitive type reasoning"
                            (cons #\0 cl-id-phrase)))
                     ((eq (access assumnote (car lst) :rune) 'equal)
                      (list " ~@0 by linearization"
                            (cons #\0 cl-id-phrase)))
                     ((symbolp (access assumnote (car lst) :rune))
                      (list " ~@0 by assuming the guard for ~x1"
                            (cons #\0 cl-id-phrase)
                            (cons #\1 (access assumnote (car lst) :rune))))
                     (t
                      (list " ~@0 by applying ~x1"
                            (cons #\0 cl-id-phrase)
                            (cons #\1 (access assumnote (car lst)
                                              :rune)))))))
         (add-to-set-equal x acc))))))

(defun tilde-*-assumnotes-column-phrase-gag-mode (assumnotes)

; We create a tilde-* phrase that will print a column of assumnotes.

  (list "" "~@*" "~@*" "~@*"
        (tilde-@-assumnotes-phrase-lst-gag-mode assumnotes nil)))

(defun process-assumptions-msg1 (forcing-round n pairs state)

; N is either nil (meaning the length of pairs is 1) or n is the length of
; pairs.

  (cond
   ((null pairs) state)
   (t (pprogn
       (let ((cl-id-phrase
              (tilde-@-clause-id-phrase
               (make clause-id
                     :forcing-round (1+ forcing-round)
                     :pool-lst nil
                     :case-lst (if n (list n) nil)
                     :primes 0))))
         (cond
          ((gag-mode)
           (fms "~@0 was forced ~*1"
                (list (cons #\0 cl-id-phrase)
                      (cons #\1 (tilde-*-assumnotes-column-phrase-gag-mode
                                 (car (car pairs)))))
                (proofs-co state) state
                (term-evisc-tuple nil state)))
          (t
           (fms "~@0, below, will focus on~%~q1,~|which was forced in~%~*2"
                (list (cons #\0 cl-id-phrase)
                      (cons #\1 (untranslate (car (last (cdr (car pairs))))
                                             t (w state)))
                      (cons #\2 (tilde-*-assumnotes-column-phrase
                                 (car (car pairs))
                                 (w state))))
                (proofs-co state) state
                (term-evisc-tuple nil state)))))
       (process-assumptions-msg1 forcing-round
                                 (if n (1- n) nil)
                                 (cdr pairs) state)))))

(defun process-assumptions-msg (forcing-round n0 n pairs state)

; This function is called when we have completed the given forcing-round and
; are about to begin the next one.  Forcing-round is an integer, r.  Pairs is a
; list of n pairs, each of the form (assumnotes . clause).  It was generated by
; cleaning up n0 assumptions.  We are about to pour all n clauses into the
; waterfall, where they will be given clause-ids of the form [r+1]Subgoal i,
; for i from 1 to n, or, if there is only one clause, [r+1]Goal.

; The list of assumnotes associated with each clause explain the need for the
; assumption.  Each assumnote is a record of that class, containing the cl-id
; of the clause we were working on when we generated the assumption, the rune
; (a symbol as per force-assumption) generating the assumption, and the target
; term to which the rule was being applied.  We print a table explaining the
; derivation of the new goals from the old ones and then announce the beginning
; of the next round.

  (io? prove nil state
       (n0 forcing-round n pairs)
       (pprogn
        (fms
         "Modulo~#g~[ the following~/ one~/~]~#0~[~/ ~n1~]~#2~[~/ newly~] ~
          forced goal~#0~[~/s~], that completes ~#2~[the proof of the input ~
          Goal~/Forcing Round ~x3~].~#4~[~/  For what it is worth, the~#0~[~/ ~
          ~n1~] new goal~#0~[ was~/s were~] generated by cleaning up ~n5 ~
          forced hypotheses.~]  See :DOC forcing-round.~%"
         (list (cons #\g (if (gag-mode) (if (cdr pairs) 2 1) 0))
               (cons #\0 (if (cdr pairs) 1 0))
               (cons #\1 n)
               (cons #\2 (if (= forcing-round 0) 0 1))
               (cons #\3 forcing-round)
               (cons #\4 (if (= n0 n) 0 1))
               (cons #\5 n0)
               (cons #\6 (1+ forcing-round)))
         (proofs-co state)
         state
         nil)
        (process-assumptions-msg1 forcing-round
                                  (if (= n 1) nil n)
                                  pairs
                                  state)
        (fms "We now undertake Forcing Round ~x0.~%"
             (list (cons #\0 (1+ forcing-round)))
             (proofs-co state)
             state
             nil))))

(defun count-assumptions (ttree)

; The soundness of the system depends on this function returning 0 only if
; there are no assumptions.

  (length (tagged-objects 'assumption ttree)))

(defun add-type-alist-runes-to-ttree1 (type-alist runes)
  (cond ((endp type-alist)
         runes)
        (t (add-type-alist-runes-to-ttree1
            (cdr type-alist)
            (all-runes-in-ttree (cddr (car type-alist))
                                runes)))))

(defun add-type-alist-runes-to-ttree (type-alist ttree)
  (let* ((runes0 (tagged-objects 'lemma ttree))
         (runes1 (add-type-alist-runes-to-ttree1 type-alist runes0)))
    (cond ((null runes1) ttree)
          ((null runes0) (extend-tag-tree 'lemma runes1 ttree))
          (t (extend-tag-tree 'lemma
                              runes1
                              (remove-tag-from-tag-tree! 'lemma ttree))))))

(defun process-assumptions-ttree (assns ttree)

; Assns is a list of assumptions records.  We extend ttree with all runes in
; assns.

  (cond ((endp assns) ttree)
        (t (process-assumptions-ttree
            (cdr assns)
            (add-type-alist-runes-to-ttree (access assumption (car assns)
                                                   :type-alist)
                                           ttree)))))

(defun process-assumptions (forcing-round pspv wrld state)

; This function is called when prove-loop1 appears to have won the
; indicated forcing-round, producing pspv.  We inspect the :tag-tree
; in pspv and determines whether there are forced 'assumptions in it.
; If so, the "win" reported is actually conditional upon the
; successful relieving of those assumptions.  We create an appropriate
; set of clauses to prove, new-clauses, each paired with a list of
; assumnotes.  We also return a modified pspv, new-pspv,
; just like pspv except with the assumptions stripped out of its
; :tag-tree.  We do the output related to explaining all this to the
; user and return (mv new-clauses new-pspv state).  If new-clauses is
; nil, then the proof is really done.  Otherwise, we are obliged to
; prove new-clauses under new-pspv and should do so in another "round"
; of forcing.

  (let ((n (count-assumptions (access prove-spec-var pspv :tag-tree))))
    (pprogn
     (cond
      ((= n 0)
       (pprogn

; We normally print "Q.E.D." for a successful proof done in gag-mode even if
; proof output is inhibited.  However, if summary output is also inhibited,
; then we guess that the user probably would prefer not to be bothered seeing
; the "Q.E.D.".

        (if (and (saved-output-token-p 'prove state)
                 (member-eq 'prove (f-get-global 'inhibit-output-lst state))
                 (not (member-eq 'summary (f-get-global 'inhibit-output-lst
                                                        state))))
            (fms "Q.E.D.~%" nil (proofs-co state) state nil)
          state)
        (io? prove nil state nil
             (fms "Q.E.D.~%" nil (proofs-co state) state nil))))
      (t
       (io? prove nil state (n)
            (fms "q.e.d. (given ~n0 forced ~#1~[hypothesis~/hypotheses~])~%"
                 (list (cons #\0 n)
                       (cons #\1 (if (= n 1) 0 1)))
                 (proofs-co state) state nil))))
     (mv-let
      (n0 assns pairs ttree1)
      (extract-and-clausify-assumptions
       nil ;;; irrelevant with only-immediatep = nil
       (access prove-spec-var pspv :tag-tree)
       nil ;;; all assumptions, not only-immediatep

; Note: We here obtain the enabled structure.  Because the rewrite-constant of
; the pspv is restored after being smashed by hints, we know that this enabled
; structure is in fact the one in the pspv on which prove was called, which is
; the global enabled structure if prove was called by defthm.

       (access rewrite-constant
               (access prove-spec-var pspv
                       :rewrite-constant)
               :current-enabled-structure)
       wrld
       (access rewrite-constant
               (access prove-spec-var pspv
                       :rewrite-constant)
               :splitter-output))
      (cond
       ((= n0 0)
        (mv nil pspv state))
       (t
        (pprogn
         (process-assumptions-msg
          forcing-round n0 (length assns) pairs state)
         (mv pairs
             (change prove-spec-var pspv
                     :tag-tree (process-assumptions-ttree assns ttree1)

; Note: In an earlier version of this code, we failed to set :otf-flg here and
; that caused us to backup and try to prove the original thm (i.e., "Goal") by
; induction.

                     :otf-flg t)
             state))))))))

(defun do-not-induct-msg (forcing-round pool-lst state)

; We print a message explaining that because of :do-not-induct, we quit.

; This function increments timers.  Upon entry, the accumulated time is
; charged to 'prove-time.  The time spent in this function is charged
; to 'print-time.

  (io? prove nil state
       (forcing-round pool-lst)
       (pprogn
        (increment-timer 'prove-time state)

; It is probably a good idea to keep the following wording in sync with
; push-clause-msg1.

        (fms "Normally we would attempt to prove ~@0 by induction.  However, a ~
             :DO-NOT-INDUCT hint was supplied to abort the proof attempt.~|"
             (list (cons #\0
                         (tilde-@-pool-name-phrase
                          forcing-round
                          pool-lst)))
             (proofs-co state)
             state
             nil)
        (increment-timer 'print-time state))))

(defun prove-loop2 (forcing-round pool-lst clauses pspv hints ens wrld ctx
                                  state step-limit)

; We are given some clauses to prove.  Forcing-round and pool-lst are the first
; two fields of the clause-ids for the clauses.  The pool of the prove spec
; var, pspv, in general contains some more clauses to work on, as well as some
; clauses tagged 'being-proved-by-induction.  In addition, the pspv contains
; the proper settings for the induction-hyp-terms and induction-concl-terms.

; Actually, when we are beginning a forcing round other than the first, clauses
; is really a list of pairs (assumnotes . clause).

; We pour all the clauses over the waterfall.  They tumble into the pool in
; pspv.  If the pool is then empty, we are done.  Otherwise, we pick one to
; induct on, do the induction and repeat.

; We return a tuple (mv new-step-limit error value state).  Either we cause an
; error (i.e., return a non-nil error as the second result), or else the value
; result is the final tag-tree.  That tag-tree might contain some byes,
; indicating that the proof has failed.

; WARNING:  A non-erroneous return is not equivalent to success!

  (sl-let (erp pspv jppl-flg state)
          (pstk
           (waterfall forcing-round pool-lst clauses pspv hints ens wrld
                      ctx state step-limit))
          (cond
           (erp (mv step-limit t nil state))
           (t
            (mv-let
             (signal pool-lst clauses hint-settings pspv state)
             (pstk
              (pop-clause forcing-round pspv jppl-flg state))
             (cond
              ((eq signal 'win)
               (mv-let
                (pairs new-pspv state)
                (pstk
                 (process-assumptions forcing-round pspv wrld state))
                (mv-let
                 (erp ttree state)
                 (accumulate-ttree-and-step-limit-into-state
                  (access prove-spec-var new-pspv :tag-tree)
                  step-limit
                  state)
                 (assert$
                  (null erp)
                  (cond ((null pairs)
                         (mv step-limit nil ttree state))
                        (t (prove-loop2 (1+ forcing-round)
                                        nil
                                        pairs
                                        (initialize-pspv-for-gag-mode new-pspv)
                                        hints ens wrld ctx state
                                        step-limit)))))))

; The following case can probably be removed.  It is probably left over from
; some earlier implementation of pop-clause.  The earlier code for the case
; below returned (value (access prove-spec-var pspv :tag-tree)), this case, and
; was replaced by the hard error on 5/5/00.

              ((eq signal 'bye)
               (mv
                step-limit
                t
                (er hard ctx
                    "Surprising case in prove-loop2; please contact the ACL2 ~
                     implementors!")
                state))
              ((eq signal 'lose)
               (mv step-limit t nil state))
              ((and (cdr (assoc-eq :do-not-induct hint-settings))
                    (not (assoc-eq :induct hint-settings)))

; There is at least one goal left to prove, yet :do-not-induct is currently in
; force.  How can that be?  The user may have supplied :do-not-induct t while
; also supplying :otf-flg t.  In that case, push-clause will return a "hit".  We
; believe that the hint-settings current at this time will reflect the
; appropriate action if :do-not-induct t is intended here, i.e., the test above
; will put us in this case and we will abort the proof.

               (pprogn (do-not-induct-msg forcing-round pool-lst state)
                       (mv step-limit t nil state)))
              (t
               (mv-let
                (signal clauses pspv state)
                (pstk
                 (induct forcing-round pool-lst clauses hint-settings pspv wrld
                         ctx state))

; We do not call maybe-warn-about-theory-from-rcnsts below, because we already
; made such a call before the goal was pushed for proof by induction.

                (cond ((eq signal 'lose)
                       (mv step-limit t nil state))
                      (t (prove-loop2 forcing-round
                                      pool-lst
                                      clauses
                                      pspv
                                      hints
                                      ens
                                      wrld
                                      ctx
                                      state
                                      step-limit)))))))))))

(defun prove-loop1 (forcing-round pool-lst clauses pspv hints ens wrld ctx
                                  state)
  (sl-let
   (erp val state)
   (catch-step-limit
    (prove-loop2 forcing-round pool-lst clauses pspv hints ens wrld ctx
                 state
                 (initial-step-limit wrld state)))
   (pprogn (f-put-global 'last-step-limit step-limit state)
           (mv erp val state))))

(defun print-summary-on-error (state)

; This function is called only when a proof attempt causes an error rather than
; merely returning (mv non-nil val state); see prove-loop0.  We formerly called
; this function pstack-and-gag-state, but now we also print the runes, and
; perhaps we will print additional information in the future.

; An alternative approach, which might avoid the need for this function, is
; represented by the handling of *acl2-time-limit* in our-abort.  The idea
; would be to continue automatically from the interrupt, but with a flag saying
; that the proof should terminate immediately.  Then any proof procedure that
; checks for this flag would return with some sort of error.  If no such proof
; procedure is invoked, then a second interrupt would immediately take effect.
; An advantage of such an alternative approach is that it would use a normal
; control flow, updating suitable state globals so that a normal call of
; print-summary could be made.  We choose, however, not to pursue this
; approach, since it might risk annoying users who find that they need to
; provide two interrupts, and because it seems inherently a bit tricky and
; perhaps easy to get wrong.

; We conclude with remarks for the case that waterfall parallelism is enabled.

; When the user has to interrupt a proof twice before it quits, the prover will
; call this function.  Based on observation by Rager, the pstack tends to be
; long and irrelevant in this case.  So, we disable the printing of the pstack
; when waterfall parallelism is enabled and waterfall-printing is something
; other than :full.  We considered not involving the current value for
; waterfall-printing, but using the :full setting is a strange thing to begin
; with.  So, we make the decision that if a user goes to the effort to use the
; :full waterfall-printing mode, that maybe they'd like to see the pstack after
; all.

; The below #+acl2-par change in definition also results in not printing
; gag-state under these conditions.  However, this is effectively a no-op,
; because the parallel waterfall does not save anything to gag-state anyway.

  (let ((chan (proofs-co state))
        (acc-ttree (f-get-global 'accumulated-ttree state)))
    (pprogn
     (clear-event-data state)
     (io? summary nil state (chan acc-ttree)
          (pprogn
           (newline chan state)
           (print-rules-and-hint-events-summary acc-ttree state)
           (print-system-attachments-summary state)))
     (cond
      #+acl2-par
      ((and (f-get-global 'waterfall-parallelism state)
            (not (eql (f-get-global 'waterfall-printing state) :full)))
       state)
      (t
       (pprogn
        (newline chan state)
        (princ$ "Here is the current pstack [see :DOC pstack]:" chan state)
        (mv-let (erp val state)
                (pstack)
                (declare (ignore erp val))
                (print-gag-state state))))))))

(defun prove-loop0 (clauses pspv hints ens wrld ctx state)

; Warning: This function assumes that *acl2-time-limit* has already been
; let-bound in raw Lisp by bind-acl2-time-limit.

; The perhaps unusual structure below is intended to invoke
; print-summary-on-error only when there is a hard error such as an interrupt.
; In the normal failure case, the pstack is not printed and the key checkpoint
; summary (from the gag-state) is printed after the summary.

  (state-global-let*
   ((guard-checking-on nil) ; see the Essay on Guard Checking
    (in-prove-flg t))
   (mv-let (interrupted-p erp-val state)
           (acl2-unwind-protect
            "prove-loop"
            (mv-let (erp val state)
                    (prove-loop1 0 nil clauses pspv hints ens wrld ctx
                                 state)
                    (mv nil (cons erp val) state))
            (print-summary-on-error state)
            state)
           (cond (interrupted-p (mv t nil state))
                 (t (mv (car erp-val) (cdr erp-val) state))))))

(defun prove-loop (clauses pspv hints ens wrld ctx state)

; We either cause an error or return a ttree.  If the ttree contains
; :byes, the proof attempt has technically failed, although it has
; succeeded modulo the :byes.

  #-acl2-loop-only
  (setq *deep-gstack* nil) ; in case we never call initial-gstack
  (prog2$ (clear-pstk)
          (pprogn
           (increment-timer 'other-time state)
           (f-put-global 'bddnotes nil state)
           (if (gag-mode)
               (pprogn (f-put-global 'gag-state *initial-gag-state* state)
                       (f-put-global 'gag-state-saved nil state))
             state)
           (mv-let (erp ttree state)
                   (bind-acl2-time-limit ; make *acl2-time-limit* be let-bound
                    (prove-loop0 clauses pspv hints ens wrld ctx state))
                   (pprogn
                    (increment-timer 'prove-time state)
                    (cond
                     (erp (mv erp nil state))
                     (t (value ttree))))))))

(defmacro make-pspv (ens wrld state &rest args)

; This macro is similar to make-rcnst, which is a little easier to understand.
; (make-pspv ens w) will make a pspv that is just *empty-prove-spec-var* except
; that the rewrite constant is (make-rcnst ens w).  More generally, you may use
; args to supply a list of alternating keyword/value pairs to override the
; default settings.  E.g.,

; (make-pspv ens w :rewrite-constant rcnst :displayed-goal dg)

; will make a pspv that is like the empty one except for the two fields
; listed above.

; Note: Ens and wrld are only used in the default setting of the
; :rewrite-constant.  If you supply a :rewrite-constant in args, then ens and
; wrld are actually irrelevant.

  `(change prove-spec-var
           (change prove-spec-var *empty-prove-spec-var*
                   :rewrite-constant (make-rcnst ,ens ,wrld ,state
                                                 :splitter-output
                                                 (splitter-output)))
           ,@args))

(defun chk-assumption-free-ttree (ttree ctx state)

; Let ttree be the ttree about to be returned by prove.  We do not want this
; tree to contain any 'assumption tags because that would be a sign that an
; assumption got ignored.  For similar reasons, we do not want it to contain
; any 'fc-derivation tags -- assumptions might be buried therein.  This
; function checks these claimed invariants of the final ttree and causes an
; error if they are violated.

; This check is stronger than necessary, of course, since an fc-derivation
; object need not contain an assumption.  See also contains-assumptionp for a
; slightly more expensive, but more precise, check.

; A predicate version of this function is assumption-free-ttreep and it should
; be kept in sync with this function, as should chk-assumption-free-ttree-1.

; While this function causes a hard error, its functionality is that of a soft
; error because it is so like our normal checkers.

  (cond ((tagged-objectsp 'assumption ttree)
         (mv t
             (er hard ctx
                 "The 'assumption ~x0 was found in the final ttree!"
                 (car (tagged-objects 'assumption ttree)))
             state))
        ((tagged-objectsp 'fc-derivation ttree)
         (mv t
             (er hard ctx
                 "The 'fc-derivation ~x0 was found in the final ttree!"
                 (car (tagged-objects 'fc-derivation ttree)))
             state))
        (t (value nil))))

#+(and write-arithmetic-goals (not acl2-loop-only))
(when (not (boundp '*arithmetic-goals-fns*))
  (defconstant *arithmetic-goals-fns*
    '(< = abs acl2-numberp binary-* binary-+ case-split complex-rationalp
        denominator equal evenp expt fix floor force if iff ifix implies integerp
        mod natp nfix not numerator oddp posp rationalp synp unary-- unary-/
        zerop zip zp signum booleanp nonnegative-integer-quotient rem truncate
        ash lognot binary-logand binary-logior binary-logxor)))

#+(and write-arithmetic-goals (not acl2-loop-only))
(when (not (boundp '*arithmetic-goals-filename*))
  (defconstant *arithmetic-goals-filename*
; Be sure to delete ~/write-arithmetic-goals.lisp before starting a regression.
; (This is done by GNUmakefile.)
    (let ((home (our-user-homedir-pathname)))
      (cond (home
             (merge-pathnames home "write-arithmetic-goals.lisp"))
            (t (error "Unable to determine (user-homedir-pathname)."))))))

(defun push-current-acl2-world (name state)
  (declare (xargs :guard (and (symbolp name)
                              (f-boundp-global 'acl2-world-alist state)
                              (alistp (f-get-global 'acl2-world-alist state)))))
  (prog2$ (or (symbolp name) ; always true if guard is checked
              (er hard 'push-current-acl2-world
                  "It is illegal to call push-current-acl2-world with ~x0, ~
                   because it is not a symbol."
                  name))
          (f-put-global 'acl2-world-alist
                        (acons name
                               (w state)
                               (f-get-global 'acl2-world-alist state))
                        state)))

(defun pop-current-acl2-world (name state)
  (declare (xargs :guard (and (symbolp name)
                              (f-boundp-global 'acl2-world-alist state)
                              (alistp (f-get-global 'acl2-world-alist state))
                              (assoc-eq name (f-get-global 'acl2-world-alist
                                                           state)))))
  (prog2$
   (or (symbolp name) ; always true if guard is checked
       (er hard 'pop-current-acl2-world
           "It is illegal to call pop-current-acl2-world with ~x0, because ~
            it is not a symbol."
           name))
   (let ((pair (assoc-eq name (f-get-global 'acl2-world-alist state))))
     (cond
      ((null pair)
       (prog2$
        (er hard 'pop-current-acl2-world
            "Attempted to pop the name ~x0, which is not bound in ~x1."
            name
            '(@ acl2-world-alist))
        state))
      (t
       (pprogn
        (set-w! (cdr pair) state)
        (f-put-global 'acl2-world-alist
                      (delete-assoc-eq name
                                       (f-get-global 'acl2-world-alist state))
                      state)))))))

(defmacro revert-world (form)

; This variant of revert-world-on-error reverts the world after execution of
; form, whether or not there is an error.

  `(acl2-unwind-protect
    "revert-world"
    (pprogn (push-current-acl2-world 'revert-world state)
            ,form)
    (pop-current-acl2-world 'revert-world state)
    (pop-current-acl2-world 'revert-world state)))

(defun prove (term pspv hints ens wrld ctx state)

; Term is a translated term.  Hints is a list of pairs as returned by
; translate-hints.

; We try to prove term using the given hints and the rules in wrld.

; Note: Having prove use hints is a break from nqthm, where only
; prove-lemma used hints.

; This function returns the traditional three values of an error
; producing/output producing function.  The first value is a Boolean
; that indicates whether an error occurred.  We cause an error if we
; terminate without proving term.  Hence, if the first result is nil,
; term was proved.  The second is a ttree that describes the proof, if
; term is proved.  The third is the final value of state.

; Commemorative Plaque:

; We began the creation of the ACL2 with an empty GNU Emacs buffer on
; August 14, 1989.  The first few days were spent writing down the
; axioms for the most primitive functions.  We then began writing
; experimental applicative code for macros such as cond and
; case-match.  The first weeks were dizzying because of the confusion
; in our minds over what was in the logic and what was in the
; implementation.  On November 3, 1989, prove was debugged and
; successfully did the associativity of append.  During that 82 days
; we worked our more or less normal 8 hours, plus an hour or two on
; weekday nights.  In general we did not work weekends, though there
; might have been two or three where an 8 hour day was put in.  We
; worked separately, "contracting" with one another to do the various
; parts and meeting to go over the code.  Bill Schelter was extremely
; helpful in tuning akcl for us.  Several times we did massive
; rewrites as we changed the subset or discovered new programming
; styles.  During that period Moore went to the beach at Rockport one
; weekend, to Carlsbad Caverns for Labor Day, to the University of
; Utah for a 4 day visit, and to MIT for a 4 day visit.  Boyer taught
; at UT from September onwards.  These details are given primarily to
; provide a measure of how much effort it was to produce this system.
; In all, perhaps we have spent 60 8 hour days each on ACL2, or about
; 1000 man hours.  That of course ignores totally the fact that we
; have thought about little else during the past three months, whether
; coding or not.

; The system as it stood November 3, 1989, contained the complete
; nqthm rewriter and simplifier (including metafunctions, compound
; recognizers, linear and a trivial cut at congruence relations that
; did not connect to the user-interface) and induction.  It did not
; include destructor elimination, cross-fertilization, generalization
; or the elimination of irrelevance.  It did not contain any notion of
; hints or disabledp.  The system contained full fledged
; implementations of the definitional principle (with guards and
; termination proofs) and defaxiom (which contains all of the code to
; generate and store rules).  The system did not contain the
; constraint or functional instantiation events or books.  We have not
; yet had a "code walk" in which we jointly look at every line.  There
; are known bugs in prove (e.g., induction causes a hard error when no
; candidates are found).

; Matt Kaufmann officially joined the project in August, 1993.  He had
; previously generated a large number of comments, engaged in a number of
; design discussions, and written some code.

; Bob Boyer requested that he be removed as a co-author of ACL2 in April, 1995,
; because, in his view, he has worked so much less on the project in the last
; few years than Kaufmann and Moore.

; End of Commemorative Plaque

; This function increments timers.  Upon entry, the accumulated time is
; charged to 'other-time.  The time spent in this function is divided
; between both 'prove-time and to 'print-time.

  (cond
   ((ld-skip-proofsp state) (value nil))
   (t
    #+(and write-arithmetic-goals (not acl2-loop-only))
    (when (ffnnames-subsetp term *arithmetic-goals-fns*)
      (with-open-file (str *arithmetic-goals-filename*
                           :direction :output
                           :if-exists :append
                           :if-does-not-exist :create)
        (let ((*print-pretty* nil)
              (*package* (find-package-fast "ACL2"))
              (*readtable* *acl2-readtable*)
              (*print-escape* t)
              *print-level*
              *print-length*)
          (prin1 term str)
          (terpri str)
          (force-output str))))
    (progn$
     (initialize-brr-stack state)
     (initialize-fc-wormhole-sites)
     (pprogn
      (f-put-global 'saved-output-reversed nil state)
      (push-current-acl2-world 'saved-output-reversed state)
      (f-put-global 'saved-output-p
                    (not (member-eq 'PROVE
                                    (f-get-global 'inhibit-output-lst state)))
                    state)
      (push-io-record
       :ctx
       (list 'mv-let
             '(col state)
             '(fmt "Output replay for: "
                   nil (standard-co state) state nil)
             (list 'mv-let
                   '(col state)
                   (list 'fmt-ctx
                         (list 'quote ctx)
                         'col
                         '(standard-co state)
                         'state)
                   '(declare (ignore col))
                   '(newline (standard-co state) state)))
       state)
      (er-let* ((ttree1 (prove-loop (list (list term))
                                    (change prove-spec-var pspv
                                            :user-supplied-term term
                                            :orig-hints hints)
                                    hints ens wrld ctx state)))
        (er-progn
         (chk-assumption-free-ttree ttree1 ctx state)
         (let ((byes (tagged-objects :bye ttree1)))
           (cond
            (byes
             (pprogn

; The use of ~*1 below instead of just ~&1 forces each of the defthm forms
; to come out on a new line indented 5 spaces.  As is already known with ~&1,
; it can tend to scatter the items randomly -- some on the left margin and others
; indented -- depending on where each item fits flat on the line first offered.

              (io? prove nil state
                   (wrld byes)
                   (fms "To complete this proof you could try to admit the ~
                        following event~#0~[~/s~]:~|~%~*1~%See the discussion ~
                        of :by hints in :DOC hints regarding the ~
                        name~#0~[~/s~] displayed above.~|"
                        (list (cons #\0 byes)
                              (cons #\1
                                    (list ""
                                          "~|~     ~q*."
                                          "~|~     ~q*,~|and~|"
                                          "~|~     ~q*,~|~%"
                                          (make-defthm-forms-for-byes
                                           byes wrld))))
                        (proofs-co state)
                        state
                        (term-evisc-tuple nil state)))
              (silent-error state)))
            (t (value ttree1)))))))))))

