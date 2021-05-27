; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

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

; This file contains the functions that check the acceptable forms for
; the various classes of rules, the functions that generate the rules
; from the forms, and finally the functions that actually do the adding.
; It also contains various history management and command facilities whose
; implementation is intertwined with the storage of rules, e.g., :pr and
; some monitoring stuff.

; The structure of the file is that we first define the checkers and
; generators for each class of rule.  Each such section has a header
; like that shown below.  When we finish all the individual classes
; we enter the final sections, headed

; Section:  Handling a List of Classes
; Section:  More History Management and Command Stuff
; Section:  The DEFAXIOM Event
; Section:  The DEFTHM Event
; Section:  Some Convenient Abbreviations for Defthm

;---------------------------------------------------------------------------
; Section:  :REWRITE Rules

; In this section we develop the function chk-acceptable-
; rewrite-rule, which checks that all the :REWRITE rules generated
; from a term are legal.  We then develop add-rewrite-rule which does
; the actual generation and addition of the rules to the world.

(defun form-of-rewrite-quoted-constant-rule (equiv lhs rhs)

; The Essay on Rewriting Quoted Constants lists three possible forms, 1, 2, or
; 3, of such rules and this function determines which form we're seeing, or nil
; if lhs and rhs are incompatible with any of the forms.  Note that a Form 3
; lhs must be unifiable with a quoted constant but we put no restrictions on
; the rhs.  Indeed, rhs could be a free variable whose value is selected by
; relieving some hyp!

  (cond ((and (not (eq equiv 'equal))
              (quotep lhs)
              (quotep rhs))
         1)
        ((and (not (eq equiv 'equal))
              (nvariablep lhs)
              (not (fquotep lhs))
              (symbolp (ffn-symb lhs))
              (cdr lhs)
              (null (cddr lhs))
              (variablep (fargn lhs 1))
              (eq (fargn lhs 1) rhs))
         2)
        ((or (variablep lhs)
             (fquotep lhs)
             (member-eq (ffn-symb lhs) *one-way-unify1-implicit-fns*))
         3)
        (t nil)))

; We use the following functions to determine the sense of the conclusion
; as a :REWRITE rule.

(defun interpret-term-as-rewrite-rule2 (qc-flg name hyps equiv lhs rhs wrld)

; Qc-flg is t if we are processing for a :rewrite-quoted-constant rule rather
; than a :rewrite rule.

  (cond
   ((equal lhs rhs)
    (msg
     "A ~x0 rule generated from ~x1 is illegal because it rewrites the ~
      term ~x2 to itself!  This can happen even when you submit a rule whose ~
      left and right sides appear to be different, in the case that those two ~
      sides represent the same term (for example, after macroexpansion).  For ~
      general information about rewrite rules in ACL2, see :DOC rewrite.  You ~
      may wish to consider submitting a DEFTHM event ending with ~
      :RULE-CLASSES NIL."
     (if qc-flg :rewrite-quoted-constant :rewrite)
     name
     lhs))
   ((and qc-flg
         (not (form-of-rewrite-quoted-constant-rule equiv lhs rhs)))
    (msg
     "A :REWRITE-QUOTED-CONSTANT rule generated from ~x0 is illegal because ~
      the conclusion is not compatible with any of the allowed forms.  To be ~
      Form [1], the conclusion must be an equivalence (other than EQUAL) ~
      between two quoted constants.  To be Form [2], the conclusion must be ~
      an equivalence (other than EQUAL) between, on the left, a call of a ~
      monadic function symbol on a variable symbol and, on the right, that ~
      same variable symbol.  To be of Form [3], the conclusion must be an ~
      equivalence relation and the left-hand side must be a variable, a ~
      quoted constant, or a call of one of the function symbols in ~
      *ONE-WAY-UNifY1-IMPLICIT-FNS* so that the left-hand side can match a ~
      quoted constant.  But the conclusion of ~x0 is ~x1."
     name
     (list equiv lhs rhs)))
   ((and (not qc-flg)
         (or (variablep lhs)
             (fquotep lhs)
             (flambda-applicationp lhs)))
    (msg
     "A :REWRITE rule generated from ~x0 is illegal because it rewrites the ~
      ~@1 ~x2.  For general information about rewrite rules in ACL2, see :DOC ~
      rewrite."
     name
     (cond ((variablep lhs) "variable symbol")
           ((fquotep lhs) "quoted constant")
           ((flambda-applicationp lhs) "LET-expression")
           (t (er hard 'interpret-term-as-rewrite-rule2
                  "Implementation error: forgot a case.  LHS:~|~x0."
                  lhs)))
     lhs))
   (t (let ((bad-synp-hyp-msg (bad-synp-hyp-msg
                               hyps (all-vars lhs) nil wrld)))
        (cond
         (bad-synp-hyp-msg
          (msg
           "A ~x0 rule generated from ~x1 is illegal because ~@2"
           (if qc-flg :rewrite-quoted-constant :rewrite)
           name
           bad-synp-hyp-msg))
         (t nil))))))

(defun interpret-term-as-rewrite-rule1 (term equiv-okp ens wrld)

; Here we do the work described in interpret-term-as-rewrite-rule.  If
; equiv-okp is nil, then no special treatment is given to equivalence relations
; other than equal, iff, and members of *equality-aliases*.

  (cond ((variablep term) (mv 'iff term *t* nil))
        ((fquotep term) (mv 'iff term *t* nil))
        ((member-eq (ffn-symb term) *equality-aliases*)
         (mv 'equal (remove-lambdas (fargn term 1)) (fargn term 2) nil))
        ((flambdap (ffn-symb term))
         (interpret-term-as-rewrite-rule1
          (subcor-var (lambda-formals (ffn-symb term))
                      (fargs term)
                      (lambda-body (ffn-symb term)))
          equiv-okp ens wrld))
        ((if equiv-okp
             (equivalence-relationp (ffn-symb term) wrld)
           (member-eq (ffn-symb term) '(equal iff)))
         (let ((lhs (remove-lambdas (fargn term 1))))
           (mv-let (equiv ttree)
             (cond ((eq (ffn-symb term) 'iff)
                    (mv-let
                      (ts ttree)
                      (type-set lhs nil nil nil ens wrld nil
                                nil nil)
                      (cond ((ts-subsetp ts *ts-boolean*)
                             (mv-let
                               (ts ttree)
                               (type-set (fargn term 2) nil nil nil ens
                                         wrld ttree nil nil)
                               (cond ((ts-subsetp ts *ts-boolean*)
                                      (mv 'equal ttree))
                                     (t (mv 'iff nil)))))
                            (t (mv 'iff nil)))))
                   (t (mv (ffn-symb term) nil)))
             (mv equiv lhs (fargn term 2) ttree))))
        ((eq (ffn-symb term) 'not)
         (mv 'equal (remove-lambdas (fargn term 1)) *nil* nil))
        (t (mv-let (ts ttree)
             (type-set term nil nil nil ens wrld nil nil nil)
             (cond ((ts-subsetp ts *ts-boolean*)
                    (mv 'equal (remove-lambdas term) *t* ttree))
                   (t (mv 'iff (remove-lambdas term) *t* nil)))))))

(defun interpret-term-as-rewrite-rule (qc-flg name hyps term ctx ens wrld)

; NOTE: Term is assumed to have had remove-guard-holders applied, which in
; particular implies that term is in quote-normal form.

; Qc-flg indicates that we are processing a :rewrite-quoted-constant rule.

; This function returns five values.  The first can be a msg for printing an
; error message.  Otherwise the first is nil, in which case the second is an
; equivalence relation, eqv; the next two are terms, lhs and rhs, such that
; (eqv lhs rhs) is propositionally equivalent to term; and the last is an
; 'assumption-free ttree justifying the claim.

; If ctx is non-nil, then print an observation, with that ctx, when we are
; avoiding the use of an equivalence relation.  Otherwise do not print that
; observation.

  (mv-let
    (eqv lhs rhs ttree)
    (interpret-term-as-rewrite-rule1 term t ens wrld)

; Note that we are insensitive to the qc-flg in the above call.  We deconstruct
; term the same way whether it's to be used as a :rewrite rule or
; :rewrite-quoted-constant rule.  But we then check slightly different
; restrictions.

    (let ((msg (interpret-term-as-rewrite-rule2
                qc-flg name hyps eqv lhs rhs wrld)))
      (cond
       (msg

; We try again, this time with equiv-okp = nil to avoid errors for a form such
; as the following.  Its evaluation caused a hard Lisp error in Version_4.3
; during the second pass of the encapsulate at the final defthm, and is based
; closely on an example sent to us by Jared Davis.

;   (encapsulate
;    ()
;    (defun my-equivp (x y)
;      (equal (nfix x) (nfix y)))
;    (local
;     (defthm my-equivp-reflexive
;       (my-equivp x x)))
;    (defequiv my-equivp)
;    (defthm my-equivp-reflexive
;      (my-equivp x x)))

        (mv-let
          (eqv2 lhs2 rhs2 ttree2)
          (interpret-term-as-rewrite-rule1 term nil ens wrld)
          (cond
           ((interpret-term-as-rewrite-rule2 qc-flg name hyps
                                             eqv2 lhs2 rhs2 wrld)
            (mv msg eqv lhs rhs ttree))
           (t (prog2$
               (and ctx
                    (observation-cw ctx
                                    "The proposed rewrite rule ~x0 may ~
                                     suggest a conclusion of the form (Equiv ~
                                     Lhs Rhs) where:~|  Equiv: ~x1~|  Lhs:   ~
                                     ~x2~|  Rhs:   ~x3~|But such a rewrite ~
                                     rule would be illegal, so the conclusion ~
                                     is treated as follows instead.~|  Equiv: ~
                                     ~x4~|  Lhs:   ~x5~|  Rhs:   ~x6~|"
                                    name
                                    eqv
                                    (untranslate lhs nil wrld)
                                    (untranslate rhs nil wrld)
                                    eqv2
                                    (untranslate lhs2 nil wrld)
                                    (untranslate rhs2 nil wrld)))
               (mv nil eqv2 lhs2 rhs2 ttree2))))))
       (t (mv nil eqv lhs rhs ttree))))))

; We inspect the lhs and some hypotheses with the following functions to
; determine if non-recursive defuns will present a problem to the user.

(mutual-recursion

(defun non-recursive-fnnames-alist-rec (term ens wrld acc)

; Accumulate, into acc, an alist that associates each enabled non-recursive
; function symbol fn of term either with the base-symbol of its most recent
; definition rune or with nil.  Our meaning of "enabled" and "non-recursive" is
; with respect to that rune (which exists except for lambdas).  We associate to
; a value of nil for two cases of the key: a lambda, and when that rune is the
; rune of the original definition.  We do not dive into lambda bodies.

  (declare (xargs :guard (and (pseudo-termp term)
                              (enabled-structure-p ens)
                              (plist-worldp wrld)
                              (alistp acc))))
  (cond
   ((variablep term) acc)
   ((fquotep term) acc)
   ((flambda-applicationp term)
    (non-recursive-fnnames-alist-rec-lst
     (fargs term) ens wrld
     (if (assoc-equal (ffn-symb term) acc)
         acc
       (acons (ffn-symb term) nil acc))))
   (t (non-recursive-fnnames-alist-rec-lst
       (fargs term) ens wrld
       (cond
        ((assoc-eq (ffn-symb term) acc)
         acc)
        (t (let ((def-body (def-body (ffn-symb term) wrld)))
             (cond
              ((and def-body
                    (enabled-numep (access def-body def-body :nume)
                                   ens)
                    (not (access def-body def-body :recursivep)))
               (let ((sym (base-symbol (access def-body def-body :rune))))
                 (acons (ffn-symb term)
                        (if (eq sym (ffn-symb term))
                            nil
                          sym)
                        acc)))
              (t acc)))))))))

(defun non-recursive-fnnames-alist-rec-lst (lst ens wrld acc)
  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (enabled-structure-p ens)
                              (plist-worldp wrld)
                              (alistp acc))))
  (cond ((endp lst) acc)
        (t (non-recursive-fnnames-alist-rec-lst
            (cdr lst) ens wrld
            (non-recursive-fnnames-alist-rec (car lst) ens wrld acc)))))
)

(defun non-recursive-fnnames-alist (term ens wrld)

; See non-recursive-fnnames-alist-rec.  (The present function reverses the
; result, to respect the original order of appearance of function symbols.)

  (reverse (non-recursive-fnnames-alist-rec term ens wrld nil)))


(defun non-recursive-fnnames-alist-lst (lst ens wrld)

; See non-recursive-fnnames-alist-rec.  (The present function takes a list of
; terms; it also reverses the result, to respect the original order of
; appearance of function symbols.)

  (reverse (non-recursive-fnnames-alist-rec-lst lst ens wrld nil)))

; The alist just constructed is odd because it may contain some lambda
; expressions posing as function symbols.  We use the following function
; to transform those into let's just for printing purposes...

(defun hide-lambdas1 (formals)

; CLTL uses # as the "too deep to show" symbol.  But if we use it, we
; print vertical bars around it.  Until we modify the printer to support
; some kind of hiding, we'll use Interlisp's ampersand.

  (cond ((null formals) nil)
        (t (cons (list (car formals) '&)
                 (hide-lambdas1 (cdr formals))))))

(defun hide-lambdas (lst)
  (cond ((null lst) nil)
        (t (cons (if (flambdap (car lst))
                     (list 'let (hide-lambdas1 (lambda-formals (car lst)))
                           (lambda-body (car lst)))
                   (car lst))
                 (hide-lambdas (cdr lst))))))

; Now we develop the stuff to determine if we have a permutative :REWRITE rule.

(defun variantp (term1 term2)

; This function returns two values:  A flag indicating whether the two
; terms are variants and the substitution which when applied to term1
; yields term2.

  (mv-let (ans unify-subst)
    (one-way-unify term1 term2)
    (cond
     (ans
      (let ((range (strip-cdrs unify-subst)))
        (mv (and (symbol-listp range)
                 (no-duplicatesp-equal range))
            unify-subst)))
     (t (mv nil nil)))))

(mutual-recursion

(defun surrounding-fns1 (vars term fn acc)

; See surrounding-fns for the definition of the notions used below.

; Vars is a list of variables.  Term is a term that occurs as an argument in
; some (here unknown) application of the function fn.  Acc is either a list of
; function symbols or the special token 'has-lambda.  Observe that if term is a
; var in vars, then fn surrounds some var in vars in whatever larger term
; contained the application of fn.

; If term is a var in vars, we collect fn into acc.  If term is not a var, we
; collect into acc all the function symbols surrounding any element of vars.
; However, if we ever encounter a lambda application surrounding a var in vars
; (including fn), we set acc to the special token 'has-lambda, and collections
; cease thereafter.

  (cond
   ((variablep term)
    (cond
     ((member-eq term vars)
      (if (or (eq acc 'has-lambda)
              (not (symbolp fn)))
          'has-lambda
          (add-to-set-eq fn acc)))
     (t acc)))
   ((fquotep term) acc)
   (t (surrounding-fns-lst vars (fargs term) (ffn-symb term) acc))))

(defun surrounding-fns-lst (vars term-list fn acc)
  (cond
   ((null term-list) acc)
   (t (surrounding-fns-lst vars (cdr term-list) fn
                           (surrounding-fns1 vars (car term-list) fn acc)))))

)

(defun surrounding-fns (vars term)

; This function returns the list of all functions fn surrounding, in term, any
; var in vars, except that if that list includes a lambda expression we return
; nil.

; We make this precise as follows.  Let us say a function symbol or lambda
; expression, fn, ``surrounds'' a variable v in term if there is a subterm of
; term that is an application of fn and v is among the actuals of that
; application.  Thus, in the term (fn (g x) (h (d x)) y), g and d both surround
; x and fn surrounds y.  Note that h surrounds no variable.

; Consider the set, s, of all functions fn such that fn surrounds a variable
; var in term, where var is a member of the list of variables var.  If s
; contains a lambda expression, we return nil; otherwise we return s.

  (cond
   ((or (variablep term)
        (fquotep term))
    nil)
   (t
    (let ((ans (surrounding-fns-lst vars (fargs term) (ffn-symb term) nil)))
      (if (eq ans 'has-lambda)
          nil
        ans)))))

(defun loop-stopper1 (alist vars lhs)
  (cond ((null alist) nil)
        ((member-eq (car (car alist))
                    (cdr (member-eq (cdr (car alist)) vars)))
         (cons (list* (caar alist)
                      (cdar alist)
                      (surrounding-fns (list (caar alist) (cdar alist)) lhs))
               (loop-stopper1 (cdr alist) vars lhs)))
        (t (loop-stopper1 (cdr alist) vars lhs))))

(defun loop-stopper (lhs rhs)

; If lhs and rhs are variants (possibly after expanding lambdas in rhs; see
; below), we return the "expansion" (see next paragraph) of the subset of the
; unifying substitution containing those pairs (x . y) in which a variable
; symbol (y) is being moved forward (to the position of x) in the print
; representation of the term.  For example, suppose lhs is (foo x y z) and rhs
; is (foo y z x).  Then both y and z are moved forward, so the loop-stopper is
; the "expansion" of '((y . z) (x . y)).  This function exploits the fact that
; all-vars returns the set of variables listed in reverse print-order.

; In the paragraph above, the "expansion" of a substitution ((x1 .  y1) ... (xn
; . yn)) is the list ((x1 y1 . fns-1) ... (xn yn .  fns-n)), where fns-i is the
; list of function symbols of subterms of lhs that contain xi or yi (or both)
; as a top-level argument.  Exception: If any such "function symbol" is a
; LAMBDA, then fns-i is nil.

; Note: John Cowles first suggested the idea that led to the idea of invisible
; function symbols as implemented here.  Cowles observation was that it would
; be very useful if x and (- x) were moved into adjacency by permutative rules.
; His idea was to redefine term-order so that those two terms were of virtually
; equal weight.  Our notion of invisible function symbols and the handling of
; loop-stopper is meant to address Cowles original concern without complicating
; term-order, which is used in places besides permutative rewriting.

  (mv-let (ans unify-subst)
    (variantp lhs

; We expect lhs and rhs to be the left- and right-hand sides of rewrite rules.
; Thus lhs was created by expanding lambdas, but not rhs.  We thus expand
; lambdas here.

              (remove-lambdas rhs))
    (cond (ans (loop-stopper1 unify-subst (all-vars lhs) lhs))
          (t nil))))

(defun remove-irrelevant-loop-stopper-pairs (pairs vars)

; Keep this in sync with irrelevant-loop-stopper-pairs.

  (if pairs
      (if (and (member-eq (caar pairs) vars)
               (member-eq (cadar pairs) vars))

; Note that the use of loop-stopper1 by loop-stopper guarantees that
; machine-constructed loop-stoppers only contain pairs (u v . fns) for
; which u and v both occur in the lhs of the rewrite rule.  Hence, it
; is reasonable to include the test above.

          (cons (car pairs)
                (remove-irrelevant-loop-stopper-pairs (cdr pairs) vars))
        (remove-irrelevant-loop-stopper-pairs (cdr pairs) vars))
    nil))

(defun put-match-free-value (match-free-value rune wrld)
  (cond
   ((eq match-free-value :all)
    (global-set 'free-var-runes-all
                (cons rune (global-val 'free-var-runes-all wrld))
                wrld))
   ((eq match-free-value :once)
    (global-set 'free-var-runes-once
                (cons rune (global-val 'free-var-runes-once wrld))
                wrld))
   ((null match-free-value)
    wrld)
   (t
    (er hard 'put-match-free-value
        "Internal ACL2 error (called put-match-free-value with ~
         match-free-value equal to ~x0).  Please contact the ACL2 implementors."
        match-free-value))))

(defun free-vars-in-hyps (hyps bound-vars wrld)

; Let hyps be a list of terms -- the hypotheses to some :REWRITE rule.
; Let bound-vars be a list of variables.  We find all the variables that
; will be free-vars in hyps when each variable in bound-vars is bound.
; This would be just (set-difference-eq (all-vars1-lst hyps) bound-vars)
; were it not for the fact that relieve-hyps interprets the hypothesis
; (equal v term), where v is free and does not occur in term, as
; a "let v be term..." instead of as a genuine free variable to be found
; by search.

; Warning: Keep this function and free-vars-in-hyps-considering-bind-free
; in sync.

  (cond ((null hyps) nil)
        (t (mv-let
            (forcep flg)
            (binding-hyp-p (car hyps)
                           (pairlis$ bound-vars bound-vars)
                           wrld)

; The odd pairlis$ above just manufactures a substitution with bound-vars as
; bound vars so we can use free-varsp to answer the question, "does
; the rhs of the equality contain any free variables?"  The range of
; the substitution is irrelevant.  If the conjunction above is true, then
; the current hyp is of the form (equiv v term) and v will be chosen
; by rewriting term.  V is not a "free variable".

            (cond ((and flg (not forcep))
                   (free-vars-in-hyps (cdr hyps)
                                      (cons (fargn (car hyps) 1)
                                            bound-vars)
                                      wrld))
                  (t (let ((hyp-vars (all-vars (car hyps))))
                       (union-eq
                        (set-difference-eq hyp-vars bound-vars)
                        (free-vars-in-hyps (cdr hyps)
                                           (union-eq hyp-vars bound-vars)
                                           wrld)))))))))

(defun free-vars-in-hyps-simple (hyps bound-vars)

; This is a simpler variant of free-vars-in-hyps that does not give special
; treatment to terms (equal variable term).

  (cond ((null hyps) nil)
        (t (let ((hyp-vars (all-vars (car hyps))))
             (union-eq (set-difference-eq hyp-vars bound-vars)
                       (free-vars-in-hyps-simple (cdr hyps)
                                                 (union-eq hyp-vars
                                                           bound-vars)))))))

(defun free-vars-in-fc-hyps (triggers hyps concls)

; This function determines whether a rule has free variables, given the
; triggers, hyps and conclusions of the rule.

  (if (endp triggers)
      nil
    (let ((vars (all-vars (car triggers))))
      (or (free-vars-in-hyps-simple hyps vars)
          (or (free-vars-in-hyps-simple concls vars)
              (free-vars-in-fc-hyps (cdr triggers) hyps concls))))))

(defun free-vars-in-hyps-considering-bind-free (hyps bound-vars wrld)

; This function is similar to the above free-vars-in-hyps.  It
; differs in that it takes into account the effects of bind-free.

; Note that a bind-free hypothesis expands to a call to synp in
; which the first arg denotes the vars that are potentially bound
; by the hyp.  This first arg will be either a quoted list of vars
; or 't which we interpret to mean all the otherwise free vars.
; Vars that are potentially bound by a bind-free hyp are not considered
; to be free vars for the purposes of this function.

; Note that a syntaxp hypothesis also expands to a call of synp,
; but that in this case the first arg is 'nil.

; Warning: Keep this function and free-vars-in-hyps in sync.

  (cond ((null hyps) nil)
        (t (mv-let
            (forcep flg)
            (binding-hyp-p (car hyps)
                           (pairlis$ bound-vars bound-vars)
                           wrld)

; The odd pairlis$ above just manufactures a substitution with bound-vars as
; bound vars so we can use free-varsp to answer the question, "does
; the rhs of the equality contain any free variables?"  The range of
; the substitution is irrelevant.  If the conjunction above is true, then
; the current hyp is of the form (equiv v term) and v will be chosen
; by rewriting term.  V is not a "free variable".

            (cond
             ((and flg (not forcep))
              (free-vars-in-hyps-considering-bind-free
               (cdr hyps)
               (cons (fargn (car hyps) 1) bound-vars)
               wrld))
             ((and (ffn-symb-p (car hyps) 'synp)
                   (not (equal (fargn (car hyps) 1) *nil*))) ; not syntaxp hyp
              (cond
               ((equal (fargn (car hyps) 1) *t*)

; All free variables are potentially bound.  The user will presumably not want
; to see a warning in this case.

                nil)
               ((and (quotep (fargn (car hyps) 1))
                     (not (collect-non-legal-variableps
                           (cadr (fargn (car hyps) 1)))))
                (free-vars-in-hyps-considering-bind-free
                 (cdr hyps)
                 (union-eq (cadr (fargn (car hyps) 1)) bound-vars)
                 wrld))
               (t (er hard 'free-vars-in-hyps-considering-bind-free
                      "We thought the first argument of synp in this context ~
                       was either 'NIL, 'T, or else a quoted true list of ~
                       variables, but ~x0 is not!"
                      (fargn (car hyps) 1)))))
             (t (let ((hyp-vars (all-vars (car hyps))))
                  (union-eq (set-difference-eq hyp-vars bound-vars)
                            (free-vars-in-hyps-considering-bind-free
                             (cdr hyps)
                             (union-eq hyp-vars bound-vars)
                             wrld)))))))))

(defun all-vars-in-hyps (hyps)

; We return a list of all the vars mentioned in hyps or, if there is
; a synp hyp whose var-list is 't, we return t.

  (cond
   ((null hyps)
    nil)
   (t
    (let ((vars (all-vars-in-hyps (cdr hyps))))
      (cond
       ((eq vars t) t)
       ((variablep (car hyps))
        (add-to-set-eq (car hyps) vars))
       ((fquotep (car hyps))
        vars)
       ((eq (ffn-symb (car hyps)) 'synp)
        (cond ((equal (fargn (car hyps) 1) *nil*)
               vars)
              ((equal (fargn (car hyps) 1) *t*)
               t)
              ((and (quotep (fargn (car hyps) 1))
                    (not (collect-non-legal-variableps
                          (cadr (fargn (car hyps) 1)))))
               (union-eq (cadr (fargn (car hyps) 1))
                         vars))
              (t (er hard 'free-vars-in-hyps-considering-bind-free
                     "We thought the first argument of synp in this context ~
                      was either 'NIL, 'T, or else a quoted true list of ~
                      variables, but ~x0 is not!"
                     (fargn (car hyps) 1)))))
       (t
        (union-eq (all-vars (car hyps))
                  vars)))))))

(defun match-free-value (match-free hyps pat wrld)
  (or match-free
      (and (free-vars-in-hyps hyps (all-vars pat) wrld)
           (or (match-free-default wrld)

; We presumably already caused an error if at this point we would find a value
; of t for state global match-free-error.

               :all))))

(defun match-free-fc-value (match-free hyps concls triggers wrld)

; This function, based on match-free-value, uses free-vars-in-fc-hyps to
; determine whether free-vars are present in a forward-chaining rule (if so it
; returns nil).  If free-vars are not present then it uses the match-free value
; of the rule (given by the match-free arg) or the match-free default value of
; the world to determine the correct match-free value for this particular rule.

  (or match-free
      (and (free-vars-in-fc-hyps triggers hyps concls)
           (or (match-free-default wrld)
               :all))))

(defun rule-backchain-limit-lst (backchain-limit-lst hyps wrld flg)
  (cond (backchain-limit-lst (cadr backchain-limit-lst))
        (t (let ((limit (default-backchain-limit wrld flg)))
             (and limit
                  (cond ((eq flg :meta) limit)
                        (t (make-list (length hyps)
                                      :initial-element
                                      limit))))))))

(defun create-rewrite-rule (qc-flg rune nume hyps equiv lhs rhs
                                   loop-stopper-lst backchain-limit-lst
                                   match-free-value wrld)

; Qc-flg indicates that we are creating a rewrite-quoted-constant rule.  Equiv
; is an equivalence relation name.  This function creates a :REWRITE rule of
; subclass 'backchain, 'abbreviation, or 'rewrite-quoted-constant from the
; basic ingredients, preprocessing the hyps and computing the loop-stopper.

  (let ((hyps (preprocess-hyps hyps wrld))
        (loop-stopper (if loop-stopper-lst
                          (remove-irrelevant-loop-stopper-pairs
                           (cadr loop-stopper-lst)
                           (all-vars lhs))
                          (loop-stopper lhs rhs))))
    (make rewrite-rule
          :rune rune
          :nume nume
          :hyps hyps
          :equiv equiv
          :lhs lhs
          :var-info (free-varsp lhs nil)
          :rhs rhs
          :subclass (cond (qc-flg 'rewrite-quoted-constant)
                          ((and (null hyps)
                                (null loop-stopper)
                                (abbreviationp nil
                                               (all-vars-bag lhs nil)
                                               rhs))
                           'abbreviation)
                          (t 'backchain))
          :heuristic-info
          (if qc-flg
              (cons (form-of-rewrite-quoted-constant-rule equiv lhs rhs)
                    loop-stopper)
              loop-stopper)

; If backchain-limit-lst is given, then it is a keyword-alist whose second
; element is a list of values of length (length hyps), and we use this value.
; Otherwise we use the default.  This will be either nil -- used directly -- or
; an integer which we expand to a list of (length hyps) copies.

          :backchain-limit-lst
          (rule-backchain-limit-lst backchain-limit-lst hyps wrld :rewrite)
          :match-free match-free-value)))

; The next subsection of our code develops various checkers to help the
; user manage his collection of rules.

(defun hyps-that-instantiate-free-vars (free-vars hyps)

; We determine the hyps in hyps that will be used to instantiate
; the free variables, free-vars, of some rule.  Here, variables "bound" by
; calls of bind-free are not considered free in the case of rewrite and linear
; rules, so would not appear among free-vars in those cases.

  (cond ((null free-vars) nil)
        ((intersectp-eq free-vars (all-vars (car hyps)))
         (cons (car hyps)
               (hyps-that-instantiate-free-vars
                (set-difference-eq free-vars (all-vars (car hyps)))
                (cdr hyps))))
        (t (hyps-that-instantiate-free-vars free-vars (cdr hyps)))))

(mutual-recursion

(defun maybe-one-way-unify (pat term alist)

; We return t if "it is possible" that pat matches term.  More accurately, if
; we return nil, then (one-way-unify1 pat term alist) definitely fails.  Thus,
; the answer t below is always safe.  The answer nil means there is no
; substitution, s extending alist such that pat/s is term.

  (cond ((variablep pat)
         (let ((pair (assoc-eq pat alist)))
           (or (not pair)
               (eq pat (cdr pair)))))
        ((fquotep pat) (equal pat term))
        ((variablep term) nil)
        ((fquotep term) t)
        ((equal (ffn-symb pat) (ffn-symb term))
         (maybe-one-way-unify-lst (fargs pat) (fargs term) alist))
        (t nil)))

(defun maybe-one-way-unify-lst (pat-lst term-lst alist)
  (cond ((endp pat-lst) t)
        (t (and (maybe-one-way-unify (car pat-lst) (car term-lst) alist)
                (maybe-one-way-unify-lst (cdr pat-lst) (cdr term-lst)
                                         alist)))))
)

(defun maybe-one-way-unify-with-some (pat term-lst alist)

; If we return nil, then there is no term in term-lst such that (one-way-unify
; pat term alist).  If we return t, then pat might unify with some member.

  (cond ((endp term-lst) nil)
        ((maybe-one-way-unify pat (car term-lst) alist) t)
        (t (maybe-one-way-unify-with-some pat (cdr term-lst) alist))))

(defun maybe-subsumes (cl1 cl2 alist)

; We return t if it is possible that the instance of cl1 via alist subsumes
; cl2.  More accurately, if we return nil then cl1 does not subsume cl2.
; Recall what it means for (subsumes cl1 cl2 alist) to return t: cl1/alist' is
; a subset of cl2, where alist' is an extension of alist.  Observe that the
; subset check would fail if cl1 contained a literal (P X) and there is no
; literal beginning with P in cl2.  More generally, suppose there is a literal
; of cl1 (e.g., (P X)) that unifies with no literal of cl2.  Then cl1 could not
; possibly subsume cl2.

; For a discussion of the origin of this function, see subsumes-rewrite-rule.
; It was made more efficient after Version_3.0, by adding an alist argument to
; eliminate the possibility of subsumption in more cases.

; Note that this function does not give special treatment for literals
; satisfying extra-info-lit-p.  We intend this function for use in checking
; subsumption of rewrite rules, and extra-info-lit-p has no special role for
; the rewriter.

  (cond ((null cl1) t)
        ((maybe-one-way-unify-with-some (car cl1) cl2 alist)
         (maybe-subsumes (cdr cl1) cl2 alist))
        (t nil)))

(defun subsumes-rewrite-rule (rule1 rule2 wrld)

; We answer the question:  does rule1 subsume rule2?  I.e., can rule1
; (probably) be applied whenever rule2 can be?  Since we don't check
; the loop-stoppers, the "probably" is warranted.  There may be other
; reasons it is warranted.  But this is just a heuristic check performed
; as a service to the user.

; One might ask why we do the maybe-subsumes.  We do the subsumes
; check on the hyps of two rules with matching :lhs.  In a hardware
; related file we were once confronted with a rule1 having :hyps

; ((BOOLEANP A0) (BOOLEANP B0) (BOOLEANP S0) (BOOLEANP C0_IN)
;  (BOOLEANP A1) (BOOLEANP B1) (BOOLEANP S1) (BOOLEANP C1_IN)
;  ...
;  (S_REL A0 B0 C0_IN S0)
;  ...)

; and a rule2 with :hyps

; ((BOOLEANP A0) (BOOLEANP B0) (BOOLEANP S0)
;  (BOOLEANP A1) (BOOLEANP B1) (BOOLEANP S1)
;  ...)

; The subsumes computation ran for over 30 minutes (and was eventually
; aborted).  The problem is that the extra variables in rule1, e.g.,
; C0_IN, were matchable in many different ways, e.g., C0_IN <- A0,
; C0_IN <- B0, etc., all of which must be tried in a subsumption
; check.  But no matter how you get rid of (BOOLEANP C0_IN) by
; choosing C0_IN, you will eventually run into the S_REL hypothesis in
; rule1 which has no counterpart in rule2.  Thus we installed the
; relatively quick maybe-subsumes check.  The check scans the :hyps of
; the first rule and determines whether there is some hypothesis that
; cannot possibly be matched against the hyps of the other rule.

; The caller is responsible for insuring that both rules are ordinary
; :rewrite rules (e.g., of :subclass abbreviation, backchain, etc) or
; :rewrite-quoted-constant rules (e.g., :subclass rewrite-quoted-constant).
; This is done by chk-rewrite-rule-warnings when it checks a new :rewrite
; rule only against existing rules in the lemmas property of the top fn, but
; checks a new :rewrite-quoted-constant rule against the rules in the global
; var rewrite-quoted-constant-rules.

; On subsumption of rewrite-quoted-constant rules.  Form [1] and [3] rules
; can be treated just like ordinary :rewrite rules.  But form [2] rules are
; different because they're of the form (equiv (fn x) x), where it is
; actually x that is matched to the quoted constant and then (fn x) is used
; to compute the new evg.  If a form [2] rule were ever party to a
; subsumption check you'd have to swap the orientation of conclusion.
; Furthermore, you'd find it would subsume any rule it was compared to, and
; you would find that no rule (except another form [2] rule) would subsume
; it.  It short, it seems pointless to include form [2] rules in subsumption
; checks!  Recal that the :heuristic-info field of a rewrite-quoted-constant
; rule is (n . loop-stopper), where n is the form number.

  (and (not (eql (car (access rewrite-rule rule1 :heuristic-info)) 2))
       (not (eql (car (access rewrite-rule rule2 :heuristic-info)) 2))
       (refinementp (access rewrite-rule rule1 :equiv)
                    (access rewrite-rule rule2 :equiv)
                    wrld)
       (mv-let (ans unify-subst)
         (one-way-unify (access rewrite-rule rule1 :lhs)
                        (access rewrite-rule rule2 :lhs))
         (and ans
              (maybe-subsumes
               (access rewrite-rule rule1 :hyps)
               (access rewrite-rule rule2 :hyps)
               unify-subst)
              (eq (subsumes *init-subsumes-count*
                            (access rewrite-rule rule1 :hyps)
                            (access rewrite-rule rule2 :hyps)
                            unify-subst)
                  t)))))

(defun find-subsumed-rule-names (lst rule ens wrld)

; Lst is a list of rewrite-rules.  Rule is a rewrite-rule.  We return
; the names of those elements of lst that are subsumed by rule.  We
; skip those rules in lst that are disabled in the global enabled structure
; and those that are META or DEFINITION rules.

  (cond ((null lst) nil)
        ((and (enabled-numep (access rewrite-rule (car lst) :nume)
                             ens)
              (not (eq (access rewrite-rule (car lst) :subclass) 'meta))
              (not (eq (access rewrite-rule (car lst) :subclass) 'definition))
              (subsumes-rewrite-rule rule (car lst) wrld))
         (cons (base-symbol (access rewrite-rule (car lst) :rune))
               (find-subsumed-rule-names (cdr lst) rule ens wrld)))
        (t (find-subsumed-rule-names (cdr lst) rule ens wrld))))

(defun find-subsuming-rule-names (lst rule ens wrld)

; Lst is a list of rewrite-rules.  Rule is a rewrite-rule.  We return
; the names of those elements of lst that subsume rule.  We skip those
; rules in lst that are disabled and that are META or DEFINITION rules.

  (cond ((null lst) nil)
        ((and (enabled-numep (access rewrite-rule (car lst) :nume)
                             ens)
              (not (eq (access rewrite-rule (car lst) :subclass) 'meta))
              (not (eq (access rewrite-rule (car lst) :subclass) 'definition))
              (subsumes-rewrite-rule (car lst) rule wrld))
         (cons (base-symbol (access rewrite-rule (car lst) :rune))
               (find-subsuming-rule-names (cdr lst) rule ens wrld)))
        (t (find-subsuming-rule-names (cdr lst) rule ens wrld))))

(defun forced-hyps (lst)
  (cond ((null lst) nil)
        ((and (nvariablep (car lst))
;             (not (fquotep (car lst)))
              (or (eq (ffn-symb (car lst)) 'force)
                  (eq (ffn-symb (car lst)) 'case-split)))
         (cons (car lst) (forced-hyps (cdr lst))))
        (t (forced-hyps (cdr lst)))))

(defun strip-top-level-nots-and-forces (hyps)
  (cond
   ((null hyps)
    nil)
   (t (mv-let (not-flg atm)
              (strip-not (if (and (nvariablep (car hyps))
;                                 (not (fquotep (car hyps)))
                                  (or (eq (ffn-symb (car hyps)) 'force)
                                      (eq (ffn-symb (car hyps)) 'case-split)))
                             (fargn (car hyps) 1)
                           (car hyps)))
              (declare (ignore not-flg))
              (cons atm (strip-top-level-nots-and-forces (cdr hyps)))))))

(defun free-variable-error? (token name ctx wrld state)
  (if (and (null (match-free-default wrld))
           (f-get-global 'match-free-error state))
      (er soft ctx
          "The warning above has caused this error in order to make it clear ~
           that there are free variables in ~s0 of a ~x1 rule generated from ~
           ~x2.  This error can be suppressed for the rest of this ACL2 ~
           session by submitting the following form:~|~%~x3~|~%However, you ~
           are advised not to do so until you have read the documentation on ~
           ``free variables'' (see :DOC free-variables) in order to understand ~
           the issues.  In particular, you can supply a :match-free value for ~
           the :rewrite rule class (see :DOC rule-classes) or a default for ~
           the book under development (see :DOC set-match-free-default)."
          (if (eq token :forward-chaining)
              "some trigger term"
            "the hypotheses")
          token name '(set-match-free-error nil))
    (value nil)))

(defun extend-geneqv-alist (var geneqv alist wrld)

; For each pair (x . y) in alist, x is a variable and y is a geneqv.  The
; result extends alist by associating variable var with geneqv, thus extending
; the generated equivalence relation already associated with var in alist.

  (put-assoc-eq var
                (union-geneqv geneqv (cdr (assoc-eq var alist)) wrld)
                alist))

(mutual-recursion

(defun covered-geneqv-alist (term geneqv pequiv-info alist ens wrld)

; Alist is an accumulator with entries of the form (v . geneqv-v), where v is a
; variable and geneqv-v is a generated equivalence relation.  We return an
; extension of alist by associating, with each variable bound in term, a list
; of all equivalence relations that are sufficient to preserve at one or more
; free occurrences of that variable in term, in order to preserve the given
; geneqv at term.

; This function creates the initial var-geneqv-alist for
; double-rewrite-opportunities; see also the comment there.  The idea is that
; for any variable occurrence, if rewriting of the actual term at that position
; took place under a given list of equivalence relations (a geneqv), then
; additional rewriting is unlikely to simplify the term further when done under
; any of those equivalence relations; but when we see that rewriting may be
; done under some equivalence relation that isn't "covered by" that geneqv --
; i.e., doesn't refine that geneqv (see also double-rewrite-opportunities) --
; then a double-rewrite warning is called for.

  (cond ((variablep term)
         (extend-geneqv-alist term geneqv alist wrld))
        ((fquotep term)
         alist)
        ((flambda-applicationp term)

; With more effort maybe we could pay more attention to patterned congruences
; in this case; but that seems like overkill for producing a warning.

         (covered-geneqv-alist-lst (fargs term)
                                   nil
                                   1
                                   (geneqv-lst (ffn-symb term) geneqv nil wrld)
                                   (ffn-symb term) ; irrelevant?
                                   geneqv
                                   nil nil alist ens wrld))
        (t
         (mv-let
           (deep-pequiv-lst shallow-pequiv-lst)
           (pequivs-for-rewrite-args (ffn-symb term)
                                     geneqv pequiv-info wrld ens)
           (covered-geneqv-alist-lst (fargs term)
                                     nil ; already-processed args
                                     1   ; bkptr
                                     (geneqv-lst (ffn-symb term)
                                                 geneqv nil wrld)
                                     (ffn-symb term) ; parent-fn
                                     geneqv ; parent-geneqv
                                     deep-pequiv-lst
                                     shallow-pequiv-lst
                                     alist ens wrld)))))

(defun covered-geneqv-alist-lst (args args-rev bkptr geneqv-lst
                                      parent-fn parent-geneqv
                                      deep-pequiv-lst shallow-pequiv-lst
                                      alist
                                      ens wrld)
  (cond ((endp args)
         alist)
        (t (mv-let
             (child-geneqv child-pequiv-info)
             (geneqv-and-pequiv-info-for-rewrite
              parent-fn bkptr args-rev args
              nil ; alist
              parent-geneqv
              (car geneqv-lst) ; child-geneqv
              deep-pequiv-lst
              shallow-pequiv-lst
              wrld)
             (covered-geneqv-alist-lst
              (cdr args)
              (cons (car args) args-rev)
              (1+ bkptr)
              (cdr geneqv-lst)
              parent-fn
              parent-geneqv
              deep-pequiv-lst shallow-pequiv-lst
              (covered-geneqv-alist (car args)
                                    child-geneqv
                                    child-pequiv-info
                                    alist ens wrld)
              ens wrld)))))
)

(defun uncovered-equivs (geneqv covered-geneqv wrld)

; Geneqv and covered-geneqv are generated equivalence relations, i.e., lists of
; equivalence relations.  We return all equivalence relations E in geneqv that
; are "uncovered" with respect to covered-geneqv, i.e., such that E does not
; refine covered-geneqv.  See uncovered-equivs-alist for motivation; briefly
; put, rewriting with respect to an uncovered equiv may be possible that was
; not possible with respect to covered-geneqv, and we want to warn with a
; suggestion to use double-rewrite to take advantage of that uncovered equiv
; when rewriting.

  (cond ((endp geneqv) nil)
        (t (let ((equiv (access congruence-rule (car geneqv) :equiv))
                 (rst (uncovered-equivs (cdr geneqv) covered-geneqv wrld)))
             (cond ((geneqv-refinementp equiv covered-geneqv wrld)
                    rst)
                   (t (cons equiv rst)))))))

(mutual-recursion

(defun uncovered-equivs-alist (term geneqv pequiv-info
                                    var-geneqv-alist var-geneqv-alist0
                                    obj-not-? acc-equivs acc-counts ens wrld)

; Accumulator acc-equivs is an alist that associates variables with lists of
; equivalence relations, and accumulator acc-counts associates variables with
; natural numbers.  We are given a term whose value is to be maintained with
; respect to the given geneqv, along with var-geneqv-alist, which associates
; variables with lists of equivalence relations.  We return extensions of
; acc-equivs, acc-counts, and var-geneqv-alist as follows.

; Consider a bound (by var-geneqv-alist) variable occurrence in term.  Its
; context is known to preserve certain equivalence relations; but some of these
; may be "uncovered", i.e., it does not refine any of those associated with
; this variable in var-geneqv-alist.  If that is the case, then we add those
; "uncovered" equivalence relations to the list associated with this variable
; in acc-equivs, and increment the value of this variable in acc-counts by 1.

; However, we skip the above analysis for the case that geneqv is *geneqv-iff*
; and the variable occurs as a branch of the IF-structure of a hypothesis.
; This function is used for creating warnings that suggest the use of
; double-rewrite, which however is generally not necessary in such situations;
; see rewrite-solidify-plus.

; For a free variable occurrence in term, we leave acc-equivs and acc-counts
; unchanged, and instead extend var-geneqv-alist by associating this variable
; with the geneqv for its context.  Var-geneqv-alist0 is left unchanged by this
; process, for purposes of checking free-ness.

; Here is a little test, showing that patterned congruences are used to uncover
; double-rewrite opportunities in hypotheses.

;   (defun foo (x y)
;     (mv x y))

;   (defthm my-cong
;     (implies (iff y1 y2)
;              (iff (mv-nth 1 (foo x y1))
;                   (mv-nth 1 (foo x y2))))
;     :rule-classes :congruence)

;   ; We get a warning here for the occurrence of y in the hypothesis:
;   (defthm bar
;     (implies (mv-nth 1 (foo x y))
;              (equal (car (cons x y)) x)))

  (cond
   ((variablep term)
    (let ((binding (assoc-eq term var-geneqv-alist0)))
      (cond ((null binding)
             (mv acc-equivs
                 acc-counts
                 (extend-geneqv-alist term geneqv var-geneqv-alist wrld)))
            ((and obj-not-?
                  (equal geneqv *geneqv-iff*))

; The call of rewrite-solidify-plus in rewrite makes it unnecessary to warn
; when the objective is other than '? and the given geneqv is *geneqv-iff*.

             (mv acc-equivs acc-counts var-geneqv-alist))
            (t (let* ((covered-geneqv (cdr binding))
                      (uncovered-equivs
                       (uncovered-equivs geneqv covered-geneqv wrld)))
                 (cond (uncovered-equivs
                        (mv (put-assoc-eq
                             term
                             (union-eq uncovered-equivs
                                       (cdr (assoc-eq term acc-equivs)))
                             acc-equivs)
                            (put-assoc-eq
                             term
                             (1+ (or (cdr (assoc-eq term acc-counts))
                                     0))
                             acc-counts)
                            var-geneqv-alist))
                       (t (mv acc-equivs acc-counts var-geneqv-alist))))))))
   ((or (fquotep term)
        (eq (ffn-symb term) 'double-rewrite))
    (mv acc-equivs acc-counts var-geneqv-alist))
   ((flambda-applicationp term)

; With more effort maybe we could pay more attention to patterned congruences
; in this case; but that seems like overkill for producing a warning.

    (uncovered-equivs-alist-lst
     (fargs term)
     nil
     1 ; bkptr
     (geneqv-lst (ffn-symb term) geneqv nil wrld)
     (ffn-symb term) ; irrelevant?
     geneqv nil nil
     var-geneqv-alist var-geneqv-alist0
     (if (and obj-not-?
              (eq (ffn-symb term) 'if))
         (list nil t t)
       nil)
     acc-equivs acc-counts ens wrld))
   (t (mv-let
        (deep-pequiv-lst shallow-pequiv-lst)
        (pequivs-for-rewrite-args (ffn-symb term) geneqv pequiv-info wrld ens)
        (uncovered-equivs-alist-lst
         (fargs term)
         nil
         1 ; bkptr
         (geneqv-lst (ffn-symb term) geneqv nil wrld)
         (ffn-symb term) ; parent-fn
         geneqv
         deep-pequiv-lst shallow-pequiv-lst
         var-geneqv-alist var-geneqv-alist0
         (if (and obj-not-?
                  (eq (ffn-symb term) 'if))
             (list nil t t)
           nil)
         acc-equivs acc-counts ens wrld)))))

(defun uncovered-equivs-alist-lst (args args-rev bkptr geneqv-lst
                                        parent-fn parent-geneqv
                                        deep-pequiv-lst shallow-pequiv-lst
                                        var-geneqv-alist
                                        var-geneqv-alist0
                                        obj-not-?-lst
                                        acc-equivs acc-counts ens wrld)
  (cond ((endp args)
         (mv acc-equivs acc-counts var-geneqv-alist))
        (t (mv-let
             (child-geneqv child-pequiv-info)
             (geneqv-and-pequiv-info-for-rewrite
              parent-fn bkptr args-rev args
              nil ; alist
              parent-geneqv
              (car geneqv-lst) ; child-geneqv
              deep-pequiv-lst
              shallow-pequiv-lst
              wrld)
             (mv-let (acc-equivs acc-counts var-geneqv-alist)
               (uncovered-equivs-alist (car args)
                                       child-geneqv
                                       child-pequiv-info
                                       var-geneqv-alist
                                       var-geneqv-alist0
                                       (car obj-not-?-lst)
                                       acc-equivs acc-counts
                                       ens wrld)
               (uncovered-equivs-alist-lst (cdr args)
                                           (cons (car args) args-rev)
                                           (1+ bkptr)
                                           (cdr geneqv-lst)
                                           parent-fn parent-geneqv
                                           deep-pequiv-lst shallow-pequiv-lst
                                           var-geneqv-alist
                                           var-geneqv-alist0
                                           (cdr obj-not-?-lst)
                                           acc-equivs acc-counts
                                           ens wrld))))))
)

(defun double-rewrite-opportunities (hyp-index hyps var-geneqv-alist
                                     final-term final-location final-geneqv
                                     ens wrld)

; We return an alist having entries (location var-equiv-alist
; . var-count-alist), where location is a string identifying a term (either the
; hyp-index_th member of the original hyps, or the final-term), var-equiv-alist
; associates variables of that term with their "uncovered equivs" as defined
; below, and var-count-alist associates variables of that term with the number
; of occurrences of a given variable that have at least one "uncovered" equiv.

; This function is called only for the purpose of producing a warning when
; there is a missed opportunity for a potentially useful call of
; double-rewrite.  Consider a variable occurrence in hyps, the hypotheses of a
; rule, in a context where it is sufficient to preserve equiv.  If that
; variable occurs in the left-hand side of a rewrite rule (or the max-term of a
; linear rule) in at least one context where it is sufficient to preserve
; equiv, that would give us confidence that the value associated with that
; occurrence (in the unifying substitution) had been fully rewritten with
; respect to equiv.  But otherwise, we want to note this "uncovered" equiv for
; that variable in that hyp.

; We give similar treatment for the right-hand side of a rewrite rule and
; conclusion of a linear rule, using the formal parameters final-xxx.

; Var-geneqv-alist is an alist that binds variables to geneqvs.  Initially, the
; keys are exactly the bound variables of the unifying substitution.  Each key
; is associated with a geneqv that represents the equivalence relation
; generated by all equivalence relations known to be preserved for at least one
; variable occurrence in the pattern that was matched to give the unifying
; substitution (the left-hand side of a rewrite rule or max-term of a linear
; rule).  As we move through hyps, we may encounter a hypothesis (equal var
; term) or (equiv var (double-rewrite term)) that binds a variable, var, in
; which case we will extend var-geneqv-alist for var at that point.  Note that
; we do not extend var-geneqv-alist for other free variables in hypotheses,
; because we do not know the equivalence relations that were maintained when
; creating the rewritten terms to which the free variables are bound.

  (cond ((endp hyps)
         (mv-let (var-equivs-alist var-counts var-geneqv-alist)
                 (uncovered-equivs-alist final-term final-geneqv nil
                                         var-geneqv-alist var-geneqv-alist
                                         nil nil nil ens wrld)
                 (declare (ignore var-geneqv-alist))
                 (if var-equivs-alist
                     (list (list* final-location var-equivs-alist var-counts))
                   nil)))
        (t
         (mv-let
           (forcep bind-flg)
           (binding-hyp-p (car hyps) var-geneqv-alist wrld)
           (let ((hyp (if forcep (fargn (car hyps) 1) (car hyps))))
             (cond (bind-flg
                    (let* ((equiv (ffn-symb hyp))
                           (var (fargn hyp 1))
                           (term0 (fargn hyp 2))
                           (term (if (ffn-symb-p term0 'double-rewrite)
                                     (fargn term0 1)
                                   term0))
                           (new-geneqv (cadr (geneqv-lst equiv
                                                         *geneqv-iff*
                                                         nil
                                                         wrld))))
                      (double-rewrite-opportunities
                       (1+ hyp-index)
                       (cdr hyps)
                       (covered-geneqv-alist term
                                             new-geneqv
                                             nil
                                             (assert$ (variablep var)
                                                      (extend-geneqv-alist
                                                       var new-geneqv
                                                       var-geneqv-alist wrld))
                                             ens wrld)
                       final-term final-location final-geneqv
                       ens wrld)))
                   (t (mv-let (var-equivs-alist var-counts var-geneqv-alist)
                              (uncovered-equivs-alist (car hyps)
                                                      *geneqv-iff*
                                                      nil
                                                      var-geneqv-alist
                                                      var-geneqv-alist
                                                      t
                                                      nil nil
                                                      ens wrld)
                        (let ((cdr-result
                               (double-rewrite-opportunities (1+ hyp-index)
                                                             (cdr hyps)
                                                             var-geneqv-alist
                                                             final-term
                                                             final-location
                                                             final-geneqv
                                                             ens wrld)))
                          (if var-equivs-alist
                              (cons (list* (msg "the ~n0 hypothesis"
                                                (list hyp-index))
                                           var-equivs-alist var-counts)
                                    cdr-result)
                            cdr-result))))))))))

(defun show-double-rewrite-opportunities1 (location var-equivs-alist
                                                    var-count-alist token name
                                                    max-term-msg ctx state)

; This should only be called in a context where we know that double-rewrite
; warnings are enabled.  Otherwise we lose efficiency, and anyhow warning$ is
; called below with ("Double-rewrite").

  (cond ((endp var-equivs-alist)
         state)
        (t (pprogn (let* ((var (caar var-equivs-alist))
                          (count (let ((pair (assoc-eq var var-count-alist)))
                                   (assert$ pair (cdr pair)))))
                     (warning$ ctx ("Double-rewrite")
                               `("In a ~x0 rule generated from ~x1~@2, ~
                                  equivalence relation~#3~[ ~&3 is~/s ~&3 ~
                                  are~] maintained at ~n4 problematic ~
                                  occurrence~#5~[~/s~] of variable ~x6 in ~
                                  ~@7, but not at any binding occurrence of ~
                                  ~x6.  Consider replacing ~#5~[that ~
                                  occurrence~/those ~n4 occurrences~] of ~x6 ~
                                  in ~@7 with ~x8.  See :doc double-rewrite ~
                                  for more information on this issue."
                                 (:doc double-rewrite)
                                 (:equivalence-relations
                                  ,(cdar var-equivs-alist))
                                 (:location ,location)
                                 ,@(and (not (equal max-term-msg ""))
                                        `((:max-term-msg ,max-term-msg)))
                                 (:new-rule ,name)
                                 (:number-of-problematic-occurrences ,count)
                                 (:rule-class ,token)
                                 (:variable ,var))
                               token name
                               max-term-msg
                               (cdar var-equivs-alist)
                               count
                               (if (eql count 1) 0 1)
                               var
                               location
                               (list 'double-rewrite var)))
                   (show-double-rewrite-opportunities1
                    location (cdr var-equivs-alist) var-count-alist
                    token name max-term-msg ctx state)))))

(defun show-double-rewrite-opportunities (hyp-var-equivs-counts-alist-pairs
                                          token name max-term-msg ctx state)

; Hyp-var-equivs-counts-alist-pairs is an alist as returned by
; double-rewrite-opportunities; see the comment there.  Final-term,
; final-location, final-var-equivs-alist, and final-var-count-alist are the
; analog of one entry of that alist, but for the right-hand side of a rewrite
; rule or the conclusion of a linear rule.

; For efficiency, check warning-disabled-p before calling this function.

  (cond ((endp hyp-var-equivs-counts-alist-pairs)
         state)
        (t (pprogn (show-double-rewrite-opportunities1
                    (caar hyp-var-equivs-counts-alist-pairs)
                    (cadar hyp-var-equivs-counts-alist-pairs)
                    (cddar hyp-var-equivs-counts-alist-pairs)
                    token name max-term-msg ctx state)
                   (show-double-rewrite-opportunities
                    (cdr hyp-var-equivs-counts-alist-pairs)
                    token name max-term-msg ctx state)))))

(defun irrelevant-loop-stopper-pairs (pairs vars)

; Keep this in sync with remove-irrelevant-loop-stopper-pairs.

  (if pairs
      (if (and (member-eq (caar pairs) vars)
               (member-eq (cadar pairs) vars))
          (irrelevant-loop-stopper-pairs (cdr pairs) vars)
        (cons (car pairs)
              (irrelevant-loop-stopper-pairs (cdr pairs) vars)))
    nil))

(defun non-rec-def-rules-msg-1 (alist)
  (cond ((endp alist) nil)
        ((null (cdar alist))
         (non-rec-def-rules-msg-1 (cdr alist)))
        (t (cons (msg "~x0 is defined with ~x1"
                      (caar alist)
                      (cdar alist))
                 (non-rec-def-rules-msg-1 (cdr alist))))))

(defun non-rec-def-rules-msg (alist)
  (let ((lst (non-rec-def-rules-msg-1 alist)))
    (cond
     ((null lst) "")
     (t (msg "  (Note that ~*0"
             (list
              "impossible" ; unreachable case (when there's nothing to print)
              "~@*.)"       ; how to print the last element
              "~@* and "   ; how to print the 2nd to last element
              "~@*, "      ; how to print all other elements
              lst))))))

(defun chk-rewrite-rule-warnings (name match-free loop-stopper rule ctx
                                       ens wrld state)
  (let* ((token (cond
                 ((eq (access rewrite-rule rule :subclass)
                      'definition)
                  :definition)
                 ((eq (access rewrite-rule rule :subclass)
                      'rewrite-quoted-constant)
                  :rewrite-quoted-constant)
                 (t :rewrite)))

; Note, first, that the contents of the :subclass field of a rewrite-rule is a
; non-keyword symbol but that token, above, is bound to a keyword.  Second,
; there are five possible values for :subclass and they are: backchain,
; abbreviation, meta, definition, and rewrite-quoted-constant.  But for this
; processing, we lump backchain, abbreviation, and meta together under the
; token :rewrite.  Finally, note that token is used below in some warning
; messages as a stand-in for the original :rule-class of the lemma.

         (hyps (access rewrite-rule rule :hyps))
         (lhs (access rewrite-rule rule :lhs))
         (warn-non-rec (not (warning-disabled-p "Non-rec")))
         (non-rec-fns-lhs-alist
          (and warn-non-rec
               (not (eq token :rewrite-quoted-constant))
               (non-recursive-fnnames-alist lhs ens wrld)))
         (lhs-vars (all-vars lhs))
         (rhs-vars (all-vars (access rewrite-rule rule :rhs)))
         (free-vars (free-vars-in-hyps-considering-bind-free
                     hyps
                     lhs-vars
                     wrld))
         (inst-hyps (hyps-that-instantiate-free-vars free-vars hyps))
         (non-rec-fns-inst-hyps-alist
          (and warn-non-rec
               (non-recursive-fnnames-alist-lst
                (strip-top-level-nots-and-forces inst-hyps) ens wrld)))
         (subsume-check-enabled (not (warning-disabled-p "Subsume")))

; We don't check subsumption between :rewrite-quoted-constant rules.  It's kind
; of messy since Form [2] rules are ``backwards'' and if checked properly
; (using the rhs as the pattern) would subsume all rules of that equivalence
; class.

         (subsumed-rule-names
          (and subsume-check-enabled
               (find-subsumed-rule-names
                (if (eq token :rewrite-quoted-constant)
                    (global-val 'rewrite-quoted-constant-rules wrld)
                    (getpropc (ffn-symb lhs) 'lemmas nil wrld))
                rule ens wrld)))
         (subsuming-rule-names
          (and subsume-check-enabled
               (not (eq token :rewrite-quoted-constant))
               (find-subsuming-rule-names
                (if (eq token :rewrite-quoted-constant)
                    (global-val 'rewrite-quoted-constant-rules wrld)
                    (getpropc (ffn-symb lhs) 'lemmas nil wrld))
                rule ens wrld)))
         (equiv (access rewrite-rule rule :equiv))
         (geneqv (cadr (geneqv-lst equiv nil nil wrld)))
         (double-rewrite-opportunities
          (and (not (warning-disabled-p "Double-rewrite"))
               (not (eq token :rewrite-quoted-constant))
               (double-rewrite-opportunities
                1
                hyps
                (covered-geneqv-alist lhs geneqv nil nil ens wrld)
                (access rewrite-rule rule :rhs)
                "the right-hand side"
                geneqv
                ens wrld))))
    (pprogn
     (cond (double-rewrite-opportunities
            (show-double-rewrite-opportunities double-rewrite-opportunities
                                               token name "" ctx state))
           (t state))
     (cond
      (non-rec-fns-lhs-alist
       (warning$ ctx "Non-rec"
                 `("A ~x0 rule generated from ~x1 will be triggered only by ~
                    terms containing the function symbol~#2~[ ~&2, which has ~
                    a non-recursive definition.~@3  Unless this definition ~
                    is~/s ~&2, which have non-recursive definitions.~@3  ~
                    Unless these definitions are~] disabled, this rule is ~
                    unlikely ever to be used."
                   (:non-recursive-fns-lhs
                    ,(hide-lambdas (strip-cars non-rec-fns-lhs-alist)))
                   (:name ,name)
                   (:rule-class ,token))
                 token
                 name
                 (hide-lambdas (strip-cars non-rec-fns-lhs-alist))
                 (non-rec-def-rules-msg non-rec-fns-lhs-alist)))
      (t state))
     (er-progn
      (cond
       ((and free-vars (null match-free))
        (pprogn
         (warning$ ctx "Free"
                   `("A ~x0 rule generated from ~x1 contains the free ~
                    variable~#2~[ ~&2.  This variable~/s ~&2.  These ~
                    variables~] will be chosen by searching for ~#3~[an ~
                    instance~/instances~] of ~*4 in the context of the term ~
                    being rewritten.  This is generally a severe restriction ~
                    on the applicability of a ~x0 rule.  See :DOC ~
                    free-variables."
                     (:doc free-variables)
                     (:free-variables ,free-vars)
                     (:instantiated-hyps ,(untranslate-lst inst-hyps t wrld))
                     (:name ,name)
                     (:rule-class ,token))
                   token name free-vars
                   inst-hyps
                   (tilde-*-untranslate-lst-phrase inst-hyps t wrld))
         (free-variable-error? token name ctx wrld state)))
       (t (value nil)))
      (pprogn
       (cond
        ((and free-vars
              (forced-hyps inst-hyps))
         (warning$ ctx "Free"
                   "For the forced ~#0~[hypothesis~/hypotheses~], ~*1, used ~
                    to instantiate free variables we will search for ~#0~[an ~
                    instance of the argument~/instances of the arguments~] ~
                    rather than ~#0~[an instance~/instances~] of the FORCE or ~
                    CASE-SPLIT ~#0~[term itself~/terms themselves~].  If a ~
                    search fails for such a hypothesis, we will cause a case ~
                    split on the partially instantiated hypothesis.  Note ~
                    that this case split will introduce a ``free variable'' ~
                    into the conjecture.  While sound, this will establish a ~
                    goal almost certain to fail since the restriction ~
                    described by this apparently necessary hypothesis ~
                    constrains a variable not involved in the problem.  To ~
                    highlight this oddity, we will rename the free variables ~
                    in such forced hypotheses by prefixing them with ~
                    ``UNBOUND-FREE-''.  This is not guaranteed to generate a ~
                    new variable but at least it generates an unusual one.  ~
                    If you see such a variable in a subsequent proof (and did ~
                    not introduce them yourself) you should consider the ~
                    possibility that the free variables of this rewrite rule ~
                    were forced into the conjecture."
                   (if (null (cdr (forced-hyps inst-hyps))) 0 1)
                   (tilde-*-untranslate-lst-phrase (forced-hyps inst-hyps) t
                                                   wrld)))
        (t state))
       (cond
        ((set-difference-eq rhs-vars lhs-vars)

; Usually the above will be nil.  If not, the recomputation below is no big
; deal.

         (cond
          ((set-difference-eq rhs-vars
                              (all-vars1-lst hyps lhs-vars))
           (warning$ ctx "Free"
                     "A ~x0 rule generated from ~x1 contains the the free ~
                      variable~#2~[~/s~] ~&2 on the right-hand side of the ~
                      rule, which ~#2~[is~/are~] not bound on the left-hand ~
                      side~#3~[~/ or in the hypothesis~/ or in any ~
                      hypothesis~].  This can cause new variables to be ~
                      introduced into the proof, which may surprise you."
                     token name
                     (set-difference-eq rhs-vars
                                        (all-vars1-lst hyps lhs-vars))
                     (zero-one-or-more hyps)))
          (t state)))
        (t state))
       (cond
        (non-rec-fns-inst-hyps-alist
         (warning$ ctx "Non-rec"
                   `("As noted, we will instantiate the free ~
                      variable~#0~[~/s~], ~&0, of a ~x1 rule generated from ~
                      ~x2, by searching for the ~#3~[hypothesis~/set of ~
                      hypotheses~] shown above.  However, ~#3~[this ~
                      hypothesis mentions~/these hypotheses mention~] the ~
                      function symbol~#4~[ ~&4, which has a non-recursive ~
                      definition.~@5  Unless this definition is disabled, ~
                      that function symbol is~/s ~&4, which have ~
                      non-recursive definitions.~@5  Unless these definitions ~
                      are disabled, those function symbols are~] unlikely to ~
                      occur in the conjecture being proved and hence the ~
                      search for the required ~#3~[hypothesis~/hypotheses~] ~
                      will likely fail."
                     (:free-variables ,free-vars)
                     (:instantiated-hyps ,inst-hyps)
                     (:non-rec-fns-inst-hyps
                      ,(hide-lambdas (strip-cars non-rec-fns-inst-hyps-alist)))
                     (:name ,name)
                     (:rule-class ,token))
                   free-vars token name inst-hyps
                   (hide-lambdas (strip-cars non-rec-fns-inst-hyps-alist))
                   (non-rec-def-rules-msg non-rec-fns-inst-hyps-alist)))
        (t state))
       (cond
        (subsumed-rule-names
         (warning$ ctx ("Subsume")
                   `("A newly proposed ~x0 rule generated from ~x1 probably ~
                     subsumes the previously added ~x3 rule~#2~[~/s~] ~
                     ~&2, in the sense that the new rule will now probably be ~
                     applied whenever the old rule~#2~[~/s~] would have been."
                     (:new-rule ,name)
                     (:rule-class-new ,token)
                     (:rule-class-old ,(if (eq token :rewrite-quoted-constant)
                                           :rewrite-quoted-constant
                                           :rewrite))
                     (:subsumed-rules ,subsumed-rule-names))
                   token name subsumed-rule-names
                   (if (eq token :rewrite-quoted-constant)
                       :rewrite-quoted-constant
                       :rewrite)))
        (t state))
       (cond
        (subsuming-rule-names
         (warning$ ctx ("Subsume")
                   `("The previously added rule~#1~[~/s~] ~&1 ~
                     subsume~#1~[s~/~] a newly proposed ~x0 rule generated ~
                     from ~x2, in the sense that the old rule~#1~[ rewrites a ~
                     more general target~/s rewrite more general targets~].  ~
                     Because the new rule will be tried first, it may ~
                     nonetheless find application."
                     (:new-rule ,name)
                     (:rule-class ,token)
                     (:subsuming-rules ,subsuming-rule-names))
                   token
                   subsuming-rule-names
                   name))
        (t state))
       (cond
        ((warning-disabled-p "Loop-Stopper")
         state)
        (t (let ((bad-pairs
                  (irrelevant-loop-stopper-pairs loop-stopper lhs-vars)))
             (cond
              (bad-pairs
               (warning$ ctx ("Loop-Stopper")
                         "When the ~x0 rule generated from ~x1 is created, ~
                          the ~#2~[entry~/entries~] ~&2 from the specified ~
                          :LOOP-STOPPER will be ignored because the two ~
                          specified variables do not both occur on the ~
                          left-hand side of the rule.  See :DOC loop-stopper."
                         token name bad-pairs))
              (t state)))))
       (value nil))))))

(defun chk-acceptable-rewrite-rule2 (qc-flg name match-free loop-stopper hyps
                                            concl ctx ens wrld state)

; This is the basic function for checking that (IMPLIES (AND . hyps) concl)
; generates a useful :REWRITE or :REWRITE-QUOTED-CONSTANT rule.  If it does
; not, we cause an error.  If it does, we may print some warnings regarding the
; rule generated.  The superior functions, chk-acceptable-rewrite-rule1 and
; chk-acceptable-rewrite-rule just cycle down to this one after flattening the
; IMPLIES/AND structure of the user's input term.  When successful, this
; function returns a ttree justifying the storage of the :REWRITE rule -- it
; sometimes depends on type-set information.

  (mv-let
   (msg eqv lhs rhs ttree)
   (interpret-term-as-rewrite-rule qc-flg name hyps concl ctx ens wrld)
   (cond
    (msg (er soft ctx "~@0" msg))
    (t (let ((rewrite-rule
              (create-rewrite-rule qc-flg
                                   *fake-rune-for-anonymous-enabled-rule*
                                   nil hyps eqv lhs rhs nil nil nil wrld)))

; The rewrite-rule record created above is used only for subsumption checking and
; then discarded.  The rune, nume, loop-stopper-lst, and match-free used are
; irrelevant.  The warning messages, if any, concerning subsumption report the
; name of the rule as name.

         (er-progn
          (chk-rewrite-rule-warnings name match-free loop-stopper
                                     rewrite-rule ctx ens wrld state)
          (value ttree)))))))

(defun chk-acceptable-rewrite-rule1 (qc-flg name match-free loop-stopper lst
                                            ctx ens wrld state)

; Each element of lst is a pair, (hyps . concl) and we check that each such
; pair, when interpreted as the term (implies (and . hyps) concl), generates a
; legal :REWRITE or :REWRITE-QUOTED-CONSTANT rule.  We return the accumulated
; ttrees.

  (cond
   ((null lst) (value nil))
   (t (er-let* ((ttree1
                 (chk-acceptable-rewrite-rule2 qc-flg name match-free
                                               loop-stopper
                                               (caar lst) (cdar lst)
                                               ctx ens wrld state))
                (ttree
                 (chk-acceptable-rewrite-rule1 qc-flg name match-free
                                               loop-stopper
                                               (cdr lst) ctx ens wrld state)))
        (value (cons-tag-trees ttree1 ttree))))))

(defun chk-acceptable-rewrite-rule (qc-flg name match-free loop-stopper
                                           term ctx ens wrld state)

; We strip the conjuncts out of term and flatten those in the hypotheses of
; implications to obtain a list of implications, each of the form (IMPLIES (AND
; . hyps) concl), and each represented simply by a pair (hyps . concl).  For
; each element of that list we then determine whether it generates a legal
; :REWRITE or :rewrite-quoted-constant rule, as per qc-flg.  See
; chk-acceptable-rewrite-rule2 for the guts of this test.  We either cause an
; error or return successfully.  We may print warning messages without causing
; an error.  On successful returns the value is a ttree that justifies the
; storage of all the :REWRITE rules.

  (chk-acceptable-rewrite-rule1 qc-flg name match-free loop-stopper
                                (unprettyify (remove-guard-holders term wrld))
                                ctx ens wrld state))

; So now we work on actually generating and adding the rules.

(defun add-rewrite-rule2 (qc-flg rune nume hyps concl loop-stopper-lst
                                 backchain-limit-lst match-free ens wrld)

; This is the basic function for generating and adding a rule named
; rune from the formula (IMPLIES (AND . hyps) concl).

  (mv-let
   (msg eqv lhs rhs ttree)
   (interpret-term-as-rewrite-rule qc-flg
                                   (base-symbol rune)
                                   hyps concl nil ens wrld)
   (declare (ignore ttree))
   (cond
    (msg

; Msg is nil if we have called chk-acceptable-rewrite-rule for the
; corresponding rule under the same event that we are processing here.  But
; suppose we are in the second pass of encapsulate or the local compatibility
; check of certify-book.  Then that check may have been done in a different
; world than the one we have now.

; Even then, we typically expect that if interpret-term-as-rewrite-rule avoids
; returning an error, then it does so for every call made on the same arguments
; other than, perhaps, the world.  Looking at the code for
; interpret-term-as-rewrite-rule2 and its callees, we see that it suffices to
; show that if interpret-term-as-rewrite-rule2 returns nil for lhs and rhs that
; are returned by a call of interpret-term-as-rewrite-rule1, then that call of
; interpret-term-as-rewrite-rule2 returns nil when the only input argument
; changes are the world and, for the latter call, equiv-okp = t.  A
; counterexample would have to be a term of the form (equiv x y), where equiv
; is an equivalence relation in the first world passed to
; interpret-term-as-rewrite-rule1 but not in the second, where
; interpret-term-as-rewrite-rule2 returns nil for lhs = x and rhs = y but
; returns a non-nil msg for lhs = (equiv x y) and rhs = *t*.  The only way that
; can happen is with the bad-synp-hyp-msg check in
; interpret-term-as-rewrite-rule2, as in the following example -- and it does
; indeed happen!  But we think this hard error is so rare that it is
; tolerable.

;   (encapsulate
;    ()
;    (defun my-equivp (x y)
;      (equal (nfix x) (nfix y)))
;    (local (defequiv my-equivp))
;    (defthm foo
;      (implies (and (bind-free (list (cons 'y x)) (y))
;                    (equal y x))
;               (my-equivp (identity x) y))))

     (er hard 'add-rewrite-rule2
         "We believe that this error is occurring because the conclusion of a ~
          proposed :REWRITE or :REWRITE-QUOTED-CONSTANT rule generated from ~
          ~x0 is of the form (equiv LHS RHS), where equiv was a known ~
          equivalence relation when this rule was originally processed, but ~
          that is no longer the case.  In any case, the rule is now ~
          ill-formed. Perhaps you can fix this problem by making equiv an ~
          equivalence relation non-locally."
         (base-symbol rune)))
    (t
     (let* ((match-free-value (match-free-value match-free hyps lhs wrld))
            (rewrite-rule (create-rewrite-rule qc-flg rune nume hyps eqv
                                               lhs rhs
                                               loop-stopper-lst
                                               backchain-limit-lst
                                               match-free-value
                                               wrld))
            (wrld1 (if qc-flg
                       (global-set
                        'rewrite-quoted-constant-rules
                        (cons rewrite-rule
                              (global-val 'rewrite-quoted-constant-rules
                                          wrld))
                        wrld)
                       (putprop (ffn-symb lhs)
                            'lemmas
                            (cons rewrite-rule
                                  (getpropc (ffn-symb lhs) 'lemmas nil wrld))
                            wrld))))
       (put-match-free-value match-free-value rune wrld1))))))

(defun add-rewrite-rule1 (qc-flg rune nume lst loop-stopper-lst
                                 backchain-limit-lst match-free ens wrld)

; Each element of lst is a pair, (hyps . concl).  We generate and
; add to wrld a :REWRITE for each.

  (cond ((null lst) wrld)
        (t (add-rewrite-rule1 qc-flg rune nume (cdr lst)
                              loop-stopper-lst
                              backchain-limit-lst
                              match-free
                              ens
                              (add-rewrite-rule2 qc-flg rune nume
                                                 (caar lst)
                                                 (cdar lst)
                                                 loop-stopper-lst
                                                 backchain-limit-lst
                                                 match-free
                                                 ens
                                                 wrld)))))

(defun add-rewrite-rule (qc-flg rune nume loop-stopper-lst term
                                backchain-limit-lst match-free ens wrld)

; This function might better be called "add-rewrite-rules" because we
; may get many :REWRITE rules from term.  But we are true to our naming
; convention.  "Consistency is the hobgoblin of small minds."  Emerson?

  (add-rewrite-rule1 qc-flg rune nume
                     (unprettyify (remove-guard-holders term wrld))
                     loop-stopper-lst backchain-limit-lst match-free ens wrld))

;---------------------------------------------------------------------------
; Section:  :LINEAR Rules

; We now move on to :LINEAR class rules.

(defun expand-inequality-fncall1 (term)

; Term is a non-variable, non-quotep term.  If it is a call of one of
; the primitive arithmetic relations, <, =, and /=, we return a
; nearly-equivalent term using not, equal, and < in place of that
; top-level call.  Otherwise, we return term.  We ignore the guards of
; arithmetic relations expanded!

; Warning: See the warning in expand-inequality-fncall below.  It is
; crucial that if (fn a b) is expanded here then the guards necessary
; to justify that expansion are implied by the rationalp assumptions
; produced during the linearization of the expanded term.  In
; particular, (rationalp a) and (rationalp b) ought to be sufficient
; to permit (fn a b) to expand to whatever we produce below.

  (let ((fn (ffn-symb term)))
    (case
     fn
     (< term)
     (= (mcons-term* 'equal (fargn term 1) (fargn term 2)))
     (/= (mcons-term* 'not (mcons-term* 'equal (fargn term 1) (fargn term 2))))
     (otherwise term))))

(defun expand-inequality-fncall (term)

; If term is a (possibly negated) call of a primitive arithmetic
; relation, <, = and /=, we re-express it in terms of
; not, equal, and < so that it can be linearized successfully.
; Otherwise, we return term.

; Warning: This function expands the definitions of the primitives
; above without considering their guards.  This is unsound if the
; expanded form is used in place of the term.  For example, (= x y)
; is here expanded to (equal x y), and in the case that the
; guards are violated the two terms are not equivalent.  Do not call
; this function casually!

; What is the intended use of this function?  Suppose the user has
; proved a theorem, (implies hyps (= a b)) and wants it stored as a
; :LINEAR rule.  We instead store a rule concluding with (equal a b)!
; Note that the rule we store is not equivalent to the rule proved!
; We've ignored the acl2-numberp guards on =.  Isn't that scary?  Yes.
; But how do :LINEAR rules get used?  Let max be one of the maximal
; terms of the rule we store and suppose we encounter a term, max',
; that is an instance of max.  Then we will instantiate the stored
; conclusion (equal a b) with the substitution derived from max' to
; obtain (equal a' b') and then linearize that.  The linearization of
; an equality insists that both arguments be known rational -- i.e.
; that their type-sets are a subset of *ts-rational*.  Thus, in
; essence we are acting as though we had the theorem (implies (and
; (rationalp a) (rationalp b) hyps) (equal a b)) and use type-set to
; relieve the first two hyps.  But this imagined theorem is an easy
; consequence of (implies hyps (= a b)) given that (rationalp a) and
; (rationalp b) let us reduce (= a b) to (equal a b).

  (mv-let (negativep atm)
          (strip-not term)
          (let ((atm (cond ((variablep atm) atm)
                           ((fquotep atm) atm)
                           (t (expand-inequality-fncall1 atm)))))
            (cond
             (negativep (dumb-negate-lit atm))
             (t atm)))))

; Once we linearize the conclusion of a :LINEAR lemma, we extract all the
; linear variables (i.e., terms in the alist of the polys) and identify
; those that are "maximal."

(defun all-vars-in-poly-lst (lst)

; Lst is a list of polynomials.  We return the list of all linear variables
; used.

  (cond ((null lst) nil)
        (t (union-equal (strip-cars (access poly (car lst) :alist))
                        (all-vars-in-poly-lst (cdr lst))))))

; Part of the notion of maximal is "always bigger", which we develop here.

(defun subbagp-eq (bag1 bag2)
  (cond ((null bag1) t)
        ((null bag2) nil)
        ((member-eq (car bag1) bag2)
         (subbagp-eq (cdr bag1) (remove1-eq (car bag1) bag2)))
        (t nil)))

(defun always-biggerp-data (term)

; See always-biggerp.

  (mv-let (fn-cnt p-fn-cnt)
          (fn-count term)
          (cons term (cons fn-cnt (cons p-fn-cnt (all-vars-bag term nil))))))

(defun always-biggerp-data-lst (lst)

; See always-biggerp.

  (cond ((null lst) nil)
        (t (cons (always-biggerp-data (car lst))
                 (always-biggerp-data-lst (cdr lst))))))

(defun always-biggerp (abd1 abd2)

; We say term1 is always bigger than term2 if all instances of term1
; have a larger fn-count (actually lexicographic order of fn-count and
; pseudo-fn-count) than the corresponding instances of term2.  This is
; equivalent to saying that the fn-count of term1 is larger than that
; of term2 (by "fn-count" here we mean the lexicographic order of
; fn-count and pseudo-fn-count) and the variable bag for term2 is a
; subbag of that for term1.

; Because we will be doing this check repeatedly across a list of terms
; we have converted the terms into "abd" (always bigger data)
; triples of the form (term fn-cnt . vars).  Our two arguments are
; abd triples for term1 and term2.

  (and (or (> (cadr abd1) (cadr abd2))
           (and (eql (cadr abd1) (cadr abd2))
                (> (caddr abd1) (caddr abd2))))
       (subbagp-eq (cdddr abd2) (cdddr abd1))))

; That completes the notion of always-biggerp.  We now complete the
; notion of "maximal term".  It is probably best to read backwards from
; that defun.

(defun no-element-always-biggerp (abd-lst abd)

; abd-lst is a list of always-biggerp-data triples.  Abd is one such
; triple.  If there is an element of the lst that is always bigger than
; abd, we return nil; else t.

  (cond ((null abd-lst) t)
        ((always-biggerp (car abd-lst) abd) nil)
        (t (no-element-always-biggerp (cdr abd-lst) abd))))

(defun maximal-terms1 (abd-lst abd-lst0 needed-vars)

; See maximal-terms.

  (cond ((null abd-lst) nil)
        ((and (nvariablep (car (car abd-lst)))
              (not (fquotep (car (car abd-lst))))
              (not (flambda-applicationp (car (car abd-lst))))
              (not (eq (ffn-symb (car (car abd-lst))) 'if))
              (subsetp-eq needed-vars (cdddr (car abd-lst)))
              (no-element-always-biggerp abd-lst0 (car abd-lst)))
         (cons (car (car abd-lst))
               (maximal-terms1 (cdr abd-lst) abd-lst0 needed-vars)))
        (t (maximal-terms1 (cdr abd-lst) abd-lst0 needed-vars))))

(defun maximal-terms (lst hyp-vars concl-vars)

; Lst is a list of terms.  Hyp-vars and concl-vars are the variables
; occurring in the hypothesis and conclusion, respectively, of some
; lemma.  We wish to return the subset of "maximal terms" in lst.
; These terms will be used as triggers to fire the :LINEAR rule built
; from (implies hyps concl).  A term is maximal if it is not a
; variable, quote, lambda-application or IF, its variables plus those
; of the hyps include those of the conclusion (so there are no free
; vars in the conclusion after we match on the maximal term and
; relieve the hyps) and there is no other term in lst that is "always
; bigger."  Intuitively, the idea behind "always bigger" is that the
; fn-count of one term is larger than that of the other, under all
; instantiations.

; The subroutine maximal-terms1 does most of the work.  We convert the
; list of terms into an abd list, containing triples of the form (term
; fn-cnt . vars) for each term in lst.  Then we pass maximal-terms1
; two copies of this; the first it recurs down so as to visit one term
; at a time and the second it holds fixed to use to search for bigger
; terms.  Finally, a condition equivalent to the variable restriction
; above is that each maximal term contain at least those variables in
; the conclusion which aren't in the hyps, and so we compute that set
; here to avoid more consing.

  (let ((abd-lst (always-biggerp-data-lst lst)))
    (maximal-terms1 abd-lst abd-lst
                    (if (eq hyp-vars t)
                        nil
                      (set-difference-eq concl-vars hyp-vars)))))

; That finishes maximal-terms.  Onward.

; We now develop the functions to support the friendly user interface.

(defun collect-when-ffnnamesp (fns lst)

; Return the subset of lst consisting of those terms that mention any
; fn in fns.

  (cond ((null lst) nil)
        ((ffnnamesp fns (car lst))
         (cons (car lst) (collect-when-ffnnamesp fns (cdr lst))))
        (t (collect-when-ffnnamesp fns (cdr lst)))))

(defun make-free-max-terms-msg1 (max-terms vars hyps)

; This function is used by make-free-max-terms-msg1 and is building a
; list of pairs of the form (str . alist').  Each such pair is
; suitable for giving to the ~@ fmt directive, which will print the
; string str under the alist obtained by appending alist' to the
; current alist.  The idea here is simply to identify those max-terms
; that give rise to free-vars in the hyps and to comment upon them.

  (cond ((null max-terms) nil)
        ((subsetp-eq vars (all-vars (car max-terms)))
         (make-free-max-terms-msg1 (cdr max-terms) vars hyps))
        (t (cons
            (cons
             "When ~xN is triggered by ~xT the variable~#V~[~/s~] ~&V ~
              will be chosen by searching for ~#H~[an ~
              instance~/instances~] of ~&H among the hypotheses of the ~
              conjecture being rewritten.  "
             (list (cons #\T (car max-terms))
                   (cons #\V (set-difference-eq vars
                                                (all-vars (car max-terms))))
                   (cons #\H (hyps-that-instantiate-free-vars
                              (set-difference-eq vars
                                                 (all-vars (car max-terms)))
                              hyps))))
            (make-free-max-terms-msg1 (cdr max-terms) vars hyps)))))

(defun make-free-max-terms-msg (name max-terms vars hyps)

; We make a message suitable for giving to the ~* fmt directive that
; will print out a sequence of sentences of the form "When name is
; triggered by foo the variables u and v will be chosen by searching
; for the hypotheses h1 and h2.  When ..."  Vars is a list of the
; variables occurring in the hypotheses of the lemma named name.
; Hyps is the list of hyps.  We always end with two spaces.

  (list* ""
         "~@*"
         "~@*"
         "~@*"
         (make-free-max-terms-msg1 max-terms vars hyps)
         (list (cons #\N name))))

(defun external-linearize (term ens wrld state)
  (linearize term
             t ;positivep
             nil ;type-alist
             ens
             (ok-to-force-ens ens)
             wrld ;wrld
             nil ;ttree
             state))

(defun bad-synp-hyp-msg-for-linear (max-terms hyps wrld)
  (if (null max-terms)
      (mv nil nil)
    (let ((bad-synp-hyp-msg (bad-synp-hyp-msg hyps (all-vars (car max-terms))
                                               nil wrld)))
      (if bad-synp-hyp-msg
          (mv bad-synp-hyp-msg (car max-terms))
        (bad-synp-hyp-msg-for-linear (cdr max-terms) hyps wrld)))))

(defun show-double-rewrite-opportunities-linear (hyps max-terms final-term name
                                                      ctx ens wrld state)
  (cond ((endp max-terms)
         state)
        (t (pprogn (show-double-rewrite-opportunities
                    (double-rewrite-opportunities
                     1
                     hyps
                     (covered-geneqv-alist (car max-terms) nil nil nil ens
                                           wrld)
                     final-term
                     "the conclusion"
                     *geneqv-iff* ; final-geneqv
                     ens wrld)
                    :linear name
                    (msg " for trigger term ~x0"
                         (untranslate (car max-terms) nil wrld))
                    ctx state)
                   (show-double-rewrite-opportunities-linear
                    hyps (cdr max-terms) final-term name ctx ens wrld
                    state)))))

(defun no-linear-msg (name concl extra ens wrld state)
  (msg
   "No :LINEAR rule can be generated from ~x0.  See :DOC linear.~@1~@2"
   name
   (mv-let (flg x ttree)
     (eval-ground-subexpressions concl ens wrld state nil)
     (declare (ignore flg ttree))
     (if (quotep x)
         (msg "  Note that after ground evaluation, the ~
                           conclusion, ~x0, was treated as the constant, ~x1."
              (untranslate concl t wrld)
              (untranslate x t wrld))
       ""))
   extra))

(defun chk-acceptable-linear-rule2 (name match-free trigger-terms hyps concl
                                         ctx ens wrld state)

; This is the basic function for checking that (implies (AND . hyps)
; concl) generates a useful :LINEAR rule.  If it does not, we cause an
; error.  If it does, we may print some warnings regarding the rule
; generated.  The superior functions, chk-acceptable-linear-rule1
; and chk-acceptable-linear-rule just cycle down to this one after
; flattening the IMPLIES/AND structure of the user's input term.

; The trigger-terms above are those supplied by the user in the rule class.  If
; nil, we are to generate the trigger terms automatically, choosing all of the
; maximal terms.  If provided, we know that each element of trigger-terms is a
; term that is a legal (if possibly silly) trigger for each rule.

  (let* ((xconcl (expand-inequality-fncall concl))
         (lst (and (null trigger-terms) ; optimization
                   (external-linearize xconcl ens wrld state))))
    (cond ((and (null trigger-terms)
                (null lst))
           (er soft ctx
               "~@0"
               (no-linear-msg name concl "" ens wrld state)))
          ((not (null (cdr lst)))
           (er soft ctx
               "No :LINEAR rule can be generated from ~x0 because the ~
                linearization of its conclusion, which in normal form is ~p1, ~
                produces a disjunction of polynomial inequalities.  See :DOC ~
                linear."
               name
               (untranslate xconcl t wrld)))
          (t
           (let* ((all-vars-hyps (and (null trigger-terms) ; optimization
                                      (all-vars-in-hyps hyps)))
                  (potential-free-vars
                   (free-vars-in-hyps-considering-bind-free hyps nil wrld))
                  (all-vars-in-poly-lst
                   (and (null trigger-terms) ; optimization
                        (all-vars-in-poly-lst (car lst))))
                  (max-terms
                   (or trigger-terms
                       (maximal-terms all-vars-in-poly-lst
                                      all-vars-hyps
                                      (all-vars concl))))
                  (warn-non-rec (not (warning-disabled-p "Non-rec")))
                  (non-rec-fns-alist
                   (and warn-non-rec
                        (non-recursive-fnnames-alist-lst max-terms ens wrld)))
                  (non-rec-fns (strip-cars non-rec-fns-alist))
                  (bad-max-terms (collect-when-ffnnamesp
                                  non-rec-fns
                                  max-terms))
                  (free-max-terms-msg
                   (make-free-max-terms-msg name
                                            max-terms
                                            potential-free-vars
                                            hyps)))
             (cond
              ((null max-terms)
               (cond
                ((and (null trigger-terms)
                      (null all-vars-in-poly-lst))
                 (er soft ctx
                     "No :LINEAR rule can be generated from ~x0 because there ~
                      are no ``maximal terms'' in the inequality produced ~
                      from its conclusion.  In fact, the inequality has ~
                      simplified to one that has no variables."
                     name))
                (t
                 (er soft ctx
                     "No :LINEAR rule can be generated from ~x0 because there ~
                      are no ``maximal terms'' in the inequality produced ~
                      from its conclusion.  The inequality produced from its ~
                      conclusion involves a linear polynomial in the ~
                      unknown~#1~[~/s~] ~&1.  No unknown above has the three ~
                      properties of a maximal term (see :DOC linear).  What ~
                      can you do?  The most direct solution is to make this a ~
                      :REWRITE rule rather than a :LINEAR rule.  Of course, ~
                      you then have to make sure your intended application ~
                      can suffer it being a :REWRITE rule!  A more ~
                      challenging (and sometimes more rewarding) alternative ~
                      is to package up some of your functions into a new ~
                      non-recursive function (either in the unknowns or the ~
                      hypotheses) so as to create a maximal term.  Of course, ~
                      if you do that, you have to arrange to use that ~
                      non-recursive function in the intended applications of ~
                      this rule."
                     name all-vars-in-poly-lst))))
              (t
               (mv-let (bad-synp-hyp-msg bad-max-term)
                 (bad-synp-hyp-msg-for-linear max-terms hyps wrld)
                 (cond
                  (bad-synp-hyp-msg
                   (er soft ctx
                       "While checking the hypotheses of ~x0 and using the ~
                        trigger term ~x1, the following error message was ~
                        generated:~%~%~@2"
                       name
                       bad-max-term
                       bad-synp-hyp-msg))
                  (t
                   (pprogn
                    (if (warning-disabled-p "Double-rewrite")
                        state
                      (show-double-rewrite-opportunities-linear
                       hyps max-terms concl name ctx ens wrld state))
                    (cond
                     ((equal max-terms bad-max-terms)
                      (warning$ ctx "Non-rec"
                                `("A :LINEAR rule generated from ~x0 will be ~
                                   triggered only by terms containing the ~
                                   function symbol~#1~[ ~&1, which has a ~
                                   non-recursive definition.~@2  Unless this ~
                                   definition is~/s ~&1, which have ~
                                   non-recursive definitions.~@2  Unless ~
                                   these definitions are~] disabled, such ~
                                   triggering terms are unlikely to arise and ~
                                   so ~x0 is unlikely to ever be used."
                                  (:name ,name)
                                  (:non-recursive-fns
                                   ,(hide-lambdas non-rec-fns))
                                  (:rule-class :linear))
                                name
                                (hide-lambdas non-rec-fns)
                                (non-rec-def-rules-msg non-rec-fns-alist)))
                     (bad-max-terms
                      (warning$ ctx "Non-rec"
                                "A :LINEAR rule generated from ~x0 will be ~
                                 triggered by the terms ~&1. ~N2 of these ~
                                 terms, namely ~&3, contain~#3~[s~/~] the ~
                                 function symbol~#4~[ ~&4, which has a ~
                                 non-recursive definition.~@5  Unless this ~
                                 definition is~/s ~&4, which have ~
                                 non-recursive definitions.~@5  Unless these ~
                                 definitions are~] disabled, ~x0 is unlikely ~
                                 to be triggered via ~#3~[this term~/these ~
                                 terms~]."
                                name
                                max-terms
                                (length bad-max-terms)
                                bad-max-terms
                                (hide-lambdas non-rec-fns)
                                (non-rec-def-rules-msg non-rec-fns-alist)))
                     (t state))
                    (cond
                     ((and (nth 4 free-max-terms-msg)
                           (null match-free))
                      (pprogn
                       (warning$ ctx "Free"
                                 "A :LINEAR rule generated from ~x0 will be ~
                                  triggered by the term~#1~[~/s~] ~&1.  ~
                                  ~*2This is generally a severe restriction ~
                                  on the applicability of the :LINEAR rule~@3."
                                 name
                                 max-terms
                                 free-max-terms-msg
                                 (let ((len-max-terms (length max-terms))
                                       (len-bad-max-terms
                                        (length (nth 4 free-max-terms-msg))))
                                   (cond ((eql len-bad-max-terms
                                               len-max-terms)
                                          "")
                                         ((eql len-bad-max-terms 1)
                                          " for this trigger")
                                         (t (msg " for these ~n0 triggers"
                                                 len-bad-max-terms)))))
                       (free-variable-error? :linear name ctx wrld state)))
                     (t (value nil))))))))))))))

(defun chk-acceptable-linear-rule1 (name match-free trigger-terms lst ctx ens
                                         wrld state)

; Each element of lst is a pair, (hyps . concl) and we check that each
; such pair, when interpreted as the term (implies (and . hyps)
; concl), generates a legal :LINEAR rule.

  (cond
   ((null lst) (value nil))
   (t (er-progn
       (chk-acceptable-linear-rule2 name match-free trigger-terms (caar lst)
                                    (cdar lst)
                                    ctx ens wrld state)
       (chk-acceptable-linear-rule1 name match-free trigger-terms (cdr lst)
                                    ctx ens wrld state)))))

(defun chk-acceptable-linear-rule (name match-free trigger-terms term ctx ens
                                        wrld state)

; We strip the conjuncts out of term and flatten those in the
; hypotheses of implications to obtain a list of implications, each of
; the form (IMPLIES (AND . hyps) concl), and each represented simply
; by a pair (hyps . concl).  For each element of that list we then
; determine whether it generates a legal :LINEAR rule.  See
; chk-acceptable-linear-rule2 for the guts of this test.  We either
; cause an error or return successfully.  We may print warning
; messages without causing an error.

  (chk-acceptable-linear-rule1 name match-free trigger-terms
                               (unprettyify (remove-guard-holders term wrld))
                               ctx ens wrld state))

; And now, to adding :LINEAR rules...

(defun add-linear-rule3 (rune nume hyps concl max-terms
                              backchain-limit-lst match-free put-match-free-done
                              wrld)
  (cond
   ((null max-terms) wrld)
   (t (let* ((match-free-value
              (match-free-value match-free hyps (car max-terms) wrld))
             (linear-rule
              (make linear-lemma
                    :rune rune
                    :nume nume
                    :hyps hyps
                    :concl concl
                    :max-term (car max-terms)
                    :backchain-limit-lst
                    (rule-backchain-limit-lst backchain-limit-lst hyps wrld
                                              :rewrite)
                    :match-free match-free-value))
             (wrld1 (putprop (ffn-symb (access linear-lemma linear-rule
                                               :max-term))
                             'linear-lemmas
                             (cons linear-rule
                                   (getpropc (ffn-symb
                                              (access linear-lemma linear-rule
                                                      :max-term))
                                             'linear-lemmas nil wrld))
                             wrld)))
        (add-linear-rule3 rune nume hyps concl (cdr max-terms)
                          backchain-limit-lst
                          match-free
                          (or put-match-free-done match-free-value)
                          (if put-match-free-done

; In this case we have already added this rune to the appropriate world global,
; so we do not want to do so again.

                              wrld1
                            (put-match-free-value match-free-value rune
                                                  wrld1)))))))

(defun add-linear-rule2 (rune nume trigger-terms hyps concl
                              backchain-limit-lst match-free ens wrld state)
  (let* ((concl (remove-guard-holders concl wrld))
         (xconcl (expand-inequality-fncall concl))
         (lst (and (null trigger-terms) ; optimization
                   (external-linearize xconcl ens wrld state)))
         (hyps (preprocess-hyps hyps wrld))
         (all-vars-hyps (and (null trigger-terms) ; optimization
                             (all-vars-in-hyps hyps)))
         (max-terms
          (or trigger-terms
              (maximal-terms (all-vars-in-poly-lst (car lst))
                             all-vars-hyps
                             (all-vars concl)))))
    (cond ((and (null trigger-terms)
                (null lst))
           (er hard 'add-linear-rule2
               "~@0"
               (no-linear-msg (base-symbol rune)
                              concl
                              (msg "  This can happen during ~x0 or the ~
                                    second pass of a call of ~x1, when the ~
                                    current-theory is different than when the ~
                                    rule was originally checked.  You can ~
                                    avoid this error by supplying ~
                                    :trigger-terms in your :linear rule-class."
                                   'include-book 'encapsulate)
                              ens wrld state)))
          (t (add-linear-rule3 rune nume hyps xconcl max-terms
                               backchain-limit-lst match-free nil wrld)))))

(defun add-linear-rule1 (rune nume trigger-terms lst
                              backchain-limit-lst match-free ens wrld state)
  (cond ((null lst) wrld)
        (t (add-linear-rule1 rune nume trigger-terms (cdr lst)
                             backchain-limit-lst
                             match-free
                             ens
                             (add-linear-rule2 rune nume
                                               trigger-terms
                                               (caar lst)
                                               (cdar lst)
                                               backchain-limit-lst
                                               match-free
                                               ens wrld state)
                             state))))

(defun add-linear-rule (rune nume trigger-terms term
                             backchain-limit-lst match-free ens wrld state)

; Sol Swords sent the following example on 10/12/09, which failed because of
; the modification after Version_3.6.1 to mv-let (to introduce mv-list in the
; expansion), until the call below of remove-guard-holders was added.

; (defun break-cons (x)
;    (mv (car x) (cdr x)))

; (defthm break-cons-size-decr-0
;    (mv-let (car cdr)
;      (break-cons x)
;      (declare (ignore cdr))
;      (implies (consp x)
;               (< (acl2-count car) (acl2-count x))))
;    :rule-classes :linear)

; (defthm break-cons-size-decr-1
;    (mv-let (car cdr)
;      (break-cons x)
;      (declare (ignore car))
;      (implies (consp x)
;               (< (acl2-count cdr) (acl2-count x))))
;    :rule-classes :linear)

; (in-theory (disable break-cons acl2-count mv-nth))

; (defun recur-over-break-cons (x)
;    (if (atom x)
;        (list x)
;      (mv-let (car cdr) (break-cons x)
;        (append (recur-over-break-cons car)
;                (recur-over-break-cons cdr)))))

  (add-linear-rule1 rune nume trigger-terms
                    (unprettyify (remove-guard-holders term wrld))
                    backchain-limit-lst match-free ens wrld state))

;---------------------------------------------------------------------------
; Section:  :WELL-FOUNDED-RELATION Rules

(defun destructure-well-founded-relation-rule (term)

; We check that term is the translation of one of the two forms
; described in :DOC well-founded-relation.  We return two results, (mv
; mp rel).  If mp is nil in the result, then term is not of the
; required form.  If mp is t, then term is of the second general form
; (i.e., we act as though t were the function symbol for (lambda (x)
; t)).  With that caveat, if the mp is non-nil then term establishes
; that rel is a well-founded relation on mp-measures.

  (case-match
   term
   (('IF ('IMPLIES (mp x) ('O-P (fn x)))
         ('IMPLIES ('IF (mp x)
                        ('IF (mp y) (rel x y) ''NIL)
                        ''NIL)
                   ('O< (fn x) (fn y)))
         ''NIL)
    (cond ((and (symbolp mp)
                (variablep x)
                (symbolp fn)
                (variablep y)
                (not (eq x y))
                (symbolp rel))
           (mv mp rel))
          (t (mv nil nil))))
   (('IF ('O-P (fn x))
         ('IMPLIES (rel x y)
                   ('O< (fn x) (fn y)))
         ''NIL)
    (cond ((and (variablep x)
                (symbolp fn)
                (variablep y)
                (not (eq x y))
                (symbolp rel))
           (mv t rel))
          (t (mv nil nil))))
   (& (mv nil nil))))

(defun chk-acceptable-well-founded-relation-rule (name term ctx wrld state)
  (mv-let
   (mp rel)
   (destructure-well-founded-relation-rule term)
   (cond
    ((null mp)
     (er soft ctx
         "No :WELL-FOUNDED-RELATION rule can be generated for ~x0 ~
          because it does not have either of the two general forms ~
          described in :DOC well-founded-relation."
         name))
    ((and (assoc-eq rel (global-val 'well-founded-relation-alist wrld))
          (not (eq (cadr (assoc-eq rel
                                   (global-val 'well-founded-relation-alist
                                               wrld)))
                   mp)))
     (er soft ctx
         "~x0 was shown in ~x1 to be well-founded~@2  We do not permit more ~
          than one domain to be associated with a well-founded relation.  To ~
          proceed in this direction, you should define some new function ~
          symbol to be ~x0 and state your well-foundedness in terms of the ~
          new function."
         rel
         (cadr (cddr (assoc-eq rel
                               (global-val 'well-founded-relation-alist
                                           wrld))))
         (if (eq (cadr (assoc-eq rel
                                 (global-val 'well-founded-relation-alist
                                             wrld)))
                 t)
             "."
             (msg " on objects satisfying ~x0."
                  (cadr (assoc-eq rel
                                  (global-val 'well-founded-relation-alist
                                              wrld)))))))
    (t (value nil)))))

(defun add-well-founded-relation-rule (rune nume term wrld)
  (declare (ignore nume))
  (mv-let (mp rel)
          (destructure-well-founded-relation-rule term)
          (global-set 'well-founded-relation-alist
                      (cons (cons rel (cons mp rune))
                            (global-val 'well-founded-relation-alist wrld))
                      wrld)))

;---------------------------------------------------------------------------
; Section:  :BUILT-IN-CLAUSE Rules

(defun chk-acceptable-built-in-clause-rule2 (name hyps concl ctx wrld state)

; This is the basic function for checking that (IMPLIES (AND . hyps) concl)
; generates a useful built-in clause rule.  If it does not, we cause an error.
; The superior functions, chk-acceptable-built-in-clause-rule1 and
; chk-acceptable-built-in-clause-rule just cycle down to this one after
; flattening the IMPLIES/AND structure of the user's input term.

  (let* ((term (if (null hyps)
                   concl
                   (mcons-term* 'if (conjoin hyps) concl *t*)))
         (clauses (clausify term nil t (sr-limit wrld))))
    (cond ((null clauses)
           (er soft ctx
               "~x0 is an illegal :built-in-clause rule because ~p1 clausifies ~
                to nil, indicating that it is a propositional tautology.  See ~
                :DOC built-in-clause."
               name
               (untranslate
                (cond ((null hyps) concl)
                      (t (mcons-term* 'implies (conjoin hyps) concl)))
                t
                wrld)))
          (t (value nil)))))

(defun chk-acceptable-built-in-clause-rule1 (name lst ctx wrld state)

; Each element of lst is a pair, (hyps . concl) and we check that each such
; pair, when interpreted as the term (implies (and . hyps) concl), generates
; one or more clauses to be built-in.

  (cond
   ((null lst) (value nil))
   (t
    (er-progn
     (chk-acceptable-built-in-clause-rule2 name (caar lst) (cdar lst) ctx
                                           wrld state)
     (chk-acceptable-built-in-clause-rule1 name (cdr lst) ctx wrld state)))))

(defun chk-acceptable-built-in-clause-rule (name term ctx wrld state)

; We strip the conjuncts out of term and flatten those in the hypotheses of
; implications to obtain a list of implications, each of the form (IMPLIES (AND
; . hyps) concl), and each represented simply by a pair (hyps . concl).  For
; each element of that list we then determine whether it generates one or more
; clauses.  See chk-acceptable-built-in-clause-rule2 for the guts of this test.
; We either cause an error or return successfully.

  (chk-acceptable-built-in-clause-rule1 name (unprettyify term) ctx
                                        wrld state))

; So now we work on actually generating and adding :BUILT-IN-CLAUSE rules.

(mutual-recursion

(defun fn-and-maximal-level-no (term wrld fn max)

; We explore term and return (mv fn max), where fn is an "explicit" function
; symbol of term, max is its get-level-no, and that level number is maximal in
; term.  By an "explicit" function symbol of term we mean one not on
; *one-way-unify1-implicit-fns*.  We return the initial fn and max unless some
; explicit symbol of term actually betters it.  If you call this with fn=nil
; and max=-1 you will get back a legitimate function symbol if term contains at
; least one explicit symbol.  Furthermore, it is always the maximal symbol
; occurring first in print-order.

  (cond
   ((variablep term) (mv fn max))
   ((fquotep term) (mv fn max))
   ((flambdap (ffn-symb term))
    (mv-let (fn max)
            (fn-and-maximal-level-no (lambda-body (ffn-symb term)) wrld fn max)
            (fn-and-maximal-level-no-lst (fargs term) wrld fn max)))
   ((member-eq (ffn-symb term) *one-way-unify1-implicit-fns*)
    (fn-and-maximal-level-no-lst (fargs term) wrld fn max))
   (t (let ((n (get-level-no (ffn-symb term) wrld)))
        (cond
         ((> n max)
          (fn-and-maximal-level-no-lst (fargs term) wrld (ffn-symb term) n))
         (t (fn-and-maximal-level-no-lst (fargs term) wrld fn max)))))))

(defun fn-and-maximal-level-no-lst (lst wrld fn max)
  (cond
   ((null lst) (mv fn max))
   (t (mv-let (fn max)
              (fn-and-maximal-level-no (car lst) wrld fn max)
              (fn-and-maximal-level-no-lst (cdr lst) wrld fn max)))))

)

(defun built-in-clause-discriminator-fn (cl wrld)
  (mv-let (fn max)
          (fn-and-maximal-level-no-lst cl wrld nil -1)
          (declare (ignore max))
          fn))

(defun all-fnnames-subsumer (cl wrld)

; Let cl be a clause which is about to be built in.  Cl subsumes another
; clause, cla, if under some instantiation of cl, cl', the literals of cl' are
; a subset of those of cla.  Thus, a necessary condition for cl to subsume cla
; is that the function symbols of cl be a subset of those of cla.  However,
; one-way-unify1 knows that (binary-+ '1 x) can be instantiated to be '7, by
; letting x be '6.  Thus, if by "the function symbols" of a clause we mean
; those that explicitly occur, i.e., all-fnnames-lst, then, contrary to what
; was just said, it is possible for cl to subsume cla without the function
; symbols of cl being a subset of those of cla:  let cl contain (binary-+ '1 x)
; where cla contains '7 and no mention of binary-+.  So we here compute the
; list of function symbols of cl which must necessarily occur in cla.  It is
; always sound to throw out symbols from the list returned here.  In addition,
; we make sure that the "discriminator function symbol" of cl occur first in
; the list.  That symbol will be used to classify this subsumer into a bucket
; in the built-in-clause list.

  (let ((syms (set-difference-eq (all-fnnames-lst cl)
                                 *one-way-unify1-implicit-fns*))
        (discrim-fn (built-in-clause-discriminator-fn cl wrld)))
    (cond ((null discrim-fn) syms)
          (t (cons discrim-fn (remove1-eq discrim-fn syms))))))

(defun make-built-in-clause-rules1 (rune nume clauses wrld)

; We build a built-in-clause record for every element of clauses.  We put the
; last literal of each clause first on the heuristic grounds that the last
; literal of a user-supplied clause is generally the most interesting and thus
; the one the subsumption check should look at first.

; Note:  The :all-fnnames computed here has the property that the discriminator
; function symbol is the car and the remaining functions are in the cdr.  When
; a built-in-clause record is stored into the built-in-clauses alist, the
; record is changed; the discriminator is stripped out, leaving the remaining
; fns as the :all-fnnames.

  (cond ((null clauses) nil)
        (t (let ((cl (cons (car (last (car clauses)))
                           (butlast (car clauses) 1))))
             (cons (make built-in-clause
                         :rune rune
                         :nume nume
                         :clause cl
                         :all-fnnames (all-fnnames-subsumer cl wrld))
                   (make-built-in-clause-rules1 rune nume
                                                (cdr clauses) wrld))))))

(defun chk-initial-built-in-clauses (lst wrld good-lst some-badp)

; This function sweeps down the list of initial built-in clause records and
; checks that the :all-fnnames of each is set properly given the current wrld.
; The standard top-level call of this function is (chk-initial-built-in-clauses
; *initial-built-in-clauses* wrld nil nil) where wrld is the world in which you
; wish to check the appropriateness of the initial setting.  This function
; returns either nil, meaning that everything was ok, or a new copy of lst
; which is correct for the current wrld.

  (cond
   ((null lst)
    (cond
     (some-badp (reverse good-lst))
     (t nil)))
   (t (let* ((clause (access built-in-clause (car lst) :clause))
             (fnnames1 (access built-in-clause (car lst) :all-fnnames))
             (fnnames2 (all-fnnames-subsumer clause wrld)))
        (chk-initial-built-in-clauses
         (cdr lst) wrld
         (cons `(make built-in-clause
                      :nume nil
                      :rune *fake-rune-for-anonymous-enabled-rule*
                      :clause ',clause
                      :all-fnnames ',fnnames2)
               good-lst)
         (or some-badp
             (not (equal fnnames1 fnnames2))))))))

(defun make-built-in-clause-rules (rune nume lst wrld)

; Each element of lst is a pair, (hyps . concl).  We generate and collect the
; clauses for each such pair.

  (cond ((null lst) nil)
        (t (let* ((hyps (caar lst))
                  (concl (cdar lst))
                  (clauses (clausify
                            (if (null hyps)
                                concl
                                (mcons-term* 'if (conjoin hyps) concl *t*))
                            nil t (sr-limit wrld))))
             (append (make-built-in-clause-rules1 rune nume clauses wrld)
                     (make-built-in-clause-rules rune nume (cdr lst) wrld))))))

(defun classify-and-store-built-in-clause-rules (lst pots wrld)

; Lst is a list of built-in-clause records.  Each record contains an
; :all-fnnames field, which contains a (possibly empty) list of function
; symbols.  The first symbol in the :all-fnnames list is the "discriminator
; function symbol" of the clause, the heaviest function symbol in the clause.
; Pots is an alist in which each entry pairs a symbol, fn, to a list of
; built-in-clause records; the list has the property that every clause in it
; has fn as its discriminator function symbol.  We add each record in lst to
; the appropriate pot in pots.

; If a record has :all-fnnames nil then it is most likely a primitive built-in
; clause, i.e., a member of *initial-built-in-clauses*.  The nil is a signal to
; this function to compute the appropriate :all-fnnames using the function
; all-fnnames-subsumer which is what we use when we build a built-in clause
; record for the user with make-built-in-clause-rules1.  This is just a rugged
; way to let the list of implicit function symbols known to one-way-unify1 vary
; without invalidating our *initial-built-in-clauses* setting.

; But it is possible, perhaps, for a user-supplied built-in clause to contain
; no function symbols of the kind returned by all-fnnames-subsumer.  For
; example, the user might prove 7 as a built-in clause.  Perhaps a
; non-pathological example arises, but I haven't bothered to think of one.
; Instead, this is handled soundly, as follows.  If the :all-fnnames is nil we
; act like it hasn't been computed yet (as above) and compute it.  Then we
; consider the discriminator function symbol to the car of the resulting list,
; which might be nil.  There is a special pot for the nil "discriminator
; function symbol".

  (cond ((null lst) pots)
        (t (let* ((bic (car lst))
                  (fns (or (access built-in-clause bic :all-fnnames)
                           (all-fnnames-subsumer
                            (access built-in-clause bic :clause)
                            wrld)))
                  (fn (car fns))
                  (pot (cdr (assoc-eq fn pots))))
             (classify-and-store-built-in-clause-rules
              (cdr lst)
              (put-assoc-eq fn
                            (cons (change built-in-clause bic
                                          :all-fnnames (cdr fns))
                                  pot)
                            pots)
              wrld)))))

(defun add-built-in-clause-rule (rune nume term wrld)

; We strip the conjuncts out of term and flatten those in the hypotheses of
; implications to obtain a list of implications and then clausify each and
; store each clause as a :BUILT-IN-CLAUSE rule.  We maintain the invariant
; that 'half-length-built-in-clauses is equal to the (floor n 2), where n
; is the length of 'built-in-clauses.

  (let ((rules (make-built-in-clause-rules rune nume (unprettyify term)
                                           wrld)))

; Every rule in rules is stored (somewhere) into built-in-clauses, so the
; number of clauses goes up by (length rules).  Once we had a bug here:  we
; incremented 'half-length-built-in-clauses by half the length of rules.  That
; was pointless since we're dealing with integers here:  rules is most often of
; length 1 and so we would increment by 0 and never accumulate all those 1/2's!

    (global-set 'half-length-built-in-clauses
                (floor (+ (length rules)
                          (length (global-val 'built-in-clauses wrld)))
                       2)
                (global-set 'built-in-clauses
                            (classify-and-store-built-in-clause-rules
                             rules
                             (global-val 'built-in-clauses wrld)
                             wrld)
                            wrld))))


;---------------------------------------------------------------------------
; Section:  :COMPOUND-RECOGNIZER Rules

(defun destructure-compound-recognizer (term)

; If term is one of the forms of a compound recognizer lemma we return
; its parity (TRUE, FALSE, WEAK-BOTH or STRONG-BOTH), the recognizer
; fn, its variablep argument in this term, and the type description
; term.  In the case of WEAK-BOTH the type description term is a pair
; -- not a term -- consisting of the true term and the false term.
; Otherwise we return four nils.

  (case-match term
              (('implies ('not (fn x)) concl)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'false fn x concl))
                     (t (mv nil nil nil nil))))
              (('implies (fn x) concl)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'true fn x concl))
                     (t (mv nil nil nil nil))))
              (('if ('implies (fn x) concl1)
                    ('implies ('not (fn x)) concl2)
                    ''nil)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'weak-both fn x (cons concl1 concl2)))
                     (t (mv nil nil nil nil))))
              (('if (fn x) concl1 concl2)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'weak-both fn x (cons concl1 concl2)))
                     (t (mv nil nil nil nil))))
              (('if ('implies ('not (fn x)) concl2)
                    ('implies (fn x) concl1)
                    ''nil)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'weak-both fn x (cons concl1 concl2)))
                     (t (mv nil nil nil nil))))
              (('if ('implies ('not (fn x)) concl2)
                    ('implies (fn x) concl1)
                    ''nil)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'weak-both fn x (cons concl1 concl2)))
                     (t (mv nil nil nil nil))))
              (('iff (fn x) concl)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'strong-both fn x concl))
                     (t (mv nil nil nil nil))))
              (('equal (fn x) concl)
               (cond ((and (variablep x)
                           (symbolp fn))
                      (mv 'strong-both fn x concl))
                     (t (mv nil nil nil nil))))
              (& (mv nil nil nil nil))))

(defun make-recognizer-tuple (rune nume parity fn var term ens wrld)

; If parity is 'WEAK-BOTH then term is really (tterm . fterm).  We
; create a recognizer-tuple from our arguments.  Nume is stored in
; the :nume and may be nil.  We return two results, the
; recognizer-tuple and the ttree justifying the type-set(s) in it.

  (case parity
        (true
         (mv-let (ts ttree)
                 (type-set-implied-by-term var nil term ens wrld nil)
                 (mv (make recognizer-tuple
                           :rune rune
                           :nume nume
                           :fn fn
                           :true-ts ts
                           :false-ts *ts-unknown*
                           :strongp nil)
                     ttree)))
        (false
         (mv-let (ts ttree)
                 (type-set-implied-by-term var nil term ens wrld nil)
                 (mv (make recognizer-tuple
                           :rune rune
                           :nume nume
                           :fn fn
                           :true-ts *ts-unknown*
                           :false-ts ts
                           :strongp nil)
                     ttree)))
        (weak-both
         (mv-let (tts ttree)
                 (type-set-implied-by-term var nil (car term) ens wrld nil)
                 (mv-let (fts ttree)
                         (type-set-implied-by-term var nil (cdr term) ens wrld ttree)
                         (mv (make recognizer-tuple
                                   :rune rune
                                   :nume nume
                                   :fn fn
                                   :true-ts tts
                                   :false-ts fts
                                   :strongp (ts= tts (ts-complement fts)))
                             ttree))))
        (otherwise

; Warning: We proved that (fn x) = term and one is tempted to build a
; :strongp = t rule.  But since we do not guarantee that term is
; equivalent to the type-set we deduce from it, we cannot just get the
; type-set for term and complement it for the false branch.  And we
; cannot guarantee to build a strong rule.  Instead, we act more or
; less like we do for weak-both: we compute independent type sets from
; term and (not term) and just in the case that they are complementary
; do we build a strong rule.

         (mv-let (tts ttree)
                 (type-set-implied-by-term var nil term ens wrld nil)
                 (mv-let (fts ttree)
                         (type-set-implied-by-term var t term ens wrld ttree)
                         (mv (make recognizer-tuple
                                   :rune rune
                                   :nume nume
                                   :fn fn
                                   :true-ts tts
                                   :false-ts fts
                                   :strongp (ts= tts (ts-complement fts)))
                             ttree))))))

(defun comment-on-new-recog-tuple1 (new-recog-tuple recognizer-alist
                                                    ctx state)

; This function compares a newly proposed recognizer tuple to each of
; the tuples on the recognizer-alist, expecting that it will be more
; restrictive than each of the existing tuples with the same :fn.  Let
; tts', fts', and strongp' be the obvious fields from the new tuple,
; and let tts, fts, and strongp be from an existing tuple.  Let ts' <=
; ts here mean (ts-subsetp ts' ts) and let strongp' <= strongp be true
; if either strongp is nil or strongp' is t.  Then we say the new
; tuple is ``more restrictive'' than the existing tuple iff

; (a) tts' <= tts & fts' <= fts & strongp' <= strongp, and

; (b) at least one of the three primed fields is different from its
; unprimed counterpart.

; For each old tuple that is at least as restrictive as the new tuple
; we print a warning.  We never cause an error.  However, we have
; coded the function and its caller so that if we someday choose to
; cause an error it will be properly handled.  (Without more experience
; with compound recognizers we do not know what sort of checks would be
; most helpful.)

  (cond
   ((null recognizer-alist) (value nil))
   ((and
     (ts-subsetp (access recognizer-tuple new-recog-tuple :true-ts)
                 (access recognizer-tuple (car recognizer-alist) :true-ts))
     (ts-subsetp (access recognizer-tuple new-recog-tuple :false-ts)
                 (access recognizer-tuple (car recognizer-alist) :false-ts))
     (or (access recognizer-tuple new-recog-tuple :strongp)
         (null (access recognizer-tuple (car recognizer-alist) :strongp)))
     (or
      (not (ts= (access recognizer-tuple new-recog-tuple :false-ts)
                (access recognizer-tuple (car recognizer-alist) :false-ts)))
      (not (ts= (access recognizer-tuple new-recog-tuple :true-ts)
                (access recognizer-tuple (car recognizer-alist) :true-ts)))
      (not (eq (access recognizer-tuple new-recog-tuple :strongp)
               (access recognizer-tuple (car recognizer-alist) :strongp)))))
    (comment-on-new-recog-tuple1 new-recog-tuple (cdr recognizer-alist)
                                 ctx state))
   (t (pprogn
       (warning$ ctx ("Compound-rec")
                 "The newly proposed compound recognizer rule ~x0 is not as ~
                  restrictive as the old rule ~x1.  See :DOC ~
                  compound-recognizer."
                 (base-symbol (access recognizer-tuple new-recog-tuple :rune))
                 (base-symbol (access recognizer-tuple (car recognizer-alist)
                                      :rune)))
       (comment-on-new-recog-tuple1 new-recog-tuple (cdr recognizer-alist)
                                    ctx state)))))

(defun comment-on-new-recog-tuple (new-recog-tuple ctx ens wrld state)

; This function prints out a warning advising the user of the type
; information to be extracted from a newly proposed compound
; recognizer.  We also print out a description of the lemmas used to
; derive this information.  We also compare the new recognizer tuple
; to any old tuples we have for the same function and print a suitable
; message should it be less ``restrictive.''

; We never cause an error, but this function and its caller are coded
; so that if we someday choose to cause an error it will be properly
; handled.  (Without more experience with compound recognizers we do
; not know what sort of checks would be most helpful.)

  (let* ((fn (access recognizer-tuple new-recog-tuple :fn))
         (pred (fcons-term* fn 'x)))
    (mv-let
     (tts-term ttree)
     (convert-type-set-to-term
      'x (access recognizer-tuple new-recog-tuple :true-ts) ens wrld nil)
     (mv-let
      (fts-term ttree)
      (convert-type-set-to-term
       'x (access recognizer-tuple new-recog-tuple :false-ts) ens wrld ttree)
      (let ((tts-term (untranslate tts-term t wrld))
            (fts-term (untranslate fts-term t wrld)))
        (er-progn
         (if (and (ts= (access recognizer-tuple new-recog-tuple :true-ts)
                       *ts-unknown*)
                  (ts= (access recognizer-tuple new-recog-tuple :false-ts)
                       *ts-unknown*))
             (er soft ctx
                 "When ~x0 is assumed true, ~x1 will allow us to deduce ~
                  nothing about the type of X.  Also, when ~x0 is assumed ~
                  false, ~x1 will allow us to deduce nothing about the type of ~
                  X.  Thus this is not a legal compound recognizer rule.  See ~
                  doc :compound-recognizer if these observations surprise you."
                 pred
                 (base-symbol (access recognizer-tuple new-recog-tuple :rune)))
             (value nil))
         (pprogn
          (observation
           ctx
           "When ~x0 is assumed true, ~x1 will allow us to deduce ~#2~[nothing ~
            about the type of X.~/~p3.~]  When ~x0 is assumed false, ~x1 will ~
            allow us to deduce ~#4~[nothing about the type of X.~/~p5.~]  Note ~
            that ~x0 is~#6~[ not~/~] a strong compound recognizer, according ~
            to this rule.  See doc :compound-recognizer if these observations ~
            surprise you.  These particular expressions of the type ~
            information are based on ~*7."
           pred
           (base-symbol (access recognizer-tuple new-recog-tuple :rune))
           (if (eq tts-term t) 0 1)
           tts-term
           (if (eq fts-term t) 0 1)
           fts-term
           (if (access recognizer-tuple new-recog-tuple :strongp) 1 0)
           (tilde-*-simp-phrase ttree))
          (if (warning-disabled-p "Compound-rec")
              (value nil)
            (comment-on-new-recog-tuple1 new-recog-tuple
                                         (getpropc fn 'recognizer-alist nil
                                                   wrld)
                                         ctx state)))))))))

(defun chk-acceptable-compound-recognizer-rule (name term ctx ens wrld state)

; If we don't cause an error, we return an 'assumption-free ttree that
; justifies the type information extracted from term.

  (mv-let
   (parity fn var term1)
   (destructure-compound-recognizer term)
   (cond
    ((null parity)
     (er soft ctx
         "No :COMPOUND-RECOGNIZER rule can be generated from ~x0 ~
          because it does not have the form described in :DOC ~
          compound-recognizer."
         name))
    (t (mv-let
        (ts ttree1)
        (type-set (mcons-term* fn var) nil nil nil ens wrld nil nil nil)
        (cond ((not (ts-subsetp ts *ts-boolean*))

; To loosen the Boolean restriction, we must change assume-true-false
; so that when a compound recognizer is assumed true its type-set is
; not just set to *ts-t*.  A comment at the defrec for
; recognizer-tuple also says that fn must be Boolean.  It would be a
; good idea, before changing this, to inspect all code involved with
; recognizer-tuples.

               (er soft ctx
                   "A function can be treated as a :COMPOUND-RECOGNIZER only ~
                    if it is Boolean valued. ~x0 is not known to be Boolean.  ~
                    See :DOC compound-recognizer."
                   fn))
              (t

; Historical Note: We used to combine the new type information with
; the old.  We do not do that anymore: we store exactly what the new
; rule tells us.  The reason is so that we can maintain a 1:1
; relationship between what we store and rule names, so that it is
; meaningful to disable a compound recognizer rule.

               (mv-let (recog-tuple ttree2)

; Note: Below we counterfeit a rune based on name, simply so that the
; recog-tuple we get back really looks like one.  The actual rule
; created for term1 will have a different name (x will be specified).
; This tuple is only used for error reporting and we dig name out of
; its rune then.

                       (make-recognizer-tuple `(:COMPOUND-RECOGNIZER ,name . x)
                                              nil parity fn var term1 ens wrld)
                       (er-progn
                        (comment-on-new-recog-tuple recog-tuple ctx ens wrld
                                                    state)
                        (value (cons-tag-trees ttree1 ttree2)))))))))))

; And to add :COMPOUND-RECOGNIZER rules...

(defun add-compound-recognizer-rule (rune nume term ens wrld)

; We construct the recognizer-tuple corresponding to term and just add it onto
; the front of the current recognizer-alist for the function symbol of term.
; We used to merge it into the existing tuple for that function symbol, if one
; existed, but that makes disabling these rules complicated.  When we retrieve
; tuples from the alist we look for the first enabled tuple for the function
; symbol in question.  So it is necessary to leave old tuples for that function
; symbol in place.

  (mv-let (parity fn var term1)
          (destructure-compound-recognizer term)
          (mv-let (recog-tuple ttree)
                  (make-recognizer-tuple rune nume parity fn var term1 ens
                                         wrld)
                  (declare (ignore ttree))
                  (putprop fn 'recognizer-alist
                           (cons recog-tuple
                                 (getpropc fn 'recognizer-alist nil wrld))
                           wrld))))

;---------------------------------------------------------------------------
; Section:  :FORWARD-CHAINING Rules

(defun chk-triggers (name match-free hyps terms hyps-vars concls-vars ctx ens
                          wrld state)

; Name is the name of a proposed forward chaining rule with hyps hyps
; and triggers terms.  We verify that every trigger is a non-variable,
; non-quote, non-lambda, non-NOT application.  We also print the
; free-variable warning messages.

  (cond ((null terms) (value nil))
        ((or (variablep (car terms))
             (fquotep (car terms))
             (flambda-applicationp (car terms))
             (eq (ffn-symb (car terms)) 'not))
         (er soft ctx
             "It is illegal to use a variable, a quoted constant, the ~
              application of a lambda-expression, a LET-expression, ~
              or a NOT-expression as the trigger of a forward ~
              chaining rule.  Your proposed trigger, ~x0, violates ~
              these restrictions.  See :DOC forward-chaining."
             (car terms)))
        ((not (subsetp-eq concls-vars
                          (all-vars1 (car terms) hyps-vars)))
         (er soft ctx
             "We cannot use ~x0 as a forward chaining rule triggered ~
              by ~x1 because the variable~#2~[ ~&2 is~/s ~&2 are~] ~
              used in the conclusion but not in the ~#3~[~/hypothesis ~
              or the ~/hypotheses or the ~]trigger.  See :DOC ~
              forward-chaining."
             name
             (car terms)
             (set-difference-eq concls-vars
                                (all-vars1 (car terms) hyps-vars))
             (zero-one-or-more hyps)))
        (t
         (let* ((warn-non-rec (not (warning-disabled-p "Non-rec")))
                (free-vars (free-vars-in-hyps hyps (all-vars (car terms)) wrld))
                (inst-hyps (hyps-that-instantiate-free-vars free-vars hyps))
                (forced-hyps (forced-hyps inst-hyps))
                (non-rec-fns-alist
                 (and warn-non-rec
                      (non-recursive-fnnames-alist (car terms) ens wrld)))
                (non-rec-fns (strip-cars non-rec-fns-alist))
                (non-rec-fns-inst-hyps-alist
                 (and warn-non-rec
                      (non-recursive-fnnames-alist-lst
                       (strip-top-level-nots-and-forces inst-hyps) ens wrld)))
                (non-rec-fns-inst-hyps
                 (strip-cars non-rec-fns-inst-hyps-alist)))
           (er-progn
            (cond
             ((and free-vars (null match-free))
              (pprogn
               (warning$ ctx "Free"
                         `("When the :FORWARD-CHAINING rule generated from ~
                            ~x0 is triggered by ~x1 it contains the free ~
                            variable~#2~[ ~&2.  This variable~/s ~&2.  These ~
                            variables~] will be chosen by searching for ~
                            ~#3~[an instance~/instances~] of ~&3 among the ~
                            hypotheses of the conjecture being rewritten.  ~
                            This is generally a severe restriction on the ~
                            applicability of the forward chaining rule."
                           (:free-variables ,free-vars)
                           (:instantiated-hyps ,inst-hyps)
                           (:name ,name)
                           (:rule-class :forward-chaining)
                           (:trigger ,(car terms)))
                         name (car terms) free-vars inst-hyps)
               (free-variable-error? :forward-chaining name ctx wrld state)))
             (t (value nil)))
            (pprogn
             (cond
              ((and free-vars forced-hyps)
               (warning$ ctx "Free"
                         "Forward chaining rule ~x0 has forced (or ~
                          case-split) ~#1~[hypothesis~/hypotheses~], ~*2, ~
                          which will be used to instantiate one or more free ~
                          variables.  We will search for suitable ~
                          instantiations (of the term inside the FORCE or ~
                          CASE-SPLIT) among the known assumptions in the ~
                          context at the time we encounter ~#1~[the~/each~] ~
                          hypothesis.  If no instances are found, we will ~
                          force or case split on the partially instantiated ~
                          ~#1~[hypothesis~/hypotheses~] instead of waiting ~
                          for future rounds of forward chaining which might ~
                          derive appropriate instances.  Note that this will ~
                          introduce a ``free variable'' into the conjecture.  ~
                          While sound, this will establish a goal almost ~
                          certain to fail since the restriction described by ~
                          this apparently necessary hypothesis constrains a ~
                          variable not involved in the problem.  To highlight ~
                          this oddity, we will rename the free variables in ~
                          such forced hypotheses by prefixing them with ~
                          ``UNBOUND-FREE-''.  This is not guaranteed to ~
                          generate a new variable but at least it generates ~
                          an unusual one.  If you see such a variable in a ~
                          subsequent proof (and did not introduce them ~
                          yourself) you should consider the possibility that ~
                          the free variables of this forward chaining rule ~
                          were forced into the conjecture."
                         name
                         (if (null (cdr forced-hyps)) 0 1)
                         (tilde-*-untranslate-lst-phrase forced-hyps t
                                                         wrld)))
              (t state))
             (cond
              (non-rec-fns
               (warning$ ctx ("Non-rec")
                         `("The term ~x0 contains the function symbol~#1~[ ~
                            ~&1, which has a non-recursive definition.~@2  ~
                            Unless this definition is~/s ~&1, which have ~
                            non-recursive definitions.~@2  Unless these ~
                            definitions are~] disabled, ~x0 is unlikely ever ~
                            to occur as a trigger for ~x3."
                           (:name ,name)
                           (:non-recursive-fns ,(hide-lambdas non-rec-fns))
                           (:trigger-term ,(car terms)))
                         (car terms)
                         (hide-lambdas non-rec-fns)
                         (non-rec-def-rules-msg non-rec-fns-alist)
                         name))
              (t state))
             (cond
              (non-rec-fns-inst-hyps
               (warning$ ctx ("Non-rec")
                         `("As noted, when triggered by ~x0, we will ~
                            instantiate the free variable~#1~[~/s~], ~&1, of ~
                            the rule ~x2, by searching for the ~
                            ~#3~[hypothesis~/set of hypotheses~] shown above. ~
                            ~ However, ~#3~[this hypothesis mentions~/these ~
                            hypotheses mention~] the function symbol~#4~[ ~
                            ~&4, which has a non-recursive definition.~@5  ~
                            Unless this definition is disabled, that function ~
                            symbol is~/s ~&4, which have non-recursive ~
                            definitions.~@5  Unless these definitions are ~
                            disabled, those function symbols are~] unlikely ~
                            to occur in the conjecture being proved and hence ~
                            the search for the required ~
                            ~#3~[hypothesis~/hypotheses~] will likely fail."
                           (:free-variables ,free-vars)
                           (:instantiated-hyps ,inst-hyps)
                           (:name ,name)
                           (:non-recursive-fns-inst-hyps
                            ,(hide-lambdas non-rec-fns-inst-hyps))
                           (:trigger-term ,(car terms)))
                         (car terms) free-vars name inst-hyps
                         (hide-lambdas non-rec-fns-inst-hyps)
                         (non-rec-def-rules-msg non-rec-fns-inst-hyps-alist)))
              (t state))
             (chk-triggers match-free name hyps (cdr terms)
                           hyps-vars concls-vars ctx ens wrld state)))))))

(defun destructure-forward-chaining-term (term wrld)

; We return two lists, hyps and concls, such that term is equivalent to
; (implies (and . hyps) (and . concls)).

; We have considered treating (IMPLIES a (IMPLIES b c)) as (IMPLIES (and a b)
; c) when we parse :forward-chaining rules.  At the moment we do not, and hence
; such a :forward-chaining rule might put (IMPLIES b c) on the type-alist.  The
; code for the ``improved'' parsing is in the comment just below.  This would
; bring the parsing of :forward-chaining rules more into line with what we do
; for :rewrite rules.  But an email from Dave Greve gave us the impression that
; he and others might intentionally put calls of IMPLIES on the type-alist.
; This is in the spirit of ``just do what the user said.''  We never ran a
; regression with the ``improved'' parsing so we don't know what effect it
; might have.  But we decided to stick with the ``just do what the user said''
; approach.

;   (let ((term (remove-lambdas (remove-guard-holders term))))
;     (cond ((or (variablep term)
;                (fquotep term)
;                (not (eq (ffn-symb term) 'implies)))
;            (mv nil (flatten-ands-in-lit term)))
;           (t
;
; ; Term is of the form (implies arg1 arg2).  We recursively
; ; destructure arg2 first, in case it is another (implies ...).
;
;            (mv-let (hyps concls)
;                    (destructure-forward-chaining-term (fargn term 2))
;                    (mv (append (flatten-ands-in-lit (fargn term 1))
;                                hyps)
;                        concls)))))

  (let ((term (remove-lambdas (remove-guard-holders term wrld))))
    (cond ((or (variablep term)
               (fquotep term)
               (not (eq (ffn-symb term) 'implies)))
           (mv nil (flatten-ands-in-lit term)))
          (t (mv (flatten-ands-in-lit (fargn term 1))
                 (flatten-ands-in-lit (fargn term 2)))))))

(defun chk-acceptable-forward-chaining-rule (name match-free trigger-terms term
                                                  ctx ens wrld state)

; Acceptable forward chaining rules are of the form

; (IMPLIES (AND . hyps)
;          (AND . concls))

; We used to split term up with unprettyify as is done for REWRITE
; class rules.  But that meant that we had to establish hyps
; once for each concl whenever the rule was triggered.

  (mv-let
   (hyps concls)
   (destructure-forward-chaining-term term wrld)
   (let ((hyps-vars (all-vars1-lst hyps nil))
         (concls-vars (all-vars1-lst concls nil)))
     (chk-triggers name match-free hyps trigger-terms
                   hyps-vars concls-vars
                   ctx ens wrld state))))

(defun putprop-forward-chaining-rules-lst
  (rune nume triggers hyps concls match-free wrld)
  (cond ((null triggers)
         (put-match-free-value match-free rune wrld))
        (t (putprop-forward-chaining-rules-lst
            rune nume
            (cdr triggers)
            hyps concls match-free
            (putprop (ffn-symb (car triggers))
                     'forward-chaining-rules
                     (cons (make forward-chaining-rule
                                 :rune rune
                                 :nume nume
                                 :trigger (car triggers)
                                 :hyps hyps
                                 :concls concls
                                 :match-free match-free)
                           (getpropc (ffn-symb (car triggers))
                                     'forward-chaining-rules nil wrld))
                     wrld)))))

(defun add-forward-chaining-rule (rune nume trigger-terms term match-free wrld)
  (mv-let
   (hyps concls)
   (destructure-forward-chaining-term term wrld)
   (putprop-forward-chaining-rules-lst rune nume
                                       trigger-terms
                                       hyps concls
                                       (match-free-fc-value match-free
                                                            hyps concls
                                                            trigger-terms
                                                            wrld)
                                       wrld)))



;---------------------------------------------------------------------------
; Section:  :META Rules

(defun evaluator-clause/arglist (evfn formals x)

; See evaluator-clause.  We return a list of the form
; '((evfn (cadr x) a) (evfn (caddr x) a) ...) containing
; as many elements as there are in formals.  The evfn and
; x we use are as provided in our arguments, but the variable
; symbol A in our answer is built-in below.

  (cond ((null formals) nil)
        (t (cons (mcons-term* evfn (mcons-term* 'car x) 'a)
                 (evaluator-clause/arglist evfn
                                           (cdr formals)
                                           (mcons-term* 'cdr x))))))

(defun evaluator-clause (evfn fn-args)

; Fn-args is of the form (fn v1 ... vn), a well-formed application of the
; function fn.  We return a clause that expresses the theorem

; (implies (and (consp x)
;               (equal (car x) 'fn))
;          (equal (evfn x a)
;                 (fn (evfn (cadr x) a)
;                     ...
;                     (evfn (cad...dr x) a))))

; where evfn and fn are the function symbols provided.  Note that the
; clause we return uses the variable symbols X and A.  These symbols
; are built into this definition and that of evaluator-clause/arglist.

  (list '(not (consp x))
        (fcons-term*
         'not
         (fcons-term* 'equal '(car x) (kwote (car fn-args))))
        (fcons-term*
         'equal
         (fcons-term* evfn 'x 'a)
         (fcons-term (car fn-args)
                     (evaluator-clause/arglist evfn
                                               (cdr fn-args)
                                               '(cdr x))))))

(defun evaluator-clauses1 (evfn fn-args-lst)
  (cond ((null fn-args-lst) nil)
        (t (cons (evaluator-clause evfn (car fn-args-lst))
                 (evaluator-clauses1 evfn (cdr fn-args-lst))))))

(defun evaluator-clauses (evfn evfn-lst fn-args-lst)

; We return the set of clauses that describe an evaluator, evfn, that
; knows about the function symbols listed in fn-args-lst.  The
; mutually recursive function that evaluates a list of such terms is
; named evfn-lst.

; This function serves two purposes: it is used to generate the constraints
; produced by the defevaluator event and it is used to check that the
; constraints on an alleged evaluator are in fact those required.  (Remember:
; the user need not have introduced an evaluator via defevaluator.)

; The clauses that describe an evaluator include an evaluator-clause
; (q.v.)  for each fn in fn-args-lst plus clauses describing evfn when
; x is a variable symbol, a quoted object, and a lambda application,
; plus clauses describing evfn-lst on nil and on conses.

; Note: The function chk-evaluator exploits the fact that if evfn is
; an evaluator, then the constraint on it will contain at least 4
; clauses.  (One of the five fixed clauses below is about only
; evfn-lst and not about evfn and hence wouldn't be among the
; constraints of evfn.)  If this changes, change chk-evaluator.
; (Note there are now at least 7 constraints about each evaluator.)

; The functions guess-fn-args-lst-for-evfn and guess-evfn-lst-for-evfn take the
; known constraints on an evfn and guess the evfn-lst and list of fns for which
; evfn might be an evaluator.  These functions knows the structure of the
; clauses generated here, in particular, the structure of the clause describing
; evfn-lst on a cons and the structure of the evaluator-clause for a given fn.
; If these structures change, change these two functions.

; WARNING: Don't change the clauses below without reading the Notes above!  In
; particular, the functions chk-evaluator and defevaluator-form/defthms both
; call this function.  Furthermore, at least the following functions know about
; the number, order, and shape of the clauses generated:
; defevaluator-form/defthm-name and defevaluator-form/defthm-hints.

  (append (sublis (list (cons 'evfn evfn)
                        (cons 'evfn-lst evfn-lst))
                  '(((not (consp x))
                     (not ; (syntaxp (not (equal a ''nil)))
                      (synp 'nil
                            '(syntaxp (not (equal a ''nil)))
                            '(if (not (equal a ''nil)) 't 'nil)))
                     (equal (car x) 'quote)
                     (equal (evfn x a)
                            (evfn (cons (car x)
                                        (kwote-lst (evfn-lst (cdr x) a)))
                                  'nil)))
                    ((not (symbolp x))

; We considered replacing the right-hand side below simply by (cdr (assoc-equal
; x a)), i.e., without making a special case for x = nil.  Our motivation was
; an observation from Sol Swords: there is a kind of mismatch between that
; special case for nil on the one hand, and the treating of nil as an ordinary
; variable by sublis-var.  Indeed, he went through some effort to deal with
; this mismatch in his community book,
; books/clause-processors/sublis-var-meaning.lisp, using a hypothesis (not
; (assoc nil alist)) in some lemmas in that book.

; However, if we were to make that change, together with the corresponding
; change in the local witness for the evaluator in the symbolp case, then the
; preceding clause (above) would no longer be valid for our local witness.
; Consider for example the case that x is '(binary-+) and a is '((nil . 7)),
; and that evfn is the local witness and understands binary-+.  Then the
; left-hand side above is 14 but the right-hand side is 0.  A fix is to modify
; the preceding clause by replacing the final 'nil by a (and then dropping the
; syntaxp hypothesis above, and even making this a definition rule with
; :controller-alist mapping the evaluator to (t nil)).  But that change would
; make invalid the lemma ev-commutes-car in community book
; books/tools/defevaluator-fast.lisp.  It would also require changing some
; hints, for example replacing the :hints in event lemma0, community book
; books/clause-processors/bv-add.lisp, by (("Goal" :expand ((evl x1 env)))).
; Who knows how many books might be affected, including some user books not in
; the regression suite?  So we have decided to leave well enough alone, at
; least for now.  If later we learn of a reason to reconsider, we may do so.

                     (equal (evfn x a)
                            (if x
                                (cdr (assoc-equal x a))
                              'nil)))
                    ((not (consp x))
                     (not (equal (car x) 'quote))
                     (equal (evfn x a) (car (cdr x))))
                    ((not (consp x))
                     (not (consp (car x)))
                     (equal (evfn x a)
                            (evfn (car (cdr (cdr (car x))))
                                  (pairlis$ (car (cdr (car x)))
                                            (evfn-lst (cdr x) a)))))
                    ((consp x-lst)
                     (equal (evfn-lst x-lst a) 'nil))
                    ((not (consp x-lst))
                     (equal (evfn-lst x-lst a)
                            (cons (evfn (car x-lst) a)
                                  (evfn-lst (cdr x-lst) a))))
                    ((consp x)
                     (symbolp x)
                     (equal (evfn x a) 'nil))
                    ((not (consp x))
                     (consp (car x))
                     (symbolp (car x))
                     (equal (evfn x a) 'nil))))
          (evaluator-clauses1 evfn fn-args-lst)))

; The function above describes the constraints on an evaluator
; function.  The user will define his own evfn and evfn-lst and prove
; the constraint formulas.  Later, when evfn is used in an alleged
; :META theorem, we will verify that it is an evaluator by getting its
; constraint, digging the clauses out of it, and comparing them to the
; list above.  But in our statement of the constraints we use car/cdr
; nests freely.  The user is liable to use cadr nests (or first,
; second, third, etc., which expand to cadr nests).  We therefore take
; time out from our development of evaluators and define the functions
; for normalizing the user's cadr nests to car/cdr nests.  The
; following code feels really clunky.

(defun cdrp (x term)

; We determine whether term is of the form (cdr (cdr ... (cdr x))),
; where there are 0 or more cdrs.

  (cond ((equal x term) t)
        ((variablep term) nil)
        ((fquotep term) nil)
        ((eq (ffn-symb term) 'cdr) (cdrp x (fargn term 1)))
        (t nil)))

; A source of confusion the user faces is that he may write
; (eq & 'fn) or (eq 'fn &) where we expect (equal & 'fn).  So we
; normalize those too, at the top-level of a clause.  We call it
; a term-lst rather than a clause for symmetry with the foregoing.

(defun expand-eq-and-atom-term-lst (lst)

; This function scans the clause lst and replaces literals of the
; form (not (eq x 'sym)), (not (eq 'sym x)), and (not (equal 'sym x))
; by (not (equal x 'sym)).  It also replaces literals of the form
; (atom x) by (not (consp x)).

  (cond ((null lst) nil)
        (t (let ((rst (expand-eq-and-atom-term-lst (cdr lst)))
                 (lit (car lst)))
             (case-match
              lit
              (('not ('eq x ('quote s)))
               (cond ((symbolp s)
                      (cons (mcons-term* 'not
                                         (mcons-term* 'equal
                                                      x
                                                      (list 'quote s)))
                            rst))
                     ((and (quotep x)
                           (symbolp (cadr x)))
                      (cons (mcons-term* 'not
                                         (mcons-term* 'equal
                                                      (list 'quote s)
                                                      x))
                            rst))
                     (t (cons lit rst))))
              (('not ('eq ('quote s) x))
               (cond ((symbolp s)
                      (cons (mcons-term* 'not
                                         (mcons-term* 'equal
                                                      x
                                                      (list 'quote s)))
                            rst))
                     (t (cons lit rst))))
              (('not ('equal ('quote s) x))
               (cond ((and (symbolp s)
                           (not (and (quotep x)
                                     (symbolp (cadr x)))))
                      (cons (mcons-term* 'not
                                         (mcons-term* 'equal
                                                      x
                                                      (list 'quote s)))
                            rst))
                     (t (cons lit rst))))
              (('atom x)
               (cons (mcons-term* 'not (mcons-term* 'consp x))
                     rst))
              (& (cons lit rst)))))))

; And here, at long last, is the function that massages a user's
; alleged evaluator constraint clause so as to unfold all the cadrs
; and cadars of the pseudo-term in question.

(defun normalize-alleged-evaluator-clause (clause)

; Supposing clause is an evaluator clause, we make the likely
; transformations to remove minor syntactic variants introduced by the
; user.  In particular, we eliminate the uses of atom and eq.

  (expand-eq-and-atom-term-lst clause))

; And here is how we massage the list of user clauses.

(defun normalize-alleged-evaluator-clause-set (lst)
  (cond ((null lst) nil)
        (t (cons (normalize-alleged-evaluator-clause (car lst))
                 (normalize-alleged-evaluator-clause-set (cdr lst))))))

(defun shallow-clausify1 (lst)

; Lst is a list of pairs, each of the form (hyps . concl) as returned
; by unprettyify.  We convert it to a list of clauses.

  (cond ((null lst) nil)
        (t (conjoin-clause-to-clause-set
            (add-literal
             (cdar lst)
             (dumb-negate-lit-lst (caar lst))
             t)
            (shallow-clausify1 (cdr lst))))))

(defun shallow-clausify (term)

; We extract a set of clauses from term whose conjunction is is
; propositionally equivalent to term.  This is like clausify except
; that we are very shallow and stupid.

; Note: Why on earth do we have this function?  The intended use for
; this function is to clausify the constraint on an alleged evaluator
; function evfn.  The idea is to convert the user's constraint to a
; set of clauses and compare that set to the canonical evaluator
; clauses.  Why not just use clausify?  If one of the functions
; interpreted by evfn is 'if then our full-blown clausify will break
; that clause apart into two unrecognizable pieces.

  (shallow-clausify1 (unprettyify term)))

; We next turn to guessing the evfn-lst and list of fns for which evfn
; is an evaluator.  Our guesses key on the structure of the clauses
; that constrain evfn.

(defun find-evfn-lst-in-clause (evfn cl)

; We are looking for the clause that specifies how evfn evaluates
; a lambda application.  That clause will mention evfn-lst, the
; function that evaluates a list of terms.  In particular, we scan
; cl looking for the literal

; (equal (evfn x a)
;        (evfn (caddar x)
;              (pairlis$ (cadar x)
;                        (evfn-lst (cdr x) a))))

; except we know that the cadr nests are in car/cdr form if this is a
; good clause.  If we find such a literal we use evfn-lst as our
; guess.  Otherwise we return nil

  (cond
   ((null cl) nil)
   (t (let ((lit (car cl)))
        (case-match
         lit
         (('equal (!evfn x a)
                  (!evfn ('car ('cdr ('cdr ('car x))))
                         ('pairlis$ ('car ('cdr ('car x)))
                                    (evfn-lst ('cdr x) a))))
          (cond ((and (variablep x)
                      (variablep a))
                 evfn-lst)
                (t (find-evfn-lst-in-clause evfn (cdr cl)))))
         (& (find-evfn-lst-in-clause evfn (cdr cl))))))))

(defun guess-evfn-lst-for-evfn (evfn cl-set)

; We look through cl-set for the clause that specifies how evfn
; evaluates lambda applications.  That clause mentions evfn-lst and if
; we find it we return the evfn-lst mentioned.  Otherwise nil.
; We insist that the clause be of length 3.

  (cond ((null cl-set) nil)
        ((and (int= (length (car cl-set)) 3)
              (find-evfn-lst-in-clause evfn (car cl-set))))
        (t (guess-evfn-lst-for-evfn evfn (cdr cl-set)))))

(defun find-fn-in-clause (cl wrld)
  (cond ((null cl) nil)
        (t (let ((lit (car cl)))
             (case-match
              lit
              (('not ('equal ('car x) ('quote fn)))
               (cond ((and (variablep x)
                           (symbolp fn)
                           (not (eq fn 'quote))
                           (function-symbolp fn wrld))
                      fn)
                     (t (find-fn-in-clause (cdr cl) wrld))))
              (& (find-fn-in-clause (cdr cl) wrld)))))))

(defun guess-fn-args-lst-for-evfn (cl-set wrld)

; We return a list of ``fn-args'', terms of the form (fn v1 ... vn) where the
; vi are the formals of fn.  The list contains a fn-arg for each function
; symbol fn such that some 3 literal clause in cl-set contains a literal of the
; form (not (equal (car x) 'fn)).

  (cond ((null cl-set) nil)
        (t (let ((fn (and (int= (length (car cl-set)) 3)
                          (find-fn-in-clause (car cl-set) wrld))))
             (cond (fn (cons (mcons-term fn (formals fn wrld))
                             (guess-fn-args-lst-for-evfn (cdr cl-set) wrld)))
                   (t (guess-fn-args-lst-for-evfn (cdr cl-set) wrld)))))))

(defun normalized-evaluator-cl-set (ev wrld)
  (normalize-alleged-evaluator-clause-set
   (shallow-clausify
    (mv-let (sym x)
            (constraint-info ev wrld)
            (assert$ (not (unknown-constraints-p x))
                     (cond
                      (sym (conjoin x))
                      (t x)))))))

(defun chk-evaluator (evfn wrld ctx state)

; Evfn must be a function symbol.  We check that evfn is an evaluator
; function in wrld, or else we cause an error.  To be an evaluator
; function evfn must be a function symbol and there must exist another
; symbol, evfn-lst, and a list of function symbols, fns, such that the
; constraints on evfn and evfn-lst are equivalent to the evaluator
; clauses for evfn, evfn-lst and fns.

; What do we mean by the constraints being "equivalent" to the evaluator
; clauses?  We convert the two constraint formulas to sets of clauses
; with shallow-clausify.  Then we expand the cadrs in the user's set.
; Then we do a bi-directional subsumption check on the evaluator clauses.
; By doing a subsumption check we permit the user to use any variable
; names he wishes and to order his clauses and the literals within his
; clauses any way he wishes.

; However, before we can do that we have to decide what evfn-lst and
; fns we will use.  We guess, by inspecting the constraints of evfn.
; If our guess is wrong we'll just end up saying that evfn is not an
; evaluator fn.  If our guess is right, we'll confirm it by the subsumption
; check.  So the guessing method is technically unimportant.  However, we
; believe it is complete:  if there exist suitable evfn-lst and fns,
; we find them.

  (let ((cl-set0 (normalized-evaluator-cl-set evfn wrld))
        (str
         "The symbol ~x0, playing the role of an evaluator in your alleged ~
          theorem, does not pass the test for an evaluator.  See :DOC meta ~
          and :DOC defevaluator.  The constraint on ~x0 is in fact ~p1.  ~@2")
        )
    (cond
     ((< (length cl-set0) 4)
      (er soft ctx str
          evfn
          (prettyify-clause-set cl-set0 nil wrld)
          "This constraint has fewer than four conjuncts."))
     (t (let ((evfn-lst
               (guess-evfn-lst-for-evfn evfn cl-set0)))
          (cond
           ((null evfn-lst)
            (er soft ctx str
                evfn
                (prettyify-clause-set cl-set0 nil wrld)
                "We cannot find the formula describing how to ~
                 evaluate lambda applications."))
           (t (let* ((fn-args-lst (guess-fn-args-lst-for-evfn cl-set0 wrld))
                     (cl-set1
                      (conjoin-clause-sets
                       cl-set0
                       (normalized-evaluator-cl-set evfn-lst wrld)))
                     (cl-set2
                      (remove-guard-holders-lst-lst
                       (evaluator-clauses evfn evfn-lst fn-args-lst)
                       wrld)))
                (cond
                 ((not (and (clause-set-subsumes nil cl-set1 cl-set2)
                            (clause-set-subsumes nil cl-set2 cl-set1)))
                  (er soft ctx
                      "If ~x0 is an evaluator then it recognizes ~#1~[no ~
                       function symbols~/only the function symbol ~&2~/the ~
                       function symbols ~&2~] and its mutually recursive ~
                       counterpart for lists of terms must be ~x3.  The ~
                       constraints on ~x0 and ~x3 must therefore be ~
                       ~P45.~|~%We would recognize ~x0 and ~x3 as evaluators ~
                       if the constraints on them subsumed and were subsumed ~
                       by the constraints above.  But, in fact, the ~
                       constraints on ~x0 and ~x3 are ~P65 and the ~
                       bidirectional subsumption check fails.  See :DOC ~
                       defevaluator."
                      evfn
                      (zero-one-or-more fn-args-lst)
                      (strip-cars fn-args-lst)
                      evfn-lst
                      (prettyify-clause-set cl-set2 nil wrld)
                      (term-evisc-tuple nil state)
                      (prettyify-clause-set cl-set1 nil wrld)))
                 (t (value nil)))))))))))

; To make it easier to introduce an evaluator, we define the following
; macro.

(defun namedp-prefix (evfn namedp)

; We generate the prefix used in naming the constraints for evaluator evfn.
; Namedp is t or nil and indicates whether we generate a name like
; evfn-OF-fn-CALL or like evfn-CONSTRAINT-i.  We return either "evfn-OF-" or
; "evfn-CONSTRAINT-".

  (if namedp
      (concatenate 'string (symbol-name evfn) "-OF-")
      (concatenate 'string (symbol-name evfn) "-CONSTRAINT-")))

(defun defevaluator-form/defthm-name (evfn evfn-lst namedp prefix i clause)

; This function generates the name of constraint i for evaluator function
; evfn.  Namedp is t or nil and indicates whether we generate a name like
; evfn-OF-fn-CALL or like evfn-CONSTRAINT-i.  Prefix is a string and is either
; of the form "evfn-OF-" or "evfn-CONSTRAINT-"; see namedp-prefix. I is the
; 0-based number of the constraint and clause is the clausal form of the
; constraint.  But when namedp is non-nil we have to solve two problems: (a)
; give special names to the first few constraints (which do not concern one of
; the function symbols to be interpreted) and (b) figure out the function
; symbol fn.

; We solve (a) by coding in our knowledge of the order of the clauses generated
; by evaluator-clauses and we solve (b) by looking into those clauses
; corresponding to calls of functions to be interpreted.

; i             name of defthm when namedp         name when not namedp

; 0             evfn-OF-FNCALL-ARGS                evfn-constraint-0
; 1             evfn-OF-VARIABLE                   evfn-constraint-1
; 2             evfn-of-QUOTE                      evfn-constraint-2
; 3             evfn-of-LAMBDA                     ...
; 4             evfn-lst-OF-ATOM
; 5             evfn-lst-OF-CONS
; 6             evfn-of-nonsymbol-atom
; 7             evfn-of-bad-fncall
; 8 ...         evfn-OF-fn-CALL, ... for each interpreted fn

; When i>7, clause is always of the form:
; ((NOT (CONSP X)) (NOT (EQUAL (CAR X) 'fn)) (EQUAL (evfn X A) (fn ...)))
; and we recover fn from the second literal as shown in the binding of
; fn below.

  (cond
   (namedp
    (let ((fn (car (fargn (caddr clause) 2))))
      (case i
        (0 (genvar evfn (concatenate 'string prefix "FNCALL-ARGS") nil nil))
        (1 (genvar evfn (concatenate 'string prefix "VARIABLE") nil nil))
        (2 (genvar evfn (concatenate 'string prefix "QUOTE") nil nil))
        (3 (genvar evfn (concatenate 'string prefix "LAMBDA") nil nil))
        (4 (genvar evfn
                   (concatenate 'string (symbol-name evfn-lst) "-OF-ATOM")
                   nil nil))
        (5 (genvar evfn
                   (concatenate 'string (symbol-name evfn-lst) "-OF-CONS")
                   nil nil))
        (6 (genvar evfn

; Perhaps "NON-SYMBOL-ATOM" is more aesthetic.  But its meaning is perhaps less
; clear than "NONSYMBOL-ATOM": a non-symbol that is an atom, rather than, say,
; something that is not a symbol or an atom.

                   (concatenate 'string prefix "NONSYMBOL-ATOM")
                   nil nil))
        (7 (genvar evfn (concatenate 'string prefix "BAD-FNCALL") nil nil))
        (otherwise
         (genvar evfn
                 (concatenate 'string prefix (symbol-name fn) "-CALL")
                 nil nil)))))
   (t (genvar evfn prefix i nil))))

(defun defevaluator-form/defthm-hints (evfn evfn-lst i)

; See the comment in defevaluator-form/defthm-name about the knowledge of
; evaluator-clauses encoded in this function.  We generate the :hints for the
; ith constraint, i.e., for the formula (prettyify-clause clause nil nil),
; where clause is (nth i (evaluator-clauses evfn evfn-lst fn-args-lst).  A
; representative value of fn-args-lst would be ((CAR X) (CONS X Y) (IF X Y Z)),
; for which suitable i would be 0, 1, ..., 8.

  (cond
   ((> i 7)
    `(("Goal" :expand
       ((,evfn X A)
        (:free (x) (HIDE x))
        (:free (fn args)
               (APPLY-FOR-DEFEVALUATOR fn args))))))
   (t
    (case i
      (0 `(("Goal" :expand
            ((:free (x) (HIDE x))
             (,evfn X A)
             (:free (args)
                    (,evfn (CONS (CAR X) ARGS) NIL)))
            :in-theory '(eval-list-kwote-lst
                         true-list-fix-ev-lst
                         car-cons cdr-cons))))
      ((1 2 3 6 7) `(("Goal" :expand ((,evfn X A)))))
      (otherwise
       `(("Goal" :expand ((,evfn-lst X-LST A)))))))))

(defun defevaluator-form/defthm (evfn evfn-lst namedp prefix i clause)

; We generate the defthm event for the ith constraint, given the clause
; expressing that constraint.  Constraints 0, 6, and 7 are disabled; the
; others are only locally disabled.

  (let* ((defthm (if (or (eql i 0) (eql i 6) (eql i 7)) 'defthmd 'defthm))
         (name (defevaluator-form/defthm-name
                 evfn evfn-lst namedp prefix i clause))
         (formula

; Notice that we pass nil to the world argument of prettyify-clause below, so
; that the user cannot affect the formula generated here, for example by
; setting the 'untranslate or 'untranslate-preprocess entry in the
; user-defined-functions-table.  We do not rely on this for soundness, however,
; since ultimately the defthm returned below would be rejected if the formula
; is unsuitable.

          (prettyify-clause clause nil nil))
         (hints (defevaluator-form/defthm-hints evfn evfn-lst i)))
    `((,defthm ,name
        ,formula
        :hints ,hints)
      (local (in-theory (disable ,name))))))

(defun defevaluator-form/defthms (evfn evfn-lst namedp prefix i clauses)
  (declare (xargs :mode :program))
  (if (endp clauses)
      nil
    (append
     (defevaluator-form/defthm evfn evfn-lst namedp prefix i (car clauses))
     (defevaluator-form/defthms evfn evfn-lst namedp prefix (+ 1 i) (cdr clauses)))))

(defun car-cadr-caddr-etc (formals x)
  (if (endp formals)
      nil
      (cons `(CAR ,x)
            (car-cadr-caddr-etc (cdr formals) `(CDR ,x)))))

(defun defevaluator-form/fns-clauses (fn-args-lst)
  (declare (xargs :mode :program))
; We return a list of cond clauses,
; (
;  ((equal (car x) 'fn1)
;   (fn1 (evfn (cadr x) a) ... (evfn (cad...dr x) a)))
;  ((equal (car x) 'fn2)
;   (fn2 (evfn (cadr x) a) ... (evfn (cad...dr x) a)))
;  ...
;   (t nil))

; containing a clause for each fni in fns plus a final t clause.

  (cond ((null fn-args-lst) '((t nil)))
        (t (cons
            (list (list 'equal 'fn (kwote (caar fn-args-lst)))
                  (cons (caar fn-args-lst)
                        (car-cadr-caddr-etc (cdar fn-args-lst)
                                                       'args)))
            (defevaluator-form/fns-clauses (cdr fn-args-lst))))))

(defconst *defevaluator-form-base-theory*
  (append *definition-minimal-theory*
          '(car-cdr-elim
            car-cons cdr-cons
            o< o-finp o-first-expt o-first-coeff o-rst natp posp
            acl2-count
            alistp
            true-list-fix kwote kwote-lst pairlis$-true-list-fix
            )))

(defun defevaluator-form (evfn evfn-lst namedp fn-args-lst)
  (declare (xargs :mode :program))
  (let* ((fns-clauses (defevaluator-form/fns-clauses fn-args-lst))
         (defthms (defevaluator-form/defthms evfn evfn-lst namedp
                    (namedp-prefix evfn namedp)
                    0
                    (evaluator-clauses evfn evfn-lst fn-args-lst))))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")
      (local (in-theory *defevaluator-form-base-theory*))
      . ,(sublis
          (list (cons 'evfn evfn)
                (cons 'evfn-lst evfn-lst)
                (cons 'fns-clauses fns-clauses)
                (cons 'defthms defthms))
          '((local (defun-nx apply-for-defevaluator (fn args)
                     (declare (xargs :verify-guards nil
                                     :normalize nil))
                     (cond . fns-clauses)))
            (local
             (mutual-recursion
              (defun-nx evfn (x a)
                (declare
                 (xargs :verify-guards nil
                        :measure (acl2-count x)
                        :well-founded-relation o<
                        :normalize nil
                        :hints (("goal" :in-theory
                                 (enable (:type-prescription
                                          acl2-count))))
                        :mode :logic))
                (cond
                 ((symbolp x) (and x (cdr (assoc-eq x a))))
                 ((atom x) nil)
                 ((eq (car x) 'quote) (car (cdr x)))
                 (t (let ((args (evfn-lst (cdr x) a)))
                      (cond
                       ((consp (car x))
                        (evfn (car (cdr (cdr (car x))))
                              (pairlis$ (car (cdr (car x)))
                                        args)))
                       ((not (symbolp (car x))) nil)
                       (t (apply-for-defevaluator (car x) args)))))))
                (defun-nx evfn-lst (x-lst a)
                  (declare (xargs :measure (acl2-count x-lst)
                                  :well-founded-relation o<))
                  (cond ((endp x-lst) nil)
                        (t (cons (evfn (car x-lst) a)
                                 (evfn-lst (cdr x-lst) a)))))))
            (local (in-theory (disable evfn evfn-lst apply-for-defevaluator)))
            (local
             (defthm eval-list-kwote-lst
               (equal (evfn-lst (kwote-lst args) a)
                      (true-list-fix args))
               :hints (("goal"
                        :expand ((:free (x y) (evfn-lst (cons x y) a))
                                 (evfn-lst nil a)
                                 (:free (x)
                                        (evfn (list 'quote x) a)))
                        :induct (true-list-fix args)))))
            (local
             (defthm true-list-fix-ev-lst
               (equal (true-list-fix (evfn-lst x a))
                      (evfn-lst x a))
               :hints (("goal" :induct (len x)
                        :in-theory (e/d ((:induction len)))
                        :expand ((evfn-lst x a)
                                 (evfn-lst nil a))))))
            (local
             (defthm ev-commutes-car
               (equal (car (evfn-lst x a))
                      (evfn (car x) a))
               :hints (("goal" :expand ((evfn-lst x a)
                                        (evfn nil a))
                        :in-theory (enable default-car)))))
            (local
             (defthm ev-lst-commutes-cdr
               (equal (cdr (evfn-lst x a))
                      (evfn-lst (cdr x) a))
               :hints (("Goal" :expand ((evfn-lst x a)
                                        (evfn-lst nil a))
                        :in-theory (enable default-cdr)))))
            . defthms)))))

(defun pairs-to-macro-alias-msgs (alist)
  (declare (xargs :guard (symbol-alistp alist)))
  (cond ((endp alist) nil)
        (t (cons (msg "~x0 is a macro alias for function ~x1"
                      (caar alist) (cdar alist))
                 (pairs-to-macro-alias-msgs (cdr alist))))))

(defun defevaluator-check-msg (alist macro-aliases wrld bad macro-alist)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (symbol-alistp macro-aliases)
                              (plist-worldp wrld)
                              (symbol-listp bad)
                              (symbol-alistp macro-alist))))
  (cond ((endp alist)
         (cond ((or bad macro-alist)
                (msg "~@0~@1"
                     (cond ((null bad) "")
                           ((null (cdr bad))
                            (msg "The symbol ~x0 is not a function symbol in ~
                                  the current ACL2 world."
                                 (car bad)))
                           (t
                            (msg "The symbols ~&0 are not function symbols in ~
                                  the current ACL2 world."
                                 bad)))
                     (cond ((null macro-alist) "")
                           (t (msg "  Note that ~*0."
                                   (list
                                    ""          ; nothing to print
                                    "~@*"       ; last element
                                    "~@*, and " ; 2nd to last element
                                    "~@*"       ; all other elements
                                    (pairs-to-macro-alias-msgs macro-alist)))))))
               (t nil)))
        ((function-symbolp (caar alist) wrld)
         (defevaluator-check-msg (cdr alist) macro-aliases wrld bad
           macro-alist))
        (t (defevaluator-check-msg (cdr alist) macro-aliases wrld
             (cons (caar alist) bad)
             (let ((entry (assoc-eq (caar alist) macro-aliases)))
               (cond (entry (cons entry macro-alist))
                     (t macro-alist)))))))

(defun defevaluator-check (x evfn evfn-lst fn-args-lst ctx state)
  (declare (xargs :guard
                  (and (state-p state)
                       (symbol-alistp fn-args-lst)
                       (symbol-alistp
                        (fgetprop 'macro-aliases-table
                                  'table-alist
                                  nil
                                  (w state))))))
  (cond ((not (and (symbolp evfn)
                   (symbolp evfn-lst)
                   (symbol-list-listp fn-args-lst)))
         (er soft ctx
             "The form of a defevaluator event is (defevaluator evfn evfn-lst ~
              fn-args-lst), where evfn and evfn-lst are symbols and ~
              fn-args-lst is a true list of lists of symbols.  Optionally, ~
              one may supply the final keyword argument :namedp with value t ~
              or nil (default).  However, ~x0 does not have this form."
             x))
        (t (let* ((wrld (w state))
                  (msg (defevaluator-check-msg
                         fn-args-lst
                         (macro-aliases wrld)
                         wrld nil nil)))
             (cond (msg (er soft ctx "~@0" msg))
                   (t (value nil)))))))

(defun defevaluator-check-form (x evfn evfn-lst fn-args-lst)
  (declare (xargs :guard t))
  `(with-output
    :off error
    :stack :push
    (make-event
     (er-progn
      (with-output
       :stack :pop
       (defevaluator-check ',x ',evfn ',evfn-lst ',fn-args-lst
         '(defevaluator . ,evfn)
         state))
      (value '(value-triple nil))))))

(defmacro defevaluator (&whole x evfn evfn-lst fn-args-lst
                               &key skip-checks namedp)

; Note: It might be nice to allow defevaluator to take a :DOC string, but that
; would require allowing encapsulate to take such a string!

; This function executes an encapsulate that defines an evaluator
; evfn (with mutually recursive counterpart evfn-lst for lists of
; terms) that recognizes the functions in fns.

; Note: This version of defevaluator was adapted, with permission, from ACL2
; Community Book tools/defevaluator-fast.lisp which was authored by Sol Swords
; and Jared Davis.  The defevaluator-fast defun-nx for evfn and evfn-lst,
; together with the preliminary lemmas and hints for the constraints were
; ripped from that book.  The code for generating those forms was refactored to
; make it clear that the :namedp option only affects the names of the
; constraint theorems.

  (let ((form (defevaluator-form evfn evfn-lst namedp fn-args-lst)))
    (cond (skip-checks form)
          (t `(progn ,(defevaluator-check-form x evfn evfn-lst fn-args-lst)
                     ,form)))))

(table term-table nil nil
       :guard
       (term-listp val world))

(table term-table t '((binary-+ x y) (binary-* '0 y) (car x)))

(defun remove-meta-extract-contextual-hyps (hyps ev mfc-symbol a)

; Return (mv hyps' flg), where hyps' is the result of removing suitable
; meta-extract-contextual-fact hypotheses from hyps and flg is true if and only
; if at least one such hypothesis was removed.  Ev is the evaluator function
; symbol and mfc-symbol is either nil or the mfc from the conclusion of a rule
; of class :meta.  See also remove-meta-extract-global-hyps for an
; corresponding function for global hypotheses.

  (cond
   ((atom hyps) (mv nil nil))
   (t (let ((hyp (car hyps)))
        (mv-let
         (hs flg)
         (remove-meta-extract-contextual-hyps (cdr hyps) ev mfc-symbol a)
         (case-match hyp
           ((!ev ('meta-extract-contextual-fact & !mfc-symbol

; Note that meta-extract-contextual-fact calls mfc- functions, which get their
; world from the mfc, not the state (at least as of this writing, on
; 4/17/2013).  Thus, we believe that meta-extract-contextual-fact is correct
; regardless of the state argument.  This belief allows us to loosen the
; restriction that the state is 'state, and instead allow an arbitrary state
; here.  But we keep the restriction that state is 'state; we may more
; carefully consider relaxing it upon request.

                                                'state)
                 !a)
            (mv hs t))
           (& (mv (cons hyp hs) flg))))))))

(defun remove-meta-extract-global-hyps (hyps ev)

; Return (mv hyps' flg), where hyps' is the result of removing suitable
; meta-extract-global-fact+ hypotheses from hyps and flg is true if and only if
; at least one such hypothesis was removed.  Ev is the evaluator function
; symbol.  See also remove-meta-extract-contextual-hyps for an analogous
; function.

  (declare (xargs :mode :program))
  (cond
   ((atom hyps) (mv nil nil))
   (t (let ((hyp (car hyps)))
        (mv-let
         (hs flg)
         (remove-meta-extract-global-hyps (cdr hyps) ev)
         (case-match hyp
           ((!ev ('meta-extract-global-fact+ & & 'state) &)
            (mv hs t))
           (& (mv (cons hyp hs) flg))))))))

(defun meta-rule-hypothesis-functions (hyp ev x a mfc-symbol)

; Here hyp is the hypothesis of the proposed meta rule (or, *t* if
; there is none).  We want to identify the hypothesis metafunction
; (see :DOC meta) of that rule.  We return nil if the hyp is
; unacceptable, t if there is no extra hypothesis, and otherwise the
; hypothesis function symbol.  Note that we allow, but do not require,
; the hypotheses (pseudo-termp x) and (alistp a) to be among the
; hypotheses, in which case we delete them before returning the
; result.

; If mfc-symbol is non-nil, this is an extended metafunction and we
; insist that the hyp function be extended also.  All extended
; functions take three arguments, the term, the context, and STATE, in
; that order.  The value of mfc-symbol is the variable symbol used to
; denote the context.

  (let ((hyps (remove1-equal
               (fcons-term* 'pseudo-termp x)
               (remove1-equal (fcons-term* 'alistp a)
                              (flatten-ands-in-lit hyp)))))
    (mv-let
     (hyps flg1)
     (if mfc-symbol
         (remove-meta-extract-contextual-hyps hyps ev mfc-symbol a)
       (mv hyps nil))
     (mv-let
      (hyps flg2)
      (remove-meta-extract-global-hyps hyps ev)
      (let ((hyp3 (car hyps))
            (extended-args
             (if mfc-symbol (cons mfc-symbol '(STATE)) nil)))
        (mv (cond
             ((null hyps) t)
             (t (and (null (cdr hyps))
                     (case-match hyp3
                       ((!ev (fn !x . !extended-args) !a)
                        (if (symbolp fn)
                            fn
                          nil))
                       (& nil)))))
            (append (and flg1 '(meta-extract-contextual-fact))
                    (and flg2 '(meta-extract-global-fact+)))))))))

(defun meta-fn-args (term extendedp ens state)
  (cond
   (extendedp
    (let ((wrld (w state)))
      (list term
            (make metafunction-context
                  :rdepth (rewrite-stack-limit wrld)
                  :type-alist nil
                  :obj '?
                  :geneqv nil
                  :wrld wrld
                  :fnstack nil
                  :ancestors nil
                  :simplify-clause-pot-lst nil
                  :rcnst
                  (make-rcnst ens wrld state
                              :force-info t
                              :top-clause (list term)
                              :current-clause (list term))
                  :gstack nil
                  :ttree nil
                  :unify-subst nil)
            (coerce-state-to-object state))))
   (t (list term))))

(defun chk-meta-function (metafn name trigger-fns extendedp
                                 term-list ctx ens state)

; If extendedp is nil we call metafn on only one term arg.  Otherwise, we call
; it on args of the type: (term context state).  We manufacture a trivial
; context.  We don't care what non-nil value extendedp is.

  (cond
   ((null term-list)
    (value nil))
   ((or (variablep (car term-list))
        (fquotep (car term-list))
        (flambda-applicationp (car term-list))
        (not (member-eq (ffn-symb (car term-list)) trigger-fns)))
    (chk-meta-function metafn name trigger-fns extendedp
                       (cdr term-list) ctx ens state))
   (t
    (let ((args (meta-fn-args (car term-list) extendedp ens state)))
      (pprogn
       (cond
        ((warning-disabled-p "Meta")
         state)
        (t
         (mv-let (erp val latches)
                 (ev-fncall-meta metafn args state)
                 (declare (ignore latches))
                 (cond
                  (erp

; We use warnings rather than errors when the checks fail, partly so
; that we can feel free to change the checks without changing what the
; prover will accept.  Put differently, we don't want user-managed
; tables to affect what the prover is able to prove.

                   (warning$ ctx ("Meta")
                             "An error occurred upon running the metafunction ~
                              ~x0 on the term ~x1.  This does not bode well ~
                              for the utility of this metafunction for the ~
                              meta rule ~x2.  See :DOC term-table."
                             metafn (car term-list) name))
                  ((termp val (w state))
                   state)
                  (t
                   (warning$ ctx ("Meta")
                             "The value obtained upon running the ~
                              metafunction ~x0 on the term ~x1 is ~x2, which ~
                              is NOT a termp in the current ACL2 world.  This ~
                              does not bode well for the utility of this ~
                              metafunction for the meta rule ~x3.  See :DOC ~
                              term-table."
                             metafn (car term-list) val name))))))
       (chk-meta-function
        metafn name trigger-fns extendedp (cdr term-list) ctx ens state))))))

(defun ev-lst-from-ev (ev wrld)

; We expect already to have checked that ev has a known constraint (see assert$
; call below).

  (guess-evfn-lst-for-evfn
   ev
   (normalized-evaluator-cl-set ev wrld)))

(defun attached-fns (fns wrld)
  (cond ((endp fns) nil)
        (t (let ((prop (attachment-alist (car fns) wrld)))
             (cond ((or (null prop)
                        (and (consp prop)
                             (eq (car prop)
                                 :attachment-disallowed)))
                    (attached-fns (cdr fns) wrld))
                   (t (cons (car fns)
                            (attached-fns (cdr fns) wrld))))))))

(defun siblings (f wrld)
  (or (getpropc f 'siblings nil wrld)
      (getpropc f 'recursivep nil wrld)
      (list f)))

(defun canonical-sibling (f wrld)
  (let ((sibs (getpropc f 'siblings nil wrld)))
    (cond (sibs (car sibs))
          (t (let ((sibs (getpropc f 'recursivep nil wrld)))
               (cond (sibs (car sibs))
                     (t f)))))))

(mutual-recursion

(defun canonical-ffn-symbs (term wrld ans ignore-fns rlp)

; For a discussion of rlp, see the end of the Essay on Correctness of Meta
; Reasoning.

  (cond
   ((variablep term) ans)
   ((fquotep term) ans)
   ((and rlp
         (eq (ffn-symb term) 'return-last)
         (not (equal (fargn term 1) ''mbe1-raw)))
    (canonical-ffn-symbs (fargn term 3) wrld ans ignore-fns rlp))
   (t (canonical-ffn-symbs-lst
       (fargs term)
       wrld
       (cond ((flambda-applicationp term)
              (canonical-ffn-symbs (lambda-body (ffn-symb term))
                                   wrld
                                   ans
                                   ignore-fns
                                   rlp))
             (t (let ((fn (canonical-sibling (ffn-symb term) wrld)))
                  (cond ((member-eq fn ignore-fns) ans)
                        (t (add-to-set-eq fn ans))))))
       ignore-fns
       rlp))))

(defun canonical-ffn-symbs-lst (lst wrld ans ignore-fns rlp)
  (cond ((null lst) ans)
        (t (canonical-ffn-symbs-lst
            (cdr lst)
            wrld
            (canonical-ffn-symbs (car lst) wrld ans ignore-fns rlp)
            ignore-fns
            rlp))))

)

(defun collect-canonical-siblings (fns wrld ans ignore-fns)
  (cond ((endp fns) ans)
        (t (collect-canonical-siblings
            (cdr fns)
            wrld
            (let ((fn (canonical-sibling (car fns) wrld)))
              (cond ((or (member-eq fn ignore-fns)
                         (member-eq fn ans))
                     ans)
                    (t (cons fn ans))))
            ignore-fns))))

(defun constraints-list (fns wrld acc seen)
  (cond ((endp fns) acc)
        (t (mv-let
            (name x)
            (constraint-info (car fns) wrld)
            (cond ((unknown-constraints-p x)
                   x)
                  (name (cond ((member-eq name seen)
                               (constraints-list (cdr fns) wrld acc seen))
                              (t (constraints-list (cdr fns)
                                                   wrld
                                                   (union-equal x acc)
                                                   (cons name seen)))))
                  (t (constraints-list (cdr fns) wrld (cons x acc) seen)))))))

(defun constraint-info+ (fn wrld)

; This function normally agrees with constraint-info, but
; extends that function's result in the case that fn is defined by
; mutual-recursion.  In that case, we return (mv t lst) where lst is the list
; of constraints of the siblings of fn.

  (let ((fns (getpropc fn 'recursivep nil wrld)))
    (cond ((and (consp fns)
                (consp (cdr fns)))
           (mv t (constraints-list fns wrld nil nil)))
          (t (constraint-info fn wrld)))))

(defun immediate-canonical-ancestors (fn wrld ignore-fns rlp)

; This function is analogous to immediate-instantiable-ancestors, but it
; traffics entirely in canonical functions and is not concerned with the notion
; of instantiablep.  To see why guards are involved, see the reference to the
; Essay on Correctness of Meta Reasoning in the Essay on Defattach, which also
; explains special handling of return-last, performed here when rlp is true.

  (let ((guard-anc
         (canonical-ffn-symbs (guard fn nil wrld) wrld nil ignore-fns rlp)))
    (mv-let (name x) ; name could be t
            (constraint-info+ fn wrld)
            (cond
             ((unknown-constraints-p x)
              (collect-canonical-siblings (unknown-constraints-supporters x)
                                          wrld guard-anc
                                          ignore-fns))
             (name (canonical-ffn-symbs-lst x wrld guard-anc ignore-fns rlp))
             (t (canonical-ffn-symbs x wrld guard-anc ignore-fns rlp))))))

(defun canonical-ancestors-rec (fns wrld ans rlp)

; See canonical-ancestors.  Unlike that function, it includes fns in the
; result, and it assumes that all functions in fns are canonical.

  (cond
   ((null fns) ans)
   ((member-eq (car fns) ans)
    (canonical-ancestors-rec (cdr fns) wrld ans rlp))
   (t
    (let* ((ans1 (cons (car fns) ans))
           (imm (immediate-canonical-ancestors (car fns) wrld ans1 rlp))
           (ans2 (canonical-ancestors-rec imm wrld ans1 rlp)))
      (canonical-ancestors-rec (cdr fns) wrld ans2 rlp)))))

(defun canonical-ancestors (fn wrld rlp)

; This function is completely analogous to instantiable-ancestors, except that
; it takes a single function that is not included in the result, it traffics
; entirely in canonical functions, and it is not concerned with the notion of
; instantiablep.  It assumes that fn is canonical.

; For a discussion of rlp, see the end of the Essay on Correctness of Meta
; Reasoning.

  (let* ((imm (immediate-canonical-ancestors fn wrld (list fn) rlp)))
    (canonical-ancestors-rec imm wrld nil rlp)))

(defun canonical-ancestors-lst (fns wrld)

; Fns is a set of function symbols, not necessarily canonical.  We return all
; canonical ancestors of fns.

  (canonical-ancestors-rec (collect-canonical-siblings fns wrld nil nil)
                           wrld nil t))

(defun chk-evaluator-use-in-rule (name meta-fn hyp-fn extra-fns rule-type ev
                                       ctx wrld state)
  (er-progn
   (let ((temp (context-for-encapsulate-pass-2 (decode-logical-name ev wrld)
                                               (f-get-global 'in-local-flg
                                                             state))))
     (case temp
       (illegal
        (er soft ctx ; see comment in defaxiom-supporters
            "The proposed ~x0 rule, ~x1, is illegal because its evaluator ~
             function symbol, ~x2, is defined in a superior non-trivial ~
             encapsulate event (``non-trivial'' in the sense that it has a ~
             non-empty signature).  See :DOC evaluator-restrictions.  In some ~
             cases, a solution is to make the current ~x0 rule LOCAL, though ~
             the alleged evaluator will probably not be available for future ~
             :META or :CLAUSE-PROCESSOR rules."
            rule-type
            name
            ev))
       (maybe
        (pprogn
         (warning$ ctx nil ; add a string here if someone wants to turn this off
                   "The proposed ~x0 rule will ultimately need to be LOCAL in ~
                    its immediately surrounding encapsulate event, because ~
                    its evaluator is introduced in a superior non-trivial ~
                    encapsulate event.  Even if this rule is LOCAL, the ~
                    alleged evaluator will probably not be available for ~
                    future :META or :CLAUSE-PROCESSOR rules. See :DOC ~
                    evaluator-restrictions."
                   rule-type
                   name
                   ev)
         (value nil)))
       (otherwise (value nil))))
   (mv-let
    (fn constraint)
    (constraint-info ev wrld)
    (declare (ignore fn))
    (cond
     ((unknown-constraints-p constraint)
      (er soft ctx ; see comment in defaxiom-supporters
          "The proposed ~x0 rule, ~x1, is illegal because its evaluator ~
           function symbol, ~x2, has unknown-constraints.  See :DOC ~
           partial-encapsulate."
          rule-type
          name
          ev))
     (t
      (let* ((ev-lst (ev-lst-from-ev ev wrld))
             (ev-prop (getpropc ev 'defaxiom-supporter nil wrld))
             (ev-lst-prop (getpropc ev-lst 'defaxiom-supporter nil wrld))
             (meta-fn-lst (if hyp-fn
                              (list meta-fn hyp-fn)
                            (list meta-fn)))
             (meta-anc (canonical-ancestors-lst meta-fn-lst wrld))
             (extra-anc (canonical-ancestors-lst extra-fns wrld))
             (ev-anc (canonical-ancestors-lst (list ev) wrld)))
        (cond
         ((and extra-fns
               (or (getpropc ev 'predefined nil wrld)
                   (getpropc ev-lst 'predefined nil wrld)))

; Note that since extra-fns are defined in the boot-strap world, this check
; guarantees that ev is not ancestral in extra-fns.

          (er soft ctx
              "The proposed evaluator function, ~x0, was defined in the ~
               boot-strap world.  This is illegal when meta-extract hypotheses ~
               are present, because for logical reasons our implementation ~
               assumes that the evaluator is not ancestral in ~v1."
              (if (getpropc ev 'predefined nil wrld)
                  ev
                ev-lst)
              '(meta-extract-contextual-fact meta-extract-global-fact+)))
         ((or ev-prop ev-lst-prop)
          (er soft ctx ; see comment in defaxiom-supporters
              "The proposed ~x0 rule, ~x1, is illegal because its evaluator ~
               function symbol, ~x2, supports the formula of the defaxiom ~
               event named ~x3.  See :DOC evaluator-restrictions."
              rule-type
              name
              (if ev-prop ev ev-lst)
              (or ev-prop ev-lst-prop)))
         (t

; We would like to be able to use attachments where possible.  However, the
; example at the end of :doc evaluator-restrictions shows that this is unsound
; in general and is followed by other relevant remarks.

          (let ((bad-attached-fns-1
                 (attached-fns (intersection-eq ev-anc meta-anc) wrld))
                (bad-attached-fns-2

; Although we need bad-attached-fns-2 to be empty (see the Essay on Correctness
; of Meta Reasoning), we could at the very least store extra-anc in the world,
; based on both meta-extract-contextual-fact and meta-extract-global-fact+, so
; that we don't have to compute extra-anc every time.  But that check is
; probably cheap, so we opt for simplicity.

                 (attached-fns (intersection-eq extra-anc meta-anc) wrld)))
              (cond
               ((or bad-attached-fns-1 bad-attached-fns-2)
                (let ((msg "because the attached function~#0~[~/s~] ~&0 ~
                            ~#0~[is~/are~] ancestral in both the ~@1 and ~@2 ~
                            functions")
                      (type-string
                       (if (eq rule-type :meta) "meta" "clause-processor")))
                  (er soft ctx ; see comment in defaxiom-supporters
                      "The proposed ~x0 rule, ~x1, is illegal ~@2~@3.  See ~
                       :DOC evaluator-restrictions."
                      rule-type
                      name
                      (msg msg
                           (or bad-attached-fns-1 bad-attached-fns-2)
                           (if bad-attached-fns-1 "evaluator" "meta-extract")
                           type-string)
                      (cond ((and bad-attached-fns-1 bad-attached-fns-2)
                             (msg ", and because ~@0"
                                  (msg msg
                                       bad-attached-fns-2
                                       "meta-extract"
                                       type-string)))
                            (t "")))))
               (t (value nil))))))))))))

(defun chk-rule-fn-guard (function-string rule-type fn ctx wrld state)

; At one time we insisted that fn not have a non-nil value for its 'constrained
; or 'non-executablep property.  With the advent of defattach, a constrained
; function may however be a reasonable choice.  Rather than do an elaborate
; check here on exactly what sort of constrained function might be attachable,
; we trust that the writer of :meta and :clause-processor rules knows better
; than to attach to functions that cannot be executed.

  (let ((guard (guard fn t wrld))
        (pseudo-termp-predicate
         (case rule-type
           (:meta 'pseudo-termp)
           (:clause-processor 'pseudo-term-listp)
           (t (er hard 'chk-rule-fn-guard
                  "Implementation error: unknown case in chk-rule-fn-guard. ~
                   Please contact the ACL2 implementors.")))))
    (cond ((or (equal guard *t*)
               (tautologyp
                (fcons-term* 'implies
                             (fcons-term* pseudo-termp-predicate
                                          (car (formals fn wrld)))
                             guard)
                wrld))
           (value nil))
          (t (er soft ctx
                 "The ~s0 of a ~x1 rule must have a guard that obviously ~
                  holds whenever its first argument is known to be a ~x2 and ~
                  any stobj arguments are assumed to satisfy their stobj ~
                  predicates.  However, the guard for ~x3 is ~p4.  See :DOC ~
                  ~@5."
                 function-string
                 rule-type
                 pseudo-termp-predicate
                 fn
                 (untranslate guard t wrld)
                 (case rule-type
                   (:meta "meta")
                   (:clause-processor "clause-processor")
                   (t (er hard 'chk-rule-fn-guard
                          "Implementation error: unknown case in ~
                           chk-rule-fn-guard.  Please contact the ACL2 ~
                           implementors."))))))))

; Essay on never-untouchable-fns

; The global-val of 'never-untouchable-fns is an alist pairing function symbols
; with lists of well-formedness-guarantees.  A well-formedness-guarantee is a
; structure of the form ((name fn thm-name1 hyp-fn thm-name2) . arity-alist),
; where hyp-fn and thm-name2 may be omitted.  It denotes the fact that the
; metatheorem named name justifies the metafunction fn (with hypothesis
; metafunction hyp-fn if present), and that the two metafunctions are
; guaranteed to return LOGIC-TERMPs by the theorems named thm-name1 and
; thm-name2 respectively, provided the world satisfies arity-alist.  The
; function symbols listed in arity-alist are the symbols that may be introduced
; by the metafunction or the hypothesis metafunction.  When a metatheorem with
; LOGIC-TERMP guarantees is added, we make sure that none of the introduced
; symbols are on (forbidden-fns wrld state).  See
; translate-well-formedness-guarantee.  We also record the fact that those
; introduced symbols should never be made untouchable, by adding the
; well-formedness-guarantee to the symbol's entry on never-untouchable-fns.
; Thereafter, we prevent any of those function symbols from being added to
; untouchable-fns.  This is done in push-untouchable, by comparing any
; about-to-be-made-untouchable function with never-untouchable-fns.

(defun add-new-never-untouchable-fns (fns well-formedness-guarantee
                                          never-untouchable-fns)

; Well-formedness-guarantee is a structure of the form ((name fn thm-name1
; hyp-fn thm-name2) . arity-alist), where hyp-fn and thm-name2 may be omitted.
; It denotes the fact that the metatheorem named name justifies the
; metafunction fn (with hypothesis metafunction hyp-fn if present), and that
; the two metafunctions are guaranteed to return LOGIC-TERMPs by the theorems
; named thm-name1 and thm-name2 respectively, provided the world satisfies
; arity-alist.  Fns, above, is a list of function symbols possibly introduced
; by the metatheorem described by well-formedness-guarantee.  (In fact, it is
; initially just the keys of the arity-alist.)  Never-untouchable-fns is an
; alist pairing function symbols to well-formedness-guarantees that may
; introduce that symbol.  We add this new well-formedness-guarantee to the
; entries for fns.

  (cond ((endp fns) never-untouchable-fns)
        (t (add-new-never-untouchable-fns
            (cdr fns)
            well-formedness-guarantee
            (put-assoc-eq
             (car fns)
             (add-to-set-equal well-formedness-guarantee
                               (cdr (assoc-eq (car fns) never-untouchable-fns)))
             never-untouchable-fns)))))

(defun collect-never-untouchable-fns-entries (fns never-untouchable-fns)

; Suppose the list of function symbols fns is to be pushed onto
; untouchable-fns.  We use this function to collect those g in fns (and
; information from their well-formedness-guarantees) which are not supposed to be
; made untouchable.  The result of this function is thus nil if there are no
; never-untouchable-fns names in fns and otherwise, for each name gi that is
; not to be made untouchable we will have an entry in the result of the form
; (gi relevant-names1 relevant-names2 ...), where each relevant-namesi is the
; car of a well-formedness-guarantee, i.e., a list of 5 (or 3) names (name fn
; thm-name1 hyp-fn thm-name2) with the last two possibly omitted.  This data
; structure is only shown to the user to help him or her figure out why we're
; rejecting a proposed untouchable function.

  (cond
   ((endp fns) nil)
   (t (let ((entry (assoc-eq (car fns) never-untouchable-fns)))
        (cond
         (entry
          (cons entry
                (collect-never-untouchable-fns-entries (cdr fns)
                                                       never-untouchable-fns)))
         (t (collect-never-untouchable-fns-entries (cdr fns)
                                                   never-untouchable-fns)))))))

(defun interpret-term-as-meta-rule (term)

; We match term against the acceptable forms of metafunction correctness
; theorems and return the pieces: (mv hyp eqv ev x a fn mfc-symbol), where hyp
; is the hypothesis term or *t*, eqv is the equivalence relation, ev is the
; evaluator, etc.  We do absolutely no well-formedness checks here, just
; deconstruct the term!  For example, eqv, ev, or fn may be (unacceptable)
; LAMBDA expressions, x may not be a variable symbol, etc.  But since term is
; known to be a term, eqv, for example, cannot be nil unless we fail to match
; any of the acceptable forms.  Our convention is to test eqv to see if the
; term was deconstructed.  If mfc-symbol is nil, fn is a vanilla flavored
; metafunction taking one argument, else it is an extended metafunction.  But,
; despite its name, we don't know that mfc-symbol is a symbol, it could be any
; term.

  (case-match term
    (('IMPLIES hyp
               (eqv (ev x a) (ev (fn x) a)))
     (mv hyp eqv ev x a fn nil))
    ((eqv (ev x a) (ev (fn x) a))
     (mv *t* eqv ev x a fn nil))
    (('IMPLIES hyp
               (eqv (ev x a)
                    (ev (fn x mfc-symbol 'STATE)
                        a)))
     (mv hyp eqv ev x a fn mfc-symbol))
    ((eqv (ev x a)
          (ev (fn x mfc-symbol 'STATE)
              a))
     (mv *t* eqv ev x a fn mfc-symbol))
    (& (mv *t* nil nil nil nil nil nil))))

(defun chk-acceptable-meta-rule (name trigger-fns term ctx ens wrld state)
  (if (member-eq 'IF trigger-fns)
      (er soft ctx
          "The function symbol IF is not an acceptable member of ~
           :trigger-fns, because the ACL2 simplifier is not set up to apply ~
           :meta rules to calls of IF.")
    (let ((str "No :META rule can be generated from ~x0 because ~p1 does not ~
                have the form of a metatheorem.  See :DOC meta."))
      (mv-let
       (hyp eqv ev x a fn mfc-symbol)
       (interpret-term-as-meta-rule term)
       (cond ((null eqv)
              (er soft ctx str name (untranslate term t wrld)))
             ((eq fn 'return-last)

; Ev-fncall-meta calls ev-fncall!.  We could make an exception for return-last,
; calling ev-fncall instead, but for now we avoid that runtime overhead by
; excluding return-last.  It's a bit difficult to imagine that anyone would
; use return-last as a metafunction anyhow.

              (er soft ctx
                  "It is illegal to use ~x0 as a metafunction, as specified ~
                   by ~x1.  See :DOC meta."
                  'return-last name))
             ((not (and (not (flambdap eqv))
                        (equivalence-relationp eqv wrld)
                        (variablep x)
                        (variablep a)
                        (not (eq x a))
                        (not (eq fn 'quote))
                        (not (flambdap fn))
                        (or (null mfc-symbol)
                            (and (variablep mfc-symbol)
                                 (no-duplicatesp (list x a mfc-symbol 'STATE))))))

; Note:  Fn must be a symbol, not a lambda expression.  That is because
; in rewrite-with-lemma, when we apply the metafunction, we use ev-fncall-meta.

              (er soft ctx str name (untranslate term t wrld)))
             ((not (member-equal (stobjs-in fn wrld)
                                 '((nil)
                                   (nil nil state))))
              (er soft ctx
                  "Metafunctions cannot take single-threaded object names ~
                   other than STATE as formal parameters. The function ~x0 ~
                   may therefore not be used as a metafunction."
                  fn))
             (t (er-progn
                 (chk-rule-fn-guard "metafunction" :meta fn ctx wrld state)
                 (mv-let
                  (hyp-fn extra-fns)
                  (meta-rule-hypothesis-functions hyp ev x a mfc-symbol)
                  (let ((term-list
                         (cdar (table-alist 'term-table (w state)))))
                    (er-progn
                     (cond
                      ((null hyp-fn)
                       (er soft ctx str name (untranslate term t wrld)))
                      ((and (not (eq hyp-fn t))
                            (not (member-equal (stobjs-in hyp-fn wrld)
                                               '((nil)
                                                 (nil nil state)))))

; It is tempting to avoid the check here that hyp-fn does not take
; stobjs in.  After all, we have already checked this for fn, and fn
; and hyp-fn have the same actuals.  But our defun warts allow certain
; functions to traffic in stobjs even though they do not use STATE (or
; another stobj name) as a formal.  So, we play it safe and check.

                       (er soft ctx
                           "Hypothesis metafunctions cannot take single ~
                           threaded object names as formal parameters.  The ~
                           function ~x0 may therefore not be used as a ~
                           hypothesis metafunction."
                           hyp-fn))
                      ((not (eq hyp-fn t))
                       (er-progn
                        (chk-evaluator-use-in-rule name
                                                   fn hyp-fn extra-fns
                                                   :meta ev ctx wrld state)
                        (chk-rule-fn-guard "hypothesis function" :meta fn ctx
                                           wrld state)))
                      (t (chk-evaluator-use-in-rule name
                                                    fn nil extra-fns
                                                    :meta ev ctx wrld state)))
                     (chk-evaluator ev wrld ctx state)

; In the code below, mfc-symbol is used merely as a Boolean indicating
; that this is an extended metafunction.

                     (chk-meta-function fn name trigger-fns mfc-symbol
                                        term-list ctx ens state)
                     (if (eq hyp-fn t)
                         (value nil)
                       (chk-meta-function hyp-fn name trigger-fns mfc-symbol
                                          term-list ctx ens state))))))))))))

; And to add a :META rule:

(defun add-meta-rule1 (lst rule wrld)

; Fn is a function symbol, not a lambda expression.

  (cond ((null lst) wrld)
        (t
         (add-meta-rule1 (cdr lst) rule
                         (putprop (car lst)
                                  'lemmas
                                  (cons rule
                                        (getpropc (car lst) 'lemmas nil wrld))
                                  wrld)))))

(defun maybe-putprop-lst (symb-lst key val wrld)
  (cond ((endp symb-lst)
         wrld)
        (t (let ((symb (car symb-lst)))
             (maybe-putprop-lst
              (cdr symb-lst) key val
              (cond ((getpropc symb key nil wrld)
                     wrld)
                    (t (putprop symb key val wrld))))))))

(defun mark-attachment-disallowed2 (fns msg wrld)

; It might be that we only need to disallow attachments to constrained
; functions.  However, our theory (Essay on Correctness of Meta Reasoning, as
; referenced in chk-evaluator-use-in-rule) doesn't address this possibility, so
; until someone complains we'll keep this simple and disallow attachments for
; each member of fns, whether or not its attachment is used in evaluation.

  (cond ((endp fns) wrld)
        (t (mark-attachment-disallowed2
            (cdr fns)
            msg
            (let ((old-prop (getpropc (car fns) 'attachment nil wrld)))
              (cond ((and (consp old-prop)
                          (eq (car old-prop)
                              :attachment-disallowed))
                     wrld)
                    (t (putprop (car fns)
                                'attachment
                                (cons :attachment-disallowed msg)
                                wrld))))))))

(defun mark-attachment-disallowed1 (canonical-fns msg wrld)
  (cond ((endp canonical-fns) wrld)
        (t (mark-attachment-disallowed1
            (cdr canonical-fns)
            msg
            (mark-attachment-disallowed2 (siblings (car canonical-fns) wrld)
                                         msg
                                         wrld)))))

(defun mark-attachment-disallowed (meta-fns ev msg wrld)

; We mark as unattachable all functions ancestral in both meta-fns and ev.  We
; obtain that set of common ancestors by restricting first to canonical
; functions, and then taking all siblings (in mark-attachment-disallowed1)
; before marking (in mark-attachment-disallowed2).

  (mark-attachment-disallowed1
   (intersection-eq (canonical-ancestors-lst meta-fns wrld)
                    (canonical-ancestors-lst (list ev) wrld))
   msg
   wrld))

(defun add-meta-rule (rune nume trigger-fns well-formedness-guarantee
                           term backchain-limit wrld)
  (mv-let
   (hyp eqv ev x a fn mfc-symbol)
   (interpret-term-as-meta-rule term)
   (mv-let
    (hyp-fn extra-fns)
    (meta-rule-hypothesis-functions hyp ev x a mfc-symbol)
    (declare (ignore extra-fns))
    (cond
     ((or (null hyp-fn) (null eqv))
      (er hard 'add-meta-rule
          "Add-meta-rule broke on args ~x0!  It seems to be out of sync with ~
           chk-acceptable-meta-rule."
          (list rune nume trigger-fns term)))
     (t

; Note: If a :meta rule has a :WELL-FORMEDNESS-GUARANTEE spec, then
; well-formedness-guarantee is (name fn thm-name1 hyp-fn thm-name2)
; . combined-arities-alist), where the hyp-fn and thm-name2 entries are omitted
; if there is no hyp-fn.  If no :WELL-FORMEDNESS-GUARANTEE was specified, the
; well-formedness-guarantee is nil.  The :heuristic-info field of the resulting
; rule contains the well-formedness-guarantee.

      (let* ((arity-alist (cdr well-formedness-guarantee))
             (wrld1
              (add-meta-rule1 trigger-fns
                              (make rewrite-rule
                                    :rune rune
                                    :nume nume
                                    :hyps (if (eq hyp-fn t) nil hyp-fn)
                                    :equiv eqv
                                    :lhs fn
                                    :var-info nil ; unused
                                    :rhs (if mfc-symbol 'extended nil)
                                    :subclass 'meta
                                    :heuristic-info well-formedness-guarantee
                                    :backchain-limit-lst
                                    (rule-backchain-limit-lst
                                     backchain-limit
                                     nil ; hyps (ignored for :meta)
                                     wrld
                                     :meta))
                              (mark-attachment-disallowed
                               (if (eq hyp-fn t)
                                   (list fn)
                                   (list hyp-fn fn))
                               ev
                               (msg "it supports both evaluator and meta functions ~
                             used in :META rule ~x0"
                                    (base-symbol rune))
                               wrld)))
             (wrld2 (global-set 'never-untouchable-fns
                                (add-new-never-untouchable-fns
                                 (strip-cars arity-alist)
                                 well-formedness-guarantee
                                 (global-val 'never-untouchable-fns wrld1))
                                wrld1)))
        wrld2))))))

;---------------------------------------------------------------------------
; Section:  Destructor :ELIM Rules

(mutual-recursion

(defun destructors (term ans)

; Union-equal into ans all of the subterms of term of the form (fn v1
; ... vn) where fn is a symbol and the vi are distinct variables.

  (cond ((or (variablep term)
             (fquotep term)
             (flambda-applicationp term))
         ans)
        (t (destructors-lst (fargs term)
                            (cond ((and (fargs term)
                                        (all-variablep (fargs term))
                                        (no-duplicatesp-equal (fargs term)))
                                   (add-to-set-equal term ans))
                                  (t ans))))))

(defun destructors-lst (lst ans)
  (cond ((null lst) ans)
        (t (destructors-lst (cdr lst)
                            (destructors (car lst) ans)))))

)

(defun strip-ffn-symbs (lst)
  (cond ((null lst) nil)
        (t (cons (ffn-symb (car lst))
                 (strip-ffn-symbs (cdr lst))))))

(defun chk-acceptable-elim-rule1 (name vars dests ctx wrld state)
  (cond
   ((null dests) (value nil))
   ((not (subsetp-eq vars (fargs (car dests))))
    (er soft ctx
        "~x0 is an unacceptable destructor elimination rule because ~
         the destructor term ~x1 does not mention ~&2.  See :DOC elim."
        name
        (car dests)
        (set-difference-eq vars (fargs (car dests)))))
   ((getpropc (ffn-symb (car dests)) 'eliminate-destructors-rule nil wrld)
    (er soft ctx
        "~x0 is an unacceptable destructor elimination rule because we ~
         already have a destructor elimination rule for ~x1, namely ~x2, and ~
         we do not support more than one elimination rule for the same ~
         function symbol."
        name
        (ffn-symb (car dests))
        (base-symbol (access elim-rule
                             (getpropc (ffn-symb (car dests))
                                       'eliminate-destructors-rule nil wrld)
                             :rune))))
   (t (chk-acceptable-elim-rule1 name vars (cdr dests) ctx wrld state))))

(defun chk-acceptable-elim-rule (name term ctx wrld state)
  (let ((lst (unprettyify term)))
    (case-match
     lst
     (((& . (equiv lhs rhs)))
      (cond
       ((not (equivalence-relationp equiv wrld))
        (er soft ctx
            "~x0 is an unacceptable destructor elimination rule ~
             because ~x1 is not a known equivalence relation.  See ~
             :DOC elim."
            name equiv))
       ((nvariablep rhs)
        (er soft ctx
            "~x0 is an unacceptable destructor elimination rule ~
             because the right-hand side of its conclusion, ~x1, is ~
             not a variable symbol.  See :DOC elim."
            name rhs))
       (t
        (let ((dests (destructors lhs nil)))
          (cond
           ((null dests)
            (er soft ctx
                "~x0 is an unacceptable destructor elimination rule ~
                 because the left-hand side of its conclusion, ~x1, ~
                 does not contain any terms of the form (fn v1 ... ~
                 vn), where fn is a function symbol and the vi are ~
                 all distinct variables.  See :DOC elim."
                name lhs))
           ((not (no-duplicatesp-equal (strip-ffn-symbs dests)))
            (er soft ctx
                "~x0 is an unacceptable destructor elimination rule ~
                 because the destructor terms, ~&1, include more than ~
                 one occurrence of the same function symbol.  See :DOC ~
                 elim."
                name dests))
           ((occur rhs (sublis-expr (pairlis-x2 dests *t*) lhs))
            (er soft ctx
                "~x0 is an unacceptable destructor elimination rule ~
                 because the right-hand side of the conclusion, ~x1, ~
                 occurs in the left-hand side, ~x2, in places other ~
                 than the destructor term~#3~[~/s~] ~&3.  See :DOC ~
                 elim."
                name rhs lhs dests))
           (t (chk-acceptable-elim-rule1 name (all-vars term)
                                         dests ctx wrld state)))))))
     (&
      (er soft ctx
          "~x0 is an unacceptable destructor elimination rule because ~
           its conclusion is not of the form (equiv lhs rhs).  See ~
           :DOC elim."
          name)))))

; and to add an :ELIM rule:

(defun add-elim-rule1 (rune nume hyps equiv lhs rhs lst dests wrld)

; Lst is a tail of dests and contains the destructor terms for which we
; have not yet added a rule.  For each destructor in lst we add an elim
; rule to wrld.

  (cond ((null lst) wrld)
        (t (let* ((dest (car lst))
                  (rule (make elim-rule
                              :rune rune
                              :nume nume
                              :hyps hyps
                              :equiv equiv
                              :lhs lhs
                              :rhs rhs
                              :crucial-position
                              (- (length (fargs dest))
                                 (length (member-eq rhs (fargs dest))))
                              :destructor-term dest
                              :destructor-terms dests)))
             (add-elim-rule1 rune nume hyps equiv lhs rhs (cdr lst) dests
                             (putprop (ffn-symb dest)
                                      'eliminate-destructors-rule
                                      rule wrld))))))

(defun add-elim-rule (rune nume term wrld)
  (let* ((lst (unprettyify term))
         (hyps (caar lst))
         (equiv (ffn-symb (cdar lst)))
         (lhs (fargn (cdar lst) 1))
         (rhs (fargn (cdar lst) 2))
         (dests (reverse (destructors lhs nil))))
    (add-elim-rule1 rune nume hyps equiv lhs rhs dests dests wrld)))

;---------------------------------------------------------------------------
; Section:  :GENERALIZE Rules

(defun chk-acceptable-generalize-rule (name term ctx wrld state)

; This function is really a no-op.  It exists simply for regularity.

  (declare (ignore name term ctx wrld))
  (value nil))

(defun add-generalize-rule (rune nume term wrld)
  (global-set 'generalize-rules
              (cons (make generalize-rule
                          :rune rune
                          :nume nume
                          :formula term)
                    (global-val 'generalize-rules wrld))
              wrld))

;---------------------------------------------------------------------------
; Section:  :TYPE-PRESCRIPTION Rules

(defun find-type-prescription-pat (term ens wrld)

; Suppose term is the translation of a legal type-prescription lemma
; conclusion, e.g.,
; (or (rationalp (fn x x y))
;     (and (symbolp (fn x x y))
;          (not (equal (fn x x y) nil)))
;     (consp (fn x x y))
;     (equal (fn x x y) y)).
; In general, term will be some IF expression giving type or equality
; information about some function application, e.g., (fn x x y) in the
; example above.  This function attempts to identify the term whose
; type is described.  The function is merely heuristic in that if it
; fails (returns nil) the user will have to tell us what term to use.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term) nil)
        ((eq (ffn-symb term) 'if)
         (or (find-type-prescription-pat (fargn term 1) ens wrld)
             (find-type-prescription-pat (fargn term 2) ens wrld)
             (find-type-prescription-pat (fargn term 3) ens wrld)))
        ((eq (ffn-symb term) 'not)
         (find-type-prescription-pat (fargn term 1) ens wrld))
        ((eq (ffn-symb term) '<)
         (if (quotep (fargn term 1))
             (fargn term 2)
             (fargn term 1)))
        ((eq (ffn-symb term) 'equal)
         (cond ((or (variablep (fargn term 1))
                    (fquotep (fargn term 1)))
                (fargn term 2))
               ((or (variablep (fargn term 2))
                    (fquotep (fargn term 2)))
                (fargn term 1))
               (t nil)))
        ((let ((recog-tuple
                (most-recent-enabled-recog-tuple (ffn-symb term) wrld ens)))
           (and recog-tuple

; An ACL2(h) "everything" regression in August 2014 failed to certify community
; book centaur/aig/aiger-help.lisp when we added the following condition.  So
; we modified two defthm forms in that book by making the :typed-term explicit.

; Note that the most-recent-enabled-recog-tuple is the one used in
; assume-true-false-rec.  So here, we only consider that tuple; if it is not
; :strongp, then we do not look for a less recent enabled recog-tuple that is
; :strongp.

                (access recognizer-tuple recog-tuple :strongp)))
         (fargn term 1))
        (t term)))

(defun add-type-prescription-rule (rune nume typed-term term
                                        backchain-limit-lst ens wrld quietp)
  (mv-let
   (erp hyps concl ts vars ttree)
   (destructure-type-prescription (base-symbol rune)
                                  typed-term term ens wrld)
   (declare (ignore concl ttree))
   (cond
    (erp
     (cond (quietp

; We pass in the quietp flag when attempting to add a :type-prescription rule
; indirectly, as under a defequiv event.  The following example causes the
; following code to be executed.  Otherwise, we see an unfortunate error.  (Or
; perhaps we really should see that error, since we will be unable to add the
; booleanp type prescription for the equivalence relation.  However, then we
; will need to re-work community book
; books/workshops/2000/manolios/pipeline/pipeline/deterministic-systems/128/top/ma128-isa128.lisp.)

;  (defun my-equal (x y)
;    (equal x y))
;
;  (in-theory (disable
;              (:type-prescription my-equal)
;              (:COMPOUND-RECOGNIZER BOOLEANP-COMPOUND-RECOGNIZER)))
;
;  (defequiv my-equal
;    :hints (("Goal" :in-theory (enable booleanp))))
;
; ; In v2-7 and presumably earlier, the above leads us to a type-prescription
; ; rule with a NIL :basic-ts field:
;
;   ACL2 !>(car (getpropc 'my-equal 'type-prescriptions t))
;   (NIL (1685 MY-EQUAL X Y)
;        NIL
;        (NIL :EQUIVALENCE MY-EQUAL-IS-AN-EQUIVALENCE)
;        BOOLEANP (MY-EQUAL X Y))
;   ACL2 !>

            (prog2$ (cw "~%NOTE:  ACL2 is unable to create a proposed ~
                         type-prescription rule from the term ~x0 for ~
                         :typed-term ~x1, so this proposed rule is not being ~
                         added.~|"
                        term typed-term)
                    wrld))
           (t
            (er hard 'add-type-prescription-rule
                "Unable to process this :TYPE-PRESCRIPTION rule.  A possible ~
                 explanation is that we are in the second pass of an ~
                 include-book or encapsulate, and although this rule was ~
                 legal in the first pass, it is not legal in the second pass. ~
                 For example, the rule may depend on a preceding ~
                 :COMPOUND-RECOGNIZER rule local to this encapsulate or ~
                 include-book.  The usual error message for ~
                 :TYPE-PRESCRIPTION rules now follows.~|~%~@0"
                erp))))
    (t
     (putprop (ffn-symb typed-term)
              'type-prescriptions
              (cons (make type-prescription
                          :rune rune
                          :nume nume
                          :term typed-term
                          :hyps hyps
                          :backchain-limit-lst
                          (rule-backchain-limit-lst
                           backchain-limit-lst hyps wrld :ts)
                          :basic-ts ts
                          :vars vars
                          :corollary term)
                    (getpropc (ffn-symb typed-term) 'type-prescriptions nil
                              wrld))
              wrld)))))

(defun strong-compound-recognizer-p1 (recognizer-alist ens)
  (cond ((endp recognizer-alist) nil)
        ((let ((recog-tuple (car recognizer-alist)))
           (and (access recognizer-tuple recog-tuple :strongp)
                (enabled-numep (access recognizer-tuple recog-tuple :nume)
                               ens)))
         t)
        (t (strong-compound-recognizer-p1 (cdr recognizer-alist) ens))))

(defun strong-compound-recognizer-p (fn ens wrld)
  (let ((alist (getpropc fn 'recognizer-alist nil wrld)))
    (and alist ; optimization
         (strong-compound-recognizer-p1 alist ens))))

(defun warned-non-rec-fns-alist-for-tp (term ens wrld)
  (cond ((or (variablep term)
             (fquotep term))
         nil)
        ((flambdap (ffn-symb term))
         (put-assoc-equal
          (ffn-symb term)
          nil
          (non-recursive-fnnames-alist-lst (fargs term) ens wrld)))
        ((eq (ffn-symb term) 'if)

; Type-set and assume-true-false explore the top-level IF structure in such a
; way that NOT and strong compound recognizers aren't problems.

         (union-equal
          (warned-non-rec-fns-alist-for-tp
           (fargn term 1) ens wrld)
          (union-equal
           (warned-non-rec-fns-alist-for-tp
            (fargn term 2) ens wrld)
           (warned-non-rec-fns-alist-for-tp
            (fargn term 3) ens wrld))))
        ((eq (ffn-symb term) 'not)
         (warned-non-rec-fns-alist-for-tp (fargn term 1) ens wrld))
        ((strong-compound-recognizer-p (ffn-symb term) ens wrld)

; We noticed in August 2014 that only the most-recent-enabled-recog-tuple is
; relevant here; see assume-true-false-rec.  But this code has been in place
; for a long time, and it's not terribly unreasonable, since enabled status can
; change.

         (non-recursive-fnnames-alist-lst (fargs term) ens wrld))
        (t (non-recursive-fnnames-alist term ens wrld))))

(defun warned-non-rec-fns-alist-tp-hyps1 (hyps ens wrld acc)
  (cond
   ((endp hyps) acc)
   (t (warned-non-rec-fns-alist-tp-hyps1
       (cdr hyps) ens wrld
       (let ((hyp (if (and (nvariablep (car hyps))
;                               (not (fquotep (car hyps))) ; implied by:
                           (member-eq (ffn-symb (car hyps))
                                      '(force case-split)))
                      (fargn (car hyps) 1)
                    (car hyps))))
         (cond
          (acc (union-equal (warned-non-rec-fns-alist-for-tp hyp ens wrld)
                            acc))
          (t (warned-non-rec-fns-alist-for-tp hyp ens wrld))))))))

(defun warned-non-rec-fns-alist-tp-hyps (hyps ens wrld)
  (warned-non-rec-fns-alist-tp-hyps1 hyps ens wrld nil))

(defun chk-acceptable-type-prescription-rule (name typed-term term
                                                   backchain-limit-lst
                                                   ctx ens wrld state)

; Like all individual rule checkers, we either cause an error or
; return a ttree that records our dependencies on lemmas.

  (declare (ignore backchain-limit-lst))
  (mv-let
   (erp hyps concl ts vars ttree)
   (destructure-type-prescription name typed-term term ens wrld)
   (declare (ignore ts concl vars))
   (cond
    (erp (er soft ctx "~@0" erp))
    (t (let* ((warned-non-rec-fns-alist
               (and (not (warning-disabled-p "Non-rec"))
                    (warned-non-rec-fns-alist-tp-hyps hyps ens wrld)))
              (warned-non-rec-fns (strip-cars warned-non-rec-fns-alist))
              (warned-free-vars
               (and (not (warning-disabled-p "Free"))
                    (free-vars-in-hyps hyps
                                       (all-vars typed-term)
                                       wrld)))
              (inst-hyps (and warned-free-vars ; optimization
                              (hyps-that-instantiate-free-vars
                               warned-free-vars hyps))))
         (pprogn
          (cond
           (warned-non-rec-fns-alist
            (warning$ ctx ("Non-rec")
                      `("The hypothesis of the :type-prescription rule ~
                         generated from ~x0 contains the function symbol~#1~[ ~
                         ~&1, which has a non-recursive definition~/s ~&1, ~
                         which have non-recursive definitions~].~@2  Since ~
                         the hypotheses of :type-prescription rules are ~
                         relieved by type reasoning alone (and not rewriting) ~
                         ~#1~[this function is~/these functions are~] liable ~
                         to make the rule inapplicable.  See :DOC ~
                         type-prescription."
                        (:doc type-prescription)
                        (:name ,name)
                        (:non-recursive-fns
                         ,(hide-lambdas warned-non-rec-fns))
                        (:rule-class :type-prescription))
                      name
                      (hide-lambdas warned-non-rec-fns)
                      (non-rec-def-rules-msg warned-non-rec-fns-alist)))
           (t state))
          (cond
           (warned-free-vars
            (warning$ ctx ("Free")
                      `("The :type-prescription rule generated from ~x0 ~
                         contains the free variable~#1~[ ~&1.  This ~
                         variable~/s ~&1.  These variables~] will be chosen ~
                         by searching for instances of ~&2 among the ~
                         hypotheses of conjectures being rewritten.  This is ~
                         generally a severe restriction on the applicability ~
                         of the :type-prescription rule."
                        (:free-variables ,warned-free-vars)
                        (:instantiated-hyps ,inst-hyps)
                        (:name ,name)
                        (:rule-class :type-prescription))
                      name warned-free-vars inst-hyps))
           (t state))
          (cond
           ((and warned-free-vars
                 (forced-hyps inst-hyps))
            (warning$ ctx ("Free")
                      "For the forced ~#0~[hypothesis~/hypotheses~], ~&1, ~
                       used to instantiate free variables we will search for ~
                       ~#0~[an instance of the argument~/instances of the ~
                       arguments~] rather than ~#0~[an instance~/instances~] ~
                       of the FORCE or CASE-SPLIT ~#0~[term itself~/terms ~
                       themselves~].  If a search fails for such a ~
                       hypothesis, we will cause a case split on the ~
                       partially instantiated hypothesis.  Note that this ~
                       case split will introduce a ``free variable'' into the ~
                       conjecture.  While sound, this will establish a goal ~
                       almost certain to fail since the restriction described ~
                       by this apparently necessary hypothesis constrains a ~
                       variable not involved in the problem.  To highlight ~
                       this oddity, we will rename the free variables in such ~
                       forced hypotheses by prefixing them with ~
                       ``UNBOUND-FREE-''.  This is not guaranteed to generate ~
                       a new variable but at least it generates an unusual ~
                       one.  If you see such a variable in a subsequent proof ~
                       (and did not introduce them yourself) you should ~
                       consider the possibility that the free variables of ~
                       this type-prescription rule were forced into the ~
                       conjecture."
                      (if (null (cdr (forced-hyps inst-hyps))) 0 1)
                      (forced-hyps inst-hyps)))
           (t state))
          (value ttree)))))))

;---------------------------------------------------------------------------
; Section:  Symbol generation utilities

; The following functions, macros and theorems are used to generate symbols.  A
; general principle for symbol generation is that generated symbols should be
; in the current package.  Doing that in ACL2 requires using make-event in a
; top level form to determine the current package from state and then passing
; this package to functions that generate symbols.  The code below was adapted
; from similar code in ACL2s.  See books/acl2s/utilities.lisp for more
; utilities for generating symbols.  See books/acl2s/defunc.lisp for an example
; of a utility that generates symbols in the current package.  Other examples
; include defequiv, defrefinement and defcong, in this file.

(defun fix-pkg (pkg)
  (declare (xargs :guard (and (or (null pkg) (stringp pkg))
                              (not (equal pkg "")))))
  (if (and pkg (not (equal pkg *main-lisp-package-name*)))
      pkg
    "ACL2"))

(defmacro fix-intern$ (name pkg)
  `(intern$ ,name (fix-pkg ,pkg)))

(defmacro fix-intern-in-pkg-of-sym (string sym)
  `(intern-in-package-of-symbol
    ,string
    (let ((sym ,sym))
      (if (equal (symbol-package-name sym) *main-lisp-package-name*)
          (pkg-witness "ACL2")
        sym))))

(defun pack-to-string (l)
  (declare (xargs :guard (good-atom-listp l)))
  (coerce (packn1 l) 'string))

(defun gen-sym-sym (l sym)

; This is a version of packn-pos that fixes the package (so that it's not
; *main-lisp-package-name*).

  (declare (xargs :guard (and (good-atom-listp l)
                              (symbolp sym))))
  (fix-intern-in-pkg-of-sym (pack-to-string l) sym))

;---------------------------------------------------------------------------
; Section:  :EQUIVALENCE Rules

; For a rule to acceptable as an :EQUIVALENCE rule, it must state the
; Boolean-ness, reflexivity, symmetry, and transitivity of a 2-place
; function symbol.  We make the user type in the desired formula and
; then check that he typed a suitable one.  This way we can define a
; simple macro that generates a suitable defthm event (rather than
; have to produce a new event type with all the prove-level hint
; passing mechanism).  To check that the formula is suitable we
; generate a canonical formula and check that the given one subsumes
; it.  To add an :EQUIVALENCE rule we add a 'coarsenings property to
; the function symbol and also set up an initial 'congruences property
; for it.

; Some of the simple functions below anticipate the day we allow n-ary
; equivalences (n>2) but don't be fooled into thinking we allow it
; today!

(defun boolean-fn (fn sym)

; The name boolean is not usable for definitions in Allegro, because
; it's in the COMMON-LISP package.  So, we'd better not use that name
; here.

  (let ((x (fix-intern-in-pkg-of-sym "X" sym))
        (y (fix-intern-in-pkg-of-sym "Y" sym)))
  `(booleanp (,fn ,x ,y))))

(defun reflexivity (fn sym)

; In this function we expect fn to have arity 2.

  (let ((x (fix-intern-in-pkg-of-sym "X" sym)))
    `(,fn ,x ,x)))

(defun symmetry (fn sym)

; This function expects fn to have arity 2.

  (let ((x (fix-intern-in-pkg-of-sym "X" sym))
        (y (fix-intern-in-pkg-of-sym "Y" sym)))
    `(implies (,fn ,x ,y)
              (,fn ,y ,x))))

(defun transitivity (fn sym)

; This function expects fn to have arity 2.

  (let ((x (fix-intern-in-pkg-of-sym "X" sym))
        (y (fix-intern-in-pkg-of-sym "Y" sym))
        (z (fix-intern-in-pkg-of-sym "Z" sym)))
    `(implies (and (,fn ,x ,y)
                   (,fn ,y ,z))
              (,fn ,x ,z))))

(defun equivalence-relation-condition (fn sym)

; This function expects fn to have arity 2.  We generate a formula that states
; that fn is Boolean, reflexive, symmetric, and transitive.

; There are at least two reasons we require equivalence relations to be
; Boolean.  One is to simplify assume-true-false.  When we assume (fn x y)
; true, we pair it with *ts-t* rather than its full type-set take away
; *ts-nil*.  The other is that from reflexivity and Boolean we get than fn is
; commutative and so can freely use (fn y x) for (fn x y).  If we did not have
; the Boolean condition we would have to be more careful about, say,
; commutative unification.

  `(and ,(boolean-fn fn sym)
        ,(reflexivity fn sym)
        ,(symmetry fn sym)
        ,(transitivity fn sym)))

(defun find-candidate-equivalence-relation (clauses)

; Clauses is a list of clauses.  We look for one of the form
; ((fn x x)) and if we find it, we return fn; else nil.  See
; chk-acceptable-equivalence-rule.

  (cond ((null clauses) nil)
        (t (let ((clause (car clauses)))
             (case-match clause
                         (((fn x x))
                          (declare (ignore x))
                          fn)
                         (& (find-candidate-equivalence-relation (cdr clauses))))))))

(defun collect-problematic-pre-equivalence-rule-names (lst)

; A problematic pre-equivalence rule about a soon-to-be-named
; equivalence relation equiv is one whose conclusion is (equiv lhs
; rhs), where lhs is not a variable or a quote.  Such a rule could be
; stored as a :REWRITE rule for lhs after equiv is known to be an
; equivalence relation; but before that, such a rule is stored to
; rewrite (equiv lhs rhs) to T.  Assuming lst is all the :REWRITE rules
; for equiv, we return the list of names of the problematic rules.

  (cond ((null lst) nil)
        ((and (eq (access rewrite-rule (car lst) :equiv) 'equal)
              (equal (access rewrite-rule (car lst) :rhs) *t*)
              (not (variablep (fargn (access rewrite-rule (car lst) :lhs) 1)))
              (not (quotep (fargn (access rewrite-rule (car lst) :lhs) 1))))
          (cons (access rewrite-rule (car lst) :rune)
                (collect-problematic-pre-equivalence-rule-names (cdr lst))))
        (t (collect-problematic-pre-equivalence-rule-names (cdr lst)))))

(defun chk-acceptable-equivalence-rule (name term ctx wrld state)

; Term supposedly states that fn is boolean, reflexive, symmetric, and
; transitive.  To check that, we generate our canonical statement of
; those four properties and then check that term subsumes it.  We
; clausify both statements with shallow-clausify, which tears apart
; the IMPLIES and AND structure of the terms without messing up the
; IFs.

; The hard part is finding out the candidate fn.  Consider the clausification
; of an acceptable term.  The clauses are shown below (ignoring choice of clause order,
; literal order and variable names):

; ((booleanp (fn x y)))
; ((fn x x))
; ((not (fn x y)) (fn y x))
; ((not (fn x z))
;  (not (fn z y))
;  (fn x y))

; So to find fn we will look for the reflexive clause.

  (let* ((act-clauses (shallow-clausify term))
         (fn (find-candidate-equivalence-relation act-clauses)))
    (cond
     ((null fn)
      (er soft ctx
          "~x0 is an unacceptable :EQUIVALENCE lemma.  Such a lemma ~
           must state that a given 2-place function symbol is ~
           Boolean, reflexive, symmetric, and transitive.  We cannot ~
           find the statement of reflexivity, which is the one we key ~
           on to identify the name of the alleged equivalence ~
           relation.  Perhaps you have forgotten to include it.  More ~
           likely, perhaps your relation takes more than two ~
           arguments.  We do not support n-ary equivalence relations, ~
           for n>2.  Sorry."
          name))
     (t (er-let*
         ((eqv-cond (translate (equivalence-relation-condition fn name)
                               t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)

         (let ((eqv-clauses (shallow-clausify eqv-cond)))

; In the first test below we open-code a call of equivalence-relationp,
; avoiding special treatment for iff since we want (defequiv iff) to succeed
; during initialization.

           (cond
            ((or (eq fn 'equal)
                 (and (not (flambdap fn))
                      (getpropc fn 'coarsenings nil wrld)))
             (er soft ctx
                 "~x0 is already known to be an equivalence relation."
                 fn))
            (t
             (let ((subsumes
                    (clause-set-subsumes *init-subsumes-count* act-clauses
                                         eqv-clauses)))
               (cond
                ((eq subsumes t)
                 (cond
                  ((warning-disabled-p "Equiv") ; optimization
                   (value nil))
                  (t
                   (let ((lst
                          (scrunch-eq
                           (collect-problematic-pre-equivalence-rule-names
                            (getpropc fn 'lemmas nil wrld)))))
                     (cond
                      (lst
                       (pprogn
                        (warning$ ctx ("Equiv")
                                  "Any lemma about ~p0, proved before ~x1 is ~
                                   marked as an equivalence relation, is ~
                                   stored so as to rewrite ~p0 to T.  After ~
                                   ~x1 is known to be an equivalence ~
                                   relation, such a rule would rewrite the ~
                                   left-hand side to the right-hand side, ~
                                   preserving ~x1.  You have previously ~
                                   proved ~n2 possibly problematic ~
                                   rule~#3~[~/s~] about ~x1, namely ~&3.  ~
                                   After ~x1 is marked as an equivalence ~
                                   relation you should reconsider ~
                                   ~#3~[this~/each~] problematic rule.  If ~
                                   the rule is merely in support of ~
                                   establishing that ~x1 is an equivalence ~
                                   relation, it may be appropriate to disable ~
                                   it permanently hereafter.  If the rule is ~
                                   now intended to rewrite left to right, you ~
                                   must prove the lemma again after ~x1 is ~
                                   known to be an equivalence relation."
                                  (fcons-term fn '(x y))
                                  fn
                                  (length lst)
                                  (strip-cadrs lst))
                        (value nil)))
                      (t (value nil)))))))
                (t (er soft ctx
                       (if subsumes ; (eq subsumes '?)

; Perhaps the user could come up with a case that puts us here, but that's
; pretty hard to imagine!  So we use *init-subsumes-count* in the call of
; clause-set-subsumes above, so that we can complain if we get to this case.

                           "This low-level implementation error is a complete ~
                            surprise, as the subsumption check returned '? ~
                            for the :EQUIVALENCE lemma ~x0 for function ~
                            symbol ~x1.  This failure occurred when it was ~
                            checked that the equivalence-relation formula ~
                            subsumes the following canonical form: ~X23.  ~
                            Please contact the ACL2 implementors."
                         "~x0 is an unacceptable :EQUIVALENCE lemma for the ~
                          function symbol ~x1.  To be acceptable the formula ~
                          being proved must state that ~x1 is Boolean, ~
                          reflexive, symmetric, and transitive.  This is ~
                          checked by verifying that the formula subsumes the ~
                          following canonical form:  ~x2.  It does not.")
                       name
                       fn
                       (prettyify-clause-set eqv-clauses nil wrld)
                       nil))))))))))))

(defun add-equivalence-rule (rune nume term ens wrld)

; Term states that some function symbol fn is an equivalence relation.
; We recover from term the fn in question and add a 'coarsenings
; property for fn, stating that it is a coarsening of itself.  This
; marks it as an equivalence relation.  We also add it to the
; coarsenings of 'equal, which is the only other equivalence relation
; that we know is a refinement of this new one.  The coarsenings of
; 'equal is thus the list of all known equivalence relations.  The car of
; the 'coarsenings property for an equivalence relation fn is always
; eq to fn itself.  However, subsequent relations are listed in
; arbitrary order.

; If fn is not "obviously" Boolean in the sense that type-set reports
; that it is Boolean, we store a type-prescription rule for it.  This is
; usually unnecessary when fn is defined.  But on the off chance that its
; Boolean nature was missed by DEFUN or -- more likely -- when fn is a
; constrained function that is undefined in this world, we often need
; this fact.

; We also add a 'congruences property for fn.  See the essay on
; equivalence, refinements, and congruence-based rewriting.
; The property that we add states that the equality of two fn expressions
; is maintained by maintaining fn in both arguments.
; That is
;  (implies (fn x1 x2) (equal (fn x1 y) (fn x2 y)))
; and
;  (implies (fn y1 y2) (equal (fn x y1) (fn x y2))).
; We prove this below.

; Suppose fn is an arbitrary equivalence relation.

;  (encapsulate (((fn * *) => *))
;   (local (defun fn (x y) (equal x y)))
;   (defequiv fn))

; We pick out from its properties just three that we care about, its
; Boolean nature, symmetry, and transitivity.  We don't care that it
; is reflexive and the proofs below go through if you constrain fn
; just to have the three properties below.  We made fn an equivalence
; relation simply so we could conclude with some :congruence lemmas
; about fn -- an act which causes an error if fn is not an equivalence
; relation.  But the theorems proved about fn are true of any relation
; with the three properties below.

;  (defthm fn-boolean (booleanp (fn x y))
;   :rule-classes :type-prescription
;   :hints (("Goal" :use fn-is-an-equivalence)))
;
;  (defthm fn-symm (implies (fn x y) (equal (fn y x) t))
;   :hints (("Goal" :use fn-is-an-equivalence)))
;
;  (defthm fn-trans (implies (and (fn x y) (fn y z)) (equal (fn x z) t))
;   :hints (("Goal" :use fn-is-an-equivalence)))

; So now we observe the first of our two congruence properties: to
; maintain identity in fn expressions it is sufficient to maintain
; "fn-ity" in the first argument position.

;  (defthm fn-congruence1
;   (implies (fn x1 x2)
;            (equal (fn x1 y) (fn x2 y)))
;   :rule-classes :congruence
;   :hints (("Goal" :use (:instance
;                         (:theorem
;                          (implies (and (booleanp p)
;                                        (booleanp q))
;                                   (equal (equal p q) (iff p q))))
;                         (p (fn x1 y))
;                         (q (fn x2 y))))
;           ("Subgoal 2.1" :use ((:instance fn-symm (x x1) (y x2)))
;                          :in-theory (disable fn-symm))))

; And, to maintain identity in fn expressions it suffices to maintain
; "fn-ity" in the second argument position.

;  (defthm fn-congruence2
;   (implies (fn y1 y2)
;            (equal (fn x y1) (fn x y2)))
;   :rule-classes :congruence
;   :hints (("Goal" :use (:instance
;                         (:theorem
;                          (implies (and (booleanp p)
;                                        (booleanp q))
;                                   (equal (equal p q) (iff p q))))
;                         (p (fn x y1))
;                         (q (fn x y2))))
;           ("Subgoal 2.1" :use ((:instance fn-symm (x y1) (y y2)))
;                          :in-theory (disable fn-symm))))

; We do not store with the equivalence relation the name of the event
; that established that it is an equivalence relation.  That means we
; can't report it in our dependencies or disable it.

  (let* ((act-clauses (shallow-clausify term))
         (fn (find-candidate-equivalence-relation act-clauses)))
    (putprop
     fn
     'coarsenings
     (list fn)
     (putprop 'equal
              'coarsenings
              (append (getpropc 'equal 'coarsenings nil wrld)
                      (list fn))
              (putprop fn
                       'congruences
                       (cons (list 'equal
                                   (list (make congruence-rule
                                               :rune rune
                                               :nume nume
                                               :equiv fn))
                                   (list (make congruence-rule
                                               :rune rune
                                               :nume nume
                                               :equiv fn)))
                             (getpropc fn 'congruences nil wrld))
                       (cond
                        ((mv-let
                          (ts ttree)
                          (type-set (fcons-term* fn 'x 'y) nil nil nil ens wrld
                                    nil nil nil)
                          (declare (ignore ttree))
                          (ts-subsetp ts *ts-boolean*))
                         wrld)
                        (t
                         (add-type-prescription-rule
                          rune nume
                          (fcons-term* fn 'x 'y)
                          (fcons-term* 'booleanp
                                       (fcons-term* fn 'x 'y))
                          nil ; backchain-limit-lst
                          ens wrld
                          t))))))))

;---------------------------------------------------------------------------
; Section:  :REFINEMENT Rules

(defun chk-acceptable-refinement-rule (name term ctx wrld state)
  (let ((str "~x0 does not have the form of a :REFINEMENT rule.  See :DOC refinement."))
    (case-match term
                (('implies (equiv1 x y) (equiv2 x y))
                 (cond
                  ((and (equivalence-relationp equiv1 wrld)
                        (equivalence-relationp equiv2 wrld)
                        (variablep x)
                        (variablep y)
                        (not (eq x y)))
                   (cond
                    ((refinementp equiv1 equiv2 wrld)
                     (er soft ctx
                         "~x0 is already known to be a refinement of ~
                          ~x1.  See :DOC refinement."
                         equiv1 equiv2))
                    (t (value nil))))
                  (t (er soft ctx str name))))
                (& (er soft ctx str name)))))

; As noted in the essay on equivalence, refinements, and
; congruence-based rewriting, we maintain our refinements database
; via the 'coarsenings property, for efficiency reasons explained in
; the essay.  Thus, if equiv1 is a refinement of equiv2 then equiv2 is
; a coarsening of equiv1.  We therefore wish to add equiv2 to the
; coarsening property of equiv1.  However, as noted in the essay, the
; coarsening properties are kept closed under transitivity.  So we need
; a transitive closure operation.

; Rather that try to implement this closure operation directly on the
; property-list world, where we would repeatedly extend the 'coarsenings
; properties of the affected equivs, we have decided on a more modular and
; elegant approach.  We will simply collect all the coarsening properties
; into an alist, close that alist under the appropriate operation, and then
; go put the new coarsenings into the property list world.

; We start with the trivial operations of collecting and then
; redistributing all the coarsenings.

(defun collect-coarsenings (wrld)

; Return an alist that pairs each equivalence relation in wrld with
; its current coarsenings.

  (let ((all-equivs (getpropc 'equal 'coarsenings nil wrld)))
    (pairlis$ all-equivs
              (getprop-x-lst all-equivs 'coarsenings wrld))))

(defun putprop-coarsenings (alist wrld)

; Alist pairs equiv relations with their new 'coarsenings property.
; Put each property, provided it is different from its current value
; in wrld.

  (cond ((null alist) wrld)
        ((equal (getpropc (caar alist) 'coarsenings nil wrld)
                (cdar alist))
         (putprop-coarsenings (cdr alist) wrld))
        (t (putprop (caar alist) 'coarsenings (cdar alist)
                    (putprop-coarsenings (cdr alist) wrld)))))

; We now develop the world's least efficient transitive closure
; algorithm.  Let alist be an alist pairing symbols to sets of
; symbols.  By ``the value of a symbol'' in this context we mean the
; value assigned by the alist.  We close the value sets under the
; operation of unioning into the set the value of any symbol already
; in the set.  This operation eventually terminates since there are
; only a finite number of symbols involved.

; We do this in a very inefficient way.  We literally just extend
; each value set by unioning into it the appropriate other sets and
; iterate that operation until there are no changes.  If we ever have
; to operate with many equivalence relations enjoying many refinement
; relationships, we'll have to look at this code again.

(defun union-values (lst alist)

; We form the union of the values of the members of lst under alist.

  (cond ((null lst) nil)
        (t (union-eq (cdr (assoc-eq (car lst) alist))
                     (union-values (cdr lst) alist)))))

(defun extend-value-set (lst alist)

; We union into lst the value under alist of each element of lst.  In
; an effort to preserve order we implement this in a slightly bizarre
; style.  This concern about order is three-fold.  First, it lets us
; code the termination check with an equality rather than a
; set-equality.  Second, it ensures maintenance of the invariant that
; the car of the coarsenings property for an equiv is the equiv
; itself, e.g., see refinementp.  Third, it means that 'coarsenings
; that don't get extended don't get changed and so don't get written
; back to the world.

  (append lst (set-difference-eq (union-values lst alist) lst)))

(defun extend-each-value-set (alist1 alist2)

; we visit each value set in alist1 and extend it with the
; values specified by alist2.

  (cond ((null alist1) nil)
        (t (cons (cons (caar alist1)
                       (extend-value-set (cdar alist1) alist2))
                 (extend-each-value-set (cdr alist1) alist2)))))

(defun close-value-sets (alist)

; We extend each value set in alist, under alist, until alist doesn't
; change.  Because we have taken care to preserve the order of things
; in extend-value-set we know that a value set doesn't change unless
; it has a new element.  Thus, we can use equal rather than set-equal
; to check for our termination condition.  But the real reason we care
; about order is so that the 'congruences properties eventually
; restored are usually unchanged.

  (let ((new-alist (extend-each-value-set alist alist)))
    (cond ((equal new-alist alist) alist)
          (t (close-value-sets new-alist)))))

(defun add-refinement-rule (name nume term wrld)
  (declare (ignore name nume))
  (let ((equiv1 (ffn-symb (fargn term 1)))
        (equiv2 (ffn-symb (fargn term 2))))

; We collect all the 'coarsenings properties into an alist, add equiv2
; to the end of the pot for equiv1, close that as discussed above, and
; then put the resulting 'coarsenings properties back into the world.

    (putprop-coarsenings
     (close-value-sets
      (put-assoc-eq equiv1
                    (append (getpropc equiv1 'coarsenings nil wrld)
                            (list equiv2))
                    (collect-coarsenings wrld)))
     wrld)))

;---------------------------------------------------------------------------
; Section:  :CONGRUENCE Rules

(defun corresponding-args-eq-except (args1 args2 xk yk)

; Suppose args1 and args2 are two true lists of equal length, args1
; contains distinct symbols, xk and yk are symbols and xk is an
; element of args1.  Then we determine whether args2 is equal to args1
; except at xk where args2 contains yk.

  (cond ((null args1) t)
        ((eq (car args1) xk)
         (and (eq (car args2) yk)
              (corresponding-args-eq-except (cdr args1) (cdr args2) xk yk)))
        (t (and (eq (car args1) (car args2))
                (corresponding-args-eq-except (cdr args1) (cdr args2) xk yk)))))

(mutual-recursion

; The two functions in this nest accumulate into seen the variables occurring
; free in the first argument, and accumulate into dups those occurring at least
; twice in term (and, more precisely, those occurring at least once in the
; first argument that already occur in seen).

(defun duplicate-vars-1 (term seen dups)
  (cond ((variablep term)
         (cond ((member-eq term dups)
                (mv seen dups))
               ((member-eq term seen)
                (mv seen (cons term dups)))
               (t
                (mv (cons term seen) dups))))
        ((fquotep term)
         (mv seen dups))
        (t (duplicate-vars-1-lst (fargs term) seen dups))))

(defun duplicate-vars-1-lst (lst seen dups)
  (cond ((endp lst) (mv seen dups))
        (t (mv-let (seen dups)
                   (duplicate-vars-1 (car lst) seen dups)
                   (duplicate-vars-1-lst (cdr lst) seen dups)))))
)

(defun duplicate-vars (term)
  (mv-let (seen dups)
          (duplicate-vars-1 term nil nil)
          (declare (ignore seen))
          dups))

(mutual-recursion

(defun replace-duplicate-vars-with-anonymous-var-1 (term dup-vars)
  (cond ((variablep term) (cond ((member-eq term dup-vars)
                                 term)
                                (t *anonymous-var*)))
        ((fquotep term) term)
        (t (cons-term (ffn-symb term)
                      (replace-duplicate-vars-with-anonymous-var-1-lst
                       (fargs term) dup-vars)))))

(defun replace-duplicate-vars-with-anonymous-var-1-lst (lst dup-vars)
  (cond ((endp lst) nil)
        (t (cons (replace-duplicate-vars-with-anonymous-var-1
                  (car lst) dup-vars)
                 (replace-duplicate-vars-with-anonymous-var-1-lst
                  (cdr lst) dup-vars)))))
)

(defun replace-duplicate-vars-with-anonymous-var (term)
  (replace-duplicate-vars-with-anonymous-var-1 term (duplicate-vars term)))

(defun split-at-position (posn lst acc)

; We pop posn - 1 elements off lst, accumulating them into acc and returning
; the resulting extension of acc together with what remains of lst.

  (cond ((eql posn 1)
         (mv acc lst))
        (t (split-at-position (1- posn) (cdr lst) (cons (car lst) acc)))))

(defun make-pequiv-pattern (term addr)

; Address is the address of a variable occurrence in term.  We return the
; corresponding pattern.  See the Essay on Patterned Congruences and
; Equivalences.

  (cond ((endp addr)
         (assert$ (variablep term)
                  term))
        (t (assert$ (and (nvariablep term)
                         (not (fquotep term))
                         (not (flambda-applicationp term)))
                    (mv-let (pre-rev next/post)
                            (split-at-position (car addr) (fargs term) nil)
                            (make pequiv-pattern
                                  :fn (ffn-symb term)
                                  :posn (car addr)
                                  :pre-rev pre-rev
                                  :post (cdr next/post)
                                  :next
                                  (make-pequiv-pattern (car next/post)
                                                       (cdr addr))))))))

(defun make-pequiv (term addr nume equiv rune)
  (make pequiv
        :pattern (make-pequiv-pattern
                  (replace-duplicate-vars-with-anonymous-var term)
                  addr)
        :unify-subst nil
        :congruence-rule (make congruence-rule
                               :rune rune
                               :nume nume
                               :equiv equiv)))

(mutual-recursion

(defun var-address (var term acc)

; Var is a variable and term is a term.  This function returns nil if var does
; not occur in term, returns t if var occurs more than once in term, and
; otherwise returns the one-based address of the unique occurrence of var in
; term (with the reverse of the accumulator appended to the front of that
; address).  A return value of nil is thus ambiguous if term is a variable.

  (declare (xargs :guard (and (symbolp var)
                              (pseudo-termp term)
                              (true-listp acc))))
  (cond ((eq var term)
         (reverse acc))
        ((variablep term) nil)
        ((fquotep term) nil)
        (t (var-address-lst var (fargs term) 1 acc))))

(defun var-address-lst (var lst position acc)
  (declare (xargs :guard (and (symbolp var)
                              (pseudo-term-listp lst)
                              (natp position)
                              (true-listp acc))))
  (cond ((endp lst) nil)
        (t (let ((addr1 (var-address var (car lst) (cons position acc)))
                 (addr2 (var-address-lst var (cdr lst) (1+ position) acc)))
             (cond ((or (and addr1 addr2)
                        (eq addr1 t)
                        (eq addr2 t))
                    t)
                   (t (or addr1 addr2)))))))
)

(defun interpret-term-as-congruence-rule (name term wrld)

; This function recognizes terms that are :CONGRUENCE lemmas.  We return two
; results.  The first result is nil when the term is not a valid :CONGRUENCE
; lemma.  If the term is a congruence lemma, the second result is a structure
; (fn equiv1 addr equiv2 . extra).  If the term represents a classic congruence
; rule, then extra is nil, addr is a positive integer k, and this structure
; states that ``equiv2 is preserved by equiv1 in the kth argument of fn.''
; Otherwise the term represents a patterned congruence rule, which is thus
; either shallow or deep, indicated by whether the first result is :SHALLOW or
; :DEEP, respectively.  In that case, extra is the lhs of the rule, and addr is
; the address of the occurrence of the rule's variable in lhs.  Finally, if the
; term is not a :CONGRUENCE rule, the second is a tilde-@ message explaining
; why.  See the essay on equivalence, refinements, and congruence-based
; rewriting for details.

; Classic :CONGRUENCE lemmas are of the form

; (implies (equiv1 xk yk)
;          (equiv2 (fn x1 ... xk ... xn) (fn x1 ... yk ... xn)))

; where fn is a function symbol, all the xi and yk are distinct variables and
; equiv1 and the equiv2 are equivalence relations.  Such a lemma is read as
; ``equiv2 is preserved by equiv1 in the kth argument of fn.''  For a
; discussion of patterned :CONGRUENCE lemmas, see the Essay on Patterned
; Congruences and Equivalences.

; We do not actually cause an error because this function is sometimes called
; when STATE is unavailable.  We combine the recognition of the :CONGRUENCE
; lemma with the construction of the structure describing it because the two
; are so intermingled that it seemed dubious to separate them into two
; functions.

  (let ((pairs (unprettyify (remove-guard-holders term wrld)))
        (hyp-msg   "~x0 is an unacceptable :CONGRUENCE rule.  The ~
                    single hypothesis of a :CONGRUENCE rule must be a ~
                    term of the form (equiv x y), where equiv has ~
                    been proved to be an equivalence relation and x ~
                    and y are distinct variable symbols.  The ~
                    hypothesis of ~x0, ~x1, is not of this form.")
        (concl-msg "~x0 is an unacceptable :CONGRUENCE rule because its ~
                    conclusion does not have the expected form.  See :DOC ~
                    congruence.")
        (failure-msg "~x0 is an unacceptable :CONGRUENCE rule because ~@1.  ~
                      See :DOC congruence."))
    (cond
     ((and (int= (length pairs) 1)
           (int= (length (caar pairs)) 1))
      (let ((hyp (caaar pairs))
            (concl

; With the advent of patterned congruences, we put the conclusion into
; quote-normal form, both to facilitate matching when the rule is subsequently
; applied and to make the test robust below where we use subst-var-lst.

             (quote-normal-form (cdar pairs))))
        (case-match
         hyp
         ((equiv1 xk yk)
          (cond
           ((and (variablep xk)
                 (variablep yk)
                 (equivalence-relationp equiv1 wrld))
            (case-match
             concl
             ((equiv2 (fn . args1) (fn . args2))
              (cond
               ((or (not (equivalence-relationp equiv2 wrld))
                    (not (symbolp fn))
                    (eq fn 'quote) ; rule out quotep for equiv2 args
                    (eq fn

; Calls of IF are handled specially in geneqv-lst, so that the first argument
; is treated propositionally and the other arguments inherit the governing
; congruence.

                        'if))
                (mv nil (msg concl-msg name)))
               ((and (all-variablep args1)
                     (no-duplicatesp-eq args1)
                     (member-eq xk args1)

; The next conjunct is critical, but was missing from Versions  6.3 and 1.9,
; hence likely in all versions between these and perhaps even before 1.9.
; Without it, one can prove nil as follows.

;   (defun e (x y)
;     (or (equal x y)
;         (and (booleanp x) (booleanp y))))
;
;   (defequiv e)
;
;   (defun h (x y)
;     (if (booleanp x)
;         (booleanp y)
;       (equal (car x) y)))
;
;   ; The following is a bogus sort of expansion of:
;   ; (defcong e equal (h x y) 2)
;
;   (defthm e-implies-equal-h-2-bad
;     (implies (e y1 y2)
;              (equal (h y2 y1)
;                     (h y2 y2)))
;     :rule-classes :congruence)
;
;   (defun true ()
;     t)
;
;   (defun false ()
;     nil)
;
;   (defthm e-true-false
;     (e (true) (false)))
;
;   (defthm fact-1
;     (h (cons t x) (true))
;     :rule-classes nil)
;
;   (defthm fact-2
;     (not (h (cons t x) (false)))
;     :rule-classes nil)
;
;   (in-theory (disable true (true) false (false)))
;
;   (defthm contradiction
;     nil
;     :hints (("Goal" :use (fact-1 fact-2)))
;     :rule-classes nil)

                     (not (member-eq yk args1))
                     (corresponding-args-eq-except args1 args2 xk yk))
                (mv :classic
                    (list* fn
                           equiv1
                           (1+ (- (length args1)
                                  (length (member-eq xk args1))))
                           equiv2
                           nil)))

; Otherwise our check is for a patterned congruence rule.

               ((or (ffnnamep-lst 'if args1)
                    (ffnnamep-lst 'implies args1)
                    (ffnnamep-lst 'equal args1)
                    (lambda-subtermp-lst args1))

; The restrictions above might be stronger than necessary.  But we have felt
; free to rely on them while developing support for patterned congruence rules.
; For example, rewrite-equal calls rewrite-args several times with arguments
; deep-pequiv-lst and shallow-pequiv-lst equal to nil, and this is safe because
; no pequivs encountered can involve the symbol EQUAL in the pattern.  Another
; example is in the body of the definition of rewrite for the case (eq
; (ffn-symb term) 'IMPLIES), where recursive calls of rewrite are passed the
; value nil for pequiv-info.

                (let ((bad-fns (append (and (ffnnamep-lst 'if args1)
                                            '(if))
                                       (and (ffnnamep-lst 'implies args1)
                                            '(implies))
                                       (and (ffnnamep-lst 'equal args1)
                                            '(equal))))
                      (bad-lambda-p (lambda-subtermp-lst args1)))
                  (mv nil
                      (msg failure-msg
                           name
                           (cond ((and bad-fns bad-lambda-p)
                                  (msg "the function symbol~#0~[ ~&0~/s ~&0~] ~
                                        and a lambda application occur in the ~
                                        conclusion of the rule"
                                       bad-fns))
                                 (bad-fns
                                  (msg "the function symbol~#0~[ ~&0 ~
                                        occurs~/s ~&0 occur~] in the ~
                                        conclusion of the rule"
                                       bad-fns))
                                 (t ; bad-lambda-p
                                  (msg "a lambda application occurs in the ~
                                        conclusion of the rule.")))))))
               ((dumb-occur-var-lst *anonymous-var* term)

; We introduce *anonymous-var*, which will be treated specially during
; matching, when creating a pequiv-pattern from term; so it would be a mistake
; to allow *anonymous-var* in term, which should not get that special
; treatment.  See the Essay on Patterned Congruences and Equivalences.

                (mv nil
                    (msg failure-msg
                         name
                         (msg "the variable ~x0, which is used in a special ~
                               way by the implementation, occurs in the rule"
                              *anonymous-var*))))
               (t
                (let ((addr1 (var-address xk (fargn concl 1) nil))
                      (addr2 (var-address yk (fargn concl 2) nil)))
                  (cond
                   ((or (null addr1) (null addr2))
                    (mv nil
                        (msg failure-msg
                             name
                             (cond
                              ((null addr1)
                               (msg "the variable ~x0 does not occur in ~x1"
                                    xk (fargn concl 1)))
                              (t
                               (msg "the variable ~x0 does not occur in ~x1"
                                    yk (fargn concl 2)))))))
                   ((or (eq addr1 t) (eq addr2 t))
                    (mv nil
                        (msg failure-msg
                             name
                             (cond
                              ((null addr1)
                               (msg "the variable ~x0 occurs more than once ~
                                     in ~x1"
                                    xk (fargn concl 1)))
                              (t
                               (msg "the variable ~x0 occurs more than once ~
                                     in ~x1"
                                    yk (fargn concl 2)))))))
                   ((not (equal addr1 addr2))
                    (mv nil
                        (msg failure-msg
                             name
                             (msg "the variables ~x0 and ~x1 occur at ~
                                   different positions in the first and ~
                                   second arguments, respectively, of ~x3 in ~
                                   the conclusion of the proposed rule"
                                  xk yk equiv2))))
                   ((not (equal args2 (subst-var-lst yk xk args1)))

; The test above is sufficient: at this point we know that xk occurs
; exactly once in args1, so if the equality is true, then the left and right
; sides of the concl are equal except at addr1 (= addr2).

                    (mv nil
                        (msg failure-msg
                             name
                             (msg "the second argument of its conclusion is ~
                                   not equal to the result of substituting ~
                                   ~x0 for ~x1 in its first argument"
                                  yk xk))))
                   (t
                    (mv (if (member-eq xk args1)
                            :shallow
                          :deep)
                        (list* fn equiv1 addr1 equiv2
                               (fargn concl 1) ; (fn . args1)
                               ))))))))
             (& (mv nil (msg concl-msg name)))))
           (t (mv nil (msg hyp-msg name hyp)))))
         (& (mv nil (msg hyp-msg name hyp))))))
     (t (mv nil (msg failure-msg
                     name
                     "the supplied formula does not generate a single ~
                      conjunct of the form (implies (equiv1 xk yk) (equiv2 ~
                      (fn ...) (fn ...))), where equiv1 and equiv2 are ~
                      equivalence relations"))))))

(defun some-congruence-rule-same (equiv rules)

; Return the first element of rules which has equiv as its :equiv field.

  (cond ((null rules) nil)
        ((eq equiv (access congruence-rule (car rules) :equiv))
         (car rules))
        (t (some-congruence-rule-same equiv (cdr rules)))))

(defun some-congruence-rule-has-refinement (equiv rules wrld)

; Return the first element of rules which has equiv as a refinement of its
; :equiv field.

  (cond ((null rules) nil)
        ((refinementp equiv (access congruence-rule (car rules) :equiv) wrld)
         (car rules))
        (t (some-congruence-rule-has-refinement equiv (cdr rules) wrld))))

(defun chk-acceptable-congruence-rule (name term ctx wrld state)

; We check that term is a legal congruence rule.

; If the rule is a classic (not patterned) congruence rule, then we print a
; warning message if we already know that equiv2 is preserved by equiv1 in the
; kth slot of fn.  We are not so much watching out for the possibility that
; equiv1 literally occurs in the list in the kth slot -- though that could
; happen and the old rule be disabled so the user is unaware that it exists.
; We are more concerned, because of efficiency when applying congruences, about
; the possibility that equiv1 is some refinement of a relation already in the
; kth slot.

  (mv-let
   (flg x)
   (interpret-term-as-congruence-rule name term wrld)
   (cond
    ((not flg) (er soft ctx "~@0" x))
    (t
     (let ((fn (car x))
           (equiv1 (cadr x))    ; inner equiv
           (addr (caddr x))     ; a number in the :classic case
           (equiv2 (cadddr x))) ; outer equiv
       (pprogn
        (cond ((eq equiv1 'equal)
               (warning$ ctx "Equiv"
                         "The :CONGRUENCE rule ~x0 will have no effect on ~
                          proofs because ACL2 already knows that ~x1 refines ~
                          every equivalence relation."
                         name 'equal))
              ((and (eq equiv2 'iff)
                    (mv-let
                     (ts ttree)
                     (type-set (cons-term fn (formals fn wrld))
                               nil nil nil (ens state) wrld
                               nil nil nil)
                     (declare (ignore ttree))
                     (ts-subsetp ts *ts-boolean*)))
               (warning$ ctx "Equiv"
                         "The :CONGRUENCE rule ~x0 can be strengthened by ~
                          replacing the outer equivalence relation, ~x1, by ~
                          ~x2.  See :DOC congruence, in particular (near the ~
                          end) the Remark on Replacing IFF by EQUAL."
                         name 'iff 'equal))
              (t state))

; The warnings below were originally errors, but as Jared Davis pointed out
; using essentially the following example, it was easy to change order to avoid
; the errors.  So we create warnings instead.

;  (defun my-equiv (x y) (equal x y))
;  (defun my-equiv2 (x y) (equal x y))
;  (defequiv my-equiv)
;  (defequiv my-equiv2)
;  (defrefinement my-equiv my-equiv2)

;   ; Then this sequence formerly resulted in an error, but not if their order
;   ; was switched or the defrefinement above was moved to after both defcong
;   ; forms.  Now, we get a warning this way but not if we switch their order
;   ; or defer the defrefinement.  We can live with that, since we suspect that
;   ; it could slow down ACL2 to do the more thorough checks.

;  (defcong my-equiv2 equal (consp x) 1)
;  (defcong my-equiv equal (consp x) 1)

        (cond
         ((eq flg :classic)
          (let* ((k addr)
                 (temp (nth k
                            (assoc-eq equiv2
                                      (getpropc fn 'congruences nil wrld)))))
            (cond
             ((some-congruence-rule-same equiv1 temp)
              (warning$ ctx "Equiv"
                        "The previously added :CONGRUENCE lemma, ~x0, ~
                         establishes that ~x1 preserves ~x2 in the ~n3 slot ~
                         of ~x4.  Thus, ~x5 is unnecessary."
                        (base-symbol
                         (access congruence-rule
                                 (some-congruence-rule-same equiv1 temp)
                                 :rune))
                        equiv1 equiv2 (cons k 'th) fn name))
             ((some-congruence-rule-has-refinement equiv1 temp wrld)
              (warning$ ctx "Equiv"
                        "The previously added :CONGRUENCE lemma, ~x0, ~
                         establishes that ~x1 preserves ~x2 in the ~n3 slot ~
                         of ~x4.  But we know that ~x5 is a refinement of ~
                         ~x1.  Thus, ~x6 is unnecessary."
                        (base-symbol
                         (access congruence-rule
                                 (some-congruence-rule-has-refinement equiv1 temp
                                                                      wrld)
                                 :rune))
                        (access congruence-rule
                                (some-congruence-rule-has-refinement equiv1 temp wrld)
                                :equiv)
                        equiv2 (cons k 'th) fn equiv1 name))
             (t state))))
         (t (observation ctx
                         "The rule ~x0 is a ~s1 patterned congruence rule.  ~
                          See :DOC patterned-congruence."
                         name
                         (if (eq flg :shallow)
                             "shallow"
                           (assert$ (eq flg :deep)
                                    "deep")))))
        (value nil)))))))

(defun add-congruence-rule-to-congruence (rule k congruence)

; Congruence is an element of the 'congruence property of some n-ary
; function fn.  As such, it is of the form (equiv geneqv1 ... geneqvk
; ... geneqvn), where equiv is some equivalence relation and each of
; the geneqvi is a list of congruence-rule records.  We add rule to
; geneqvk.

  (update-nth k (cons rule (nth k congruence)) congruence))

(defun cons-assoc-eq-rec (key val alist)

; This function is analogous to put-assoc-eq, but instead of replacing the
; value of key in alist, that value -- which should be a true list -- is
; extended by consing val onto the front of it.

  (declare (xargs :guard (and (symbol-alistp alist)
                              (true-list-listp alist)
                              (assoc-eq key alist))))
  (cond ((endp alist)
         (er hard 'cons-assoc-eq-rec
             "Implementation error: Reached the end of the alist for key ~x0!"
             key))
        ((eq key (caar alist))
         (acons key
                (cons val (cdar alist))
                (cdr alist)))
        (t (cons (car alist)
                 (cons-assoc-eq-rec key val (cdr alist))))))

(defun cons-assoc-eq (key val alist)

; This function is analogous to put-assoc-eq, but instead of replacing the
; value of key in alist, that value -- which should be a true list -- is
; extended by consing val onto the front of the old value of key in alist.

; As an optimization, we handle specially the case that key is not already a
; key of alist.

  (declare (xargs :guard (and (symbol-alistp alist)
                              (true-list-listp alist))))
  (cond ((endp alist) (list (list key val)))
        ((assoc-eq key alist)
         (cons-assoc-eq-rec key val alist))
        (t (acons key (list val) alist))))

(defun add-congruence-rule (rune nume term wrld)

; See the Essay on Patterned Congruences and Equivalences.

  (mv-let
   (flg x)
   (interpret-term-as-congruence-rule (base-symbol rune) term wrld)
   (let ((fn (car x))
         (equiv1 (cadr x))   ; inner equiv
         (addr (caddr x))    ; a number when flg is :classic
         (equiv2 (cadddr x)) ; outer equiv
         (lhs (cddddr x)))
     (cond
      ((eq flg :classic)
       (let* ((k addr)
              (temp (assoc-eq equiv2
                              (getpropc fn 'congruences nil wrld)))
              (equiv2-congruence
               (or temp
                   (cons equiv2 (make-list-ac (arity fn wrld) nil nil))))
              (rst (if temp
                       (remove1-equal temp
                                      (getpropc fn 'congruences nil wrld))
                     (getpropc fn 'congruences nil wrld))))
         (putprop fn
                  'congruences
                  (cons (add-congruence-rule-to-congruence
                         (make congruence-rule
                               :rune rune
                               :nume nume
                               :equiv equiv1)
                         k
                         equiv2-congruence)
                        rst)
                  wrld)))
      ((null flg)

; This case is unexpected, given the check on :congruence rules in
; chk-acceptable-rules; see the comment there.

       (er hard! 'add-congruence-rule
           "Implementation error: ~x0 returned failure when attempting to ~
            apply ~x1.  Please contact the ACL2 implementors."
           'interpret-term-as-congruence-rule
           'add-congruence-rule))
      (t
       (assert$
        (and (member-eq flg '(:deep :shallow))
             (not (or (variablep lhs)
                      (fquotep lhs)
                      (lambda-applicationp lhs)))
             (consp addr))
        (let* ((pequiv (make-pequiv lhs addr nume equiv1 rune))
               (sym (if (eq flg :shallow)
                        fn
                      (let ((arg ; (nth (1- (car addr)) (fargs lhs))
                             (nth (car addr) lhs)))
                        (assert$
                         (not (or (variablep arg)
                                  (fquotep arg)
                                  (lambda-applicationp arg)))
                         (ffn-symb arg)))))
               (prop (getpropc sym 'pequivs nil wrld))
               (new-prop
                (let ((prop (or prop
                                *empty-pequivs-property*)))
                  (cond ((eq flg :shallow)
                         (change pequivs-property prop
                                 :shallow
                                 (cons-assoc-eq equiv2
                                                pequiv
                                                (pequivs-property-field
                                                 prop :shallow))))
                        (t ; (eq flg :deep)
                         (let ((new (cons-assoc-eq equiv2
                                                   pequiv
                                                   (pequivs-property-field
                                                    prop :deep))))
                           (cond ((and (eq fn sym)

; Normally we will set :deep-pequiv-p for fn based on parent prop; see below.
; However, if fn and sym are the same then we do that here instead.  Except,
; there is no need to set the :deep-pequiv-p field if it is already set.

                                       (not (pequivs-property-field
                                             prop
                                             :deep-pequiv-p)))
                                  (change pequivs-property prop
                                          :deep new
                                          :deep-pequiv-p t))
                                 (t
                                  (change pequivs-property prop
                                          :deep new))))))))
               (parent-prop
                (and (eq flg :deep) ; optimization
                     (not (eq fn sym)) ; optimization
                     (getpropc fn 'pequivs nil wrld))))
          (putprop sym 'pequivs new-prop
                   (cond
                    ((or (eq fn sym) ; putprop above overrides putprop below
                         (eq flg :shallow))
                     wrld)
                    ((null parent-prop) ; and flg is :deep
                     (putprop fn 'pequivs
                              (make pequivs-property
                                    :shallow nil
                                    :deep nil
                                    :deep-pequiv-p t)
                              wrld))
                    ((pequivs-property-field parent-prop :deep-pequiv-p)
                     wrld)
                    (t
                     (putprop fn 'pequivs
                              (change pequivs-property parent-prop
                                      :deep-pequiv-p t)
                              wrld)))))))))))

;---------------------------------------------------------------------------
; Section:  :DEFINITION rules

(defun chk-destructure-definition (name term ctx wrld state)
  (mv-let (hyps equiv fn args body ttree)
          (destructure-definition term nil nil wrld nil)
          (declare (ignore hyps equiv args body ttree))
          (cond ((null fn)
                 (er soft ctx
                     "~x0 cannot be stored as a :DEFINITION rule ~
                      because the :COROLLARY formula, ~p1, is not of ~
                      the proper form.  See :DOC definition."
                     name (untranslate term t wrld)))
                (t (value nil)))))

(defun chk-acceptable-definition-install-body (fn hyps equiv args body
                                                  install-body
                                                  install-body-supplied-p
                                                  ctx state)

; This function should be called even during include-book, since we check for
; an equivalence relation that might not be a known equivalence relation during
; the first pass of certification or encapsulate.

  (let ((install-body (if install-body-supplied-p
                          install-body
                        :NORMALIZE))
        (er-preamble
         (msg "For a :DEFINITION rule with non-nil :INSTALL-BODY value~@0,"
              (if install-body-supplied-p
                  ""
                " (default :NORMALIZE)")))
        (install-body-msg
         (if install-body-supplied-p
             ""
           (msg "  Please add :INSTALL-BODY ~x0 to your :DEFINITION rule ~
                 class."
                nil))))
    (cond
     ((null install-body)
      (value nil))
     ((not (arglistp args))
      (er soft ctx
          "~@0 the arguments on the left-hand side of the rule must be a list ~
           of distinct variables, unlike ~x1.~@2  See :DOC definition."
          er-preamble
          args
          install-body-msg))
     ((not (equivalence-relationp equiv (w state)))
      (er soft ctx
          "~@0 the function symbol at the top of the conclusion must be an ~
           equivalence relation, unlike ~x1.~@2  See :DOC definition."
          er-preamble
          equiv
          install-body-msg))
     ((free-varsp-member-lst hyps args)
      (er soft ctx
          "~@0 the hypotheses must not contain free variables that are not ~
           among the variables on its left-hand side.  The ~#1~[variable ~&1 ~
           violates~/variables ~&1 violate~] this requirement.~@2  See :DOC ~
           definition."
          er-preamble
          (reverse (set-difference-eq (all-vars1-lst hyps nil) args))
          install-body-msg))
     ((free-varsp-member body args)
      (er soft ctx
          "~@0 the right-hand side of a :DEFINITION rule must not contain free ~
           variables that are not among the variables on its left-hand side.  ~
           The ~#1~[variable ~&1 violates~/variables ~&1 violate~] this ~
           requirement.~@2  See :DOC definition."
          er-preamble
          (reverse (set-difference-eq (all-vars body) args))
          install-body-msg))
     (t (pprogn (cond ((member-eq fn *definition-minimal-theory*)

; This restriction is to allow us to assume that calls of (body fn t wrld),
; which occur in several places in the source code, refer to the original
; normalized body of fn, which excuses us from tracking the corresponding rune.

                       (warning$ ctx "Definition"
                                 "The proposed :DEFINITION rule might not ~
                                  always be the one applied when expanding ~
                                  calls of ~x0 during proofs.  Instead, these ~
                                  calls and, more generally, calls of any ~
                                  function symbol that is in the list ~x1, ~
                                  will often be expanded using the original ~
                                  definition of the function symbol.  Add ~
                                  :INSTALL-BODY ~x2 to the proposed ~
                                  :DEFINITION rule class to avoid this ~
                                  warning."
                                 fn '*definition-minimal-theory* nil))
                      (t state))
                (value nil))))))

(defun chk-acceptable-definition-rule
  (name clique controller-alist install-body-tail term ctx ens wrld state)

; Term is a translated term that is the :COROLLARY of a :DEFINITION with the
; given :CLIQUE and :CONTROLLER-ALIST.  We know the clique and alist are well
; formed.  But to check that during rule class translation, we had to
; destructure term with chk-destructure-definition and it must have passed.
; The only things left to check are the various subsumption-type conditions on
; rewrite rules, as well as the :install-body argument, passed in as
; install-body-tail of the form (:install-body value ...) if :install-body was
; supplied by the user, and as nil otherwise.

  (mv-let
   (hyps equiv fn args body ttree)
   (destructure-definition term nil ens wrld nil)
   (cond
    ((eq fn 'hide)
     (er soft ctx
         "It is illegal to make a definition rule for ~x0, because of the ~
          special role of this function in the ACL2 rewriter."
         'hide))
    (t
     (let ((rule
            (make rewrite-rule
                  :rune *fake-rune-for-anonymous-enabled-rule*
                  :nume nil
                  :hyps (preprocess-hyps hyps wrld)
                  :equiv equiv
                  :lhs (mcons-term fn args)
                  :var-info (var-counts args body)
                  :rhs body
                  :subclass 'definition
                  :heuristic-info (cons clique controller-alist)
                  :backchain-limit-lst nil)))
       (er-progn (chk-rewrite-rule-warnings name
                                            nil ; match-free
                                            nil ; loop-stopper
                                            rule ctx ens wrld state)
                 (chk-acceptable-definition-install-body
                  fn hyps equiv args body
                  (cadr install-body-tail)
                  install-body-tail ctx state)
                 (value ttree)))))))

; add-definition-rule was defined in defuns.lisp in order to implement
; defuns-fn0.

;---------------------------------------------------------------------------
; Section:  :INDUCTION rules

(defun chk-acceptable-induction-rule (name term ctx wrld state)

; This function is really a no-op.  It exists simply for regularity.

  (declare (ignore name term ctx wrld))
  (value nil))

(defun add-induction-rule (rune nume pat-term cond-term scheme-term term wrld)
  (declare (ignore term))
  (let ((fn (ffn-symb pat-term)))
    (putprop fn 'induction-rules
             (cons (make induction-rule
                         :rune rune
                         :nume nume
                         :pattern pat-term
                         :condition cond-term
                         :scheme scheme-term)
                   (getpropc fn 'induction-rules nil wrld))
             wrld)))

;---------------------------------------------------------------------------
; Section:  :TYPE-SET-RECOGNIZER-TERM Rules

(defun chk-acceptable-type-set-inverter-rule (name ts term ctx ens wrld state)
  (let* ((vars (all-vars term)))
    (cond
     ((not (and (ffn-symb-p term 'equal)
                (equal vars '(X))
                (equal (all-vars (fargn term 1))
                       (all-vars (fargn term 2)))))
      (er soft ctx
          "The :COROLLARY of a :TYPE-SET-INVERTER rule must be of the form ~
           (equal old-expr new-expr), where new-expr and old-expr are each ~
           terms containing the single free variable X.  ~p0 is not of this ~
           form, so ~x1 is an illegal :TYPE-SET-INVERTER rule.  See :DOC ~
           type-set-inverter."
          (untranslate term t wrld)
          name))
     (t
      (mv-let
       (ts2 ttree)
       (cond ((null ts)
              (type-set-implied-by-term 'X nil (fargn term 2) ens wrld nil))
             (t (mv ts nil)))
       (cond
        ((not (and (integerp ts2)
                   (<= *min-type-set* ts2)
                   (<= ts2 *max-type-set*)))

; It is believed neither of the following errors will ever occur.  The hard
; error won't occur because type-set-implied-by-term always returns a type-set.
; The soft error won't occur because translate-rule-class-alist insists, when a
; :TYPE-SET is supplied, that the type-set be proper and causes this error
; there.

         (cond ((null ts)
                (mv t
                    (er hard ctx
                        "Type-set-implied-by-term returned ~x0 instead of a ~
                         type-set!"
                        ts2)
                    state))
               (t (er soft ctx
                      "The :TYPE-SET of a :TYPE-SET-INVERTER rule must be a ~
                       type-set, i.e., an integer n such that ~x0 <= n <= ~x1. ~
                       But ~x2 is not so ~x3 is an illegal :TYPE-SET-INVERTER ~
                       rule.  See :DOC type-set-inverter."
                      *min-type-set*
                      *max-type-set*
                      ts2 name))))
        (t
         (mv-let
          (required-old-expr ttree)
          (convert-type-set-to-term 'X ts2 ens wrld ttree)
          (cond
           ((not
             (tautologyp (fcons-term* 'iff (fargn term 2) required-old-expr)
                         wrld))
            (er soft ctx
                "The right-hand side of the :COROLLARY of a :TYPE-SET-INVERTER ~
                 rule with :TYPE-SET ~x0 must be propositionally equivalent to ~
                 ~p1 but you have specified ~p2.  Thus, ~x3 is an illegal ~
                 :TYPE-SET-INVERTER rule.  See :doc type-set-inverter."
                ts2
                (untranslate required-old-expr t wrld)
                (untranslate (fargn term 2) t wrld)
                name))
           (t (value ttree)))))))))))

(defun add-type-set-inverter-rule (rune nume ts term ens wrld)
  (mv-let (ts ttree)
          (cond ((null ts)
                 (type-set-implied-by-term
                  'X
                  nil
                  (fargn term 2)
                  ens wrld nil))
                (t (mv ts nil)))
          (declare (ignore ttree))
          (global-set 'type-set-inverter-rules
                      (cons (make type-set-inverter-rule
                                  :nume nume
                                  :rune rune
                                  :ts ts
                                  :terms (flatten-ands-in-lit (fargn term 1)))
                            (global-val 'type-set-inverter-rules wrld))
                      wrld)))

; --------------------------------------------------------------------------
; Section: :TAU-SYSTEM rules

; The code for adding :tau-system rules is in a prior file, namely
; history-management, where it is used in install-event as part of
; tau-auto-modep.

;---------------------------------------------------------------------------
; Section:  :CLAUSE-PROCESSOR Rules

(defun tilde-@-illegal-clause-processor-sig-msg (cl-proc stobjs-in stobjs-out)

; A clause-processor should have signature of the form
; (cl-proc cl) => cl-list
; or
; (cl-proc cl hint) => cl-list
; or
; (cl-proc cl hint st_1 ... st_k) => (erp cl-list st_i1 ... st_in)
; or
; (cl-proc cl hint st_1 ... st_k) => (erp cl-list st_i1 ... st_in d)

  (cond
   ((null (cdr stobjs-out)) ; first two signatures
    (cond ((car stobjs-out)
           (msg "~x0 returns a single argument but it is a stobj"
                cl-proc))
          ((or (equal stobjs-in '(nil))
               (equal stobjs-in '(nil nil)))
           nil)
          (t (msg "~x0 returns a single argument, but doesn't take exactly one ~
                   or two arguments, both not stobjs"
                  cl-proc))))
   ((and (null (car stobjs-in))
         (cdr stobjs-in)
         (null (cadr stobjs-in))
         (not (member-eq nil (cddr stobjs-in)))
         (null (car stobjs-out))
         (cdr stobjs-out)
         (null (cadr stobjs-out))
         (member-equal (member-eq nil (cddr stobjs-out))
                       '(nil (nil))))
    nil)
   (t
    (msg "both the arguments and results of ~x0 in this case are expected to ~
          contain stobjs in exactly all positions other than the first two ~
          and possibly the last"
         cl-proc))))

(defun destructure-clause-processor-rule (term)

; We destructure the translated term term in the form of a :clause-processor
; correctness theorem.  We return
; (mv flg fn cl alist rest-args ev call xflg)
; where
; flg:   :error, if term is not the right shape
;        t, if the clause processor function returns (mv erp clauses ...)
;           and is thus to be accessed with CLAUSES-RESULT
;        nil, if the clause processor returns a set of clauses.
; fn:    the clause processor function (presumably a function symbol)
; cl:    the first argument to fn (presumably a variable symbol denoting the
;        input clause)
; alist: the evaluator's alist (presumably a variable symbol)
; rest-args: the arguments of fn after the first (presumably a hint possibly
;        followed by a list of stobj names)
; ev:    the evaluator function (presumably a function symbol)
; call:  the actual call of fn
; flg:   a boolean indicating whether meta-extract-global-fact+ hyps were found
; We also may presume that all the variables above are distinct.

; This function does not check the presumptions above but
; chk-acceptable-clause-processor-rule does and causes an error if they are not
; true.

  (case-match term
    (('IMPLIES hyp
               (ev ('DISJOIN clause) alist))
     (mv-let
      (hyps meta-extract-flg)
      (remove-meta-extract-global-hyps
       (remove1-equal (fcons-term* 'pseudo-term-listp clause)
                      (remove1-equal (fcons-term* 'alistp alist)
                                     (flatten-ands-in-lit hyp)))
       ev)
      (case-match hyps
        (((ev ('CONJOIN-CLAUSES cl-result)
              &))
         (case-match cl-result
           (('CLAUSES-RESULT (cl-proc !clause . rest-args))
            (mv t cl-proc clause alist rest-args ev (cadr cl-result)
                meta-extract-flg))
           ((cl-proc !clause . rest-args)
            (mv nil cl-proc clause alist rest-args ev cl-result
                meta-extract-flg))
           (& (mv :error nil nil nil nil nil nil nil))))
        (& (mv :error nil nil nil nil nil nil nil)))))
    (& (mv :error nil nil nil nil nil nil nil))))

(defun chk-acceptable-clause-processor-rule (name term ctx wrld state)

; Note that term has been translated (as it comes from a translated rule
; class), but not for execution.

  (let ((str "No :CLAUSE-PROCESSOR rule can be generated from ~x0 ~
              because~|~%~p1~|~%does not have the necessary form:  ~@2.  See ~
              :DOC clause-processor."))
    (mv-let
     (clauses-result-call-p cl-proc clause alist rest-args ev cl-proc-call
                            meta-extract-flg)
     (destructure-clause-processor-rule term)
     (cond
      ((eq clauses-result-call-p :error)
       (er soft ctx str name (untranslate term t wrld)
           "it fails to satisfy basic syntactic criteria"))
      ((not (and (symbolp cl-proc)
                 (function-symbolp cl-proc wrld)))
       (er soft ctx str name (untranslate term t wrld)

; We may never see the following message, but it seems harmless to do this
; check.

           (msg "the symbol ~x0 is not a function symbol in the current world"
                cl-proc)))
      (t
       (mv-let
        (erp t-cl-proc-call bindings state)

; Here we catch the use of the wrong stobjs.  Other checking is done below.

        (translate1 cl-proc-call
                    :stobjs-out ; clause-processor call must be executable
                    '((:stobjs-out . :stobjs-out))
                    t ctx wrld state)
        (declare (ignore bindings))
        (cond
         (erp (er soft ctx str name (untranslate term t wrld)
                  (msg "the clause-processor call is not in a form suitable ~
                        for evaluation (as may be indicated by an error ~
                        message above)")))
         (t
          (assert$ ; If translation changes cl-proc-call, we want to know!
           (equal cl-proc-call t-cl-proc-call)
           (let* ((stobjs-in (stobjs-in cl-proc wrld))
                  (stobjs-out (stobjs-out cl-proc wrld)))
             (er-progn
              (cond ((if clauses-result-call-p ; expected: iff at least 2 args
                         (equal stobjs-out '(nil))
                       (not (equal stobjs-out '(nil))))
                     (er soft ctx str name (untranslate term t wrld)
                         (msg "~x0 returns ~#1~[only~/more than~] one value ~
                               and hence there should be ~#1~[no~/a~] call of ~
                               ~x2"
                              cl-proc
                              (if clauses-result-call-p 0 1)
                              'clauses-result)))
                    (t
                     (let ((msg (tilde-@-illegal-clause-processor-sig-msg
                                 cl-proc stobjs-in stobjs-out)))
                       (cond (msg (er soft ctx str name
                                      (untranslate term t wrld)
                                      msg))
                             (t (value nil))))))
              (let* ((user-hints-p (cdr stobjs-in))
                     (user-hints (cond (user-hints-p (car rest-args))
                                       (t nil)))
                     (stobjs-called (cond (user-hints-p (cdr rest-args))
                                          (t rest-args)))
                     (non-alist-vars
                      (if user-hints
                          (list* clause user-hints stobjs-called)
                        (list* clause stobjs-called)))
                     (vars (cons alist non-alist-vars))
                     (bad-vars (collect-non-legal-variableps vars)))
                (cond (bad-vars
                       (er soft ctx str name (untranslate term t wrld)
                           (msg "the clause-processor function must be ~
                                 applied to a list of distinct variable and ~
                                 stobj names, but ~&0 ~#0~[is~/are~] not"
                                (untranslate-lst bad-vars nil wrld))))
                      ((not (no-duplicatesp vars))
                       (cond ((no-duplicatesp non-alist-vars)
                              (er soft ctx str name (untranslate term t wrld)
                                  (msg "the proposed :clause-processor rule ~
                                        uses ~x0 as its alist variable, but ~
                                        this variable also occurs in the ~
                                        argument list of the clause-processor ~
                                        function, ~x1"
                                       alist
                                       cl-proc)))
                             (t
                              (er soft ctx str name (untranslate term t wrld)
                                  (msg "the clause-processor function must be ~
                                        applied to a list of distinct ~
                                        variable and stobj names, but the ~
                                        list ~x0 contains duplicates"
                                       non-alist-vars)))))
                      (t (value nil))))
              (chk-evaluator-use-in-rule name cl-proc nil
                                         (and meta-extract-flg
                                              '(meta-extract-global-fact+))
                                         :clause-processor
                                         ev ctx wrld state)
              (chk-rule-fn-guard "clause-processor" :clause-processor cl-proc
                                 ctx wrld state)
              (chk-evaluator ev wrld ctx state))))))))))))

(defun add-clause-processor-rule (name well-formedness-guarantee term wrld)

; Warning: Keep this in sync with chk-acceptable-clause-processor-rule.

; This function is non-standard, as the other add-x-rule functions traffic in
; runes and numes.  If we ever decide to support automatic application of
; clause-processor rules, along with enabling and disabling, then we should
; modify this to fit into that common mold.  For now, it seems misleading to
; deal with runes, since these rules cannot be enabled or disabled or applied
; automatically.

  (mv-let
   (clauses-result-call-p cl-proc clause alist rest-args ev cl-proc-call
                          meta-extract-flg)
   (destructure-clause-processor-rule term)
   (declare (ignore clause alist rest-args cl-proc-call meta-extract-flg))
   (assert$
    (and (not (eq clauses-result-call-p :error))
         (symbolp cl-proc)
         (function-symbolp cl-proc wrld))
    (putprop
     cl-proc 'clause-processor
     (or well-formedness-guarantee
         t)

; We keep a global list of clause-processor-rules, simply in order to be
; able to print them.  But someone may find other uses for this list, in
; particular in order to code computed hints that look for applicable
; clause-processor rules.

     (global-set 'clause-processor-rules
                 (acons name
                        term
                        (global-val 'clause-processor-rules wrld))
                 (mark-attachment-disallowed
                  (list cl-proc)
                  ev
                  (msg "it supports both the evaluator and clause-processor ~
                        function used in :CLAUSE-PROCESSOR rule ~x0"
                       name)
                  wrld))))))

; Finally, we develop code for trusted clause-processors.  This has nothing to
; do with defthm, but it seems reasonable to place it immediately below code
; for verified clause-processors.

(defun trusted-cl-proc-table-guard (key val wrld)

; There is not much point in checking whether the key is already designated as
; a clause-processor, because a redundant table event won't even result in such
; a check.  We could at least do this check for the non-redundant case, but
; there isn't really any need: It's perfectly OK to redefine the supporters and
; property of being a dependent clause-processor, provided the rest of the
; checks pass.  The user might be surprised in such cases, so the macro
; define-trusted-clause-processor causes an error if the proposed trusted
; clause-processor is already designated as such.

; At one time we insisted that key not have a non-nil value for its
; 'constrained or 'non-executablep property.  With the advent of defattach, a
; constrained function may however be a reasonable choice.  Rather than do an
; elaborate check here on exactly what sort of constrained function might be
; attachable (none, if it is a dependent clause-processor), we trust that the
; writer of :meta and :clause-processor rules knows better than to attach to
; functions that cannot be executed.

  (let ((er-msg "The proposed designation of a trusted clause-processor is ~
                 illegal because ~@0.  See :DOC ~
                 define-trusted-clause-processor."))
    (cond
     ((not (or (ttag wrld)
               (global-val 'boot-strap-flg wrld)))
      (mv nil
          (msg er-msg
               "there is not an active ttag (also see :DOC ttag)")))
     ((not (symbolp key))
      (mv nil
          (msg er-msg
               (msg "the clause-processor must be a symbol, unlike ~x0"
                    key))))
     ((not (function-symbolp key wrld))
      (mv nil
          (msg er-msg
               (msg "the clause-processor must be a function symbol, unlike ~
                     ~x0"
                    key))))
     ((not (all-function-symbolps val wrld))
      (cond ((not (symbol-listp val))
             (mv nil
                 (msg er-msg
                      "the indicated supporters list is not a true list of ~
                       symbols")))
            (t (mv nil
                   (msg er-msg
                        (msg "the indicated supporter~#0~[ ~&0 is not a ~
                              function symbol~/s ~&0 are not function ~
                              symbols~] in the current ACL2 world"
                             (non-function-symbols val wrld)))))))
     (t
      (let ((failure-msg (tilde-@-illegal-clause-processor-sig-msg
                          key
                          (stobjs-in key wrld)
                          (stobjs-out key wrld))))
        (cond
         (failure-msg
          (mv nil
              (msg er-msg failure-msg)))
         (t (mv t nil))))))))

(table trusted-cl-proc-table nil nil
       :guard
       (trusted-cl-proc-table-guard key val world))

(defmacro define-trusted-clause-processor
  (clause-processor supporters
                    &key
                    (label 'nil label-p) ;;; default is clause-processor$label
                    partial-theory       ;;; optional
                    ttag                 ;;; optional; nil is same as missing
                    )
  (let* ((ctx 'define-trusted-clause-processor)
         (er-msg "The proposed use of define-trusted-clause-processor is ~
                  illegal because ~@0.  See :DOC ~
                  define-trusted-clause-processor.")
         (assert-check
          `(assert-event
            (not (assoc-eq ',clause-processor
                           (table-alist 'trusted-cl-proc-table
                                        (w state))))
            :msg (msg "The function ~x0 is already indicated as a trusted ~
                       clause-processor."
                      ',clause-processor)
            :on-skip-proofs t))
         (ttag-extra (and ttag `((defttag ,ttag))))
         (label (if label-p
                    label

; A label is needed for supporting redundancy in the case that :partial-theory
; is nil; else, the event will not be redundant.  For uniformity we generate a
; deflabel by default even if :partial-theory is not nil.  The user may supply
; nil explicitly to defeat generation of a deflabel form.

                  (and (symbolp clause-processor) ; else cause error below
                       (add-suffix clause-processor
                                   "$LABEL"))))
         (label-extra (and label
                           `((deflabel ,label))))
         (extra (append ttag-extra label-extra)))
    (cond
     ((not (symbol-listp supporters))
      (er hard ctx er-msg
          "the second (supporters) argument must be a true list of symbols"))
     ((not (symbolp clause-processor)) ; expansion will do stronger check
      (er hard ctx er-msg
          "the first argument must be a symbol (in fact, must be a defined ~
           function symbol in the current ACL2 world)"))
     (t
      (case-match partial-theory
        (nil
         `(encapsulate
            ()
            ,assert-check
            ,@extra
            (table trusted-cl-proc-table ',clause-processor ',supporters)))
        (('encapsulate sigs . events)
         (cond
          ((atom sigs)
           (er hard ctx er-msg
               "the encapsulate event associated with :partial-theory has an ~
                empty signature list"))
          ((atom events)
           (er hard ctx er-msg
               "the encapsulate event associated with :partial-theory has an ~
                empty list of sub-events"))
          ((not (true-listp events))
           (er hard ctx er-msg
               "the encapsulate event associated with :partial-theory has a ~
                list of sub-events that is not a true-listp"))
          (t `(encapsulate
                ,sigs
                ,assert-check
                (logic) ; to avoid skipping local events
                ,@events
                ,@extra
                (set-unknown-constraints-supporters ,@supporters)
                (table trusted-cl-proc-table ',clause-processor
                       ',supporters)))))
        (& (er hard ctx er-msg
               "a supplied :partial-theory argument must be a call of ~
                encapsulate")))))))

;---------------------------------------------------------------------------
; Section:  Handling a List of Classes

; We start by translating the user-supplied list of rule-class tokens.

; Once upon a time we considered the idea of permitting rule classes, e.g.,
; :FORWARD-CHAINING, to be abbreviated by arbitrary subsequences of their
; characters.  We implemented the idea via "disambiguation alists."  We have
; since scrapped the idea for user-level consistency: rule classes are only one
; source of long keywords.  Do we permit the abbreviation of, say, :HINTS by
; :H?  Do we permit the abbreviation of :RULE-CLASSES to :RC?  Do we permit the
; abbreviation of the :PROPS keyword command of LP?  There is a good argument
; that we ought to permit a powerful symbol-level abbreviation convention.
; Macros suffer by requiring parentheses.  But since we don't have the time,
; now, to carry out the root-and-branch implementation of keyword
; disambiguation, we have scrapped the idea for now.  We leave the following
; dead code in place.

; (defun char-subsequencep (x y)
;
; ; Determine whether x is a subsequence of y, e.g., '(#\B #\D) is a
; ; char-subsequencep of '(#\A #\B #\C #\D) but not of '(#\A #\D #\B).
; ; X and y must be true lists of characters.
;
;   (cond ((null x) t)
;         ((null y) nil)
;         ((eql (car x) (car y))
;          (char-subsequencep (cdr x) (cdr y)))
;         (t (char-subsequencep x (cdr y)))))
;
; (defun disambiguate1 (x alist)
;
; ; Alist should pair character lists with arbitrary values.  We select those
; ; pairs whose key have x as a subsequence.
;
;   (cond ((null alist) nil)
;         ((char-subsequencep x (caar alist))
;          (cons (car alist) (disambiguate1 x (cdr alist))))
;         (t (disambiguate1 x (cdr alist)))))
;
; (defun make-disambiguation-alist (lst)
;
; ; This function is used to preprocess a true list of symbols into an
; ; alist suitable for disambiguate.  For example, '(FOO BAR) is
; ; transformed into '(((#\F #\O #\O) . FOO) ((#\B #\A #\R) . BAR)).
;
;   (cond ((null lst) nil)
;         (t (cons (cons (coerce (symbol-name (car lst)) 'list) (car lst))
;                  (make-disambiguation-alist (cdr lst))))))
;
; (defun assoc-cdr (x alist)
;
; ; Like assoc-equal but uses the cdr of each pair in alist as the key.
;
;   (cond ((null alist) nil)
;         ((equal x (cdar alist)) (car alist))
;         (t (assoc-cdr x (cdr alist)))))
;
; (defun disambiguate (token alist ctx phrase state)
;
; ; This function disambiguates token wrt alist or else causes an error.
; ; Token must be a symbol and alist must be a ``disambiguation alist,''
; ; an alist pairing lists of characters to symbols.  For example, if
; ; token is :EM and alist includes the pair ((#\E #\L #\I #\M) . :ELIM)
; ; and no other pair whose key has EM as a subsequence, then no error
; ; is caused and :ELIM is returned as the value.  If the token is a
; ; subsequence of no key or of more than one key, an error is caused.
; ; Phrase is a tilde-@ phrase that fills in the sentence: "The
; ; acceptable ~@1 are ..." so, for example, phrase might be "rule
; ; classes".
;
; ; We adopt the convention, for sanity, that if token is eq to the
; ; value component of some pair in alist, then its meaning is itself.
; ; This guarantees that if you spell a token out completely you get that
; ; token and no other; in particular, you don't get an ambiguity error
; ; just one key in the alist is a subsequence of another.
;
;   (cond
;    ((assoc-cdr token alist) (value token))
;    (t
;     (let ((winners (disambiguate1 (coerce (symbol-name token) 'list) alist)))
;       (cond ((null winners)
;              (er soft ctx "The token ~x0 denotes none of the acceptable ~@1: ~&2."
;                  token
;                  phrase
;                  (strip-cdrs alist)))
;             ((null (cdr winners))
;              (value (cdar winners)))
;             (t (er soft ctx "The token ~x0 is ambiguously denotes the ~@1:  ~&2."
;                    token
;                    phrase
;                    (strip-cdrs winners))))))))
;
; (defun tilde-@-abbreviates-but-phrase (x y)
;
; ; We produce a tilde-@ phrase that prints as "x abbreviates y, but y"
; ; if x is different from y and that is just "y" otherwise.  Both x and
; ; y are symbols.  This is used to print such messages as ":RWT
; ; abbreviates :REWRITE, but :REWRITE cannot be used as a structured
; ; rule class."
;
;   (cond ((eq x y) (msg "~x0" y))
;         (t (msg "~x0 abbreviates ~x1, but ~x1" x y))))
;
; ; Thus ends the dead code devoted to disambiguation.
;

; Now we stub out the proof-builder's sense of "instructions."

(defun primitive-instructionp (instr state)
  (let* ((cmd (car (make-official-pc-instr instr)))
         (typ (pc-command-type cmd)))
    (and (member-eq typ '(primitive atomic-macro))
         (acl2-system-namep-state
          (intern-in-package-of-symbol (symbol-name cmd) 'acl2-pc::induct)
          state))))

(defun non-primitive-instructions (instructions state)
  (cond
   ((endp instructions)
    nil)
   ((primitive-instructionp (car instructions) state)
    (non-primitive-instructions (cdr instructions) state))
   (t
    (cons (car instructions)
          (non-primitive-instructions (cdr instructions) state)))))

(defun chk-primitive-instruction-listp (instructions ctx state)
  (if (true-listp instructions)
      (value nil)
    (er soft ctx
        "An :instructions argument must be a ~
         true-list and ~x0 is not."
        instructions)))

(defun translate-instructions (name instructions ctx wrld state)
  (declare (ignore name wrld))
  (if (eq instructions t)
      (value t)
    (er-progn (chk-primitive-instruction-listp instructions ctx state)
              (value instructions))))

(defun controller-alistp (clique alist wrld)

; Clique is a list of function symbols.  Alist is an arbitrary object.
; We confirm that alist is an alist that maps each fn in clique to a
; mask of t's and nil's whose length is the arity of the corresponding
; fn.

  (cond ((atom alist)
         (cond ((null alist) (null clique))
               (t nil)))
        ((and (consp (car alist))
              (symbolp (caar alist))
              (member-eq (caar alist) clique)
              (boolean-listp (cdar alist))
              (= (length (cdar alist)) (arity (caar alist) wrld)))
         (controller-alistp (remove1-eq (caar alist) clique)
                            (cdr alist)
                            wrld))
        (t nil)))

(defun alist-to-keyword-alist (alist ans)

; Convert ((key1 . val1) ... (keyn . valn)) to a keyword alist, i.e.,
; (keyn valn ... key1 val1).  Note that we reverse the order of the
; "key pairs."

  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) ans)
        (t (alist-to-keyword-alist (cdr alist)
                                   (cons (caar alist)
                                         (cons (cdar alist) ans))))))

(defun eliminate-macro-aliases (lst macro-aliases wrld)

; Returns (mv flg lst), where flg is nil if lst is unchanged, :error if there
; is an error (some element is neither a function symbol nor a macro aliases)
; -- in which case lst is a string giving a reason for the error after "but
; <original_list> " -- else :changed if there is no error but at least one
; macro alias was found.

  (cond ((atom lst)
         (cond ((null lst) (mv nil nil))
               (t (mv :error "does not end in nil"))))
        (t (mv-let (flg rst)
                   (eliminate-macro-aliases (cdr lst) macro-aliases wrld)
                   (cond ((eq flg :error)
                          (mv :error rst))
                         (t (let* ((next (car lst))
                                   (fn (deref-macro-name next macro-aliases)))
                              (cond ((not (and (symbolp fn)
                                               (function-symbolp fn wrld)))
                                     (mv :error
                                         (msg "contains ~x0"
                                              next)))
                                    ((or (eq flg :changed)
                                         (not (eq next fn)))
                                     (mv :changed (cons fn rst)))
                                    (t (mv nil lst))))))))))

(defun fix-loop-stopper-alist (x macro-aliases wrld)

; Returns (mv flg x').  If x is a valid loop-stopper alist then flg is flg0 and
; x' is x.  If x is valid except that some symbols that are expected to be
; function symbols are actually macro aliases, then flg is t and x' is the
; result of replacing each such macro aliases by the corresponding function.
; Otherwise flg is :error.

  (cond
   ((null x) (mv nil nil))
   ((atom x) (mv :error nil))
   ((not (and (true-listp (car x))
              (<= 2 (length (car x)))
              (legal-variablep (caar x))
              (legal-variablep (cadar x))
              (not (eq (caar x) (cadar x)))))
    (mv :error nil))
   (t (mv-let (flg1 fns)
              (eliminate-macro-aliases (cddar x) macro-aliases wrld)
              (cond ((eq flg1 :error) (mv :error nil))
                    (t (mv-let
                        (flg2 rest)
                        (fix-loop-stopper-alist (cdr x) macro-aliases wrld)
                        (cond (flg1 (mv t (cons (list* (caar x) (cadar x) fns)
                                                rest)))
                              (flg2 (mv t (cons (car x) rest)))
                              (t (mv nil x))))))))))

(defun guess-controller-alist-for-definition-rule (names formals body ctx wrld
                                                         state)

; Names is a singleton list containing a function name to be used as the clique
; for a :definition rule with the indicated formals and body.  We guess a
; :controller-alist or cause an error.

  (let ((t-machine (termination-machine nil nil names formals body nil nil
                                        (default-ruler-extenders wrld))))
    (er-let*
     ((m (guess-measure (car names) nil formals 0 t-machine ctx wrld state)))
     (value (list (cons (car names)
                        (make-controller-pocket formals
                                                (all-vars m))))))))

(defun chk-legal-linear-trigger-terms1 (term lst name ctx state)
  (cond ((null lst) (value nil))
        ((let ((hyp-vars (all-vars-in-hyps (caar lst))))

; We use all-vars-in-hyps here, in checking that the explicitly supplied
; :trigger-terms are all maximal terms, for consistency with the use of
; all-vars-in-hyps in add-linear-rule2 and chk-acceptable-linear-rule2 to
; compute maximal terms heuristically.

           (or (eq hyp-vars t)
               (subsetp-eq (set-difference-eq (all-vars (cdar lst))
                                              hyp-vars)
                           (all-vars term))))
         (chk-legal-linear-trigger-terms1 term (cdr lst) name ctx state))
        (t (er soft ctx
               "Each term in the :TRIGGER-TERMS of a :LINEAR rule should be a ~
                legal trigger for the rule generated for each branch through ~
                the corollary.  But the the proposed trigger ~p0 for the ~
                :LINEAR rule ~x1 is illegal for the branch ~p2 because it ~
                contains insufficient variables.  See :DOC linear."
               (untranslate term nil (w state))
               name
               (untranslate
                (if (caar lst)
                    (fcons-term* 'implies (conjoin (caar lst)) (cdar lst))
                    (cdar lst))
                t
                (w state))))))

(defun chk-legal-linear-trigger-terms (terms lst name ctx state)

; When the user supplies some :TRIGGER-TERMS for a :LINEAR rule, we must check
; that each trigger is legal for every rule generated from the unprettyified
; corollary.  Here, terms is a true-list of terms proposed as triggers and lst
; is the unprettyification of the corollary, i.e., a list of pairs of the form
; ((hyps1 . concl1) ... (hypsk . conclk)).  To be legal, each term must be a
; non-variable, non-quote, non-lambda application, non-IF and must, for each
; (hypsi . concli) pair, contain sufficient variables so that the vars in hypsi
; plus those in the term include all the vars in concli.  We check these
; conditions and return nil or cause an error.

  (cond
   ((null terms) (value nil))
   ((and (nvariablep (car terms))
         (not (fquotep (car terms)))
         (not (flambda-applicationp (car terms)))
         (not (eq (ffn-symb (car terms)) 'if)))
    (er-progn
     (chk-legal-linear-trigger-terms1 (car terms) lst name ctx state)
     (chk-legal-linear-trigger-terms (cdr terms) lst name ctx state)))
   (t (er soft ctx
          "The term ~p0 supplied as a :TRIGGER-TERM for the :LINEAR rule ~x1 ~
           is illegal because it is either a variable, a quoted constant, a ~
           lambda application (or LET-expression), or an IF-expression."
          (untranslate (car terms) nil (w state))
          name))))

(defun backchain-limit-listp (lst)

; Recognizer for true-lists each of whose elements is either NIL or a
; non-negative integer.

  (cond ((atom lst)
         (equal lst nil))
        ((or (null (car lst))
             (natp (car lst)))
         (backchain-limit-listp (cdr lst)))
        (t
         nil)))

(defun recover-metafunction-or-clause-processor-signatures (token term)

; Term is supposed to be either a metafunction correctness theorem or a
; clause-processor correctness theorem, depending on token being :meta or
; :clause-processor.  (But it may not be of the correct form.)  We return (mv
; triple-flg fn hyp-fn rest-args), where hyp-fn is nil if no hypothesis fn is
; involved.  Rest-args are all the arguments of fn after the first.  Triple-flg
; is :error if term cannot be parsed according to token, is t if the identified
; metafunction or clause processor, fn, returns an error triple (and thus must
; actually be a clause-processor whose result is to be accessed with
; CLAUSES-RESULT), or nil if fn returns a simple value (term or set of
; clauses).

; In the case of a :meta fn, triple-flg is :error or nil and rest-args may be
; nil or something like (mfc state).  In the case of a :clause-processor,
; triple-flg may be :error, t, or nil and rest-args may be nil or (hint) or
; (hint stobj1 stobj2 ...).  When hyp-fn is present, we know that it can take
; the same arguments as fn.

; If triple-flg is :error then we know chk-acceptable-x-rule will cause an
; error.  Otherwise, we guarantee that fn is a function symbol, hyp-fn is nil
; or a function symbol of the same arity as fn, that the arity of both
; functions is (+ 1 (len rest-args)), and that rest-args is a list of distinct
; variable symbols, and that result of fn is either a triple (whose value is to
; be accessed with CLAUSES-RESULT) or a single value according to triple-flg.

  (cond
   ((eq token :meta)
    (mv-let
     (hyp eqv ev x a fn mfc-symbol)
     (interpret-term-as-meta-rule term)
     (mv-let
      (hyp-fn extra-fns)
      (meta-rule-hypothesis-functions hyp ev x a mfc-symbol)
      (declare (ignore extra-fns))
      (cond

; If hyp-fn is nil, it means the hyp didn't parse.  If hyp-fn is t it means the
; hyp parsed but there is no hyp-fn.

; Note that to insure that fn, for example, is a function symbol of the correct
; signature, we only need to check that it is a symbol, since term is a
; translated term.

       ((or (null eqv)
            (not (symbolp fn))
            (null hyp-fn)
            (not (symbolp hyp-fn))
            (not (symbolp mfc-symbol)))
        (mv :error nil nil nil))
       (t (mv nil
              fn
              (if (eq hyp-fn t) nil hyp-fn)
              (if mfc-symbol
                  (list mfc-symbol 'STATE)
                  nil)))))))
   (t
    (mv-let
     (flg fn cl alist rest-args ev call xflg)
     (destructure-clause-processor-rule term)
     (declare (ignore call xflg))
     (cond
      ((or (eq flg :error)
           (not (symbolp fn))
           (not (symbolp cl))
           (not (symbolp alist))
           (not (symbol-listp rest-args))
           (not (symbolp ev))
           (not (no-duplicatesp (list* cl alist rest-args))))
       (mv :error nil nil nil))
      (t (mv flg fn nil rest-args)))))))

(defun equal-except-on-non-stobjs (arglist1 arglist2 w)

; Given two lists of symbols, we check that when corresponding elements are
; different they are not stobjs.  That is, the two lists are equal except on
; the non-stobj elements.  This is implied by (equal arglist1 arglist2) and
; implies (equal (len arglist1) (len arglist2)).

  (cond ((atom arglist1)
         (and (equal nil arglist1)
              (equal nil arglist2)))
        ((atom arglist2) nil)
        ((equal (car arglist1) (car arglist2))
         (equal-except-on-non-stobjs (cdr arglist1) (cdr arglist2) w))
        ((or (stobjp (car arglist1) t w)
             (stobjp (car arglist2) t w))
         nil)
        (t (equal-except-on-non-stobjs (cdr arglist1) (cdr arglist2) w))))

(defun arity-alistp (alist)
; We check that alist binds symbols to naturals and that no symbol is bound
; twice.
  (cond
   ((atom alist) (eq alist nil))
   ((and (consp (car alist))
         (symbolp (car (car alist)))
         (natp (cdr (car alist)))
         (arity-alistp (cdr alist))
         (not (assoc-eq (car (car alist)) (cdr alist))))
    t)
   (t nil)))

(defun compatible-arity-alistsp (alist1 alist2)

; Both arguments are arity-alists.  We want to know if their union is also.  We
; do this in the most brute-force way imaginable except that we recognize the
; special cases where the two alists are identical.

  (cond ((equal alist1 alist2) t)
        (t (arity-alistp (union-equal alist1 alist2)))))

(defun collect-disagreeing-arity-assumptions (alist1 alist2)
  (cond ((endp alist1) nil)
        ((and (assoc (car (car alist1)) alist2)
              (not (equal (cdr (car alist1))
                          (cdr (assoc (car (car alist1)) alist2)))))
         (cons (car (car alist1))
               (collect-disagreeing-arity-assumptions (cdr alist1) alist2)))
        (t (collect-disagreeing-arity-assumptions (cdr alist1) alist2))))

(defun interpret-term-as-well-formedness-guarantee-thm (token fn thm)

; Token must be :META or :CLAUSE-PROCESSOR.  In the former case,
; thm is a term (actually a theorem) and we interpret it as

; (IMPLIES (AND (LOGIC-TERMP tvar wvar)
;               (ARITIES-OKP '((fn1 . k1) ...) wvar))
;          (LOGIC-TERMP (fn tvar) wvar))

; In the latter case, we interpret thm as

; (IMPLIES (AND (LOGIC-TERM-LISTP tvar wvar)
;               (ARITIES-OKP '((fn1 . k1) ...) wvar))
;          (LOGIC-TERM-LIST-LISTP (fn tvar) wvar))

; or

; (IMPLIES (AND (LOGIC-TERM-LISTP tvar wvar)
;               (ARITIES-OKP '((fn1 . k1) ...) wvar))
;          (LOGIC-TERM-LIST-LISTP (CLAUSES-RESULT (fn tvar)) wvar))

; But we recognize certain equivalent or stronger variants, including allowing
; fewer or rearranged hypotheses and allowing for fn to have additional
; arguments as permitted for metafunctions and clause-processors.  We return
; (mv tvar wvar alist triple-flg rest-args), where alist is the evg of the quoted
; arities alist found and rest-args is the list of arguments to fn after tvar.
; and triple-flg is :error, t, or nil with :error meaning we couldn't parse
; thm appropriately, t meaning that fn returns a triple whose value is accessed
; by CLAUSES-RESULT, and nil meaning fn returns a single value.

; If triple-flg is :error, thm is not of the appropriate form; otherwise it is.
; But we do not check anything about the components returned!  For example,
; tvar, which is guaranteed to be a term may not actually be a variable symbol,
; etc.  These constraints must be checked by the caller.

; We actually accept the thm (LOGIC-TERMP (fn tvar) wvar) and
; (LOGIC-TERM-LIST-LISTP (fn tvar) wvar) without any hypotheses, though the
; only functions we can think of for which this is provable are those that
; return constants and hence can't be correct metafunctions or clause
; processor.

; We could code this more efficiently but we don't expect well-formedness
; guarantees to be very common.

  (let ((pre (if (eq token :META) 'LOGIC-TERMP 'LOGIC-TERM-LISTP))
        (post (if (eq token :META) 'LOGIC-TERMP 'LOGIC-TERM-LIST-LISTP)))
    (case-match thm
      (('IMPLIES ('IF (!pre tvar wvar)
                      ('ARITIES-OKP ('QUOTE alist) wvar)
                      ''NIL)
                 (!post (!fn tvar . rest-args) wvar))
       (mv tvar wvar alist nil rest-args))
      (('IMPLIES ('IF ('ARITIES-OKP ('QUOTE alist) wvar)
                      (!pre tvar wvar)
                      ''NIL)
                 (!post (!fn tvar . rest-args) wvar))
       (mv tvar wvar alist nil rest-args))
      (('IMPLIES (!pre tvar wvar)
                 (!post (!fn tvar . rest-args) wvar))
       (mv tvar wvar nil nil rest-args))
      (('IMPLIES ('ARITIES-OKP ('QUOTE alist) wvar)
                 (!post (!fn tvar . rest-args) wvar))
       (mv tvar wvar alist nil rest-args))
      ((!post (!fn tvar . rest-args) wvar)
       (mv tvar wvar nil nil rest-args))

; Now we repeat the same patterns except this time allow for CLAUSES-RESULT
; around the fn call:

      (('IMPLIES ('IF (!pre tvar wvar)
                      ('ARITIES-OKP ('QUOTE alist) wvar)
                      ''NIL)
                 (!post ('CLAUSES-RESULT (!fn tvar . rest-args)) wvar))
       (mv tvar wvar alist t rest-args))
      (('IMPLIES ('IF ('ARITIES-OKP ('QUOTE alist) wvar)
                      (!pre tvar wvar)
                      ''NIL)
                 (!post ('CLAUSES-RESULT (!fn tvar . rest-args)) wvar))
       (mv tvar wvar alist t rest-args))
      (('IMPLIES (!pre tvar wvar)
                 (!post ('CLAUSES-RESULT (!fn tvar . rest-args)) wvar))
       (mv tvar wvar nil t rest-args))
      (('IMPLIES ('ARITIES-OKP ('QUOTE alist) wvar)
                 (!post ('CLAUSES-RESULT (!fn tvar . rest-args)) wvar))
       (mv tvar wvar alist t rest-args))
      ((!post ('CLAUSES-RESULT (!fn tvar . rest-args)) wvar)
       (mv tvar wvar nil t rest-args))
      (& (mv nil nil nil :error nil)))))

(defun translate-well-formedness-guarantee (token x name corollary ctx wrld
                                                  state)

; Token is either :META or :CLAUSE-PROCESSOR and indicates what class of rule
; we're creating.  X is the value supplied for the :WELL-FORMEDNESS-GUARANTEE
; component of the rule class.  Name is the name of the correctness theorem for
; a metafunction (perhaps with a hypothesis metafunction) or clause-processor
; and corollary is the statement of that correctness theorem.  X must be one
; of:

; [1] thm-name1               token = :META or :CLAUSE-PROCESSOR
; [2] (thm-name1)             token = :META
; [3] (thm-name1 thm-name2)   token = :META

; If token is :CLAUSE-PROCESSOR, token must be of form [1].  If token is :META
; and the metatheorem named by name has a hypothesis metafunction, token must
; be of form [3].  In all cases, thm-name1 and thm-name2 (when relevant) must
; be symbols that name theorems that guarantee that the metafunction or clause
; processor together with the hypothesis metafunction, as appropriate, return
; well-formed results.  In the case of token :META ``well-formed'' means the
; output is a LOGIC-TERMP if the input is; in the case of token
; :CLAUSE-PROCESSOR, ``well-formed'' means the output is a
; LOGIC-TERM-LIST-LISTP if the input is a LOGIC-TERM-LISTP..  In both
; cases, the well-formedness theorems also involve assumptions about the
; arities of certain logic-mode functions.

; The result of this function either an error or a ``well-formedness
; guarantee'' of the form:

; (cons (list name fn thm-name1 hyp-fn thm-name2)
;       combined-arity-alist)

; where the list of length 5 above is shortened to 3 if there no hyp-fn is
; involved, and combined-arity-alist is the union of the two arity-alists.  We
; keep all this information to make error reporting easier.  The list of length
; 5 (or 3) is displayed to the user when he or she tries to make one of the
; functions on the combined-arity-alist untouchable.  The combined-arity-alist
; is checked against the current world when the metatheorem or clause processor
; is applied.  The value of this function is stored in the :heuristic-info
; field of the :rewrite-rule created for this metatheorem and on the property
; list of the metafunction under the WELL-FORMEDNESS-GUARANTEE property.

; So much for the spec and use of this function.  Now for the operational
; details.   To allow some code sharing we often act like a
; clause-processor is just a metafunction (e.g., we use the same name, fn, for
; both) without a hyp-fn; of course, we must interpret ``well-formedness''
; appropriately.

; But we must recover the metafunction or clause-processor function name, fn,
; (and, possibly, the hypothesis metafunction name, hyp-fn) from the translated
; corollary formula, which means we must parse corollary as a formula of the
; appropriate shape.  But rule classes are translated -- resulting in this
; function being called -- before the translated rule class (always now
; containing a translated :corollary term) is checked for well-formedness.  So
; here we're in the odd position of wanting to know whether x names theorems
; about certain functions, fn and hyp-fn, proved sound by corollary, without
; knowing that corollary establishes soundness for anything!  So what do we do
; if corollary has the wrong shape and we cannot recover fn and hyp-fn from it?
; Answer: we ``approve'' x (by causing no error and acting as though there were
; well-formedness guarantee)!  We know that corollary will be checked later and
; will cause the whole rule to fail if it's not of the right shape.

  (cond
   ((not (or (and (symbolp x)
                  (formula x nil wrld))
             (and (eq token :META)
                  (consp x)
                  (symbolp (car x))
                  (null (cdr x))
                  (formula (car x) nil wrld))
             (and (eq token :META)
                  (consp x)
                  (symbolp (car x))
                  (consp (cdr x))
                  (symbolp (cadr x))
                  (null (cddr x))
                  (formula (car x) nil wrld)
                  (formula (cadr x) nil wrld))))
    (if (eq token :META)
        (er soft ctx
            "The :WELL-FORMEDNESS-GUARANTEE of :META rule ~x0 is ill-formed.  ~
             In general, a :WELL-FORMEDNESS-GUARANTEE must be of one of the ~
             following forms:~%[1]  thm-name1~%[2]  (thm-name1)~%[3]  ~
             (thm-name1 thm-name2)~%where thm-name1 names a previously proved ~
             theorem guaranteeing that the relevant metafunction returns a ~
             LOGIC-TERMP when given a LOGIC-TERMP.  See :DOC logic-termp.  ~
             Form [3] is only permitted (and is required!) when the ~
             metatheorem has a hypothesis metafunction, in which case ~
             thm-name2 names a previously proved theorem guaranteeing that ~
             the hypothesis metafunction also returns a LOGIC-TERMP when ~
             given one.  ~x1 is of none of the expected forms.  See :DOC ~
             well-formedness-guarantee for details."
            name x)
        (er soft ctx
            "The :WELL-FORMEDNESS-GUARANTEE of :CLAUSE-PROCESSOR rule ~x0 ~
             must be the name of a theorem guaranteeing that the clause ~
             processor returns a LOGIC-TERM-LIST-LISTP when given a ~
             LOGIC-TERM-LISTP.  ~x1 is not such a name.  See :DOC ~
             logic-term-listp, :DOC logic-term-list-listp, and :DOC ~
             well-formedness-guarantee for details."
             name x)))
   (t (let* ((thm-name1 (cond ((symbolp x) x)
                              (t (car x))))
             (thm-name2 (cond ((symbolp x) nil) ; might be nil
                              (t (cadr x))))
             (thm1 (formula thm-name1 nil wrld))
             (thm2 (if (null thm-name2)         ; might be nil
                       nil
                       (formula thm-name2 nil wrld))))

        (mv-let
         (triple-flg fn hyp-fn rest-args)
         (recover-metafunction-or-clause-processor-signatures token corollary)
         (let ((expected-fn-form
                `(IMPLIES
                  (AND (,(if (eq token :meta)
                             'LOGIC-TERMP
                           'LOGIC-TERM-LISTP)
                        X W)
                       (ARITY-ALISTP '<alist> W))
                  (,(if (eq token :meta)
                        'LOGIC-TERMP
                      'LOGIC-TERM-LIST-LISTP)
                   ,(if triple-flg
                        `(CLAUSES-RESULT (,fn X ,@rest-args))
                        `(,fn X ,@rest-args))
                   W)))
               (expected-hyp-fn-form
                (if hyp-fn
                    `(IMPLIES
                      (AND (LOGIC-TERMP X W)
                           (ARITY-ALISTP '<alist> W))
                      (LOGIC-TERMP (,hyp-fn X ,@rest-args)
                             W))
                    nil))
               (evisc (evisc-tuple nil nil
                                   '((<alist> . "((fn1 . n1) ... (fnk . nk))"))
                                   nil)))
         (cond
          ((eq triple-flg :error)

; The corollary didn't parse as a meta/clause-processor rule (as per token).
; But we quietly accept it knowing that the corresponding chk-acceptable-x-rule
; will cause an error.

            (value nil))

; Otherwise, fn is the metafunction or clause processor function, as per token.
; We know that fn is a function symbol of arity (+ 1 (len rest-args)), that fn
; returns an error triple iff triple-flg is t (and so its value must be
; accessed with CLAUSES-RESULT), that hyp-fn is either nil or a function symbol
; of the same arity as fn, and that `(,fn x ,@rest-args) and `(,hyp-fn x
; ,@rest-args) are legal calls of those functions (assuming hyp-fn is non-nil).

; We also know that x names at least one theorem, thm1 with name thm-name1.  We
; know that thm2 is either a theorem with name thm-name2 or else thm2 and
; thm-name2 are both nil.  Thm1 and thm2 are supposedly well-formedness
; guarantees for fn and hyp-fn.  But we must confirm that.

           (t (mv-let
               (tvar1 wvar1 alist1 triple-flg1 rest-args1)
               (interpret-term-as-well-formedness-guarantee-thm token fn thm1)
               (cond
                ((eq triple-flg1 :error)
                 (er soft ctx
                     "The :WELL-FORMEDNESS-GUARANTEE of ~x0 rule ~x1 is ~
                      ill-formed.  We cannot interpret the theorem named ~x2 ~
                      as a well-formedness guarantee for the function ~x3.  ~
                      We expected the name of a theorem like ~X45.  See :DOC ~
                      well-formedness-guarantee for details of the acceptable ~
                      forms."
                     token name thm-name1 fn
                     expected-fn-form
                     evisc))
                ((and

; Now we know that the alleged well-formedness theorem, thm1, is about the same
; function symbol, fn!  Given the possibility that fn has changed since thm1
; was proved, we do another check.  This is just out of politeness: fn could
; only change due to a redefinition and soundness is now the user's
; responsibility!  But we know that if this metatheorem/clause-processor is
; approved, we're going to call fn on the arguments we see in corollary and we
; want some assurance that thm1 guarantees the well-formedness of the result!
; For example, imagine that when thm1 was proved about a metafunction fn, the
; formals of fn were (x state mfc) but then before corollary was proved fn was
; redefined with arguments (x mfc state).  If we were to approve this thm as a
; well-formedness guarantee then we'd be wrong!  Of course, if fn has been
; redefined, it hardly matters that the arguments are the same!  But since the
; introduction of a non-term is a pretty difficult bug to diagnose, we prefer
; to do what we can to prevent it even if it's the user's own fault!

                  (equal-except-on-non-stobjs rest-args rest-args1 wrld)
                  (eq triple-flg triple-flg1)

                  (variablep tvar1)
                  (variablep wvar1)
                  (symbol-listp rest-args1) ;``(variable-listp rest-args1)''
                  (no-duplicatesp-equal
                   (list* tvar1 wvar1 rest-args1))
                  (arity-alistp alist1))

; We know thm is of the form (for token :meta):
; (IMPLIES (AND (LOGIC-TERMP tvar1 wvar1)
;               (ARITIES-OKP '<alist1> wvar1))
;          (LOGIC-TERMP (fn tvar1 . rest-args1) wvar1))

; For token :clause-processor we know:
; (IMPLIES (AND (LOGIC-TERM-LISTP tvar1 wvar1)
;               (ARITIES-OKP '<alist1> wvar1))
;          (LOGIC-TERM-LIST-LISTP (fn tvar1 . rest-args1) wvar1))

; possibly with a CLAUSES-RESULT wrapped around the fn call.  Now we know that
; all the terms used as variables above really are variables and they're
; distinct, and that alist1 pairs symbols to naturals.  (For politeness only we
; know that the same stobjs are given to fn in both the corollary and thm1 and
; that the output of fn is either a triple or a single value as specified by
; triple-flg in both theorems.)

; We claim the tests above insure that thm1 guarantees that fn always returns a
; LOGIC-TERMP or LOGIC-TERM-LIST-LISTP provided the arity alist, alist1, is
; valid in the current world.  Now we check the same things for the hyp-fn, if
; any.

                 (cond
                  ((null hyp-fn)
                   (cond
                    (thm-name2
                     (er soft ctx
                         "The ~x0 rule ~x1 mentions the metafunction ~x2 but ~
                          does not mention a hypothesis metafunction.  ~
                          Therefore, it makes no sense to name a previously ~
                          proved theorem that provides a well-formedness ~
                          guarantee for a hypothesis metafunction.  But you ~
                          have specified such a name, ~x4, with your ~
                          :WELL-FORMEDNESS-GUARANTEE ~x3.  This may indicate ~
                          a misunderstanding.  Replace your guarantee with ~
                          :WELL-FORMEDNESS-GUARANTEE ~x5."
                         token name fn x thm-name2 (list thm-name1)))
                    (t
                     (value (cons (list name fn thm-name1)
                                  alist1)))))

; Token is :META because we have a hyp-fn.

                  ((null thm-name2)
                   (er soft ctx
                       "The :META rule ~x0 mentions the metafunction ~x1 and ~
                        the hypothesis metafunction ~x2.  You have correctly ~
                        named ~x3 as a previously proved theorem guaranteeing ~
                        that ~x1 always returns a LOGIC-TERMP, but you have ~
                        not specified such a name for ~x2.  We require that ~
                        you do so.  That is, prove a theorem like ~X45 with ~
                        some name and change your :WELL-FORMEDNESS-GUARANTEE ~
                        value to (~x3 name)."
                       name fn hyp-fn thm-name1 expected-hyp-fn-form evisc))
                  (t (mv-let
                      (tvar2 wvar2 alist2 triple-flg2 rest-args2)
                      (interpret-term-as-well-formedness-guarantee-thm
                       token hyp-fn thm2)
                      (cond
                       ((and
                         (equal-except-on-non-stobjs rest-args rest-args2 wrld)
                         (eq triple-flg triple-flg2)
                         (variablep tvar2)
                         (variablep wvar2)
                         (no-duplicatesp-equal
                          (list* tvar2 wvar2 rest-args2))
                         (arity-alistp alist2))
                        (cond
                         ((compatible-arity-alistsp alist1 alist2)
                          (value (cons (list name
                                             fn thm-name1
                                             hyp-fn thm-name2)
                                       (union-equal alist1 alist2))))
                         (t (er soft ctx
                                "The :WELL-FORMEDNESS-GUARANTEE of the :META ~
                                 rule ~x0 for the metafunction ~x1 with ~
                                 hypothesis metafunction ~x2 is inadmissible ~
                                 because the two LOGIC-TERMP theorems (~x3 ~
                                 and ~x4) assume different arities for one or ~
                                 more function symbols, to wit ~&5.  You will ~
                                 have to prove LOGIC-TERMP guarantee theorems ~
                                 that make compatible arity assumptions!"
                                name fn hyp-fn thm-name1 thm-name2
                                (collect-disagreeing-arity-assumptions
                                 alist1 alist2)))))
                       (t (er soft ctx
                              "The :WELL-FORMEDNESS-GUARANTEE of the :META ~
                               rule ~x0 for the metafunction ~x1 with ~
                               hypothesis metafunction ~x2 specified that ~x3 ~
                               is the name of the previously proved theorem ~
                               that guarantees that ~x2 always returns a ~
                               LOGIC-TERMP.  But theorem ~x3 is not of the ~
                               expected form.  We expected it to be something ~
                               like:~X45.  See :DOC well-formedness-guarantee."
                              name fn hyp-fn thm-name2
                              expected-hyp-fn-form evisc)))))))
                (t (er soft ctx
                       "The :WELL-FORMEDNESS-GUARANTEE of the ~x0 rule ~x1 ~
                        for ~x2 specified that ~x3 is the name of the ~
                        previously proved theorem that established that ~x2 ~
                        always returns a LOGIC-TERMP.  But theorem ~x3 is not ~
                        of the expected form.  We expected it to be something ~
                        like ~X45. See :DOC well-formedness-guarantee."
                       token name fn thm-name1
                       expected-fn-form evisc))))))))))))

(defun translate-rule-class-alist (token alist seen corollary name x ctx ens
                                         wrld state)

; Alist is the untranslated alist of a rule-class with car token.
; Corollary is the translated value of the :COROLLARY entry in alist
; (which is guaranteed to be present).  Seen is an alist of the keys
; seen so far and their translated values.  It is in fact the reverse
; of the final answer.  We translate the values in alist, making sure
; that no key is seen twice, that the keys seen are appropriate for
; the class named by token, and that all required keys (other than
; :COROLLARY) are present.  The variable x is the object the user
; supplied to specify this class and is used only in error messages.
; Name is the name of the event for which this rule class is being
; translated and is used in the translation of :BY hints.

; WARNING: If you add new keywords, be sure to change the
; documentation under deflabel rule-classes.

  (cond
   ((null alist)
    (cond
     ((eq token :META)
      (cond ((not (assoc-eq :TRIGGER-FNS seen))
             (er soft ctx
                 "The :META rule class must specify :TRIGGER-FNS.  ~
                  The rule class ~x0 is thus illegal.  See :DOC meta."
                 x))
            (t (value (alist-to-keyword-alist seen nil)))))
     ((eq token :FORWARD-CHAINING)
      (cond ((not (assoc-eq :TRIGGER-TERMS seen))
             (mv-let (hyps concls)
                     (destructure-forward-chaining-term corollary wrld)
                     (declare (ignore concls))
                     (cond ((null hyps)
                            (er soft ctx
                                "When no :TRIGGER-TERMS component is ~
                                 specified for a :FORWARD-CHAINING ~
                                 rule class, the first hypothesis of ~
                                 the conjecture is used as the only ~
                                 trigger.  But ~p0 has no hypotheses ~
                                 and thus ~x1 is an illegal rule ~
                                 class.  See :DOC forward-chaining."
                                (untranslate corollary t wrld)
                                x))
                           (t (let* ((first-hyp
                                      (if (and (nvariablep (car hyps))
;                                              (not (fquotep (car hyps)))
                                               (or (eq (ffn-symb (car hyps))
                                                       'force)
                                                   (eq (ffn-symb (car hyps))
                                                       'case-split)))
                                          (fargn (car hyps) 1)
                                        (car hyps)))
                                     (trigger-term
                                      (if (ffn-symb-p first-hyp 'not)
                                          (fargn first-hyp 1)
                                        first-hyp)))
                                (pprogn
                                 (observation ctx
                                              "The :TRIGGER-TERMS for the ~
                                               :FORWARD-CHAINING rule ~x0 will ~
                                               consist of the list containing ~p1."
                                              name
                                              (untranslate trigger-term nil wrld))
                                 (value (alist-to-keyword-alist
                                         seen
                                         (list :TRIGGER-TERMS
                                               (list trigger-term))))))))))
            (t (value (alist-to-keyword-alist seen nil)))))
     ((eq token :TYPE-PRESCRIPTION)
      (cond ((not (assoc-eq :TYPED-TERM seen))
             (mv-let
              (hyps concl)
              (unprettyify-tp (remove-guard-holders corollary wrld))
              (declare (ignore hyps))
              (let ((pat (cond ((ffn-symb-p concl 'implies)
                                (find-type-prescription-pat (fargn concl 2)
                                                            ens wrld))
                               (t (find-type-prescription-pat concl ens
                                                              wrld)))))
                (cond ((null pat)
                       (er soft ctx
                           "When no :TYPED-TERM component is specified for a ~
                            :TYPE-PRESCRIPTION rule class, a suitable term is ~
                            selected heuristically from the conjecture.  But ~
                            our heuristics identify no candidate term in ~p0. ~
                             Thus, ~x1 is an illegal rule class.  See :DOC ~
                            type-prescription."
                           (untranslate corollary t wrld)
                           x))
                      (t (pprogn
                          (if (ld-skip-proofsp state)
                              state
                            (observation ctx
                                         "Our heuristics choose ~p0 as the ~
                                         :TYPED-TERM."
                                         (untranslate pat nil wrld)))
                          (value (alist-to-keyword-alist
                                  seen
                                  (list :TYPED-TERM pat)))))))))
            (t (value (alist-to-keyword-alist seen nil)))))
     ((eq token :DEFINITION)
      (er-progn
       (chk-destructure-definition name corollary ctx wrld state)
       (mv-let
        (hyps equiv fn args body ttree)
        (destructure-definition corollary nil nil wrld nil)
        (declare (ignore hyps equiv ttree))

; Rockwell Addition:  In the old code, the recursivep property of a
; singly recursive function was the function name itself; the
; recursivep property of a function in a mutually-recursive clique was
; the list of all the fns in the clique.  In order to speed up the
; check to determine if there is a recursive function on the fnstack,
; I decided to make the recursivep property of a recursive fn be
; a list of all the fns in its "clique" -- possibly the singleton
; list containing just the singly recursive function name.  That way,
; if the fnstack contains a function name, I know it is non-recursive.
; In support of this change, I changed the processing of :definition
; rules.  In the old code, the translated clique of a :definition was
; made atomic (i.e., the fn name itself) if the clique was a singleton.
; For sanity, I don't do that now:  the translated clique is what
; you wrote.  This change shows up several times in the window-compare
; because in the old code we had to change back and forth between
; (fn) and fn.

        (er-let* ((clique
                   (value
                    (cond
                     ((assoc-eq :clique seen)
                      (cdr (assoc-eq :clique seen)))
                     ((ffnnamep fn body) (list fn))
                     (t nil))))
                  (controller-alist
                   (cond
                    ((assoc-eq :CONTROLLER-ALIST seen)
                     (value (cdr (assoc-eq :CONTROLLER-ALIST seen))))
                    ((null clique)
                     (value nil))
                    ((null (cdr clique))
                     (guess-controller-alist-for-definition-rule
                      clique args body ctx wrld state))
                    (t (er soft ctx
                           "We are unable to guess a :CONTROLLER-ALIST for a ~
                            :DEFINITION rule if the :CLIQUE contains more ~
                            than one function symbol.  Therefore, you must ~
                            supply a :CONTROLLER-ALIST entry for ~x0."
                           name)))))
          (cond
           ((controller-alistp clique controller-alist wrld)
            (value (alist-to-keyword-alist
                    seen
                    (append (if (assoc-eq :CLIQUE seen)
                                nil
                              (list :CLIQUE clique))
                            (if (assoc-eq :CONTROLLER-ALIST seen)
                                nil
                              (list :CONTROLLER-ALIST controller-alist))))))
           (t (er soft ctx
                  "The :CONTROLLER-ALIST of a :DEFINITION must be an alist ~
                   that maps each function symbol in the :CLIQUE to a list of ~
                   t's and nil's whose length is equal to the arity of the ~
                   function symbol. ~x0 is an inappropriate controller alist ~
                   for the ~@1.  See :DOC definition."
                  controller-alist
                  (cond ((null clique) "empty clique")
                        (t (msg ":CLIQUE consisting of ~&0" clique))))))))))
     ((eq token :INDUCTION)
      (cond ((not (assoc-eq :PATTERN seen))
             (er soft ctx
                 "The :INDUCTION rule class requires the specification of a ~
                  :PATTERN term and ~x0 contains no such entry."
                 x))
            ((not (assoc-eq :SCHEME seen))
             (er soft ctx
                 "The :INDUCTION rule class requires the specification of a ~
                  :SCHEME term and ~x0 contains no such entry."
                 x))
            (t (let* ((pat-term (cdr (assoc-eq :pattern seen)))
                      (cond-term (or (cdr (assoc-eq :condition seen)) *t*))
                      (scheme-term (cdr (assoc-eq :scheme seen)))
                      (pat-vars (all-vars pat-term))
                      (cond-vars (all-vars cond-term))
                      (scheme-vars (all-vars scheme-term)))
                 (cond
                  ((not (subsetp-eq cond-vars pat-vars))
                   (er soft ctx
                       "The variables occurring freely in the :CONDITION term ~
                        of an :INDUCTION rule class must be a subset of those ~
                        occurring freely in the :PATTERN term.  But the ~
                        condition term ~x0 mentions ~&1, which ~#1~[does~/do~] ~
                        not occur in the pattern term ~x2.  Thus the ~
                        :INDUCTION rule class specified for ~x3 is illegal."
                       cond-term
                       (reverse (set-difference-eq cond-vars pat-vars))
                       pat-term
                       name))
                  ((not (subsetp-eq scheme-vars pat-vars))
                   (er soft ctx
                       "The variables occurring freely in the :SCHEME term ~
                        of an :INDUCTION rule class must be a subset of those ~
                        occurring freely in the :PATTERN term.  But the ~
                        scheme term ~x0 mentions ~&1, which ~#1~[does~/do~] ~
                        not occur in the pattern term ~x2.  Thus the ~
                        :INDUCTION rule class specified for ~x3 is illegal."
                       scheme-term
                       (reverse (set-difference-eq scheme-vars pat-vars))
                       pat-term
                       name))
                  ((assoc-eq :condition seen)
                   (value (alist-to-keyword-alist seen nil)))
                  (t (value (alist-to-keyword-alist
                             seen
                             (list :CONDITION *t*)))))))))
     (t (value (alist-to-keyword-alist seen nil)))))
   ((assoc-eq (car alist) seen)
    (er soft ctx
        "Rule classes may not contain duplicate keys, but ~x0 occurs ~
         twice in ~x1.  See :DOC rule-classes."
        (car alist)
        x))
   (t
    (let ((assumep (or (eq (ld-skip-proofsp state) 'include-book)
                       (eq (ld-skip-proofsp state) 'include-book-with-locals)
                       (eq (ld-skip-proofsp state) 'initialize-acl2))))
      (er-let*
          ((val (case (car alist)
                  (:COROLLARY
                   (value corollary))
                  (:HINTS
                   (cond
                    ((assoc-eq :INSTRUCTIONS seen)
                     (er soft ctx
                         "It is illegal to supply both :INSTRUCTIONS ~
                         and :HINTS in a rule class.  Hence, ~x0 is ~
                         illegal.  See :DOC rule-classes."
                         x))
                    (t
                     (er-let* ((hints (if assumep
                                          (value nil)
                                        (translate-hints+
                                         (cons "Corollary of " name)
                                         (cadr alist)
                                         (default-hints wrld)
                                         ctx wrld state))))
                       (value hints)))))
                  (:INSTRUCTIONS
                   (cond
                    ((assoc-eq :HINTS seen)
                     (er soft ctx
                         "It is illegal to supply both :HINTS and ~
                          :INSTRUCTIONS in a rule class.  Hence, ~x0 is ~
                          illegal.  See :DOC rule-classes."
                         x))
                    (t
                     (er-let* ((instrs (if assumep
                                           (value nil)
                                         (translate-instructions
                                          (cons "Corollary of " name)
                                          (cadr alist)
                                          ctx wrld state))))
                       (value instrs)))))
                  (:OTF-FLG
                   (value (cadr alist)))
                  (:TRIGGER-FNS
                   (cond
                    ((eq token :FORWARD-CHAINING)
                     (er soft ctx
                         "The :FORWARD-CHAINING rule class may specify ~
                          :TRIGGER-TERMS but may not specify :TRIGGER-FNS.  ~
                          Thus, ~x0 is illegal.  See :DOC forward-chaining ~
                          and :DOC meta."
                         x))
                    ((not (eq token :META))
                     (er soft ctx
                         ":TRIGGER-FNS can only be specified for :META rules. ~
                           Thus, ~x0 is illegal.  See :DOC ~@1."
                         x
                         (symbol-name token)))
                    ((atom (cadr alist))
                     (er soft ctx
                         "The :TRIGGER-FNS component of a :META rule class ~
                          must be a non-empty true-list of function symbols.  ~
                          But ~x0 is empty.  See :DOC meta."
                         (cadr alist)))
                    ((eq (car (cadr alist)) 'quote)
                     (er soft ctx
                         "The :TRIGGER-FNS component of a :META rule class ~
                          must be a non-empty true-list of function symbols.  ~
                          You specified ~x0 for this component, but the list ~
                          is not to be quoted.~@1  See :DOC meta."
                         (cadr alist)
                         (cond ((and (consp (cdr (cadr alist)))
                                     (symbol-listp (cadr (cadr alist)))
                                     (null (cddr (cadr alist))))
                                (msg "  Perhaps you intended ~x0 instead."
                                     (cadr (cadr alist))))
                               (t ""))))
                    (t (mv-let (flg lst)
                               (eliminate-macro-aliases (cadr alist)
                                                        (macro-aliases wrld)
                                                        wrld)
                               (cond ((eq flg :error)
                                      (er soft ctx
                                          "The :TRIGGER-FNS component of a ~
                                           :META rule class must be a ~
                                           non-empty true-list of function ~
                                           symbols, but ~x0 ~@1.  See :DOC ~
                                           meta."
                                          (cadr alist) lst))
                                     (t (value lst)))))))
                  (:TRIGGER-TERMS
                   (cond
                    ((eq token :META)
                     (er soft ctx
                         "The :META rule class may specify :TRIGGER-FNS but ~
                          may not specify :TRIGGER-TERMS.  Thus, ~x0 is ~
                          illegal.  See :DOC meta and :DOC forward-chaining."
                         x))
                    ((not (true-listp (cadr alist)))
                     (er soft ctx
                         "The :TRIGGER-TERMS must be a list true list.  Thus ~
                          the rule class ~x0 proposed for ~x1 is illegal."
                         x name))
                    ((eq token :LINEAR)

; We allow but do not require :TRIGGER-TERMS to be provided for :LINEAR rules.
; The whole idea of :TRIGGER-TERMS specified at the rule-class level is a
; little jarring in the case of linear rules because we generate a linear rule
; for each unprettyified branch through the COROLLARY of the rule class and the
; appropriate trigger terms for one branch may not be those for another.
; Nevertheless, when :TRIGGER-TERMS is provided, we store the rule for every
; branch under every given trigger.  You get what you ask for.  The moral is
; that if you are going to provide :TRIGGER-TERMS you would be well-advised to
; provide a corollary with only one branch.

                     (er-let*
                         ((terms (translate-term-lst (cadr alist)
                                                     t t t ctx wrld state)))
                       (cond
                        ((null terms)
                         (er soft ctx
                             "For the :LINEAR rule ~x0 you specified an empty ~
                              list of :TRIGGER-TERMS.  This is illegal.  If ~
                              you wish to cause ACL2 to compute the trigger ~
                              terms, omit the :TRIGGER-TERMS field entirely.  ~
                              See :DOC linear."
                             name))
                        (t
                         (let ((terms (remove-guard-holders-lst terms wrld)))
                           (er-progn
                            (chk-legal-linear-trigger-terms
                             terms
                             (unprettyify
                              (remove-guard-holders corollary wrld))
                             name ctx state)
                            (value terms)))))))
                    ((eq token :FORWARD-CHAINING)
                     (er-let*
                         ((terms (translate-term-lst (cadr alist)
                                                     t t t ctx wrld state)))
                       (cond ((null terms)
                              (er soft ctx
                                  ":FORWARD-CHAINING rules must have at least ~
                                   one trigger.  Your rule class, ~x0, ~
                                   specifies none.  See :DOC forward-chaining."
                                  x))
                             (t (value
                                 (remove-guard-holders-lst terms wrld))))))
                    (t
                     (er soft ctx
                         ":TRIGGER-TERMS can only be specified for ~
                          :FORWARD-CHAINING and :LINEAR rules.  Thus, ~x0 is ~
                          illegal.  See :DOC ~@1."
                         x
                         (symbol-name token)))))
                  (:WELL-FORMEDNESS-GUARANTEE
                   (cond
                    ((and (not (eq token :META))
                          (not (eq token :CLAUSE-PROCESSOR)))
                     (er soft ctx
                         "Only :META and :CLAUSE-PROCESSOR rule classes are ~
                          permitted to have a :WELL-FORMEDNESS-GUARANTEE ~
                          component.  Thus, ~x0 is illegal.  See :DOC ~
                          well-formedness-guarantee."
                         x))
                    (t (er-let*
                         ((well-formedness-guarantee
                           (translate-well-formedness-guarantee
                            token
                            (cadr alist)
                            name corollary ctx wrld state)))

; well-formedness-guarantee is of the form ((name fn thm-name1 hyp-fn
; thm-name2) .  alist), where hyp-fn and thm-name2 are omitted if there is no
; hyp-fn.  Alist is the combined arity alist of both logic-termp theorems.
; We next check that all of these functions have appropriate arities in the
; current world and that none are currently on forbidden-fns.

                         (let* ( ; (fn (nth 1 (car well-formedness-guarantee)))
                                (thm-name1
                                 (nth 2 (car well-formedness-guarantee)))
                                (hyp-fn
                                 (nth 3 (car well-formedness-guarantee))) ; may be nil
                                (thm-name2
                                 (nth 4 (car well-formedness-guarantee))) ; may be nil
                                (alist
                                 (cdr well-formedness-guarantee))
                                (bad-arity-info (collect-bad-fn-arity-info
                                                 alist wrld nil nil))
                                (bad-arity-alist (car bad-arity-info))
                                (non-logic-fns (cdr bad-arity-info))
                                (forbidden-fns
                                 (intersection-eq (strip-cars alist)
                                                  (forbidden-fns wrld state))))
                           (cond
                            (bad-arity-alist
                             (er soft ctx
                                 "~x0 rule ~x1 is inadmissible because its ~
                                  :WELL-FORMEDNESS-GUARANTEE ~
                                  theorem~#2~[~/s~], named ~&2, ~
                                  ~#2~[is~/are~] incompatible with the ~
                                  current world.  In particular, the ~
                                  ~#2~[theorem makes~/theorems make~] invalid ~
                                  assumptions about the arities of one or ~
                                  more function symbols possibly introduced ~
                                  by the ~s3.  The following alist ~
                                  shows assumed arities that are different ~
                                  from the actual arities of those symbols in ~
                                  the current world: ~X45."
                                 token
                                 name
                                 (if hyp-fn
                                     (list thm-name1 thm-name2)
                                     (list thm-name1))
                                 (if (eq token :META)
                                     "metafunction"
                                   "clause-processor")
                                 bad-arity-alist
                                 nil))
                            (non-logic-fns
                             (er soft ctx
                                 "~x0 rule ~x1 is inadmissible because its ~
                                  :WELL-FORMEDNESS-GUARANTEE ~
                                  theorem~#2~[~/s~], named ~&2, ~
                                  ~#2~[is~/are~] incompatible with the ~
                                  current world.  In particular, the ~
                                  ~#2~[theorem assumes~/theorems assume~] ~
                                  that relevant functions are in :logic mode, ~
                                  but :program mode function symbol~#3~[ ~&3 ~
                                  is~/s ~&3 are~] perhaps introduced by the ~
                                  ~s4, ~&3."
                                 token
                                 name
                                 (if hyp-fn
                                     (list thm-name1 thm-name2)
                                   (list thm-name1))
                                 non-logic-fns
                                 (if (eq token :META)
                                     "metafunction"
                                   "clause-processor")))
                            (forbidden-fns
                             (er soft ctx
                                 "~x0 rule ~x1 is inadmissible because its ~
                                  well-formedness theorem~#2~[~/s~], named ~
                                  ~&2, ~#2~[is~/are~] incompatible with the ~
                                  current world.  In particular, judging by ~
                                  the ARITIES-OKP ~
                                  ~#2~[hypothesis~/hypotheses~] of the ~
                                  theorem~#2~[~/s~], the specified ~s3 may ~
                                  introduce one or more functions that are ~
                                  currently forbidden, to wit ~&4.  See :DOC ~
                                  set-skip-meta-termp-checks and :DOC ~
                                  well-formedness-guarantee."
                                 token
                                 name
                                 (if hyp-fn
                                     (list thm-name1 thm-name2)
                                     (list thm-name1))
                                 (if (eq token :META)
                                     "metafunction"
                                   "clause-processor")
                                 forbidden-fns))
                            (t (value well-formedness-guarantee))))))))
                  (:TYPED-TERM
                   (cond
                    ((not (eq token :TYPE-PRESCRIPTION))
                     (er soft ctx
                         "Only :TYPE-PRESCRIPTION rule classes are permitted ~
                          to have a :TYPED-TERM component.  Thus, ~x0 is ~
                          illegal.  See :DOC ~@1."
                         x
                         (symbol-name token)))
                    (t (er-let* ((term (translate (cadr alist)
                                                  t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
                         (value term)))))
                  (:BACKCHAIN-LIMIT-LST
                   (let ((hyps-concl-pairs

; We could call unprettyify in all cases below (not always with
; remove-guard-holders, though).  But it seems more appropriate not to rely on
; unprettyify to handle the very specific legal forms of meta rules.

; Warning: Keep this in sync with destructure-type-prescription.

                          (case token
                            (:meta
                             (case-match corollary
                               (('implies hyp concl)
                                (list (cons (list hyp) concl)))
                               (& (list (cons nil corollary)))))
                            (:type-prescription
                             (mv-let
                              (hyps concl)
                              (unprettyify-tp
                               (remove-guard-holders corollary wrld))
                              (list (cons hyps concl))))
                            (otherwise
                             (unprettyify
                              (remove-guard-holders corollary wrld))))))
                     (cond
                      ((not (member-eq token
                                       '(:REWRITE :META :LINEAR
                                                  :TYPE-PRESCRIPTION)))
                       (er soft ctx
                           "The rule-class ~@0 is not permitted to have a ~
                            :BACKCHAIN-LIMIT-LST component.  Hence, ~x1 is ~
                            illegal.  See :DOC ~@0."
                           (symbol-name token) x))
                      ((not (equal (length (remove-duplicates-equal
                                            (strip-cars hyps-concl-pairs)))
                                   1))
                       (er soft ctx
                           "We do not allow you to specify the ~
                            :BACKCHAIN-LIMIT-LST when more than one rule is ~
                            produced from the corollary and at least two such ~
                            rules have different hypothesis lists.  You ~
                            should split the corollary of ~x0 into parts and ~
                            specify a limit for each."
                           x))
                      (t
                       (let ((hyps (car (car hyps-concl-pairs))))
                         (cond
                          ((null hyps)
                           (er soft ctx
                               "There are no hypotheses, so ~
                                :BACKCHAIN-LIMIT-LST makes no sense.  See ~
                                :DOC RULE-CLASSES."))
                          ((null (cadr alist))
                           (value nil))
                          ((and (integerp (cadr alist))
                                (<= 0 (cadr alist)))
                           (cond ((eq token :META)
                                  (value (cadr alist)))
                                 (t
                                  (value (make-list
                                          (length hyps)
                                          :initial-element (cadr alist))))))
                          ((eq token :META)
                           (er soft ctx
                               "The legal values of :BACKCHAIN-LIMIT-LST for ~
                                rules of class :META are nil or a ~
                                non-negative integer.  See :DOC RULE-CLASSES."))
                          ((and (backchain-limit-listp (cadr alist))
                                (eql (length (cadr alist)) (length hyps)))
                           (value (cadr alist)))
                          (t
                           (er soft ctx
                               "The legal values of :BACKCHAIN-LIMIT-LST are ~
                                nil, a non-negative integer, or a list of ~
                                these of the same length as the flattened ~
                                hypotheses.  In this case the list of ~
                                flattened hypotheses, of length ~x0, is:~%  ~
                                ~x1.~%See :DOC RULE-CLASSES."
                               (length hyps) hyps))))))))
                  (:MATCH-FREE
                   (cond
                    ((not (member-eq token '(:REWRITE :LINEAR :FORWARD-CHAINING)))
                     (er soft ctx
                         "Only :REWRITE, :FORWARD-CHAINING, and :LINEAR rule ~
                          classes are permitted to have a :MATCH-FREE ~
                          component.  Thus, ~x0 is illegal.  See :DOC ~
                          free-variables."
                         x))
                    ((not (member-eq (cadr alist) '(:ALL :ONCE)))
                     (er soft ctx
                         "The legal values of :MATCH-FREE are :ALL and :ONCE. ~
                          Thus, ~x0 is illegal.  See :DOC free-variables."
                         x))
                    (t (value (cadr alist)))))
                  (:CLIQUE
                   (cond
                    ((not (eq token :DEFINITION))
                     (er soft ctx
                         "Only :DEFINITION rule classes are permitted to have ~
                          a :CLIQUE component.  Thus, ~x0 is illegal.  See ~
                          :DOC ~@1."
                         x
                         (symbol-name token)))
                    (t (er-progn
                        (chk-destructure-definition name corollary ctx wrld state)
                        (mv-let
                         (hyps equiv fn args body ttree)
                         (destructure-definition corollary nil nil wrld nil)
                         (declare (ignore hyps equiv args ttree))
                         (let ((clique
                                (cond ((null (cadr alist)) nil)
                                      ((atom (cadr alist)) (list (cadr alist)))
                                      (t (cadr alist)))))
                           (cond ((not (and (all-function-symbolps clique wrld)
                                            (no-duplicatesp-equal clique)))
                                  (mv-let
                                   (flg lst)
                                   (eliminate-macro-aliases (cadr alist)
                                                            (macro-aliases wrld)
                                                            wrld)
                                   (er soft ctx
                                       "The :CLIQUE of a :DEFINITION must be ~
                                        a truelist of function symbols ~
                                        (containing no duplications) or else ~
                                        a single function symbol.  ~x0 is ~
                                        neither.~@1  See :DOC definition."
                                       (cadr alist)
                                       (cond ((eq flg :error) "")
                                             (t (msg "  Note that it is ~
                                                      illegal to use ~v0 ~
                                                      here, because we ~
                                                      require function ~
                                                      symbols, not merely ~
                                                      macros that are aliases ~
                                                      for function symbols ~
                                                      (see :DOC ~
                                                      macro-aliases-table)."
                                                     (set-difference-equal
                                                      (cadr alist)
                                                      lst)))))))
                                 ((and (ffnnamep fn body)
                                       (not (member-eq fn clique)))
                                  (er soft ctx
                                      "The :CLIQUE of a :DEFINITION must ~
                                       contain the defined function, ~x0, if ~
                                       the body calls the function.  See :DOC ~
                                       definition."
                                      fn))
                                 ((and clique
                                       (not (member-eq fn clique)))
                                  (er soft ctx
                                      "The :CLIQUE of a :DEFINITION, when ~
                                       non-nil, must contain the function ~
                                       defined.  ~x0 does not contain ~x1.  ~
                                       See :DOC definition."
                                      (cadr alist)
                                      fn))
                                 (t (value clique)))))))))
                  (:CONTROLLER-ALIST
                   (cond
                    ((not (eq token :DEFINITION))
                     (er soft ctx
                         "Only :DEFINITION rule classes are permitted to have ~
                          a :CONTROLLER-ALIST component.  Thus, ~x0 is ~
                          illegal.  See :DOC ~@1."
                         x
                         (symbol-name token)))
                    (t

; Actually, the rules on a controller alist involve the clique in question.
; We don't necessarily know the clique yet.  We wait until the end, when
; :CLIQUE will have been processed, to check that the following value is ok.

                     (value (cadr alist)))))
                  (:INSTALL-BODY
                   (cond
                    ((not (eq token :DEFINITION))
                     (er soft ctx
                         "Only :DEFINITION rule classes are permitted to have ~
                          an :INSTALL-BODY component.  Thus, ~x0 is illegal.  ~
                          See :DOC ~@1."
                         x
                         (symbol-name token)))
                    ((not (member-eq (cadr alist)
                                     '(t nil :NORMALIZE)))
                     (er soft ctx
                         "The :INSTALL-BODY component of a  :DEFINITION rule ~
                          class must have one of the values ~v0.  Thus, ~x1 ~
                          is illegal.  See :DOC ~@2."
                         '(t nil :NORMALIZE)
                         (cadr alist)
                         (symbol-name token)))
                    (t
                     (value (cadr alist)))))
                  (:LOOP-STOPPER
                   (cond
                    ((not (or (eq token :REWRITE)
                              (eq token :REWRITE-QUOTED-CONSTANT)))
                     (er soft ctx
                         "Only :REWRITE and :REWRITE-QUOTED-CONSTANT rule ~
                          classes are permitted to have a :LOOP-STOPPER ~
                          component.  Thus, ~x0 is illegal.  See :DOC ~
                          rule-classes."
                         x))
                    (t (mv-let
                        (flg loop-stopper-alist)
                        (fix-loop-stopper-alist
                         (cadr alist) (macro-aliases wrld) wrld)
                        (cond
                         ((eq flg :error)
                          (er soft ctx
                              "The :LOOP-STOPPER for a rule class must be a ~
                               list whose elements have the form (variable1 ~
                               variable2 . fns), where variable1 and ~
                               variable2 are distinct variables and fns is a ~
                               list of function symbols (or macro-aliases for ~
                               function symbols), but ~x0 does not have this ~
                               form.  Thus, ~x1 is illegal.  See :DOC ~
                               rule-classes."
                              (cadr alist)
                              x))
                         ((not (subsetp-eq
                                (union-eq (strip-cars loop-stopper-alist)
                                          (strip-cadrs loop-stopper-alist))
                                (all-vars corollary)))
                          (let ((bad-vars
                                 (set-difference-eq
                                  (union-eq (strip-cars loop-stopper-alist)
                                            (strip-cadrs loop-stopper-alist))
                                  (all-vars corollary))))
                            (er soft ctx
                                "The variables from elements (variable1 ~
                                 variable2 . fns) of a :LOOP-STOPPER ~
                                 specified for a rule class must all appear ~
                                 in the :COROLLARY theorem for that rule ~
                                 class.  However, the ~#0~[variables ~&1 ~
                                 do~/variable ~&1 does~] not appear in ~p2.  ~
                                 Thus, ~x3 is illegal.  See :DOC rule-classes."
                                (if (cdr bad-vars) 0 1)
                                bad-vars
                                (untranslate corollary t wrld)
                                x)))
                         (t
                          (value loop-stopper-alist)))))))
                  (:PATTERN
                   (cond
                    ((not (eq token :INDUCTION))
                     (er soft ctx
                         "Only :INDUCTION rule classes are permitted to have ~
                          a :PATTERN component.  Thus, ~x0 is illegal.  See ~
                          :DOC ~@1."
                         x
                         (symbol-name token)))
                    (t (er-let*
                           ((term (translate (cadr alist) t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
                         (cond
                          ((or (variablep term)
                               (fquotep term)
                               (flambdap (ffn-symb term)))
                           (er soft ctx
                               "The :PATTERN term of an :INDUCTION rule class ~
                                may not be a variable symbol, constant, or ~
                                the application of a lambda expression.  Thus ~
                                ~x0 is illegal.  See :DOC induction."
                               x))
                          (t (value term)))))))
                  (:CONDITION
                   (cond
                    ((not (eq token :INDUCTION))
                     (er soft ctx
                         "Only :INDUCTION rule classes are permitted to have ~
                          a :CONDITION component.  Thus, ~x0 is illegal.  See ~
                          :DOC ~@1."
                         x
                         (symbol-name token)))
                    (t (er-let*
                           ((term (translate (cadr alist) t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
                         (value term)))))
                  (:SCHEME
                   (cond
                    ((not (eq token :INDUCTION))
                     (er soft ctx
                         "Only :INDUCTION rule classes are permitted to have ~
                          a :SCHEME component.  Thus, ~x0 is illegal.  See ~
                          :DOC ~@1."
                         x
                         (symbol-name token)))
                    (t (er-let*
                           ((term (translate (cadr alist) t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
                         (cond
                          ((or (variablep term)
                               (fquotep term)
                               (flambdap (ffn-symb term)))
                           (er soft ctx
                               "The :SCHEME term of an :INDUCTION rule class ~
                                may not be a variable symbol, constant, or ~
                                the application of a lambda expression.  Thus ~
                                ~x0 is illegal.  See :DOC induction."
                               x))
                          ((not (or (getpropc (ffn-symb term)
                                              'induction-machine
                                              nil wrld)
                                    (getpropc (ffn-symb term) 'induction-rules
                                              nil wrld)))
                           (er soft ctx
                               "The function symbol of the :SCHEME term of an ~
                                :INDUCTION rule class must, at least ~
                                sometimes, suggest an induction and ~x0 does ~
                                not.  See :DOC induction."
                               (ffn-symb term)))
                          (t (value term)))))))
                  (:TYPE-SET
                   (cond
                    ((not (eq token :TYPE-SET-INVERTER))
                     (er soft ctx
                         "Only :TYPE-SET-INVERTER rule classes are permitted ~
                          to have a :TYPE-SET component.  Thus ~x0 is ~
                          illegal.  See :DOC type-set-inverter."
                         x))
                    ((not (and (integerp (cadr alist))
                               (<= *min-type-set* (cadr alist))
                               (<= (cadr alist) *max-type-set*)))
                     (er soft ctx
                         "The :TYPE-SET of a :TYPE-SET-INVERTER rule must be ~
                          a type-set, i.e., an integer between ~x0 and ~x1, ~
                          inclusive.  ~x2 is not a type-set.  See :DOC ~
                          type-set and :DOC type-set-inverter."
                         *min-type-set*
                         *max-type-set*
                         (cadr alist)))
                    (t (value (cadr alist)))))
                  (otherwise
                   (er soft ctx
                       "The key ~x0 is unrecognized as a rule class ~
                        component.  See :DOC rule-classes."
                       (car alist))))))
        (translate-rule-class-alist token (cddr alist)
                                    (cons (cons (car alist) val) seen)
                                    corollary
                                    name x ctx ens wrld state))))))

(defun translate-rule-class1 (class tflg name x ctx ens wrld state)

; Class is a candidate rule class.  We know it is of the form (:key
; :key1 val1 ... :keyn valn).  We know that among the :keyi is
; :COROLLARY and that if tflg is on then the :COROLLARY value has
; already been translated.  Make sure class is syntactically legal and
; translate all the vals in it.  X is the user's original
; specification of this class and is used only in error messages.
; Name is the name of the event for which this class is being
; translated.

; The binding below exhibits all the rule tokens and identifies the
; special additional keywords allowed (or required) by them.  All of
; the tokens allow the keywords :COROLLARY, :HINTS, :INSTRUCTIONS, and
; :OTF-FLG.

; Note: The "definitive" description of the fields in our rule classes is to be
; found in :DOC rule-classes.  It is hygienic to compare periodically the
; setting below to the form described there.

  (let ((rule-tokens '(:REWRITE
                       :REWRITE-QUOTED-CONSTANT
                       :LINEAR            ; :TRIGGER-TERMS (optional)
                       :WELL-FOUNDED-RELATION
                       :BUILT-IN-CLAUSE
                       :COMPOUND-RECOGNIZER
                       :ELIM
                       :GENERALIZE
                       :META              ; :TRIGGER-FNS
                       :FORWARD-CHAINING  ; :TRIGGER-TERMS (optional)
                       :EQUIVALENCE
                       :REFINEMENT
                       :CONGRUENCE
                       :TYPE-PRESCRIPTION ; :TYPED-TERM (optional)
                       :DEFINITION        ; :CLIQUE and :CONTROLLER-ALIST
                       :INDUCTION         ; :PATTERN, :CONDITION (optional),
                                          ;   and :SCHEME
                       :TYPE-SET-INVERTER ; :TYPE-SET (optional)
                       :CLAUSE-PROCESSOR
                       :TAU-SYSTEM
                       )))
  (cond
   ((not (member-eq (car class) rule-tokens))
    (er soft ctx
        "~x0 is not one of the known rule tokens, ~&1.  See :DOC ~
         rule-classes."
        (car class)
        rule-tokens))
   (t (er-let*
       ((corollary
         (cond (tflg (value (cadr (assoc-keyword :corollary (cdr class)))))
               (t (translate (cadr (assoc-keyword :corollary (cdr class)))
                             t t t ctx wrld state))))
; known-stobjs = t (stobjs-out = t)
        (alist
         (translate-rule-class-alist (car class)
                                     (cdr class)
                                     nil
                                     corollary
                                     name x ctx ens wrld state)))
       (value (cons (car class) alist)))))))

(defun reason-for-non-keyword-value-listp (x)
  (cond
   ((atom x)
    (cond
     ((null x)
      (er hard 'reason-for-non-keyword-value-listp
          "Uh oh, it was a keyword-value-listp after all!"))
     (t
      (msg "there is a non-nil final cdr of ~x0"
           x))))
   ((not (keywordp (car x)))
    (msg "we found a non-keyword, ~x0, where a keyword was expected"
         (car x)))
   ((atom (cdr x))
    (msg "the value corresponding to the final key of ~x0 was missing"
         (car x)))
   (t
    (reason-for-non-keyword-value-listp (cddr x)))))

(defun translate-rule-class (name x thm ctx ens wrld state)

; Warning: We depend on the property that the resulting :corollary field is
; independent of context.  See redundant-theoremp.

; X is an untranslated rule class.  For example, x may be :REWRITE or (:META
; :TRIGGER-FNS (fn1 ... fnk)) or even (:REWRITE :COROLLARY (IMPLIES p q) :HINTS
; ...).  We either translate x into a "fully elaborated" rule class or else
; cause an error.  A fully elaborated rule class starts with one of the rule
; class keywords, token, followed by an alternating keyword/value list.  Every
; fully elaborated class has a :COROLLARY component.  In addition, every :META
; class has a :TRIGGER-FNS component, every :FORWARD-CHAINING class has a
; :TRIGGER-TERMS component, and every :TYPE-PRESCRIPTION has a :TYPED-TERM
; component.  No keyword is bound twice in the list and the values associated
; with each keyword is syntactically correct in a local sense, e.g., alleged
; function symbols are really function symbols, alleged terms are translated
; terms, alleged hints are translated hints, etc.  We do not make the non-local
; checks, such as that the :COROLLARY of a :TYPE-PRESCRIPTION rule actually
; prescribes the type of the :TYPED-TERM.  Those checks are made by the
; individual acceptability checkers.

  (let ((er-string
         "The object ~x0 is not a rule class.  Rule classes are either certain ~
          keywords, e.g., :REWRITE, or lists of the form (:rule-token :key1 ~
          val1 :key2 val2 ...), as in (:REWRITE :COROLLARY term :HINTS ...).  ~
          In your case, ~@1.  See :DOC rule-classes."))
    (cond
     ((or (keywordp x)
          (and (consp x)
               (keywordp (car x))
               (keyword-value-listp (cdr x))))
      (translate-rule-class1

; Note that we observe the requirement discussed in the comment (warning) at the
; top of this definition, about the :corollary field being independent of
; context.

       (cond ((symbolp x) (list x :COROLLARY thm))
             ((assoc-keyword :COROLLARY (cdr x)) x)
             (t `(,(car x) :COROLLARY ,thm ,@(cdr x))))
       (or (symbolp x)
           (not (assoc-keyword :COROLLARY (cdr x))))
       name x ctx ens wrld state))
     ((not (consp x))
      (er soft ctx
          er-string
          x "the rule class is a non-keyword atom"))
     ((not (keywordp (car x)))
      (er soft ctx
          er-string
          x
          "the rule class starts with the non-keyword ~x2"
          (car x)))
     (t
      (er soft ctx er-string
          x (reason-for-non-keyword-value-listp (cdr x)))))))

(defun translate-rule-classes1 (name classes thm ctx ens wrld state)

; We make sure that classes is a true list of legal rule classes.  We
; translate the terms that occur in the classes and return the
; translated list of classes, i.e., a list of fully elaborated rule
; classes.

  (cond
   ((atom classes)
    (cond ((null classes) (value nil))
          (t (er soft ctx
                 "The list of rule classes is supposed to a true ~
                  list, but your list ends in ~x0.  See :DOC ~
                  rule-classes."
                 classes))))
   (t (er-let*
       ((class (translate-rule-class name (car classes) thm ctx ens wrld
                                     state))
        (rst (translate-rule-classes1 name (cdr classes) thm ctx ens wrld
                                      state)))
       (value (cons class rst))))))

(defun translate-rule-classes (name classes thm ctx ens wrld state)

; We adopt the convention that if a non-nil atomic classes is provided
; it is understood as the singleton list containing that atom.  Thus,
; one is permitted to write
;   :rule-classes :elim
; and have it understood as
;   :rule-classes (:elim).
; However, it is not possible to so abbreviate non-atomic classes.
; That is, one might expect to be able to write:
;   :rule-classes (:TYPE-PRESCRIPTION :TYPED-TERM (foo a b))
; but one would be disappointed if one did.  Any non-atomic value for
; classes is treated as though it were a list of rule classes.  The effect
; intended by the above example can only be achieved by writing
;   :rule-classes ((:TYPE-PRESCRIPTION :TYPED-TERM (foo a b))).

  (translate-rule-classes1 name
                           (cond ((null classes) nil)
                                 ((atom classes) (list classes))
                                 (t classes))
                           thm
                           ctx ens wrld state))

; We now turn our attention to the function that checks that a given
; term generates acceptable rules in all of a specified set of
; classes.  The basic function is the one below, that takes a class
; token and calls the appropriate acceptability checker.  In all of
; the code below we can assume that "class" is one of the objects
; produced by translate-rule-class above and "classes" is a true list
; of such objects.

(defun chk-acceptable-x-rule (name class ctx ens wrld state)

; We check that the :COROLLARY term of class can be used as a rule of
; the class specified.  Class is a fully elaborated, translated rule
; class.  This function is just a big switch.  Each exit subroutine
; returns a ttree justifying the claim that class describes a rule.

  (let ((term (cadr (assoc-keyword :COROLLARY (cdr class)))))
    (case (car class)
          (:REWRITE
           (chk-acceptable-rewrite-rule nil ; = qc-flg
                                        name
                                        (cadr (assoc-keyword :MATCH-FREE
                                                             (cdr class)))
                                        (cadr (assoc-keyword :LOOP-STOPPER
                                                             (cdr class)))
                                        term ctx ens wrld state))
          (:REWRITE-QUOTED-CONSTANT
           (chk-acceptable-rewrite-rule t ; = qc-flg
                                        name
                                        (cadr (assoc-keyword :MATCH-FREE
                                                             (cdr class)))
                                        (cadr (assoc-keyword :LOOP-STOPPER
                                                             (cdr class)))
                                        term ctx ens wrld state))
          (:LINEAR
           (chk-acceptable-linear-rule
            name
            (cadr (assoc-keyword :MATCH-FREE (cdr class)))
            (cadr (assoc-keyword :TRIGGER-TERMS (cdr class)))
            term ctx ens wrld state))
          (:WELL-FOUNDED-RELATION
           (chk-acceptable-well-founded-relation-rule name term ctx wrld state))
          (:BUILT-IN-CLAUSE
           (chk-acceptable-built-in-clause-rule name term ctx wrld state))
          (:COMPOUND-RECOGNIZER
           (chk-acceptable-compound-recognizer-rule name term ctx ens wrld
                                                    state))
          (:ELIM
           (chk-acceptable-elim-rule name term ctx wrld state))
          (:GENERALIZE
           (chk-acceptable-generalize-rule name term ctx wrld state))
          (:EQUIVALENCE
           (chk-acceptable-equivalence-rule name term ctx wrld state))
          (:CONGRUENCE
           (chk-acceptable-congruence-rule name term ctx wrld state))
          (:REFINEMENT
           (chk-acceptable-refinement-rule name term ctx wrld state))
          (:META

; We already know that the :TRIGGER-FNS of a :META rule class are all function
; symbols.  However, we need them in order to produce warning messages when
; metafunctions produce non-termps.  See chk-acceptable-meta-rule.

           (chk-acceptable-meta-rule
            name
            (cadr (assoc-keyword :TRIGGER-FNS (cdr class)))
            term ctx ens wrld state))
          (:CLAUSE-PROCESSOR
           (chk-acceptable-clause-processor-rule name term ctx wrld state))
          (:FORWARD-CHAINING
           (chk-acceptable-forward-chaining-rule
            name
            (cadr (assoc-keyword :MATCH-FREE (cdr class)))
            (cadr (assoc-keyword :TRIGGER-TERMS (cdr class)))
            term ctx ens wrld state))
          (:TYPE-PRESCRIPTION
           (chk-acceptable-type-prescription-rule
            name
            (cadr (assoc-keyword :TYPED-TERM (cdr class)))
            term
            (assoc-keyword :BACKCHAIN-LIMIT-LST (cdr class))
            ctx ens wrld state))
          (:DEFINITION
           (chk-acceptable-definition-rule
            name
            (cadr (assoc-keyword :CLIQUE (cdr class)))
            (cadr (assoc-keyword :CONTROLLER-ALIST (cdr class)))
            (assoc-keyword :INSTALL-BODY (cdr class))
            term ctx ens wrld state))
          (:INDUCTION
           (chk-acceptable-induction-rule name term ctx wrld state))
          (:TYPE-SET-INVERTER
           (chk-acceptable-type-set-inverter-rule
            name
            (cadr (assoc-keyword :TYPE-SET (cdr class)))
            term ctx ens wrld state))
          (:TAU-SYSTEM
           (chk-acceptable-tau-rule name term ctx wrld state))
          (otherwise
           (value (er hard ctx
                      "Unrecognized rule class token ~x0 in CHK-ACCEPTABLE-X-RULE."
                      (car class)))))))

(defun chk-acceptable-x-rules (name classes ctx ens wrld state)

; Classes has already been translated and hence is known to be a true
; list of fully elaborated rule classes.  Each class has a :COROLLARY
; term and we check that the term can be used as a rule of the
; indicated class.  We return a tag-tree supporting the claim.

  (cond ((null classes) (value nil))
        (t (er-let*
            ((ttree1 (chk-acceptable-x-rule name (car classes) ctx ens wrld
                                            state))
             (ttree  (chk-acceptable-x-rules name (cdr classes) ctx ens wrld
                                             state)))
            (value (cons-tag-trees ttree1 ttree))))))

(defun collect-keys-eq (sym-list alist)
  (cond ((endp alist) nil)
        ((member-eq (caar alist) sym-list)
         (cons (car alist) (collect-keys-eq sym-list (cdr alist))))
        (t (collect-keys-eq sym-list (cdr alist)))))

; So here is how you check that it is legal to add the rules from a
; thm term, named name, in all of the classes classes.

(defun chk-acceptable-rules (name classes ctx ens wrld state)

; The classes have already been translated, so we do not need to worry about
; unrecognized classes.  Each class contains a :COROLLARY which is a translated
; term.  We check that the :COROLLARY term can be used as a rule of the class
; indicated.  We either cause an error or return a ttree justifying whatever
; pre/post-processing is done to store the rules.  If we are under include-book
; or the second pass of encapsulate, we skip the checks.

  (let ((classes
         (cond ((or (eq (ld-skip-proofsp state) 'include-book)
                    (eq (ld-skip-proofsp state) 'include-book-with-locals))

; We avoid the check for :REWRITE rules, tolerating a rare hard error as a
; result.  See the comment just above the hard error in add-rewrite-rule2.

; We need to check :meta and :clause-processor rules even when skipping proofs.
; Below is a slight modification of a proof of nil sent by Dave Greve and Jared
; Davis, which is no longer possible after this check (namely: meta-foo-rule
; fails).  In this example, the :meta rule is not supported by an evaluator in
; the second pass through the encapsulate.  The Essay on Correctness of Meta
; Reasoning makes it clear that we need the evaluator axioms to justify the
; application of a :meta or :clause-processor rule.

;  (defun meta-foo (term)
;    (if (and (consp term)
;             (equal (car term) 'foo))
;        *nil*
;      term))
;
;  (encapsulate
;   (((evx * *) => *)
;    ((evx-list * *) => *)
;    ((foo *) => *))
;
;   (local
;    (defun foo (x)
;      (declare (ignore x))
;      nil))
;
;   (local
;    (defevaluator evx evx-list
;      ((foo x))))
;
;   (defthm meta-foo-rule
;     (equal (evx term a)
;            (evx (meta-foo term) a))
;     :rule-classes ((:meta :trigger-fns (foo)))))
;
;  (defun goo (x)
;    (declare (ignore x))
;    t)
;
;  (defthm qed
;    (not (goo x))
;    :hints (("goal" :use (:functional-instance (:theorem (not (foo x)))
;                                               (foo goo))
;             :in-theory (disable
;                         goo
;                         (:type-prescription goo)
;                         (goo))))
;    :rule-classes nil)
;
;  (defthm contradiction
;    nil
;    :hints (("goal" :use qed :in-theory (enable goo)))
;    :rule-classes nil)

; We also check for :congruence rules even when skipping proofs.  Without this
; check we can get a hard error during the local compatibility check of
; certify-book.  Those hard errors appear to be rare (probably the first one
; was reported by Nathan Guermond in October, 2018), but :congruence rules are
; much less common than :rewrite rules, so we prefer to do the extra check here
; so that a nice, soft error is reported.  Without this check we can get a hard
; (implementation) error after a failed call of
; interpret-term-as-congruence-rule in add-congruence-rule.

                (collect-keys-eq '(:meta :clause-processor :congruence)
                                 classes))
               (t classes))))
    (cond
     ((null classes) ; optimization
      (value nil))
     (t
      (er-let* ((ttree1 (chk-acceptable-x-rules name classes ctx ens wrld
                                                state)))

; At one time we accumulated ttree1 into state.  But that caused rules to be
; reported during a failed proof that are not actually used in the proof.  It
; is better to let install-event take care of accumulating this ttree (as part
; of the final ttree) into state, so that users can see the relevant
; explanatory message, "The storage of ... depends upon ...".

               (er-progn
                (chk-assumption-free-ttree ttree1 ctx state)
                (value ttree1)))))))

; We now turn to actually adding the rules generated.  The development is
; exactly analogous to the checking above.

(defun add-x-rule (rune nume class ens wrld state)

; We add the rules of class class derived from term.

; WARNING: If this function is changed, change info-for-x-rules (and/or
; subsidiaries) and find-rules-of-rune2.

; WARNING:  If you add a new type of rule record, update access-x-rule-rune.

  (let ((term (cadr (assoc-keyword :COROLLARY (cdr class)))))
    (case (car class)
          (:REWRITE
           (add-rewrite-rule nil ; qc-flg
                             rune nume
                             (assoc-keyword :LOOP-STOPPER (cdr class))
                             term
                             (assoc-keyword :BACKCHAIN-LIMIT-LST (cdr class))
                             (cadr (assoc-keyword :MATCH-FREE (cdr class)))
                             ens
                             wrld))
          (:REWRITE-QUOTED-CONSTANT
           (add-rewrite-rule t ; qc-flg
                             rune nume
                             (assoc-keyword :LOOP-STOPPER (cdr class))
                             term
                             (assoc-keyword :BACKCHAIN-LIMIT-LST (cdr class))
                             (cadr (assoc-keyword :MATCH-FREE (cdr class)))
                             ens
                             wrld))
          (:LINEAR
           (add-linear-rule rune nume
                            (cadr (assoc-keyword :TRIGGER-TERMS (cdr class)))
                            term
                            (assoc-keyword :BACKCHAIN-LIMIT-LST (cdr class))
                            (cadr (assoc-keyword :MATCH-FREE (cdr class)))
                            ens wrld state))
          (:WELL-FOUNDED-RELATION
           (add-well-founded-relation-rule rune nume term wrld))
          (:BUILT-IN-CLAUSE
           (add-built-in-clause-rule rune nume term wrld))
          (:COMPOUND-RECOGNIZER
           (add-compound-recognizer-rule rune nume term ens wrld))
          (:ELIM
           (add-elim-rule rune nume term wrld))
          (:GENERALIZE
           (add-generalize-rule rune nume term wrld))
          (:EQUIVALENCE
           (add-equivalence-rule rune nume term ens wrld))
          (:REFINEMENT
           (add-refinement-rule rune nume term wrld))
          (:CONGRUENCE
           (add-congruence-rule rune nume term wrld))
          (:META
           (add-meta-rule rune nume
                          (cadr (assoc-keyword :TRIGGER-FNS (cdr class)))
                          (cadr (assoc-keyword :WELL-FORMEDNESS-GUARANTEE
                                               (cdr class)))
                          term
                          (assoc-keyword :BACKCHAIN-LIMIT-LST (cdr class))
                          wrld))
          (:CLAUSE-PROCESSOR
           (add-clause-processor-rule (base-symbol rune)
                                      (cadr (assoc-keyword
                                             :WELL-FORMEDNESS-GUARANTEE
                                             (cdr class)))
                                      term wrld))
          (:FORWARD-CHAINING
           (add-forward-chaining-rule rune nume
                                      (cadr (assoc-keyword :TRIGGER-TERMS
                                                           (cdr class)))
                                      term
                                      (cadr (assoc-keyword :MATCH-FREE
                                                           (cdr class)))
                                      wrld))
          (:TYPE-PRESCRIPTION
           (add-type-prescription-rule rune nume
                                       (cadr (assoc-keyword :TYPED-TERM
                                                            (cdr class)))
                                       term
                                       (assoc-keyword :BACKCHAIN-LIMIT-LST
                                                      (cdr class))
                                       ens wrld nil))
          (:DEFINITION
           (add-definition-rule rune nume
                                (cadr (assoc-keyword :CLIQUE (cdr class)))
                                (cadr (assoc-keyword :CONTROLLER-ALIST
                                                     (cdr class)))
                                (let ((pair (assoc-keyword :INSTALL-BODY
                                                           (cdr class))))
                                  (if pair
                                      (cadr pair)
                                    :NORMALIZE))
                                term ens wrld))
          (:INDUCTION
           (add-induction-rule rune nume
                               (cadr (assoc-keyword :PATTERN (cdr class)))
                               (cadr (assoc-keyword :CONDITION (cdr class)))
                               (cadr (assoc-keyword :SCHEME (cdr class)))
                               term wrld))
          (:TYPE-SET-INVERTER
           (add-type-set-inverter-rule
            rune nume
            (cadr (assoc-keyword :TYPE-SET (cdr class)))
            term ens wrld))

          (:TAU-SYSTEM

; One might think that :tau-system rules are added here, since every other rule
; class is handled here.  But one would be wrong!  Because of the automatic mode in
; the tau system and because of the facility for regenerating the tau database,
; :tau-system rules are added by the tau-visit code invoked most often from
; install-event.

           wrld)

; WARNING: If this function is changed, change info-for-x-rules (and/or
; subsidiaries) and find-rules-of-rune2.

; WARNING:  If you add a new type of rule record, update access-x-rule-rune.

          (otherwise
           (er hard 'add-x-rule
               "Unrecognized rule class token ~x0 in ADD-X-RULE."
               (car class))))))

(defun add-rules1 (mapping-pairs classes ens wrld state)

; Mapping-pairs is in 1:1 correspondence with classes.  Each mapping
; pair is of the form (nume . rune) and gives the nume and rune we are
; to use for the rule built according to the corresponding element of
; classes.  Recall that each element of classes has a :COROLLARY component
; which is the term describing the rule.  Thus, term (above) is actually
; not used to build any rule.

  (cond ((null classes) wrld)
        (t (add-rules1 (cdr mapping-pairs)
                       (cdr classes)
                       ens
                       (add-x-rule (cdr (car mapping-pairs))
                                   (car (car mapping-pairs))
                                   (car classes)
                                   ens wrld state)
                       state))))

(defun truncate-class-alist (alist term)

; Alist is the cdr of a fully elaborated rule class and hence is a
; keyword-alistp -- not a regular alist!  As such it contains a :COROLLARY
; field and perhaps :HINTS and :INSTRUCTIONS.  A truncated class is a fully
; elaborated class with the :HINTS and :INSTRUCTIONS fields thrown out.  In
; addition, we throw out the :COROLLARY field if its value is term.

  (cond ((null alist) nil)
        ((or (eq (car alist) :HINTS)
             (eq (car alist) :INSTRUCTIONS)
             (and (eq (car alist) :COROLLARY)
                  (equal (cadr alist) term)))
         (truncate-class-alist (cddr alist) term))
        (t (cons (car alist)
                 (cons (cadr alist)
                       (truncate-class-alist (cddr alist) term))))))

(defun truncate-classes (classes term)

; This function generates the value we store under the
; 'truncated-classes property of an event whose 'theorem property is
; term.  It seems sensible to us to store the fully elaborated rule
; classes for a name and term.  For example, from them you can recover
; the exact logical expression of a given rule.  But a fully
; elaborated rule class can be an exceedingly large object to display,
; e.g., with :PROPS, because its translated :HINTS fields may contain
; large theories.  Thus, we "truncate" the elaborated classes,
; throwing away :HINTS, :INSTRUCTIONS, and perhaps (if it is identical
; to term, the 'theorem field of the event).

  (cond ((null classes) nil)
        (t (cons (cons (caar classes)
                       (truncate-class-alist (cdar classes) term))
                 (truncate-classes (cdr classes) term)))))

(defun make-runes1 (event-name classes runes)

; Event-name is a symbol and classes is a list of fully elaborated
; rule classes.  Hence, each element of classes is a list that starts
; with a rule token keyword, e.g., :REWRITE, :META, etc.  We make up a
; list of runes in 1:1 correspondence with classes.  The general form
; of a name is (token event-name . i), where token is the keyword for
; the class and i enumerates how many occurrences we have already
; counted for that keyword.  So for example, suppose event-name is FOO
; and classes contains, in order two :REWRITE classes and an :ELIM
; class, then we will name them (:REWRITE FOO . 1) (:REWRITE FOO . 2)
; (:ELIM FOO).  Note the oddity: if there is just one rule with a
; given token, its i is nil; otherwise i is an integer that counts
; from 1.

  (cond
   ((null classes) (revappend runes nil))
   (t (let* ((token (caar classes))
             (temp (assoc-eq token runes)))
        (make-runes1
         event-name
         (cdr classes)

; The new name we add is of the form (token event-name . i) where
; i is: 1, if we haven't seen token before but there is another occurrence
; of token in classes; nil, if we haven't seen token before and we won't
; see it again; and one more than the last i for token if we've seen
; token before.

         (cons
          (cons token
                (cons event-name
                      (cond ((null temp)
                             (cond ((assoc-eq token (cdr classes))
                                    1)
                                   (t nil)))
                            (t (1+ (cddr temp))))))
          runes))))))

(defun make-runes (event-name classes)

; Given an event name and the rule classes for the event we create the
; list of runes naming each rule.  The list is in 1:1 correspondence
; with classes.

  (make-runes1 event-name classes nil))

(defun make-runic-mapping-pairs (nume runes)

; Given the nume to be assigned to the first rune in a list of runes,
; we return a list, in ascending order by nume, of the mapping pairs,
; each pair of the form (nume . rune), in 1:1 correspondence with
; runes.

  (cond ((null runes)
         (prog2$ (or (<= nume (fixnum-bound))
                     (max-nume-exceeded-error 'make-runic-mapping-pairs))
                 nil))
        (t (cons (cons nume (car runes))
                 (make-runic-mapping-pairs (1+ nume) (cdr runes))))))

(defun add-rules (name classes term untranslated-term ens wrld state)

; Name is an event name.  We store term under the 'theorem property
; for name.  Under the 'truncated-classes for name we store the
; truncated, but otherwise fully elaborated, rule classes.  Under the
; 'runic-mapping-pairs we store the alist mapping numes to runes,
; i.e., ((n1 . rune1) ... (nk . runek)), where the runes are in 1:1
; correspondence with classes.  The numes are consecutive integers
; uniquely associated with the corresponding runes.  N1 is the least,
; Nk is the greatest, and thus Nk+1 is the next available nume in the
; world resulting from this addition.  For more on runes and numes,
; see runep.  See also the Essay on the Assignment of Runes and Numes
; by DEFUNS.

  (let ((runic-mapping-pairs
         (make-runic-mapping-pairs (get-next-nume wrld)
                                   (make-runes name classes))))
    (putprop name 'runic-mapping-pairs runic-mapping-pairs
     (putprop name 'theorem term
      (putprop name 'untranslated-theorem untranslated-term
       (putprop name 'classes (truncate-classes classes term)
                (add-rules1 runic-mapping-pairs classes ens wrld state)))))))

(defun redundant-theoremp (name term classes event-form wrld)

; We know name is a symbol, but it may or may not be new.  We return t if name
; is already defined as the name of the theorem term with the given
; rule-classes, or if event-form -- which is a defthm or defaxiom event -- is
; an existing event in the world.  We do the first test first since perhaps it
; is more efficient.

; Through Version_6.5 we had only the first test of this disjunction.  But
; Jared Davis and Sol Swords sent us small examples including the following,
; which failed because the translated rule-classes had changed.

;   (defund foop (x) (consp x))
;
;   (defthm booleanp-of-foop
;     (booleanp (foop x))
;     :rule-classes :type-prescription)
;
;   (in-theory (disable booleanp-compound-recognizer))
;
;   ; Was not redundant, because the generated corollary's :typed-term changes:
;   (defthm booleanp-of-foop
;     (booleanp (foop x))
;     :rule-classes :type-prescription)

; Now that we treat the second event as redundant, imagine a book consisting of
; the four events above except that the first defthm is local.  Then we get a
; different rule when including the book.  That seems harmless enough, but
; perhaps we should be more concerned if using encapsulate instead of a book,
; since we have seen soundness bugs when constraints change.  There are two
; reasons why we don't see a soundness issue here.

; First, if there is a soundness issue here, then there was already a soundness
; issue by converting each (defthm ...) to (encapsulate () (defthm ...)),
; because syntactic equality implies redundancy for encapsulate events.

; Second, the :corollary for a rule is independent of context; for example, the
; enabled status of booleanp-compound-recognizer in the example above only
; affects the :typed-term for the rule, not the :corollary.  The reason is that
; when a :corollary is implicit, then translate-rule-class generates the
; :corollary to be exactly the original theorem.

  (or (and (equal term (getpropc name 'theorem 0 wrld))
           (equal (truncate-classes classes term)
                  (getpropc name 'classes 0 wrld)))
      (assert$ event-form
               (equal event-form
                      (get-event name wrld)))))

; The next part develops the functions for proving that each alleged
; corollary in a rule class follows from the theorem proved.

(defun non-tautological-classes (term classes)

; Term is a translated term (indeed, it known to be a theorem).
; Classes is a list of translated rule classes, each therefore having
; a :COROLLARY field.  We'll say an element of classes is
; "tautological" if its :COROLLARY is implied by term, e.g., if
; (IMPLIES term corollary) is a theorem.  Return that sublist of
; classes consisting of the non-tautological elements.

  (cond ((null classes) nil)
        ((let ((cor
                (cadr (assoc-keyword :COROLLARY (cdr (car classes))))))
           (or (equal term cor)
               (if-tautologyp (mcons-term* 'if term cor *t*))))
         (non-tautological-classes term (cdr classes)))
        (t (cons (car classes)
                 (non-tautological-classes term (cdr classes))))))

(defun prove-corollaries1 (name term i n rule-classes ens wrld ctx state ttree)

; Term is a theorem just proved.  Rule-classes is a list of translated
; rule classes and each is known to be non-tautological wrt term.  We
; prove that term implies the :corollary of each rule class, or cause
; an error.  We return the ttree accumulated from all the proofs.  The
; two variables i and n are integers and used merely to control the
; output that enumerates where we are in the process: i is a 1-based
; counter indicating the position in the enumeration of the next rule
; class; n is the number of rule classes in all.

  (cond
   ((null rule-classes) (value ttree))
   (t (let ((goal (fcons-term* 'implies
                               term
                               (cadr (assoc-keyword
                                      :COROLLARY
                                      (cdr (car rule-classes))))))
            (otf-flg (cadr (assoc-keyword :OTF-FLG (cdr (car rule-classes)))))
            (hints (cadr (assoc-keyword :HINTS (cdr (car rule-classes)))))
            (instructions (cadr (assoc-keyword :INSTRUCTIONS
                                               (cdr (car rule-classes))))))
        (er-let*
         ((hints (if hints
                     (value hints) ; already translated, with default-hints
                   (let ((default-hints (default-hints wrld)))
                     (if default-hints ; not yet translated; no explicit hints
                         (translate-hints
                          (cons "Corollary of " name)
                          default-hints ctx wrld state)
                       (value nil))))))
         (pprogn
          (io? event nil state
               (wrld goal n i)
               (fms "The~#0~[~/ first~/ second~/ next~/ last~] goal is ~p1.~%"
                    (list (cons #\0 (cond ((and (= i 1) (= n 1)) 0)
                                          ((= i 1) 1)
                                          ((= i 2) 2)
                                          ((= i n) 4)
                                          (t 3)))
                          (cons #\1 (untranslate goal t wrld)))
                    (proofs-co state)
                    state
                    (term-evisc-tuple nil state)))
          (er-let*
           ((ttree1 (cond
                     (instructions
                      (proof-builder nil (untranslate goal t wrld)
                                     goal nil instructions
                                     wrld state))
                     (t (prove goal
                               (make-pspv ens wrld state
                                          :displayed-goal goal
                                          :otf-flg otf-flg)
                               hints ens wrld ctx state)))))
           (prove-corollaries1 name term (1+ i) n (cdr rule-classes) ens wrld
                               ctx state
                               (cons-tag-trees ttree1 ttree)))))))))

(defun prove-corollaries (name term rule-classes ens wrld ctx state)

; Rule-classes is a list of translated rule classes.  The basic idea
; is to prove the :COROLLARY of every class in rule-classes.  Like
; prove, we return an error triple; the non-erroneous value is a ttree
; signaling the successful proof of all the corollaries.

  (let* ((classes (non-tautological-classes term rule-classes))
         (n (length classes)))
    (cond
     ((= n 0)
      (value nil))
     (t (pprogn
         (io? event nil state
              (rule-classes n)
              (fms
               "~%We now consider~#2~[ the~/, in turn, the ~x0~]~#1~[~/ ~
                non-trivial~] ~#2~[corollary~/corollaries~] claimed in the ~
                specified rule ~#3~[class~/classes~].~%"
               (list (cons #\0 n)
                     (cons #\1 (if (= (length rule-classes) 1) 0 1))
                     (cons #\2 (if (= n 1) 0 1))
                     (cons #\3 (if (= (length rule-classes) 1) 0 1)))
               (proofs-co state)
               state
               (term-evisc-tuple nil state)))
         (prove-corollaries1 name term 1 n classes ens wrld ctx state nil))))))

;---------------------------------------------------------------------------
; Section:  More History Management and Command Stuff

; While we are at it, we here develop the code for printing out all the
; rules added by a particular event.

(defun enabled-runep-string (rune ens wrld)
  (if (enabled-runep rune ens wrld)
      "Enabled"
    "Disabled"))

(defun untranslate-hyps (hyps wrld)
  (cond ((null hyps) t)
        ((null (cdr hyps)) (untranslate (car hyps) t wrld))
        (t (cons 'and (untranslate-lst hyps t wrld)))))

(defun info-for-lemmas (lemmas numes ens wrld)
  (if (null lemmas)
      nil
    (let* ((rule                (car lemmas))
           (nume                (access rewrite-rule rule :nume))
           (rune                (access rewrite-rule rule :rune))
           (subclass            (access rewrite-rule rule :subclass))
           (lhs                 (access rewrite-rule rule :lhs))
           (rhs                 (access rewrite-rule rule :rhs))
           (hyps                (access rewrite-rule rule :hyps))
           (equiv               (access rewrite-rule rule :equiv))
           (backchain-limit-lst (access rewrite-rule rule
                                        :backchain-limit-lst))
           (heuristic-info      (access rewrite-rule rule :heuristic-info)))
      (if (or (eq numes t)
              (member nume numes))
          (cons `((:rune            ,rune :rewrite ,nume)
                  (:enabled         ,(and (enabled-runep rune ens wrld) t))
                  ,@(if (eq subclass 'meta)
                        `((:hyp-fn  ,(or hyps :none) hyps)
                          (:equiv   ,equiv)
                          (:meta-fn ,lhs))
                      `((:hyps  ,(untranslate-hyps hyps wrld) hyps)
                        (:equiv ,equiv)
                        (:lhs   ,(untranslate lhs nil wrld) lhs)
                        (:rhs   ,(untranslate rhs nil wrld) rhs)))
                  (:backchain-limit-lst ,backchain-limit-lst)
                  (:subclass            ,subclass)
                  ,@(cond ((eq subclass 'backchain)
                           `((:loop-stopper ,heuristic-info)))
                          ((eq subclass 'definition)
                           `((:clique           ,(car heuristic-info))
                             (:controller-alist ,(cdr heuristic-info))))
                          ((eq subclass 'rewrite-quoted-constant)
                           `((:form ,(car heuristic-info))
                             (:loop-stopper ,(cdr heuristic-info))))
                          (t
                           nil)))
                (info-for-lemmas (cdr lemmas) numes ens wrld))
        (info-for-lemmas (cdr lemmas) numes ens wrld)))))

(defun assoc-eq-eq (x y alist)

; We look for a pair on alist of the form (x y . val) where we compare with x
; and y using eq.  We return the pair or nil.

  (cond ((endp alist) nil)
        ((and (eq (car (car alist)) x)
              (eq (car (cdr (car alist))) y))
         (car alist))
        (t (assoc-eq-eq x y (cdr alist)))))

(defun info-for-well-founded-relation-rules (rules)

; There is not record class corresponding to well-founded-relation rules.  But
; the well-founded-relation-alist contains triples of the form (rel mp . rune)
; and we assume rules is a list of such triples.

  (if (null rules)
      nil
    (let* ((rule (car rules))
           (rune (cddr rule)))
      (cons (list (list :rune rune :well-founded-relation)
                  (list :domain-predicate      (cadr rule))
                  (list :well-founded-relation (car rule)))
            (info-for-well-founded-relation-rules (cdr rules))))))

(defun info-for-built-in-clause-rules1 (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule   (car rules))
           (nume   (access built-in-clause rule :nume))
           (rune   (access built-in-clause rule :rune))
           (clause (access built-in-clause rule :clause)))
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune     rune
                            :built-in-clause nume)
                      (list :enabled  (and (enabled-runep rune ens wrld) t))
                      (list :clause   (prettyify-clause clause nil wrld)
                            clause))
                (info-for-built-in-clause-rules1 (cdr rules) numes ens wrld))
        (info-for-built-in-clause-rules1 (cdr rules) numes ens wrld)))))

(defun info-for-built-in-clause-rules (alist numes ens wrld)
  (if (null alist)
      nil
    (append (info-for-built-in-clause-rules1 (cdar alist) numes ens wrld)
            (info-for-built-in-clause-rules (cdr alist) numes ens wrld))))

(defun info-for-compound-recognizer-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule     (car rules))
           (nume     (access recognizer-tuple rule :nume))
           (rune     (access recognizer-tuple rule :rune))
           (true-ts  (access recognizer-tuple rule :true-ts))
           (false-ts (access recognizer-tuple rule :false-ts))
           (strongp  (access recognizer-tuple rule :strongp)))
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune     rune
                            :compound-recognizer nume)
                      (list :enabled  (and (enabled-runep rune ens wrld) t))
                      (list :fn       (access recognizer-tuple rule :fn))
                      (list :true-ts  (decode-type-set true-ts)
                            true-ts)
                      (list :false-ts (decode-type-set false-ts)
                            false-ts)
                      (list :strongp
                            strongp))
                (info-for-compound-recognizer-rules (cdr rules) numes ens wrld))
        (info-for-compound-recognizer-rules (cdr rules) numes ens wrld)))))

(defun info-for-generalize-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule    (car rules))
           (nume    (access generalize-rule rule :nume))
           (rune    (access generalize-rule rule :rune))
           (formula (access generalize-rule rule :formula)))
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune    rune
                            :generalize nume)
                      (list :enabled (and (enabled-runep rune ens wrld) t))
                      (list :formula (untranslate formula t wrld)
                            formula))
                (info-for-generalize-rules (cdr rules) numes ens wrld))
        (info-for-generalize-rules (cdr rules) numes ens wrld)))))

(defun info-for-linear-lemmas (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule                (car rules))
           (nume                (access linear-lemma rule :nume))
           (rune                (access linear-lemma rule :rune))
           (hyps                (access linear-lemma rule :hyps))
           (concl               (access linear-lemma rule :concl))
           (max-term            (access linear-lemma rule :max-term))
           (backchain-limit-lst (access linear-lemma rule
                                        :backchain-limit-lst)))
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune                rune
                            :linear nume)
                      (list :enabled             (and (enabled-runep rune
                                                                     ens
                                                                     wrld)
                                                      t))
                      (list :hyps                (untranslate-hyps hyps wrld)
                            hyps)
                      (list :concl               (untranslate concl nil wrld)
                            concl)
                      (list :max-term            (untranslate max-term nil
                                                              wrld)
                            max-term)
                      (list :backchain-limit-lst backchain-limit-lst))
                (info-for-linear-lemmas (cdr rules) numes ens wrld))
        (info-for-linear-lemmas (cdr rules) numes ens wrld)))))

(defun info-for-eliminate-destructors-rule (rule numes ens wrld)
  (let ((rune             (access elim-rule rule :rune))
        (nume             (access elim-rule rule :nume))
        (hyps             (access elim-rule rule :hyps))
        (equiv            (access elim-rule rule :equiv))
        (lhs              (access elim-rule rule :lhs))
        (rhs              (access elim-rule rule :rhs))
        (destructor-term  (access elim-rule rule :destructor-term))
        (destructor-terms (access elim-rule rule :destructor-terms))
        (crucial-position (access elim-rule rule :crucial-position)))
    (if (or (eq numes t)
            (member nume numes))
        (list (list (list :rune rune
                          :elim nume)
                    (list :enabled          (and (enabled-runep rune ens wrld) t))
                    (list :hyps             (untranslate-hyps hyps wrld)
                          hyps)
                    (list :equiv            equiv)
                    (list :lhs              (untranslate lhs nil wrld)
                          lhs)
                    (list :rhs              (untranslate rhs nil wrld)
                          rhs)
                    (list :destructor-term  (untranslate destructor-term nil wrld)
                          destructor-term)
                    (list :destructor-terms (untranslate-lst destructor-terms nil
                                                             wrld)
                          destructor-terms)
                    (list :crucial-position crucial-position)))
      nil)))

(defun info-for-congruences (val numes ens wrld)

; val is of the form (equiv geneqv1 ... geneqvk ... geneqvn).
; This seems complicated so we'll punt for now.

  (declare (ignore val numes ens wrld))
  nil)

(defun info-for-pequivs (val numes ens wrld)

; This seems complicated so we'll punt for now.

  (declare (ignore val numes ens wrld))
  nil)

(defun info-for-coarsenings (val numes ens wrld)

; It is not obvious how to determine which coarsenings are really new, so we
; print nothing.

  (declare (ignore val numes ens wrld))
  nil)

(defun info-for-forward-chaining-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule    (car rules))
           (rune    (access forward-chaining-rule rule :rune))
           (nume    (access forward-chaining-rule rule :nume))
           (trigger (access forward-chaining-rule rule :trigger))
           (hyps    (access forward-chaining-rule rule :hyps))
           (concls  (access forward-chaining-rule rule :concls)))
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune    rune
                            :forward-chaining nume)
                      (list :enabled (and (enabled-runep rune ens wrld) t))
                      (list :trigger (untranslate trigger nil wrld)
                            trigger)
                      (list :hyps    (untranslate-hyps hyps wrld)
                            hyps)
                      (list :concls

; The :concls of a forward-chaining rule is really a implicit conjunction of
; all the conclusions you can draw.  So we untranslate the list and put an
; AND on the front, which is just what untranslate-hyps does, oddly enough.

                                      (untranslate-hyps concls wrld) concls))
                (info-for-forward-chaining-rules (cdr rules) numes ens wrld))
        (info-for-forward-chaining-rules (cdr rules) numes ens wrld)))))

(defun decode-type-set-lst (lst)
  (if lst
      (cons (decode-type-set (car lst))
            (decode-type-set-lst (cdr lst)))
    nil))

(defun info-for-type-prescriptions (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule      (car rules))
           (rune      (access type-prescription rule :rune))
           (nume      (access type-prescription rule :nume))
           (term      (access type-prescription rule :term))
           (hyps      (access type-prescription rule :hyps))
           (backchain-limit-lst (access type-prescription rule
                                        :backchain-limit-lst))
           (basic-ts  (access type-prescription rule :basic-ts))
           (vars      (access type-prescription rule :vars))
           (corollary (access type-prescription rule :corollary)))
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune      rune :type-prescription nume)
                      (list :enabled   (and (enabled-runep rune ens wrld) t))
                      (list :hyps      (untranslate-hyps hyps wrld)
                            hyps)
                      (list :term      (untranslate term nil wrld)
                            term)
                      (list :backchain-limit-lst backchain-limit-lst)
                      (list :basic-ts  (decode-type-set basic-ts)
                            basic-ts)
                      (list :vars      vars)
                      (list :corollary (untranslate corollary t wrld)
                            corollary))
                (info-for-type-prescriptions (cdr rules) numes ens wrld))
        (info-for-type-prescriptions (cdr rules) numes ens wrld)))))

(defun info-for-induction-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule      (car rules))
           (rune      (access induction-rule rule :rune))
           (nume      (access induction-rule rule :nume))
           (pattern   (access induction-rule rule :pattern))
           (condition (access induction-rule rule :condition))
           (scheme    (access induction-rule rule :scheme)))
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune      rune
                            :induction nume)
                      (list :enabled   (and (enabled-runep rune ens wrld) t))
                      (list :pattern   (untranslate pattern nil wrld)
                            pattern)
                      (list :condition (untranslate condition t wrld)
                            condition)
                      (list :scheme    (untranslate scheme nil wrld)
                            scheme))
                (info-for-induction-rules (cdr rules) numes ens wrld))
        (info-for-induction-rules (cdr rules) numes ens wrld)))))

(defun info-for-type-set-inverter-rules (rules numes ens wrld)
  (if (null rules)
      nil
    (let* ((rule     (car rules))
           (rune     (access type-set-inverter-rule rule :rune))
           (nume     (access type-set-inverter-rule rule :nume))
           (type-set (access type-set-inverter-rule rule :ts))
           (terms    (access type-set-inverter-rule rule :terms))
           )
      (if (or (eq numes t)
              (member nume numes))
          (cons (list (list :rune      rune
                            :type-set-inverter nume)
                      (list :enabled   (and (enabled-runep rune ens wrld) t))
                      (list :type-set  type-set)
                      (list :condition (untranslate-hyps terms wrld)
                            terms))
                (info-for-type-set-inverter-rules (cdr rules) numes ens wrld))
        (info-for-type-set-inverter-rules (cdr rules) numes ens wrld)))))

(defun info-for-x-rules (sym key val numes ens wrld)

; See add-x-rule for an enumeration of rule classes that generate the
; properties shown below.

; Warning: Keep this function in sync with find-rules-of-rune2.  In that
; spirit, tau rules are completely invisible and so we return nil for
; any property affected by tau rules.

; Info functions inspect the various rules and turn them into alists of the
; form:

;   (key . (value1 ... valueN))

; When we print these alists with :pr, we only print "key: value1".  This lets
; you store additional information in later values.  For example, value1 might
; want to untranslate the term for prettier printing to the user, or decode the
; type-set, etc.  Value2 can then include the original term or undecoded
; type-set, so that programs can use that value instead.

  (cond
   ((eq key 'global-value)
    (case sym
      (well-founded-relation-alist

; Avoid printing the built-in anonymous rule if that is all we have here.

       (if (consp (cdr val))
           (info-for-well-founded-relation-rules val)
         nil))
      (built-in-clauses
       (info-for-built-in-clause-rules val numes ens wrld))
      (type-set-inverter-rules
       (info-for-type-set-inverter-rules val numes ens wrld))
      (generalize-rules
       (info-for-generalize-rules val numes ens wrld))
      (rewrite-quoted-constant-rules
       (info-for-lemmas val numes ens wrld))
      (otherwise nil)))
   (t
    (case key
      (lemmas
       (info-for-lemmas val numes ens wrld))
      (linear-lemmas
       (info-for-linear-lemmas val numes ens wrld))
      (eliminate-destructors-rule
       (info-for-eliminate-destructors-rule val numes ens wrld))
      (congruences
       (info-for-congruences val numes ens wrld))
      (pequivs
       (info-for-pequivs val numes ens wrld))
      (coarsenings
       (info-for-coarsenings val numes ens wrld))
      (forward-chaining-rules
       (info-for-forward-chaining-rules val numes ens wrld))
      (type-prescriptions
       (info-for-type-prescriptions val numes ens wrld))
      (induction-rules
       (info-for-induction-rules val numes ens wrld))
      (recognizer-alist
       (info-for-compound-recognizer-rules val numes ens wrld))
      (otherwise nil)))))

(defun info-for-rules (props numes ens wrld)
  (cond ((null props)
         nil)
        ((eq (cadar props) *acl2-property-unbound*)
         (info-for-rules (cdr props) numes ens wrld))
        (t
         (append (info-for-x-rules (caar props) (cadar props) (cddar props)
                                   numes ens wrld)
                 (info-for-rules (cdr props) numes ens wrld)))))

(defun print-info-for-rules-entry (keys vals chan state)
  (if (not (consp keys))
      state
    (mv-let (col state)
            (fmt1 "~s0:"
                  (list (cons #\0 (let* ((name (symbol-name (car keys)))
                                         (lst (coerce name 'list)))
                                    (coerce (cons (car lst)
                                                  (string-downcase1 (cdr lst)))
                                            'string))))
                  0 chan state nil)
            (mv-let (col state)
                    (cond ((< col 14)
                           (fmt1 "~t0~q1"
                                 (list (cons #\0 14)
                                       (cons #\1 (caar vals)))
                                 col chan state nil))
                          (t (fmt1 " ~q0"
                                   (list (cons #\0 (caar vals)))
                                   col chan state nil)))
                    (declare (ignore col))
                    (print-info-for-rules-entry (cdr keys) (cdr vals) chan
                                                state)))))

(defun print-info-for-rules (info chan state)
  (if (not (consp info))
      (value :invisible)
    (pprogn (newline chan state)
            (print-info-for-rules-entry (strip-cars (car info))
                              (strip-cdrs (car info))
                              chan
                              state)
            (print-info-for-rules (cdr info) chan state))))

(defun pr-body (wrld-segment numes wrld state)
  (print-info-for-rules
   (info-for-rules (actual-props wrld-segment nil nil)
                   numes
                   (ens-maybe-brr state)
                   wrld)
   (standard-co state)
   state))

(defun pr-fn (name state)
  (cond ((and (symbolp name)
              (not (keywordp name)))
         (let* ((wrld (w state))
                (name (deref-macro-name name (macro-aliases wrld)))
                (numes (strip-cars
                        (getpropc name 'runic-mapping-pairs nil wrld)))
                (wrld-segment (world-to-next-event
                               (cdr (decode-logical-name name wrld)))))
           (pr-body wrld-segment numes wrld state)))
        (t (er soft 'pr
               "The argument to PR must be a non-keyword symbol.  Perhaps you ~
                should use PR! instead."))))

(defun print-clause-processor-rules1 (alist wrld state)
  (if (null alist)
      (value :invisible)
    (let* ((pair (car alist))
           (name (car pair))
           (term (cdr pair)))
      (pprogn (fms "Rule ~x0:~|~P12~|"
                   (list (cons #\0 name)
                         (cons #\1 (untranslate term nil wrld))
                         (cons #\2 (term-evisc-tuple nil state)))
                   (standard-co state) state nil)
              (print-clause-processor-rules1 (cdr alist) wrld state)))))

(defmacro print-clause-processor-rules ()
  '(let ((wrld (w state)))
     (print-clause-processor-rules1 (global-val 'clause-processor-rules wrld)
                                    wrld
                                    state)))

(defun new-numes (world-segment)
  (cond
   ((null world-segment)
    nil)
   ((and (eq (cadr (car world-segment)) 'runic-mapping-pairs)
         (not (eq (cddr (car world-segment)) *acl2-property-unbound*)))
    (append (strip-cars (cddr (car world-segment)))
            (new-numes (cdr world-segment))))
   (t
    (new-numes (cdr world-segment)))))

(defun world-to-next-command (wrld ans)
  (cond ((null wrld) (reverse ans))
        ((and (eq (caar wrld) 'command-landmark)
              (eq (cadar wrld) 'global-value))
         (reverse ans))
        (t (world-to-next-command (cdr wrld) (cons (car wrld) ans)))))

(defun pr!-fn (cd state)

; We assume that the world starts with a command landmark.

  (let ((wrld (w state)))
    (er-let* ((wrld-tail (er-decode-cd cd wrld 'print-new-rules state)))
             (pr-body (world-to-next-command (cdr wrld-tail) nil)
                      t wrld state))))

(defmacro pr (name)
  (list 'pr-fn name 'state))

(defmacro pr! (cd)
  (list 'pr!-fn cd 'state))

(defun disabledp-fn-lst (runic-mapping-pairs ens)
  (declare (xargs :guard ; see guard on enabled-runep
                  (and (enabled-structure-p ens)
                       (nat-alistp runic-mapping-pairs))))
  (cond ((endp runic-mapping-pairs) nil)
        ((enabled-numep (caar runic-mapping-pairs) ens)
         (disabledp-fn-lst (cdr runic-mapping-pairs) ens))
        (t (cons (cdar runic-mapping-pairs)
                 (disabledp-fn-lst (cdr runic-mapping-pairs) ens)))))

(defun disabledp-fn (name ens wrld)
  (declare (xargs :guard (and (enabled-structure-p ens)
                              (plist-worldp wrld)
                              (symbol-alistp (macro-aliases wrld))
                              (r-symbol-alistp (macro-aliases wrld))
                              (known-package-alistp
                               (global-val 'known-package-alist wrld))
                              (cond
                               ((symbolp name)
                                (let ((name2 (deref-macro-name
                                              name
                                              (macro-aliases wrld))))
                                  (cond ((and (not (eq name2 :here))
                                              name2
                                              (logical-namep name2 wrld))
                                         (nat-alistp
                                          (getpropc name2 'runic-mapping-pairs
                                                    nil wrld)))
                                        (t t))))
                               (t (and (consp name)
                                       (consp (cdr name))
                                       (symbolp (cadr name))
                                       (let ((rune (translate-abbrev-rune
                                                     name
                                                     (macro-aliases wrld))))
                                         (nat-alistp
                                          (getpropc (base-symbol rune)
                                                    'runic-mapping-pairs
                                                    nil
                                                    wrld)))))))))
  (cond ((symbolp name)
         (let ((name2 (deref-macro-name name (macro-aliases wrld))))
           (cond
            ((and (not (eq name2 :here))
                  name2
                  (logical-namep name2 wrld))
             (disabledp-fn-lst (getpropc name2 'runic-mapping-pairs nil wrld)
                               ens))
            (t (er hard? 'disabledp
                   "Illegal call of disabledp on symbolp argument ~x0.  See ~
                    :DOC disabledp."
                   name)))))
        (t (let* ((rune (translate-abbrev-rune name (macro-aliases wrld))))
             (cond
              ((runep rune wrld)
               (not (enabled-runep rune ens wrld)))
              (t (er hard? 'disabledp
                     "Illegal call of disabledp: ~x0 does not designate a ~
                      rune or a list of runes.  See :DOC disabledp."
                     name)))))))

(defmacro disabledp (name)
  `(disabledp-fn ,name (ens-maybe-brr state) (w state)))

(defun collect-abbreviation-subclass (rules)

; Rules is a list of REWRITE-RULEs.  We collect all those that are of :subclass
; 'ABBREVIATION.

  (cond ((null rules) nil)
        ((eq (access rewrite-rule (car rules) :subclass) 'ABBREVIATION)
         (cons (car rules) (collect-abbreviation-subclass (cdr rules))))
        (t (collect-abbreviation-subclass (cdr rules)))))

(defun runes-to-monitor1 (runes x wrld ctx state
                                only-simple only-simple-count
                                some-simple some-s-all some-s-bad
                                acc)
  (cond
   ((endp runes)
    (cond
     ((null acc)
      (er soft ctx
          "~x0 does not represent any runes to be monitored.  See :DOC ~
           monitor."
          x))
     (t
      (pprogn
       (cond
        (only-simple
         (warning$ ctx "Monitor"
                   "The rune~#0~[~/s~] ~&0 name~#0~[s~/~] only~#1~[ a~/~] ~
                    simple abbreviation rule~#1~[~/s~].  Monitors can be ~
                    installed on abbreviation rules, but will not fire during ~
                    preprocessing, so you may want to supply the hint :DO-NOT ~
                    '(PREPROCESS); see :DOC hints.  For an explanation of ~
                    what a simple abbreviation rule is, see :DOC simple.  ~
                    Also, see :DOC monitor."
                   only-simple
                   (if (> only-simple-count 1) 1 0)))
        (t state))
       (cond
        (some-simple
         (assert$
          (< 1 some-s-all)
          (warning$ ctx "Monitor"
                    "Among the ~n0 rules named ~v1 ~#2~[is a simple ~
                     abbreviation rule~/are ~n3 simple abbreviation rules~].  ~
                     Such rules can be monitored, but will not fire during ~
                     preprocessing, so you may want to supply the hint ~
                     :DO-NOT '(PREPROCESS); see :DOC hints.  For an ~
                     explanation of what a simple abbreviation rule is, see ~
                     :DOC simple.  Also, see :DOC monitor."
                    some-s-all
                    some-simple
                    (if (< 1 some-s-bad) 1 0)
                    some-s-bad)))
        (t state))
       (value (reverse acc))))))
   (t
    (let ((rune (car runes)))
      (cond
       ((member-eq (car rune) '(:rewrite :definition))
        (let ((rules (find-rules-of-rune rune wrld)))
          (cond
           ((null rules)
            (pprogn (warning$ ctx "Monitor"
                              "No rules are named ~x0."
                              rune)
                    (runes-to-monitor1
                     (cdr runes) x wrld ctx state
                     only-simple
                     only-simple-count
                     some-simple some-s-all some-s-bad
                     acc)))
           (t
            (let ((bad-rewrite-rules (collect-abbreviation-subclass rules)))
              (cond
               ((equal (length bad-rewrite-rules) (length rules))
                (runes-to-monitor1
                 (cdr runes) x wrld ctx state
                 (cons rune only-simple)
                 (+ (length rules) only-simple-count)
                 some-simple some-s-all some-s-bad
                 (cons rune acc)))
               (bad-rewrite-rules
                (runes-to-monitor1
                 (cdr runes) x wrld ctx state
                 only-simple only-simple-count
                 (cons rune some-simple)
                 (+ (length rules) some-s-all)
                 (+ (length bad-rewrite-rules) some-s-bad)
                 (cons rune acc)))
               (t (runes-to-monitor1 (cdr runes) x wrld ctx state
                                     only-simple only-simple-count
                                     some-simple some-s-all some-s-bad
                                     (cons rune acc)))))))))
       (t (runes-to-monitor1 (cdr runes) x wrld ctx state
                             only-simple only-simple-count
                             some-simple some-s-all some-s-bad
                             (cons rune acc))))))))

(defconst *monitorable-rune-types*
  '(:rewrite :rewrite-quoted-constant :definition :linear))

(defun monitorable-runes (lst)
  (cond ((endp lst) nil)
        ((member-eq (caar lst) *monitorable-rune-types*)
         (cons (car lst)
               (monitorable-runes (cdr lst))))
        (t (monitorable-runes (cdr lst)))))

(defun monitorable-runes-from-mapping-pairs (sym wrld)

; Note: another function that deals in runic mapping pairs is
; convert-theory-to-unordered-mapping-pairs1.  In both cases we are guided by
; the discussion of runic designators in :doc theories.  However, here we do
; not include :induction runes, and we do not accommodate theories because we
; wonder what complexity that might introduce in providing useful errors and
; warnings from :monitor, and we don't (yet?)  consider it likely that users
; will want to monitor theories.

; We accumulate runic mapping pairs of sym into ans, except in the case that
; sym is a defined function, we only include the :definition rune and, if indp
; is true, the induction rune.

  (let ((temp (strip-cdrs
               (getpropc (deref-macro-name sym (macro-aliases wrld))
                         'runic-mapping-pairs nil wrld))))
    (monitorable-runes temp)))

(defun runes-to-monitor (x ctx state)
  (er-let* ((wrld (value (w state)))
            (runes
             (cond
              ((symbolp x)
               (value (monitorable-runes-from-mapping-pairs x wrld)))
              (t
               (let ((rune (translate-abbrev-rune x (macro-aliases wrld))))
                 (cond
                  ((not (runep rune wrld))
                   (er soft ctx "~x0 does not designate a (valid) rune."
                       rune))
                  ((not (member-eq (car rune) *monitorable-rune-types*))
                   (er soft ctx
                       "Only ~&0 runes may be monitored.  We cannot break ~x1."
                       *monitorable-rune-types*
                       rune))
                  (t (value (list rune)))))))))
    (runes-to-monitor1 runes x wrld ctx state
                       nil 0
                       nil 0 0
                       nil)))

(defun remove1-assoc-equal? (key alist)
  (cond ((assoc-equal key alist)
         (remove1-assoc-equal key alist))
        (t alist)))

(defun remove1-assoc-equal?-lst (lst alist)
  (declare (xargs :guard (alistp alist)))
  (if (consp lst)
      (remove1-assoc-equal?-lst (cdr lst)
                                (remove1-assoc-equal? (car lst) alist))
    alist))

(defun monitor1 (x form ctx state)

; The list of monitored runes modified by this function is a brr-global.
; Thus, this function should only be evaluated within a wormhole.  The macro
; monitor can be called in either a wormhole state or a normal state.

  (er-let* ((runes (runes-to-monitor x ctx state))
            (term (translate-break-condition form ctx state)))
    (prog2$
     (or (f-get-global 'gstackp state)
         (cw "Note: Enable break-rewrite with :brr t.~%"))
     (pprogn
      (f-put-global 'brr-monitored-runes
                    (append (pairlis-x2 runes (list term))
                            (remove1-assoc-equal?-lst
                             runes
                             (get-brr-global 'brr-monitored-runes
                                             state)))
                    state)
      (value (get-brr-global 'brr-monitored-runes state))))))

(defun remove1-assoc-equal-lst (lst alist)
  (declare (xargs :guard (alistp alist)))
  (if (consp lst)
      (remove1-assoc-equal-lst (cdr lst)
                               (remove1-assoc-equal (car lst) alist))
    alist))

(defun set-difference-assoc-equal (lst alist)
  (declare (xargs :guard (and (true-listp lst)
                              (alistp alist))))
  (cond ((endp lst) nil)
        ((assoc-equal (car lst) alist)
         (set-difference-assoc-equal (cdr lst) alist))
        (t (cons (car lst) (set-difference-assoc-equal (cdr lst) alist)))))

(defun unmonitor1 (x ctx state)
  (let* ((wrld (w state))
         (runes (cond
                 ((symbolp x)
                  (monitorable-runes-from-mapping-pairs x wrld))
                 (t (list (translate-abbrev-rune x (macro-aliases wrld)))))))
    (cond
     ((null runes)
      (er soft ctx
          "The value ~x0 does not specify any runes that could be monitored."
          x))
     (t
      (let* ((monitored-runes-alist
              (get-brr-global 'brr-monitored-runes state))
             (bad-runes ; specified to unmonitor, but not monitored
              (set-difference-assoc-equal runes monitored-runes-alist)))
        (er-progn
         (cond ((null bad-runes)
                (value nil))
               ((not (intersectp-equal runes (strip-cars monitored-runes-alist)))
                (cond
                 ((null (cdr runes)) ; common case
                  (er soft ctx "~x0 is not monitored." (car runes)))
                 (t
                  (er soft ctx
                      "None of the ~n0 runes specified to be unmonitored is ~
                       currently monitored."
                      (length runes)))))
               (t
                (pprogn (warning$ ctx "Monitor"
                                  "Skipping the rune~#0~[~/s~] ~&0, as ~
                                   ~#0~[it is~/they are~] not currently ~
                                   monitored."
                                  bad-runes)
                        (value nil))))
         (pprogn
          (f-put-global 'brr-monitored-runes
                        (remove1-assoc-equal-lst runes monitored-runes-alist)
                        state)
          (prog2$
           (cond ((and (f-get-global 'gstackp state)
                       (null monitored-runes-alist))
                  (cw "Note:  No runes are being monitored.  Disable ~
                       break-rewrite with :brr nil.~%"))
                 (t nil))
           (value monitored-runes-alist)))))))))

(defun monitor-fn (x expr quietp state)

; If we are not in a wormhole, get into one.  Then we set brr-monitored-runes
; appropriately.  We always print the final value of brr-monitored-runes to the
; comment window and we always return (value :invisible).

  (cond
   ((eq (f-get-global 'wormhole-name state) 'brr)
    (er-progn
     (monitor1 x expr 'monitor state)
     (prog2$
      (and (not quietp)
           (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil))
      (value (if quietp t :invisible)))))
   (t (prog2$
       (brr-wormhole
        '(lambda (whs)
           (set-wormhole-entry-code whs :ENTER))
        nil
        `(er-progn
          (monitor1 ',x ',expr 'monitor state)
          (prog2$
           (and (not ',quietp)
                (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil))
           (value nil)))
        nil)
       (value (if quietp t :invisible))))))

(defun unmonitor-fn (x ctx state)
  (cond
   ((eq (f-get-global 'wormhole-name state) 'brr)
    (er-progn
     (cond ((eq x :all)
            (pprogn (f-put-global 'brr-monitored-runes nil state)
                    (value nil)))
           (t (unmonitor1 x ctx state)))
     (prog2$
      (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil)
      (value :invisible))))
   (t
    (prog2$
     (brr-wormhole
      '(lambda (whs)
         (set-wormhole-entry-code whs :ENTER))
      nil
      `(er-progn
        (cond ((eq ',x :all)
               (pprogn (f-put-global 'brr-monitored-runes nil state)
                       (value nil)))
              (t (unmonitor1 ',x ',ctx state)))
        (prog2$
         (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil)
         (value nil)))
      nil)
     (value :invisible)))))

(defun monitored-runes-fn (state)
  (cond
   ((eq (f-get-global 'wormhole-name state) 'brr)
    (prog2$ (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil)
            (value :invisible)))
   (t
    (prog2$
     (brr-wormhole
      '(lambda (whs)
         (set-wormhole-entry-code whs :ENTER))
      nil
      `(prog2$ (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil)
               (value nil))
      nil)
     (value :invisible)))))

(defun brr-fn (flg quietp state)
  (cond
   #+acl2-par
   ((and flg
         (f-get-global 'waterfall-parallelism state))
    (er soft 'brr
        "Brr is not supported in ACL2(p) with waterfall parallelism on.  See ~
         :DOC unsupported-waterfall-parallelism-features."))
   (flg
    (pprogn
     (f-put-global 'gstackp t state)
     (maybe-initialize-brr-evisc-tuple state)
     (cond
      (quietp (value t))
      (t
       (prog2$ (cw "Use :a! to exit break-rewrite.~|See :DOC ~
                    set-brr-evisc-tuple and :DOC iprint to control ~
                    suppression of details when printing.~|~%The monitored ~
                    runes are:~%")
               (er-progn (monitored-runes-fn state)
                         (value t)))))))
   (t (pprogn (f-put-global 'gstackp nil state)
              (value nil)))))

(defmacro brr (flg &optional quietp)
  `(brr-fn ,flg ,quietp state))

(defmacro monitor! (x expr)
  `(er-progn (brr t t)
             (monitor ,x ,expr t)))

(defmacro brr@ (sym)
  (declare (xargs :guard (member-eq sym '(:target
                                          :unify-subst
                                          :wonp
                                          :rewritten-rhs
                                          :poly-list
                                          :failure-reason
                                          :lemma
                                          :type-alist
                                          :ancestors
                                          :initial-ttree
                                          :final-ttree
                                          :gstack))))
  (case sym
        (:target '(get-brr-local 'target state))
        (:unify-subst '(get-brr-local 'unify-subst state))
        (:wonp '(get-brr-local 'wonp state))
        (:rewritten-rhs '(get-brr-local 'brr-result state))
        (:poly-list '(brr-result state))
        (:failure-reason '(get-brr-local 'failure-reason state))
        (:lemma '(get-brr-local 'lemma state))
        (:type-alist '(get-brr-local 'type-alist state))
        (:ancestors '(get-brr-local 'ancestors state))
        (:initial-ttree '(get-brr-local 'initial-ttree state))
        (:final-ttree '(get-brr-local 'final-ttree state))
        (otherwise '(get-brr-global 'brr-gstack state))))

(defmacro monitor (x expr &optional quietp)
  `(monitor-fn ,x ,expr ,quietp state))

(defmacro unmonitor (rune)
  `(unmonitor-fn ,rune 'unmonitor state))

(defmacro monitored-runes ()
  `(monitored-runes-fn state))

(defun proceed-from-brkpt1 (action runes ctx state)

; Action may be
; silent - exit brr with no output except the closing parenthesis
; print -  exit brr after printing results of attempted application
; break -  do not exit brr

; Runes is allegedly either t or a list of runes (or any runic designators
; legal for monitoring) to be used as brr-monitored-runes after pairing every
; rune with *t*.  If it is t, it means use the same brr-monitored-runes.
; Otherwise, we check that they are all legal.  If not, we warn and do not
; exit.  We may wish someday to provide the capability of proceeding with
; conditions other than *t* on the various runes, but I haven't seen a nice
; design for that yet.

  (er-let*
   ((lst (cond ((eq runes t)
                (value nil))
               ((eq runes nil)

; This special case avoids getting an error when calling runes-to-monitor.

                (value nil))
               (t (runes-to-monitor runes ctx state)))))
   (pprogn
    (put-brr-local 'saved-standard-oi
                   (f-get-global 'standard-oi state)
                   state)
    (put-brr-local 'saved-brr-monitored-runes
                   (get-brr-global 'brr-monitored-runes state)
                   state)
    (put-brr-local 'saved-brr-evisc-tuple
                   (get-brr-global 'brr-evisc-tuple state)
                   state)
    (if (eq runes t)
        state
        (f-put-global 'brr-monitored-runes lst state))
    (put-brr-local 'action action state)
    (exit-brr-wormhole state))))

(defun exit-brr (state)

; The assoc-eq on 'wonp below determines if we are in brkpt2 or brkpt1.

  (cond
   ((assoc-eq 'wonp (get-brr-global 'brr-alist state))
    (prog2$ (cw "~F0)~%" (get-brr-local 'depth state))
            (pprogn (pop-brr-stack-frame state)
                    (exit-brr-wormhole state))))
   (t (proceed-from-brkpt1 'silent t 'exit-brr state))))

(defun ok-if-fn (term state)
  (er-let*
   ((pair
     (simple-translate-and-eval term nil '(state)
                                "The ok-if test" 'ok-if (w state) state t)))
   (cond ((cdr pair) (exit-brr state))
         (t (value nil)))))

(defmacro ok-if (term)
  `(ok-if-fn ,term state))

;---------------------------------------------------------------------------

; Section:  The DEFAXIOM Event

(defun print-rule-storage-dependencies (name ttree state)
  (cond
   ((ld-skip-proofsp state) (value nil))
   (t (pprogn
       (io? event nil state
            (name ttree)
            (let ((simp-phrase (tilde-*-simp-phrase ttree)))
              (cond ((nth 4 simp-phrase)
                     (fms "The storage of ~x0 depends upon ~*1.~%"
                          (list (cons #\0 name)
                                (cons #\1 simp-phrase))
                          (proofs-co state)
                          state
                          nil))
                    (t state))))
       (value nil)))))

(defun defaxiom-supporters (tterm name ctx wrld state)

; Here we document requirements on disjointness of the sets of evaluator
; functions and defaxiom supporters.

; First, consider the following comment from relevant-constraints (which should
; be kept in sync with that comment), regarding functional instantiation of a
; theorem, thm, using a functional substitution, alist.

; The relevant theorems are the set of all terms, term, such that
;   (a) term mentions some function symbol in the domain of alist,
;   AND
;   (b) either
;      (i) term arises from a definition of or constraint on a function symbol
;          ancestral either in thm or in some defaxiom,
;       OR
;      (ii) term is the body of a defaxiom.

; Then when we (conceptually at least) functionally instantiate a theorem
; using a functional substitution of the form fs = ((evl evl') (evl-list
; evl'-list)), we need to know that the above proof obligations are met.

; ACL2 insists (in function chk-evaluator-use-in-rule) that the evaluator evl
; of a proposed :meta or :clause-processor rule is not ancestral in any
; defaxiom, nor is it ancestral in meta-extract-global-fact+ and
; meta-extract-contextual-fact if they are used in the rule.  Thus, when we
; functionally instantiate formula (2) in the Essay on Correctness of Meta
; Reasoning, which has calls of only those meta-extract function symbols and
; evl, the only relevant theorems for (i) above are the constraints on evl, and
; there are no relevant theorems for (ii) above.  We can use our usual
; computation of "ancestral", which does not explore below functions that are
; not instantiablep, since (presumably!) non-instantiablep functions are
; primitives in which no evaluator function is ancestral.

; But there is a subtlety not fully addressed above.  Consider the following
; case: a legitimate :meta (or :clause-processor) rule, with evaluator evl, is
; followed by a defaxiom event for which evl (or evl-list) is ancestral.  Does
; this new defaxiom invalidate the existing rule?  The answer is no, but the
; argument above doesn't quite explain why, so we elaborate here.  Let C0 be
; the chronology in which the meta rule was proved and let C1 be the current
; chronology, which extends C0.  Let C2 be the result of extending C0 with a
; defstub for every function symbol of C1 that is not in C0, except for the
; evaluator pair evl'/evl'-list, introduced at the end for all function symbols
; of C1.  Then the argument applies to C2, so the desired functional instance
; is a theorem of C2.  But the theory of C2 is a subtheory of C1, so the
; desired functional instance is a theorem of C1.

  (declare (ignore name ctx))
  (let ((supporters (instantiable-ancestors (all-fnnames tterm) wrld nil)))
    (value supporters)))

(defun defaxiom-fn (name term state rule-classes event-form)

; Important Note: Don't change the formals of this function without reading the
; *initial-event-defmacros* discussion in axioms.lisp.

  (when-logic
   "DEFAXIOM"
   (with-ctx-summarized
    (make-ctx-for-event event-form (cons 'defaxiom name))

; At one time we thought that event-form could be nil.  It is simplest, for
; checking redundancy, not to consider the case of manufacturing an event-form,
; so now we insist on event-form being supplied (not nil).

    (assert$
     event-form
     (let ((wrld (w state))
           (ens (ens state)))
       (er-progn
        (chk-all-but-new-name name ctx nil wrld state)
        (er-let* ((tterm (translate term t t t ctx wrld state))
; known-stobjs = t (stobjs-out = t)
                  (supporters (defaxiom-supporters tterm name ctx wrld state))
                  (classes (translate-rule-classes name rule-classes tterm ctx
                                                   ens wrld state)))
          (cond
           ((redundant-theoremp name tterm classes event-form wrld)
            (stop-redundant-event ctx state))
           (t

; Next we implement Defaxiom Restriction for Defattach from The Essay on
; Defattach: no ancestor (according to the transitive closure of the
; immediate-supporter relation) of a defaxiom event has an attachment.  Since
; this is all about logic, we remove guard-holders from term before doing this
; check.

            (let ((attached-fns
                   (attached-fns (canonical-ancestors-lst
                                  (all-ffn-symbs
                                   (remove-guard-holders tterm wrld)
                                   nil)
                                  wrld)
                                 wrld)))
              (cond
               (attached-fns
                (er soft ctx
                    "The following function~#0~[ has an attachment, but is~/s ~
                    have attachments, but are~] ancestral in the proposed ~
                    axiom: ~&0. ~ See :DOC defattach."
                    attached-fns))
               (t
                (enforce-redundancy
                 event-form ctx wrld
                 (er-let*
                     ((ttree1 (chk-acceptable-rules name classes ctx ens wrld
                                                    state))
                      (wrld1 (chk-just-new-name name nil 'theorem nil ctx wrld
                                                state))
                      (ttree3
                       (cond ((ld-skip-proofsp state)
                              (value nil))
                             (t
                              (prove-corollaries name tterm classes ens wrld1 ctx
                                                 state)))))
                   (let* ((wrld2
                           (add-rules name classes tterm term ens wrld1 state))
                          (wrld3 (global-set
                                  'nonconstructive-axiom-names
                                  (cons name
                                        (global-val 'nonconstructive-axiom-names wrld))
                                  wrld2))
                          (wrld4 (maybe-putprop-lst supporters 'defaxiom-supporter
                                                    name wrld3))
                          (ttree4 (cons-tag-trees ttree1 ttree3)))
                     (pprogn
                      (f-put-global 'axiomsp t state)
                      (er-progn
                       (chk-assumption-free-ttree ttree4 ctx state)
                       (print-rule-storage-dependencies name ttree1 state)
                       (install-event name
                                      event-form
                                      'defaxiom
                                      name
                                      ttree4
                                      nil :protect ctx wrld4
                                      state))))))))))))))))))


;---------------------------------------------------------------------------
; Section:  The DEFTHM Event

(defun warn-on-inappropriate-defun-mode (assumep event-form ctx state)
  (if (or assumep
          (eq (default-defun-mode (w state)) :logic))
      state
    (warning$ ctx "Defun-Mode"
             "It is perhaps unusual to execute the event ~x0 in the ~
              :program default-defun-mode when ld-skip-proofsp has not been ~
              set to T."
             event-form)))

;; Historical Comment from Ruben Gamboa:
;; this trio of functions adds the hypothesis "(standardp x)"
;; for each variable x in the theorem.

#+:non-standard-analysis
(defun add-hyp-standardp-var-lst (vars)
  (if (consp vars)
      (cons (list 'standardp (car vars))
            (add-hyp-standardp-var-lst (cdr vars)))
    nil))

#+:non-standard-analysis
(defun strengthen-hyps-using-transfer-principle (hyps vars)

; Hyps is an untranslated expression.

  (cons 'and
        (append (add-hyp-standardp-var-lst vars)
                (if (and (consp hyps)
                         (eq (car hyps) 'and))
                    (cdr hyps)
                    (list hyps)))))

#+:non-standard-analysis
(defun weaken-using-transfer-principle (term)

; Term is an untranslated expression.

  (let ((vars (all-vars term)))
    (case-match term
                (('implies hyps ('standardp subterm))
                 (declare (ignore subterm))
                 (list 'implies
                       hyps
                       (cons 'and (add-hyp-standardp-var-lst vars))))
                (('standardp subterm)
                 (declare (ignore subterm))
                 (cons 'and (add-hyp-standardp-var-lst vars)))
                (('implies hyps concls)
                 (list 'implies
                       (strengthen-hyps-using-transfer-principle hyps vars)
                       concls))
                (&
                 (list 'implies
                       (cons 'and (add-hyp-standardp-var-lst vars))
                       term)))))

#+:non-standard-analysis
(defun remove-standardp-hyp (tterm)
  (if (and (consp tterm)
           (eq (car tterm) 'standardp)
           (variablep (car (cdr tterm))))
      (list 'eq (car (cdr tterm)) (car (cdr tterm)))
      tterm))

#+:non-standard-analysis
(defun remove-standardp-hyps (tterm)
  (if (and (consp tterm)
           (eq (car tterm) 'if)
           (equal (car (cdr (cdr (cdr tterm))))
                  (list 'quote nil)))
      (list 'if
            (remove-standardp-hyp (car (cdr tterm)))
            (remove-standardp-hyps (car (cdr (cdr tterm))))
            (list 'quote nil))
      (remove-standardp-hyp tterm)))

#+:non-standard-analysis
(defun remove-standardp-hyps-and-standardp-conclusion (tterm)
  (case-match tterm
              (('implies hyps ('standardp subterm))
               (list 'implies
                     (remove-standardp-hyps hyps)
                     subterm))
              (('standardp subterm)
               subterm)
              (& tterm)))

#+:non-standard-analysis
(defun chk-classical-term-or-standardp-of-classical-term (tterm term ctx wrld state)

; Tterm is the translation of term.

  (let* ((names (all-fnnames (remove-standardp-hyps-and-standardp-conclusion tterm)))
         (non-classical-fns (get-non-classical-fns-from-list names wrld nil)))
    (if (null non-classical-fns)
        (value nil)
      (er soft ctx
          "It is illegal to use DEFTHM-STD to prove non-classical ~
           formulas.  However, there has been an attempt to prove ~
           the formula ~x0 using DEFTHM-STD, even though it ~
           contains the non-classical function ~*1."
          term
          `("<MissingFunction>" "~x*" "~x* and " "~x*,"
            ,non-classical-fns)))))

#+(and acl2-par (not acl2-loop-only))
(defmacro with-waterfall-parallelism-timings (name form)
  `(unwind-protect-disable-interrupts-during-cleanup
    (progn (setup-waterfall-parallelism-ht-for-name ,name)
           (reset-future-queue-length-history)
           (setf *acl2p-starting-proof-time*
                 (get-internal-real-time))
           ,form)
    (clear-current-waterfall-parallelism-ht)))

#-(and acl2-par (not acl2-loop-only))
(defmacro with-waterfall-parallelism-timings (name form)
  (declare (ignore name))
  form)

(defun translate-for-defthm (name term ctx wrld state)
  (let ((rec (get-translate-cert-data-record
              :defthm
              (cert-data-val name (cert-data-entry :translate state))
              state)))
    (cond (rec (value (assert$ (equal (access translate-cert-data-record rec
                                              :inputs)
                                      name)
                               (cons nil ; do not store
                                     (access translate-cert-data-record rec
                                             :value)))))
          (t (er-let* ((tterm (translate term t t t ctx wrld state)))
               (value (cons (store-cert-data tterm wrld state)
                            tterm)))))))

(defun defthm-fn1 (name term state
                        rule-classes
                        instructions
                        hints
                        otf-flg
                        event-form
                        #+:non-standard-analysis std-p)
  (with-ctx-summarized
   (make-ctx-for-event event-form (cons 'defthm name))

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
                                   (translate-instructions name instructions
                                                           ctx wrld1 state)))

; Observe that we do not translate the hints if ld-skip-proofsp is non-nil.
; Once upon a time we translated the hints unless ld-skip-proofsp was
; 'include-book, which meant we translated them if it was t, which meant we did
; it during initialize-acl2.  That caused a failure due to the fact that ENABLE
; was not defined when it was first used in axioms.lisp.  This choice is
; a little unsettling because it means

                   (hints (if (or (eq ld-skip-proofsp 'include-book)
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
                                   (cond (hints (er soft ctx
                                                    "It is not permitted to ~
                                                 supply both :INSTRUCTIONS ~
                                                 and :HINTS to DEFTHM."))
                                         (t (value nil)))
                                   #+:non-standard-analysis
                                   (if std-p

; How could this happen?  Presumably the user created a defthm event using the
; proof-builder, and then absent-mindedly somehow suffixed "-std" on to the
; car, defthm, of that form.

                                       (er soft ctx
                                           ":INSTRUCTIONS are not supported for ~
                                        defthm-std events.")
                                     (value nil))
                                   (proof-builder name term
                                                  tterm classes instructions
                                                  wrld1 state)))
                                 (t (prove tterm
                                           (make-pspv ens wrld1 state
                                                      :displayed-goal term
                                                      :otf-flg otf-flg)
                                           hints ens wrld1 ctx state))))
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
                                  nil :protect ctx wrld3
                                  state)))))))))))))))

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
   (defthm-fn1 name term state
     rule-classes
     instructions
     hints
     otf-flg
     event-form
     #+:non-standard-analysis std-p)))

(defun thm-fn (term state hints otf-flg)
  (er-progn
   (with-ctx-summarized
    (make-ctx-for-event
     (list* 'THM term (if (or hints otf-flg) '(irrelevant) nil))
     "( THM ...)")
    (cond
     ((member-eq (ld-skip-proofsp state)
                 '(include-book include-book-with-locals initialize-acl2))
      (value nil))
     (t
      (let ((wrld (w state))
            (ens (ens state)))
        (er-let* ((hints (translate-hints+ 'thm
                                           hints
                                           (default-hints wrld)
                                           ctx wrld state)))
          (er-let* ((tterm (translate term t t t ctx wrld state))
; known-stobjs = t (stobjs-out = t)
                    (ttree (prove tterm
                                  (make-pspv ens wrld state
                                             :displayed-goal term
                                             :otf-flg otf-flg)
                                  hints ens wrld ctx state)))
            (value nil)))))))
   (pprogn (io? summary nil state
                nil
                (fms (if (ld-skip-proofsp state)
                         "Proof skipped.~%"
                       "Proof succeeded.~%")
                     nil
                     (proofs-co state) state nil))
           (value :invisible))))

(defmacro thm (term &key hints otf-flg)

; We started using make-event here in January, 2019.  Instead of defining
; thm-fn above and generating a call of it below, we could presumably generate
; a new name and instead call defthm with that name, adding :rule-classes nil.
; But to reduce risk and potential churn we decided, when introducing
; make-event here, to continue with the existing definition of thm-fn, and
; essentially the same use of thm-fn.  It seems very reasonable to try the
; defthm approach instead if someone wants to do that.

  `(with-output :off summary :stack :push
     (make-event (er-progn (with-output :stack :pop
                             (thm-fn ',term
                                     state
                                     ',hints
                                     ',otf-flg))
                           (value '(value-triple :invisible)))
                 :expansion? (value-triple :invisible)
                 :on-behalf-of :quiet!)))

; Note:  During boot-strapping the thm macro is unavailable because it is
; not one of the *initial-event-defmacros*.

;---------------------------------------------------------------------------
; Section:  Some Convenient Abbreviations for Defthm

(defun chk-extensible-rule-classes (rule-classes ctx state)
  (cond ((or (symbolp rule-classes)
             (true-listp rule-classes))
         (value nil))
        (t (er soft ctx
               "The :rule-classes argument to must be either ~
                a symbol or a true-listp.  Your rule-classes is ~x0."
               rule-classes))))

(defun extend-rule-classes (class rule-classes)
  (cond ((symbolp rule-classes)
         (cond ((null rule-classes)
                class)
               ((eq rule-classes class)
                rule-classes)
               (t (list class rule-classes))))
        ((member-eq class rule-classes)
         rule-classes)
        (t (cons class rule-classes))))

(defconst *defequiv-package-values* '(:current :equiv :legacy))

(defun defequiv-form (equiv package current-pkg event-name
                            rule-classes instructions hints otf-flg)
  (declare (xargs :guard
                  (and (symbolp equiv)
                       (member-eq package *defequiv-package-values*)
                       (or (null current-pkg) (stringp current-pkg))
                       (symbolp event-name))))
  (let* ((sym (case package
                (:current (pkg-witness current-pkg))
                (otherwise equiv)))
         (default-name (gen-sym-sym (list equiv "-IS-AN-EQUIVALENCE") sym))
         (event-name (or event-name default-name))
         (equivalence-condition (equivalence-relation-condition equiv sym)))
    `(defthm ,event-name
       ,equivalence-condition
       :rule-classes
       ,(extend-rule-classes :equivalence rule-classes)
       ,@(if instructions (list :instructions instructions) nil)
       ,@(if hints (list :hints hints) nil)
       ,@(if otf-flg (list :otf-flg otf-flg) nil))))

(defun defequiv-fn (equiv package event-name rule-classes instructions hints
                          otf-flg)
  (let ((ctx (cons 'defequiv equiv)))
    (cond
     ((not (symbolp equiv))
      `(er soft ',ctx
           "The first argument of ~x0 must be a symbol, but ~x1 is not.  See ~
            :DOC defequiv."
           'defequiv
           ',equiv))
     ((not (member-eq package *defequiv-package-values*))
      `(er soft ',ctx
           "The (optional) :PACKAGE keyword of ~x0 must be ~v1, but ~x2 is ~
            none of these.  See :DOC defequiv."
           'defequiv
           *defequiv-package-values*
           ',package))
     ((not (symbolp event-name))
      `(er soft ',ctx
           "The (optional) :EVENT-NAME keyword argument of ~x0 must be a ~
            symbol, but ~x1 is not.  See :DOC defequiv."
           'defequiv
           ',event-name))
     ((not (eq package :current))
      (defequiv-form equiv package nil event-name
        rule-classes instructions hints otf-flg))
     (t `(make-event (defequiv-form
                       ',equiv
                       ',package
                       (current-package state)
                       ',event-name
                       ',rule-classes
                       ',instructions
                       ',hints
                       ',otf-flg))))))

(defmacro defequiv (equiv
                    &key
                    (package ':current)
                    event-name
                    (rule-classes '(:equivalence))
                    instructions
                    hints
                    otf-flg)
  (defequiv-fn equiv package event-name rule-classes instructions hints
    otf-flg))

(defconst *defrefinement-package-values* '(:current :equiv1 :equiv2 :legacy))

(defun defrefinement-form (equiv1 equiv2 package current-pkg event-name
                                  rule-classes instructions hints otf-flg)
  (declare (xargs :guard
                  (and (symbolp equiv1)
                       (symbolp equiv2)
                       (member package *defrefinement-package-values*)
                       (or (null current-pkg) (stringp current-pkg))
                       (symbolp event-name))))
  (let* ((sym (case package
                (:current (pkg-witness current-pkg))
                (:equiv2 equiv2)
                (otherwise equiv1)))
         (default-name
           (gen-sym-sym (list equiv1 "-REFINES-" equiv2) sym))
         (event-name (or event-name default-name))
         (x (fix-intern-in-pkg-of-sym "X" sym))
         (y (fix-intern-in-pkg-of-sym "Y" sym)))
    `(defthm ,event-name
       (implies (,equiv1 ,x ,y) (,equiv2 ,x ,y))
       :rule-classes
       ,(extend-rule-classes :refinement rule-classes)
       ,@(if instructions (list :instructions instructions) nil)
       ,@(if hints (list :hints hints) nil)
       ,@(if otf-flg (list :otf-flg otf-flg) nil))))

(defun defrefinement-fn (equiv1 equiv2 package event-name rule-classes
                                instructions hints otf-flg)
  (let ((ctx (cons 'defrefinement equiv1)))
    (cond
     ((not (and (symbolp equiv1)
                (symbolp equiv2)))
      `(er soft ',ctx
           "The first two arguments of ~x0 must be symbols, but ~@1.  See ~
            :DOC defrefinement."
           'defrefinement
           ,(cond ((symbolp equiv1)
                   `(msg "~x0 is not" ',equiv2))
                  ((symbolp equiv2)
                   `(msg "~x0 is not" ',equiv1))
                  (t
                   `(msg "~&0 are not" '(,equiv1 ,equiv2))))))
     ((not (member-eq package *defrefinement-package-values*))
      `(er soft ',ctx
           "The (optional) :PACKAGE keyword of ~x0 must be ~v1, but ~x2 is ~
            none of these.  See :DOC defequiv."
           'defrefinement
           *defrefinement-package-values*
           ',package))
     ((not (symbolp event-name))
      `(er soft ',ctx
           "The (optional) :EVENT-NAME keyword argument of ~x0 must be a ~
            symbol, but ~x1 is not.  See :DOC defequiv."
           'defrefinement
           ',event-name))
     ((not (eq package :current))
      (defrefinement-form equiv1 equiv2 package nil event-name
        rule-classes instructions hints otf-flg))
     (t `(make-event (defrefinement-form
                       ',equiv1
                       ',equiv2
                       ',package
                       (current-package state)
                       ',event-name
                       ',rule-classes
                       ',instructions
                       ',hints
                       ',otf-flg))))))

(defmacro defrefinement (equiv1
                         equiv2
                         &key
                         (package ':current)
                         event-name
                         (rule-classes '(:refinement))
                         instructions
                         hints
                         otf-flg)
  (defrefinement-fn equiv1 equiv2 package event-name rule-classes instructions
    hints otf-flg))

(defconst *defcong-package-values* '(:current :equiv1 :legacy :equiv2 :function))

(defun defcong-form (equiv1 equiv2 fn-args k package current-pkg event-name
                            rule-classes instructions hints otf-flg )
  (declare (xargs :guard
                  (and (symbolp equiv1)
                       (symbolp equiv2)
                       (symbol-listp fn-args)
                       (no-duplicatesp-equal (cdr fn-args))
                       (integerp k)
                       (< 0 k)
                       (< k (length fn-args))
                       (not (eq (car fn-args) 'if))
                       (member package *defcong-package-values*)
                       (or (null current-pkg) (stringp current-pkg))
                       (symbolp event-name))))
  (let* ((fn (car fn-args))
         (sym (case package
                (:current (pkg-witness current-pkg))
                (:equiv2 equiv2)
                (:function fn)
                (otherwise equiv1)))
         (default-name
           (gen-sym-sym (list equiv1 "-IMPLIES-" equiv2 "-" fn "-" k)
                        sym))
         (event-name (or event-name default-name))
         (kth-arg (nth k fn-args))
         (arg-k-equiv (gen-sym-sym (list kth-arg '-equiv) sym))
         (updated-fn-args (update-nth k arg-k-equiv fn-args)))
    `(defthm ,event-name
       (implies (,equiv1 ,kth-arg ,arg-k-equiv)
                (,equiv2 ,fn-args ,updated-fn-args))
       :rule-classes
       ,(extend-rule-classes :CONGRUENCE rule-classes)
       ,@(if instructions (list :instructions instructions) nil)
       ,@(if hints (list :hints hints) nil)
       ,@(if otf-flg (list :otf-flg otf-flg) nil))))

(defun defcong-fn (equiv1 equiv2 fn-args k package event-name rule-classes
                          instructions hints otf-flg)
  (let ((ctx (cons 'defcong equiv1)))
    (cond
     ((not (and (symbolp equiv1)
                (symbolp equiv2)))
      `(er soft ',ctx
           "The first two arguments of ~x0 must be symbols, but ~@1.  See ~
            :DOC defcong."
           'defcong
           ,(cond ((symbolp equiv1)
                   `(msg "~x0 is not" ',equiv2))
                  ((symbolp equiv2)
                   `(msg "~x0 is not" ',equiv1))
                  (t
                   `(msg "~&0 are not" '(,equiv1 ,equiv2))))))
     ((not (and (symbol-listp fn-args)
                (no-duplicatesp-eq (cdr fn-args))
                (not (eql (car fn-args) 'acl2::if))))
      `(er soft ',ctx
           "The third argument of ~x0 must be a list, starting with a symbol ~
            other than ~x1 and followed by a duplicate-free list of symbols. ~
            However, ~x2 is not of this form.  See :DOC defcong."
           'defcong
           'if
           ',fn-args))
     ((not (and (integerp k)
                (< 0 k)
                (< k (length fn-args))))
      `(er soft ',ctx
           "The fourth argument of ~x0, ~x1, is illegal.  It must be a ~
            positive integer less than the length of the third argument ~
            (which in this case is ~x2).  See :DOC defcong."
           'defcong
           ',k
           ',(length fn-args)))
     ((not (member-eq package *defcong-package-values*))
      `(er soft ',ctx
           "The (optional) :PACKAGE keyword of ~x0 must be ~v1, but ~x2 is ~
            none of these.  See :DOC defcong."
           'defcong
           *defcong-package-values*
           ',package))
     ((not (symbolp event-name))
      `(er soft ',ctx
           "The (optional) :EVENT-NAME keyword argument of ~x0 must be a ~
            symbol, but ~x1 is not.  See :DOC defcong."
           'defcong
           ',event-name))
     ((not (equal package :current))
      (defcong-form equiv1 equiv2 fn-args k package nil event-name
        rule-classes instructions hints otf-flg ))
     (t `(make-event (defcong-form
                       ',equiv1
                       ',equiv2
                       ',fn-args
                       ',k
                       ',package
                       (current-package state)
                       ',event-name
                       ',rule-classes
                       ',instructions
                       ',hints
                       ',otf-flg))))))

(defmacro defcong (equiv1
                   equiv2
                   fn-args
                   k
                   &key (package ':current)
                   event-name
                   (rule-classes '(:congruence))
                   instructions
                   hints
                   otf-flg)
  (defcong-fn equiv1 equiv2 fn-args k package event-name rule-classes
    instructions hints otf-flg))
