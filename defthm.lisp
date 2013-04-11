; ACL2 Version 6.1 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2013, Regents of the University of Texas

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
; Austin, TX 78701 U.S.A.

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

(mutual-recursion

(defun remove-lambdas (term)
  (if (or (variablep term)
          (fquotep term))
      term
    (let ((args (remove-lambdas-lst (fargs term)))
          (fn (ffn-symb term)))
      (if (flambdap fn)
          (subcor-var (lambda-formals fn) args (remove-lambdas (lambda-body fn)))
        (cons-term fn args)))))

(defun remove-lambdas-lst (termlist)
  (if termlist
      (cons (remove-lambdas (car termlist))
            (remove-lambdas-lst (cdr termlist)))
    nil))

)

; We use the following functions to determine the sense of the conclusion
; as a :REWRITE rule.

(defun interpret-term-as-rewrite-rule2 (name hyps lhs rhs wrld)
  (cond
   ((equal lhs rhs)
    (msg
     "A :REWRITE rule generated from ~x0 is illegal because it rewrites the ~
      term ~x1 to itself!  This can happen even when you submit a rule whose ~
      left and right sides appear to be different, in the case that those two ~
      sides represent the same term (in particular, after macroexpansion).  ~
      See :DOC rewrite.  You may wish to consider submitting a DEFTHM event ~
      ending with :RULE-CLASSES NIL."
     name
     lhs))
   ((or (variablep lhs)
        (fquotep lhs)
        (flambda-applicationp lhs)
        (eq (ffn-symb lhs) 'if))
    (msg
     "A :REWRITE rule generated from ~x0 is illegal because it rewrites the ~
      ~@1 ~x2.  See :DOC rewrite."
     name
     (cond ((variablep lhs) "variable symbol")
           ((fquotep lhs) "quoted constant")
           ((flambda-applicationp lhs) "LET-expression")
           (t "IF-expression"))
     lhs))
   (t (let ((bad-synp-hyp-msg (bad-synp-hyp-msg
                               hyps (all-vars lhs) nil wrld)))
        (cond
         (bad-synp-hyp-msg
          (msg
           "A rewrite rule generated from ~x0 is illegal because ~@1"
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
         (mv 'equal (fargn term 1) (fargn term 2) nil))
        ((if equiv-okp
             (equivalence-relationp (ffn-symb term) wrld)
           (member-eq (ffn-symb term) '(equal iff)))
         (mv-let (equiv ttree)
                 (cond ((eq (ffn-symb term) 'iff)
                        (mv-let
                         (ts ttree)
                         (type-set (fargn term 1) nil nil nil ens wrld nil
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
                 (mv equiv (fargn term 1) (fargn term 2) ttree)))
        ((eq (ffn-symb term) 'not) (mv 'equal (fargn term 1) *nil* nil))
        (t (mv-let (ts ttree)
                   (type-set term nil nil nil ens wrld nil nil nil)
                   (cond ((ts-subsetp ts *ts-boolean*)
                          (mv 'equal term *t* ttree))
                         (t (mv 'iff term *t* nil)))))))

(defun interpret-term-as-rewrite-rule (name hyps term ens wrld)

; This function returns five values.  The first can be a msg for printing an
; error message.  Otherwise the first is nil, in which case the second is an
; equivalence relation, eqv; the next two are terms, lhs and rhs, such that
; (eqv lhs rhs) is propositionally equivalent to term; and the last is an
; 'assumption-free ttree justifying the claim.

  (let ((term (remove-lambdas term)))
    (mv-let
     (eqv lhs rhs ttree)
     (interpret-term-as-rewrite-rule1 term t ens wrld)
     (let ((msg (interpret-term-as-rewrite-rule2 name hyps lhs rhs wrld)))
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
           ((interpret-term-as-rewrite-rule2 name hyps lhs2 rhs2 wrld)
            (mv msg eqv lhs rhs ttree))
           (t (mv nil eqv2 lhs2 rhs2 ttree2)))))
        (t (mv nil eqv lhs rhs ttree)))))))

; We inspect the lhs and some hypotheses with the following function
; to determine if non-recursive defuns will present a problem to the
; user.

(mutual-recursion

(defun non-recursive-fnnames (term ens wrld)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (add-to-set-equal (ffn-symb term)
                           (non-recursive-fnnames-lst (fargs term) ens wrld)))
        ((let ((def-body (def-body (ffn-symb term) wrld)))
           (and def-body
                (enabled-numep (access def-body def-body :nume)
                               ens)
                (not (access def-body def-body :recursivep))))
         (add-to-set-eq (ffn-symb term)
                        (non-recursive-fnnames-lst (fargs term) ens wrld)))
        (t (non-recursive-fnnames-lst (fargs term) ens wrld))))

(defun non-recursive-fnnames-lst (lst ens wrld)
  (cond ((null lst) nil)
        (t (union-equal (non-recursive-fnnames (car lst) ens wrld)
                        (non-recursive-fnnames-lst (cdr lst) ens wrld)))))

)

; The list just constructed is odd because it may contain some lambda
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

; If lhs and rhs are variants, we return the "expansion" (see next
; paragraph) of the subset of the unifying substitution containing
; those pairs (x . y) in which a variable symbol (y) is being moved
; forward (to the position of x) in the print representation of the
; term.  For example, suppose lhs is (foo x y z) and rhs is (foo y z
; x).  Then both y and z are moved forward, so the loop-stopper is the
; "expansion" of '((y . z) (x . y)).  This function exploits the fact
; that all-vars returns the set of variables listed in reverse
; print-order.

; In the paragraph above, the "expansion" of a substitution ((x1 .
; y1) ... (xn . yn)) is the list ((x1 y1 . fns-1) ... (xn yn .
; fns-n)), where fns-i is the list of function symbols of subterms of
; lhs that contain xi or yi (or both) as a top-level argument.
; Exception: If any such "function symbol" is a LAMBDA, then fns-i is
; nil.

; Note: John Cowles first suggested the idea that led to the idea of
; invisible function symbols as implemented here.  Cowles observation
; was that it would be very useful if x and (- x) were moved into
; adjacency by permutative rules.  His idea was to redefine term-order
; so that those two terms were of virtually equal weight.  Our notion
; of invisible function symbols and the handling of loop-stopper is
; meant to address Cowles original concern without complicating
; term-order, which is used in places besides permutative rewriting.

  ":Doc-Section Miscellaneous

  limit application of permutative rewrite rules~/

  ~l[rule-classes] for a discussion of the syntax of the
  ~c[:loop-stopper] field of ~c[:]~ilc[rewrite] rule-classes.  Here we describe how
  that field is used, and also how that field is created when the user
  does not explicitly supply it.

  For example, the built-in ~c[:]~ilc[rewrite] rule ~c[commutativity-of-+],
  ~bv[]
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (+ x y) (+ y x))),
  ~ev[]
  creates a rewrite rule with a loop-stopper of ~c[((x y binary-+))].
  This means, very roughly, that the term corresponding to ~c[y] must be
  ``smaller'' than the term corresponding to ~c[x] in order for this rule
  to apply.  However, the presence of ~ilc[binary-+] in the list means that
  certain functions that are ``invisible'' with respect to ~ilc[binary-+]
  (by default, ~ilc[unary--] is the only such function) are more or less
  ignored when making this ``smaller'' test.  We are much more precise
  below.~/

  Our explanation of loop-stopping is in four parts.  First we discuss
  ACL2's notion of ``term order.''  Next, we bring in the notion of
  ``invisibility'', and use it together with term order to define
  orderings on terms that are used in the loop-stopping algorithm.
  Third, we describe that algorithm.  These topics all assume that we
  have in hand the ~c[:loop-stopper] field of a given rewrite rule; the
  fourth and final topic describes how that field is calculated when
  it is not supplied by the user.

  ACL2 must sometimes decide which of two terms is syntactically
  simpler.  It uses a total ordering on terms, called the ``term
  order.''  Under this ordering constants such as ~c['(a b c)] are simpler
  than terms containing variables such as ~c[x] and ~c[(+ 1 x)].  Terms
  containing variables are ordered according to how many occurrences
  of variables there are.  Thus ~c[x] and ~c[(+ 1 x)] are both simpler than
  ~c[(cons x x)] and ~c[(+ x y)].  If variable counts do not decide the order,
  then the number of function applications are tried.  Thus ~c[(cons x x)]
  is simpler than ~c[(+ x (+ 1 y))] because the latter has one more
  function application.  Finally, if the number of function
  applications do not decide the order, a lexicographic ordering on
  Lisp objects is used.  ~l[term-order] for details.

  When the loop-stopping algorithm is controlling the use of
  permutative ~c[:]~ilc[rewrite] rules it allows ~c[term1] to be moved leftward over
  ~c[term2] only if ~c[term1] is smaller, in a suitable sense.  Note: The
  sense used in loop-stopping is ~st[not] the above explained term order
  but a more complicated ordering described below.  The use of a total
  ordering stops rules like commutativity from looping indefinitely
  because it allows ~c[(+ b a)] to be permuted to ~c[(+ a b)] but not vice
  versa, assuming ~c[a] is smaller than ~c[b] in the ordering.  Given a set of
  permutative rules that allows arbitrary permutations of the tips of
  a tree of function calls, this will normalize the tree so that the
  smallest argument is leftmost and the arguments ascend in the order
  toward the right.  Thus, for example, if the same argument appears
  twice in the tree, as ~c[x] does in the ~ilc[binary-+] tree denoted by the
  term ~c[(+ a x b x)], then when the allowed permutations are done, all
  occurrences of the duplicated argument in the tree will be adjacent,
  e.g., the tree above will be normalized to ~c[(+ a b x x)].

  Suppose the loop-stopping algorithm used term order, as noted above,
  and consider the ~ilc[binary-+] tree denoted by ~c[(+ x y (- x))].  The
  arguments here are in ascending term order already.  Thus, no
  permutative rules are applied.  But because we are inside a
  ~c[+-expression] it is very convenient if ~c[x] and ~c[(- x)] could be given
  virtually the same position in the ordering so that ~c[y] is not
  allowed to separate them.  This would allow such rules as
  ~c[(+ i (- i) j) = j] to be applied.  In support of this, the
  ordering used in the control of permutative rules allows certain
  unary functions, e.g., the unary minus function above, to be
  ``invisible'' with respect to certain ``surrounding'' functions,
  e.g., ~ilc[+] function above.

  Briefly, a unary function symbol ~c[fn1] is invisible with respect to a
  function symbol ~c[fn2] if ~c[fn2] belongs to the value of ~c[fn1] in
  ~ilc[invisible-fns-table]; also ~pl[set-invisible-fns-table], which
  explains its format and how it can be set by the user.  Roughly
  speaking, ``invisible'' function symbols are ignored for the
  purposes of the term-order test.

  Consider the example above, ~c[(+ x y (- x))].  The translated version
  of this term is ~c[(binary-+ x (binary-+ y (unary-- x)))].  The initial
  ~ilc[invisible-fns-table] makes ~ilc[unary--] invisible with repect to ~ilc[binary-+].
  The commutativity rule for ~ilc[binary-+] will attempt to swap ~c[y] and
  ~c[(unary-- x)] and the loop-stopping algorithm is called to approve or
  disapprove.  If term order is used, the swap will be disapproved.
  But term order is not used.  While the loop-stopping algorithm is
  permuting arguments inside a ~ilc[binary-+] expression, ~ilc[unary--] is
  invisible.  Thus, insted of comparing ~c[y] with ~c[(unary-- x)], the
  loop-stopping algorithm compares ~c[y] with ~c[x], approving the swap
  because ~c[x] comes before ~c[y].

  Here is a more precise specification of the total order used for
  loop-stopping with respect to a list, ~c[fns], of functions that are to
  be considered invisible.  Let ~c[x] and ~c[y] be distinct terms; we specify
  when ``~c[x] is smaller than ~c[y] with respect to ~c[fns].''  If ~c[x] is the
  application of a unary function symbol that belongs to ~c[fns], replace
  ~c[x] by its argument.  Repeat this process until the result is not the
  application of such a function; let us call the result ~c[x-guts].
  Similarly obtain ~c[y-guts] from ~c[y].  Now if ~c[x-guts] is the same term as
  ~c[y-guts], then ~c[x] is smaller than ~c[y] in this order iff ~c[x] is smaller than
  ~c[y] in the standard term order.  On the other hand, if ~c[x-guts] is
  different than ~c[y-guts], then ~c[x] is smaller than ~c[y] in this order iff
  ~c[x-guts] is smaller than ~c[y-guts] in the standard term order.

  Now we may describe the loop-stopping algorithm.  Consider a rewrite
  rule with conclusion ~c[(equiv lhs rhs)] that applies to a term ~c[x] in a
  given context; ~pl[rewrite].  Suppose that this rewrite rule has
  a loop-stopper field (technically, the ~c[:heuristic-info] field) of
  ~c[((x1 y1 . fns-1) ... (xn yn . fns-n))].  (Note that this field can be
  observed by using the command ~c[:]~ilc[pr] with the name of the rule;
  ~pl[pr].)  We describe when rewriting is permitted.  The
  simplest case is when the loop-stopper list is ~c[nil] (i.e., ~c[n] is ~c[0]);
  in that case, rewriting is permitted.  Otherwise, for each ~c[i] from 1
  to ~c[n] let ~c[xi'] be the actual term corresponding to the variable ~c[xi]
  when ~c[lhs] is matched against the term to be rewritten, and similarly
  correspond ~c[yi'] with ~c[y].  If ~c[xi'] and ~c[yi'] are the same term for all ~c[i],
  then rewriting is not permitted.  Otherwise, let ~c[k] be the least ~c[i]
  such that ~c[xi'] and ~c[yi'] are distinct.  Let ~c[fns] be the list of all
  functions that are invisible with respect to every function in
  ~c[fns-k], if ~c[fns-k] is non-empty; otherwise, let ~c[fns] be ~c[nil].  Then
  rewriting is permitted if and only if ~c[yi'] is smaller than ~c[xi'] with
  respect to ~c[fns], in the sense defined in the preceding paragraph.

  It remains only to describe how the loop-stopper field is calculated
  for a rewrite rule when this field is not supplied by the user.  (On
  the other hand, to see how the user may specify the ~c[:loop-stopper],
  ~pl[rule-classes].)  Suppose the conclusion of the rule is of
  the form ~c[(equiv lhs rhs)].  First of all, if ~c[rhs] is not an instance
  of the left hand side by a substitution whose range is a list of
  distinct variables, then the loop-stopper field is ~c[nil].  Otherwise,
  consider all pairs ~c[(u . v)] from this substitution with the property
  that the first occurrence of ~c[v] appears in front of the first
  occurrence of ~c[u] in the print representation of ~c[rhs].  For each such ~c[u]
  and ~c[v], form a list ~c[fns] of all functions ~c[fn] in ~c[lhs] with the property
  that ~c[u] or ~c[v] (or both) appears as a top-level argument of a subterm
  of ~c[lhs] with function symbol ~c[fn].  Then the loop-stopper for this
  rewrite rule is a list of all lists ~c[(u v . fns)].~/"

  (mv-let (ans unify-subst)
    (variantp lhs rhs)
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
; the subsitution is irrelevant.  If the conjunction above is true, then
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
; the subsitution is irrelevant.  If the conjunction above is true, then
; the current hyp is of the form (equiv v term) and v will be chosen
; by rewriting term.  V is not a "free variable".

            (cond
             ((and flg (not forcep))
              (free-vars-in-hyps-considering-bind-free
               (cdr hyps)
               (cons (fargn (car hyps) 1) bound-vars)
               wrld))
             ((and (nvariablep (car hyps))
                   (not (fquotep (car hyps)))
                   (eq (ffn-symb (car hyps)) 'synp)
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

  (cond ((null hyps)
         nil)
        ((variablep (car hyps))
         (add-to-set-eq (car hyps)
                        (all-vars-in-hyps (cdr hyps))))
        ((fquotep (car hyps))
         (all-vars-in-hyps (cdr hyps)))
        ((eq (ffn-symb (car hyps)) 'synp)
         (cond ((equal (fargn (car hyps) 1) *nil*)
                (all-vars-in-hyps (cdr hyps)))
               ((equal (fargn (car hyps) 1) *t*)
                t)
               ((and (quotep (fargn (car hyps) 1))
                     (not (collect-non-legal-variableps
                           (cadr (fargn (car hyps) 1)))))
                (union-eq (cadr (fargn (car hyps) 1))
                          (all-vars-in-hyps (cdr hyps))))
               (t (er hard 'free-vars-in-hyps-considering-bind-free
                      "We thought the first argument of synp in this context ~
                       was either 'NIL, 'T, or else a quoted true list of ~
                       variables, but ~x0 is not!"
                      (fargn (car hyps) 1)))))
        (t
         (union-eq (all-vars (car hyps))
                   (all-vars-in-hyps (cdr hyps))))))

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
                  (make-list (length hyps)
                             :initial-element
                             limit))))))

(defun create-rewrite-rule (rune nume hyps equiv lhs rhs loop-stopper-lst
                                 backchain-limit-lst match-free-value wrld)

; This function creates a :REWRITE rule of subclass 'backchain or
; 'abbreviation from the basic ingredients, preprocessing the hyps and
; computing the loop-stopper.  Equiv is an equivalence relation name.

  (let ((hyps (preprocess-hyps hyps))
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
          :subclass (cond ((and (null hyps)
                                (null loop-stopper)
                                (abbreviationp nil
                                               (all-vars-bag lhs nil)
                                               rhs))
                           'abbreviation)
                          (t 'backchain))
          :heuristic-info loop-stopper
          
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

  (and (refinementp (access rewrite-rule rule1 :equiv)
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
              (not (fquotep (car lst)))
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
                                  (not (fquotep (car hyps)))
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
; result extends alist by assocating variable var with geneqv, thus extending
; the generated equivalence relation already associated with var in alist.

  (put-assoc-eq var
                (union-geneqv geneqv (cdr (assoc-eq var alist)) wrld)
                alist))

(mutual-recursion

(defun covered-geneqv-alist (term geneqv alist wrld)

; Extends alist, an accumulator, as follows.  The result associates, with each
; variable bound in term, a geneqv representing the list of all equivalence
; relations that are sufficient to preserve at one or more free occurrences of
; that variable in term, in order to preserve the given geneqv at term.  This
; function creates the initial bound-vars-alist for
; double-rewrite-opportunities; see also the comment there.

; Alist is an accumulator with entries of the form (variable . geneqv).

  (cond ((variablep term)
         (extend-geneqv-alist term geneqv alist wrld))
        ((fquotep term)
         alist)
        (t
         (covered-geneqv-alist-lst (fargs term)
                                   (geneqv-lst (ffn-symb term) geneqv nil wrld)
                                   alist
                                   wrld))))

(defun covered-geneqv-alist-lst (termlist geneqv-lst alist wrld)
  (cond ((endp termlist)
         alist)
        (t (covered-geneqv-alist-lst (cdr termlist)
                                     (cdr geneqv-lst)
                                     (covered-geneqv-alist (car termlist) (car geneqv-lst)
                                                           alist wrld)
                                     wrld))))
)

(defun uncovered-equivs (geneqv covered-geneqv wrld)
  (cond ((endp geneqv) nil)
        (t (let ((equiv (access congruence-rule (car geneqv) :equiv))
                 (rst (uncovered-equivs (cdr geneqv) covered-geneqv wrld)))
             (cond ((geneqv-refinementp equiv covered-geneqv wrld)
                    rst)
                   (t (cons equiv rst)))))))

(mutual-recursion

(defun uncovered-equivs-alist (term geneqv var-geneqv-alist var-geneqv-alist0
                                    obj-not-? acc-equivs acc-counts wrld)

; Accumulator acc-equiv is an alist that associates variables with lists of
; equivalence relations, and accumulator acc-counts associates variables with
; natural numbers.  We are given a term whose value is to be maintained with
; respect to the given geneqv, along with var-geneqv-alist, which associates
; variables with ilsts of equivalence relations.  We return extensions of
; acc-equivs, acc-counts, and var-geneqv-alist as follows.

; Consider a bound (by var-geneqv-alist) variable occurrence in term.  Its
; context is known to preserve certain equivalence relations; but some of these
; may be "uncovered", i.e., not among the ones associated with this variable in
; var-geneqv-alist.  If that is the case, then add those "uncovered"
; equivalence relations to the list associated with this variable in
; acc-equivs, and increment the value of this variable in acc-counts by 1.

; However, we skip the above analysis for the case that geneqv is *geneqv-iff*
; and we are at the top level of the IF-structure of the top-level term (not
; including the tests).  This function is used for creating warnings that
; suggest the use of double-rewrite, which however is generally not necessary
; in such situations; see rewrite-solidify-plus.

; For a free variable occurrence in term, we leave acc-equivs and acc-counts
; unchanged, and instead extend var-geneqv-alist by associating this variable
; with the geneqv for its context.  Var-geneqv-alist0 is left unchanged by this
; process, for purposes of checking free-ness.

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
   ((and obj-not-?
         (eq (ffn-symb term) 'if))
    (mv-let (acc-equivs acc-counts var-geneqv-alist)
            (uncovered-equivs-alist
             (fargn term 3)
             geneqv
             var-geneqv-alist
             var-geneqv-alist0
             t
             acc-equivs acc-counts
             wrld)
            (mv-let (acc-equivs acc-counts var-geneqv-alist)
                    (uncovered-equivs-alist
                     (fargn term 2)
                     geneqv
                     var-geneqv-alist
                     var-geneqv-alist0
                     t
                     acc-equivs acc-counts
                     wrld)
                    (uncovered-equivs-alist
                     (fargn term 1)
                     *geneqv-iff*
                     var-geneqv-alist
                     var-geneqv-alist0
                     nil
                     acc-equivs acc-counts
                     wrld))))
   (t (uncovered-equivs-alist-lst
       (fargs term)
       (geneqv-lst (ffn-symb term) geneqv nil wrld)
       var-geneqv-alist var-geneqv-alist0 acc-equivs acc-counts wrld))))

(defun uncovered-equivs-alist-lst (termlist geneqv-lst var-geneqv-alist
                                            var-geneqv-alist0 acc-equivs
                                            acc-counts wrld)
  (cond ((endp termlist)
         (mv acc-equivs acc-counts var-geneqv-alist))
        (t (mv-let (acc-equivs acc-counts var-geneqv-alist)
             (uncovered-equivs-alist (car termlist)
                                     (car geneqv-lst)
                                     var-geneqv-alist
                                     var-geneqv-alist0
                                     nil
                                     acc-equivs acc-counts
                                     wrld)
             (uncovered-equivs-alist-lst (cdr termlist) (cdr geneqv-lst)
                                         var-geneqv-alist
                                         var-geneqv-alist0
                                         acc-equivs acc-counts
                                         wrld)))))
)

(defun double-rewrite-opportunities (hyp-index hyps var-geneqv-alist
                                     final-term final-location final-geneqv
                                     wrld)

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
; conclusion of a linear rule, using the parameters final-xxx.

; Var-geneqv-alist is an alist that binds variables to geneqvs.  Initially, the
; keys are exactly the bound variables of the unifying substitution.  Each key
; is associated with a geneqv that represents the equivalence relation
; generated by all equivalence relations known to be preserved for at least one
; variable occurrence in the pattern that was matched to give the unifying
; substitution (the left left-hand side of a rewrite rule or max-term of a
; linear rule).  As we move through hyps, we may encounter a hypothesis (equal
; var term) or (equiv var (double-rewrite term)) that binds a variable, var, in
; which case we will extend var-geneqv-alist for var at that point.  Note that
; we do not extend var-geneqv-alist for other free variables in hypotheses,
; because we do not know the equivalence relations that were maintained when
; creating the rewritten terms to which the free variables are bound.

  (cond ((endp hyps)
         (mv-let (var-equivs-alist var-counts var-geneqv-alist)
                 (uncovered-equivs-alist final-term final-geneqv
                                         var-geneqv-alist var-geneqv-alist
                                         nil nil nil wrld)
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
                           (term (if (and (nvariablep term0)
                                          (not (fquotep term0))
                                          (eq (ffn-symb term0)
                                              'double-rewrite))
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
                                             (assert$ (variablep var)
                                                      (extend-geneqv-alist
                                                       var new-geneqv
                                                       var-geneqv-alist wrld))
                                             wrld)
                       final-term final-location final-geneqv
                       wrld)))
                   (t (mv-let (var-equivs-alist var-counts var-geneqv-alist)
                              (uncovered-equivs-alist (car hyps)
                                                      *geneqv-iff*
                                                      var-geneqv-alist
                                                      var-geneqv-alist
                                                      t
                                                      nil nil
                                                      wrld)
                        (let ((cdr-result
                               (double-rewrite-opportunities (1+ hyp-index)
                                                             (cdr hyps)
                                                             var-geneqv-alist
                                                             final-term
                                                             final-location
                                                             final-geneqv
                                                             wrld)))
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
                               "In a ~x0 rule generated from ~x1~@2, ~
                                equivalence relation~#3~[ ~&3~ is~/s ~&3 ~
                                are~] maintained at ~n4 problematic ~
                                occurrence~#5~[~/s~] of variable ~x6 in ~@7, ~
                                but not at any binding occurrence of ~x6.  ~
                                Consider replacing ~#5~[that ~
                                occurrence~/those ~n4 occurrences~] of ~x6 in ~
                                ~@7 with ~x8.  See :doc double-rewrite for ~
                                more information on this issue."
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

(defun chk-rewrite-rule-warnings (name match-free loop-stopper rule ctx ens
                                       wrld state)
  (let* ((token (if (eq (access rewrite-rule rule :subclass)
                        'definition)
                    :definition
                  :rewrite))
         (hyps (access rewrite-rule rule :hyps))
         (lhs (access rewrite-rule rule :lhs))
         (non-rec-fns-lhs (non-recursive-fnnames lhs ens wrld))
         (lhs-vars (all-vars lhs))
         (rhs-vars (all-vars (access rewrite-rule rule :rhs)))
         (free-vars (free-vars-in-hyps-considering-bind-free
                     hyps
                     lhs-vars
                     wrld))
         (inst-hyps (hyps-that-instantiate-free-vars free-vars hyps))
         (non-rec-fns-inst-hyps
          (non-recursive-fnnames-lst 
           (strip-top-level-nots-and-forces inst-hyps) ens wrld))
         (subsume-check-enabled (not (warning-disabled-p "Subsume")))
         (subsumed-rule-names
          (and subsume-check-enabled
               (find-subsumed-rule-names (getprop (ffn-symb lhs) 'lemmas nil
                                                  'current-acl2-world wrld)
                                         rule ens wrld)))
         (subsuming-rule-names
          (and subsume-check-enabled
               (find-subsuming-rule-names (getprop (ffn-symb lhs) 'lemmas nil
                                                   'current-acl2-world wrld)
                                          rule ens wrld)))
         (equiv (access rewrite-rule rule :equiv))
         (double-rewrite-opportunities
          (and (not (warning-disabled-p "Double-rewrite"))
               (double-rewrite-opportunities
                1
                hyps
                (covered-geneqv-alist
                 lhs
                 (cadr (geneqv-lst equiv nil nil wrld)) ; geneqv
                 nil wrld)
                (access rewrite-rule rule :rhs)
                "the right-hand side"
                (cadr (geneqv-lst (access rewrite-rule rule :equiv) nil nil wrld))
                wrld))))
    (pprogn
     (cond (double-rewrite-opportunities
            (show-double-rewrite-opportunities double-rewrite-opportunities
                                               token name "" ctx state))
           (t state))
     (cond
      (non-rec-fns-lhs
       (warning$ ctx "Non-rec"
                 "A ~x0 rule generated from ~x1 will be ~
                 triggered only by terms containing the non-recursive ~
                 function symbol~#2~[ ~&2.  Unless this function ~
                 is~/s ~&2.  Unless these functions are~] disabled, ~
                 this rule is unlikely ever to be used."
                 token name (hide-lambdas non-rec-fns-lhs)))
      (t state))
     (er-progn
      (cond
       ((and free-vars (null match-free))
        (pprogn
         (warning$ ctx "Free"
                   "A ~x0 rule generated from ~x1 contains the free ~
                    variable~#2~[ ~&2.  This variable~/s ~&2.  These ~
                    variables~] will be chosen by searching for ~#3~[an ~
                    instance~/instances~] of ~*4 in the context of the term ~
                    being rewritten.  This is generally a severe restriction ~
                    on the applicability of a ~x0 rule.  See :DOC ~
                    free-variables."
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
        (non-rec-fns-inst-hyps
         (warning$ ctx "Non-rec"
                   "As noted, we will instantiate the free ~
                    variable~#0~[~/s~], ~&0, of a ~x1 rule generated from ~
                    ~x2, by searching for the ~#3~[hypothesis~/set of ~
                    hypotheses~] shown above.  However, ~#3~[this hypothesis ~
                    mentions~/these hypotheses mention~] the function ~
                    symbol~#4~[ ~&4, which is~/s ~&4, which are~] defun'd ~
                    non-recursively.  Unless disabled, ~#4~[this function ~
                    symbol is~/these function symbols are~] unlikely to occur ~
                    in the conjecture being proved and hence the search for ~
                    the required ~#3~[hypothesis~/hypotheses~] will likely ~
                    fail."
                   free-vars token name inst-hyps
                   (hide-lambdas non-rec-fns-inst-hyps)))
        (t state))
       (cond
        (subsumed-rule-names
         (warning$ ctx ("Subsume")
                   "A newly proposed ~x0 rule generated from ~x1 probably ~
                    subsumes the previously added :REWRITE rule~#2~[~/s~] ~
                    ~&2, in the sense that the new rule will now probably be ~
                    applied whenever the old rule~#2~[~/s~] would have been."
                   token name subsumed-rule-names))
        (t state))
       (cond
        (subsuming-rule-names
         (warning$ ctx ("Subsume")
                   "The previously added rule~#1~[~/s~] ~&1 subsume~#1~[s~/~] ~
                    a newly proposed ~x0 rule generated from ~x2, in the ~
                    sense that the old rule~#1~[ rewrites a more general ~
                    target~/s rewrite more general targets~].  Because the ~
                    new rule will be tried first, it may nonetheless find ~
                    application."
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

(defun chk-acceptable-rewrite-rule2 (name match-free loop-stopper hyps concl
                                          ctx ens wrld state)

; This is the basic function for checking that (IMPLIES (AND . hyps)
; concl) generates a useful :REWRITE rule.  If it does not, we cause an
; error.  If it does, we may print some warnings regarding the rule
; generated.  The superior functions, chk-acceptable-rewrite-rule1
; and chk-acceptable-rewrite-rule just cycle down to this one after
; flattening the IMPLIES/AND structure of the user's input term.  When
; successful, this function returns a ttree justifying the storage of
; the :REWRITE rule -- it sometimes depends on type-set information.

  (mv-let
   (msg eqv lhs rhs ttree)
   (interpret-term-as-rewrite-rule name hyps concl ens wrld)
   (cond
    (msg (er soft ctx "~@0" msg))
    (t (let ((rewrite-rule
              (create-rewrite-rule *fake-rune-for-anonymous-enabled-rule*
                                   nil hyps eqv lhs rhs nil nil nil wrld)))

; The :REWRITE rule created above is used only for subsumption checking and
; then discarded.  The rune, nume, loop-stopper-lst, and match-free used are
; irrelevant.  The warning messages, if any, concerning subsumption report the
; name of the rule as name.

         (er-progn
          (chk-rewrite-rule-warnings name match-free loop-stopper
                                     rewrite-rule ctx ens wrld state)
          (value ttree)))))))

(defun chk-acceptable-rewrite-rule1 (name match-free loop-stopper lst ctx ens
                                          wrld state)

; Each element of lst is a pair, (hyps . concl) and we check that each
; such pair, when interpreted as the term (implies (and . hyps)
; concl), generates a legal :REWRITE rule.  We return the accumulated
; ttrees.

  (cond
   ((null lst) (value nil))
   (t (er-let* ((ttree1
                 (chk-acceptable-rewrite-rule2 name match-free loop-stopper
                                               (caar lst) (cdar lst)
                                               ctx ens wrld state))
                (ttree
                 (chk-acceptable-rewrite-rule1 name match-free loop-stopper
                                               (cdr lst) ctx ens wrld state)))
               (value (cons-tag-trees ttree1 ttree))))))

(defun chk-acceptable-rewrite-rule (name match-free loop-stopper term ctx ens
                                         wrld state)

; We strip the conjuncts out of term and flatten those in the
; hypotheses of implications to obtain a list of implications, each of
; the form (IMPLIES (AND . hyps) concl), and each represented simply
; by a pair (hyps . concl).  For each element of that list we then
; determine whether it generates a legal :REWRITE rule.  See
; chk-acceptable-rewrite-rule2 for the guts of this test.  We either
; cause an error or return successfully.  We may print warning
; messages without causing an error.  On successful returns the value
; is a ttree that justifies the storage of all the :REWRITE rules.

  (chk-acceptable-rewrite-rule1 name match-free loop-stopper
                                (unprettyify (remove-guard-holders term))
                                ctx ens wrld state))

; So now we work on actually generating and adding the rules.

(defun add-rewrite-rule2 (rune nume hyps concl loop-stopper-lst
                               backchain-limit-lst match-free ens wrld)

; This is the basic function for generating and adding a rule named
; rune from the formula (IMPLIES (AND . hyps) concl).

  (mv-let
   (msg eqv lhs rhs ttree)
   (interpret-term-as-rewrite-rule (base-symbol rune) hyps concl ens wrld)
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
          proposed :REWRITE rule generated from ~x0 is of the form (equiv LHS ~
          RHS), where equiv was a known equivalence relation when this rule ~
          was originally processed, but that is no longer the case.  As a ~
          result,the rule is now treated as rewriting (equiv LHS RHS) to t, ~
          and yet a BIND-FREE hypothesis is attempting to bind a variable in ~
          RHS.  Perhaps you can fix this problem by making equiv an ~
          equivalence relation non-locally."
         (base-symbol rune)))
    (t
     (let* ((match-free-value (match-free-value match-free hyps lhs wrld))
            (rewrite-rule (create-rewrite-rule rune nume hyps eqv
                                               lhs rhs
                                               loop-stopper-lst
                                               backchain-limit-lst
                                               match-free-value
                                               wrld))
            (wrld1 (putprop (ffn-symb lhs)
                            'lemmas
                            (cons rewrite-rule
                                  (getprop (ffn-symb lhs) 'lemmas nil
                                           'current-acl2-world wrld))
                            wrld)))
       (put-match-free-value match-free-value rune wrld1))))))

(defun add-rewrite-rule1 (rune nume lst loop-stopper-lst
                               backchain-limit-lst match-free ens wrld)

; Each element of lst is a pair, (hyps . concl).  We generate and
; add to wrld a :REWRITE for each.

  (cond ((null lst) wrld)
        (t (add-rewrite-rule1 rune nume (cdr lst)
                              loop-stopper-lst
                              backchain-limit-lst
                              match-free
                              ens
                              (add-rewrite-rule2 rune nume
                                                 (caar lst)
                                                 (cdar lst)
                                                 loop-stopper-lst
                                                 backchain-limit-lst
                                                 match-free
                                                 ens
                                                 wrld)))))

(defun add-rewrite-rule (rune nume loop-stopper-lst term
                              backchain-limit-lst match-free ens wrld)

; This function might better be called "add-rewrite-rules" because we
; may get many :REWRITE rules from term.  But we are true to our naming
; convention.  "Consistency is the hobgoblin of small minds."  Emerson?

  (add-rewrite-rule1 rune nume
                     (unprettyify (remove-guard-holders term))
                     loop-stopper-lst backchain-limit-lst match-free ens wrld))

;---------------------------------------------------------------------------
; Section:  :LINEAR Rules

; We now move on to :LINEAR class rules.

(deflabel linear
  :doc
  ":Doc-Section Rule-Classes

  make some arithmetic inequality rules~/

  ~l[rule-classes] for a general discussion of rule classes and how they are
  used to build rules from formulas.  An example ~c[:]~ilc[corollary] formula
  from which a ~c[:linear] rule might be built is:
  ~bv[]
  Example:
  (implies (and (eqlablep e)           if inequality reasoning begins to
                (true-listp x))        consider how (length (member a b))
           (<= (length (member e x))   compares to any other term, add to
               (length x)))            set of known inequalities the fact
                                       that it is no larger than (length b),
                                       provided (eqlablep a) and (true-listp b)
                                       rewrite to t

  General Form:
  (and ...
       (implies (and ...hi...)
                (implies (and ...hk...)
                         (and ...
                              (rel lhs rhs)
                              ...)))
       ...)
  ~ev[]

  Note: One ~c[:linear] rule class object might create many linear arithmetic
  rules from the ~c[:]~ilc[corollary] formula.  To create the rules, we first
  flatten the ~ilc[and] and ~ilc[implies] structure of the formula,
  transforming it into a conjunction of formulas, each of the form
  ~bv[]
  (implies (and h1 ... hn) (rel lhs rhs))
  ~ev[]
  where no hypothesis is a conjunction and ~c[rel] is one of the inequality
  relations ~ilc[<], ~ilc[<=], ~ilc[=], ~ilc[>], or ~ilc[>=].  If necessary,
  the hypothesis of such a conjunct may be vacuous.  We create a ~c[:linear]
  rule for each such conjunct, if possible, and otherwise cause an error.~/

  Each rule has one or more ``trigger terms'' which may be specified by the
  user using the ~c[:trigger-terms] field of the rule class or which may be
  defaulted to values chosen by the system.  We discuss the determination of
  trigger terms after discussing how linear rules are used.

  ~c[:Linear] rules are used by an arithmetic decision procedure during
  rewriting.  ~l[linear-arithmetic] and ~pl[non-linear-arithmetic].  Here we
  assume that the reader is familiar with the material described in
  ~ilc[linear-arithmetic].

  Recall that we eliminate the unknowns of an inequality in term-order, largest
  unknowns first.  (~l[term-order].)  In order to facilitate this strategy, we
  store the inequalities in ``linear pots''.  For purposes of the present
  discussion, let us say that an inequality is ``about'' its largest unknown.
  Then, all of the inequalities about a particular unknown are stored in the
  same linear pot, and the pot is said to be ``labeled'' with that unknown.
  This storage layout groups all of the inequalities which are potential
  candidates for cancellation with each other into one place.  It is also key
  to the efficient operation of ~c[:linear] rules.

  If the arithmetic decision procedure has stabilized and not yielded a
  contradiction, we scan through the list of linear pots examining each label
  as we go.  If the trigger term of some ~c[:linear] rule can be instantiated
  to match the label, we so instantiate that rule and attempt to relieve the
  hypotheses with general-purpose rewriting.  If we are successful, we add the
  rule's instantiated conclusion to our set of inequalities.  This may let
  cancellation continue.

  Note: Problems may arise if you explicitly store a linear lemma under a
  trigger term that, when instantiated, is not the largest unknown in the
  instantiated concluding inequality.  Suppose for example you store the linear
  rule ~c[(<= (fn i j) (/ i (* j j)))] under the trigger term ~c[(fn i j)].
  Then when the system ``needs'' an inequality about ~c[(fn a b)], (i.e.,
  because ~c[(fn a b)] is the label of some linear pot, and hence the largest
  unknown in some inequality), it will appeal to the rule and deduce
  ~c[(<= (fn a b) (/ a (* b b)))].  However, the largest unknown in this
  inequality is ~c[(/ a (* b b))] and hence it will be stored in a linear pot
  labeled with ~c[(/ a (* b b))].  The original, triggering inequality which is
  in a pot about ~c[(fn a b)] will therefore not be cancelled against the new
  one.  It is generally best to specify as a trigger term one of the
  ``maximal'' terms of the polynomial, as described below.

  We now describe how the trigger terms are determined.  Most of the time, the
  trigger terms are not specified by the user and are instead selected by the
  system.  However, the user may specify the terms by including an explicit
  ~c[:trigger-terms] field in the rule class, e.g.,
  ~bv[]
  General Form of a Linear Rule Class:
  (:LINEAR :COROLLARY formula
           :TRIGGER-TERMS (term1 ... termk))
  ~ev[]
  Each ~c[termi] must be a term and must not be a variable, quoted constant,
  lambda application, ~c[let-expression] or ~c[if-expression].  In addition,
  each ~c[termi] must be such that if all the variables in the term are
  instantiated and then the hypotheses of the corollary formula are relieved
  (possibly instantiating additional free variables), then all the variables in
  the concluding inequality are instantiated.  We generate a linear rule for
  each conjuctive branch through the corollary and store each rule under each
  of the specified triggers.  Thus, if the corollary formula contains several
  conjuncts, the variable restrictions on the ~c[termi] must hold for each
  conjunct.

  If ~c[:trigger-terms] is omitted the system computes a set of trigger terms.
  Each conjunct of the corollary formula may be given a unique set of triggers
  depending on the variables that occur in the conjunct and the addends that
  occur in the concluding inequality.  In particular, the trigger terms for a
  conjunct is the list of all ``maximal addends'' in the concluding inequality.

  The ``addends'' of ~c[(+ x y)] and ~c[(- x y)] are the union of the addends
  of ~c[x] and ~c[y].  The addends of ~c[(- x)] and ~c[(* n x)], where ~c[n] is
  a rational constant, is just ~c[{x}].  The addends of an inequality are the
  union of the addends of the left- and right-hand sides.  The addends of any
  other term, ~c[x], is ~c[{x}].

  A term is maximal for a conjunct ~c[(implies hyps concl)] of the corollary if
  (a) the term is a non-variable, non-quote, non-lambda application,
  non-~ilc[let] and non-~ilc[if] expression, (b) the term contains enough
  variables so that when they are instantiated and the hypotheses are relieved
  (which may bind some free variables; ~pl[free-variables]) then all the
  variables in ~c[concl] are instantiated, and (c) no other addend is always
  ``bigger'' than the term, in the technical sense described below.

  The technical notion referenced above depends on the notion of ~em[fn-count],
  the number of function symbols in a term, and ~em[pseudo-fn-count], which is
  essentially the number of function symbols implicit in a constant
  (~pl[term-order], specifically the discussion of ``pseudo-function
  application count'' at the end).  We say ~c[term1] is always bigger than
  ~c[term2] if all instances of ~c[term1] have a larger fn-count (actually
  lexicographic order of fn-count and pseudo-fn-count) than the corresponding
  instances of ~c[term2].  This is equivalent to saying that the fn-count of
  ~c[term1] is larger than that of ~c[term2] (by ``fn-count'' here we mean the
  lexicographic order of fn-count and pseudo-fn-count) and the variable bag for
  ~c[term2] is a subbag of that for ~c[term1].  For example, ~c[(/ a (* b b))]
  is always bigger than ~c[(fn a b)] because the first has two function
  applications and ~c[{a b}] is a subbag of ~c[a b b], but ~c[(/ a (* b b))] is
  not always bigger than ~c[(fn a x)].")

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
; relation, <, = and /=, we reexpress it in terms of
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
                                                      ctx wrld state)
  (cond ((endp max-terms)
         state)
        (t (pprogn (show-double-rewrite-opportunities
                    (double-rewrite-opportunities
                     1
                     hyps
                     (covered-geneqv-alist (car max-terms) nil nil wrld)
                     final-term
                     "the conclusion"
                     *geneqv-iff* ; final-geneqv
                     wrld)
                    :linear name
                    (msg " for trigger term ~x0"
                         (untranslate (car max-terms) nil wrld))
                    ctx state)
                   (show-double-rewrite-opportunities-linear
                    hyps (cdr max-terms) final-term name ctx wrld
                    state)))))

(defun chk-acceptable-linear-rule2
  (name match-free trigger-terms hyps concl ctx ens wrld state)

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
         (lst (external-linearize xconcl ens wrld state)))
    (cond ((null lst)
           (er soft ctx
               "No :LINEAR rule can be generated from ~x0.  See :DOC linear."
               name))
          ((not (null (cdr lst)))
           (er soft ctx
               "No :LINEAR rule can be generated from ~x0 because the ~
                linearization of its conclusion, which in normal form is ~p1, ~
                produces a disjunction of polynomial inequalities.  See :DOC ~
                linear."
               name
               (untranslate xconcl t wrld)))
          (t (let* ((all-vars-hyps (all-vars-in-hyps hyps))
                    (potential-free-vars
                     (free-vars-in-hyps-considering-bind-free hyps nil wrld))
                    (all-vars-in-poly-lst
                     (all-vars-in-poly-lst (car lst)))
                    (max-terms
                     (or trigger-terms
                         (maximal-terms all-vars-in-poly-lst
                                        all-vars-hyps
                                        (all-vars concl))))
                    (non-rec-fns (non-recursive-fnnames-lst
                                  max-terms ens wrld))
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
                  ((null all-vars-in-poly-lst)
                   (er soft ctx 
                       "No :LINEAR rule can be generated from ~x0 because ~
                        there are no ``maximal terms'' in the inequality ~
                        produced from its conclusion.  In fact, the inequality ~
                        has simplified to one that has no variables." 
                       name))
                  (t
                   (er soft ctx
                       "No :LINEAR rule can be generated from ~x0 because ~
                        there are no ``maximal terms'' in the inequality ~
                        produced from its conclusion.  The inequality produced ~
                        from its conclusion involves a linear polynomial in ~
                        the unknown~#1~[~/s~] ~&1.  No unknown above has the ~
                        three properties of a maximal term (see :DOC linear).  ~
                        What can you do?  The most direct solution is to make ~
                        this a :REWRITE rule rather than a :LINEAR rule.  Of ~
                        course, you then have to make sure your intended ~
                        application can suffer it being a :REWRITE rule!  A ~
                        more challenging (and sometimes more rewarding) ~
                        alternative is to package up some of your functions ~
                        into a new non-recursive function (either in the ~
                        unknowns or the hypotheses) so as to create a maximal ~
                        term.  Of course, if you do that, you have to arrange ~
                        to use that non-recursive function in the intended ~
                        applications of this rule."
                       name all-vars-in-poly-lst))))
                (t
                 (mv-let (bad-synp-hyp-msg bad-max-term)
                   (bad-synp-hyp-msg-for-linear max-terms hyps wrld)
                   (cond
                    (bad-synp-hyp-msg
                     (er soft ctx
                         "While checking the hypotheses of ~x0 and using ~
                          the trigger term ~x1, the following error message ~
                          was generated: ~% ~%~
                          ~@2"
                         name
                         bad-max-term
                         bad-synp-hyp-msg))
                    (t
                     (pprogn
                      (if (warning-disabled-p "Double-rewrite")
                          state
                        (show-double-rewrite-opportunities-linear
                         hyps max-terms concl name ctx wrld state))
                      (cond
                       ((equal max-terms bad-max-terms)
                        (warning$ ctx "Non-rec"
                                  "A :LINEAR rule generated from ~x0 will be ~
                                   triggered only by terms containing the ~
                                   non-recursive function symbol~#1~[ ~&1.  Unless ~
                                   this function is~/s ~&1.  Unless these functions ~
                                   are~] disabled, such triggering terms are ~
                                   unlikely to arise and so ~x0 is unlikely to ever ~
                                   be used."
                                  name (hide-lambdas non-rec-fns)))
                       (bad-max-terms
                        (warning$ ctx "Non-rec"
                                  "A :LINEAR rule generated from ~x0 will be ~
                                   triggered by the terms ~&1. ~N2 of these terms, ~
                                   namely ~&3, contain~#3~[s~/~] the non-recursive ~
                                   function symbol~#4~[ ~&4.  Unless this function ~
                                   is~/s ~&4.  Unless these functions are~] ~
                                   disabled, ~x0 is unlikely to be triggered via ~
                                   ~#3~[this term~/these terms~]."
                                  name
                                  max-terms
                                  (length bad-max-terms)
                                  bad-max-terms
                                  (hide-lambdas non-rec-fns)))
                       (t state))
                      (cond
                       ((and (car (cddddr free-max-terms-msg))
                             (null match-free))
                        (pprogn
                         (warning$ ctx "Free"
                                   "A :LINEAR rule generated from ~x0 will be ~
                                    triggered by the term~#1~[~/s~] ~&1.  ~*2This is ~
                                    generally a severe restriction on the ~
                                    applicability of the :LINEAR rule."
                                   name
                                   max-terms
                                   free-max-terms-msg)
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
                               (unprettyify (remove-guard-holders term))
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
                                   (getprop (ffn-symb
                                             (access linear-lemma linear-rule
                                                     :max-term))
                                            'linear-lemmas nil
                                            'current-acl2-world
                                            wrld))
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
  (let* ((concl (remove-guard-holders concl))
         (xconcl (expand-inequality-fncall concl))
         (lst (external-linearize xconcl ens wrld state))
         (hyps (preprocess-hyps hyps))
         (all-vars-hyps (all-vars-in-hyps hyps))
         (max-terms
          (or trigger-terms
              (maximal-terms (all-vars-in-poly-lst (car lst))
                             all-vars-hyps
                             (all-vars concl)))))
    (add-linear-rule3 rune nume hyps xconcl max-terms backchain-limit-lst
                      match-free nil wrld)))

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
                    (unprettyify (remove-guard-holders term))
                    backchain-limit-lst match-free ens wrld state))

;---------------------------------------------------------------------------
; Section:  :WELL-FOUNDED-RELATION Rules

(deflabel well-founded-relation
  :doc
  ":Doc-Section Rule-Classes

  show that a relation is well-founded on a set~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  An example
  ~c[:]~ilc[corollary] formula from which a ~c[:well-founded-relation] rule might be
  built is as follows.  (Of course, the functions ~c[pairp], ~c[lex2p], and
  ~c[ordinate] would have to be defined first.)
  ~bv[]
  Example:
  (and (implies (pairp x) (o-p (ordinate x)))
       (implies (and (pairp x)
                     (pairp y)
                     (lex2p x y))
                (o< (ordinate x) (ordinate y))))
  ~ev[]
  The above example establishes that ~c[lex2p] is a well-founded
  relation on ~c[pairp]s.  We explain and give details below.~/

  Exactly two general forms are recognized:
  ~bv[]
  General Forms
  (AND (IMPLIES (mp x) (O-P (fn x)))              ; Property 1
       (IMPLIES (AND (mp x)                       ; Property 2
                     (mp y)
                     (rel x y))
                (O< (fn x) (fn y)))),
  ~ev[]
  or
  ~bv[]
  (AND (O-P (fn x))                               ; Property 1
       (IMPLIES (rel x y)                         ; Property 2
                (O< (fn x) (fn y))))
  ~ev[]
  where ~c[mp], ~c[fn], and ~c[rel] are function symbols, ~c[x] and ~c[y] are distinct
  variable symbols, and no other ~c[:well-founded-relation] theorem about
  ~c[fn] has been proved.  When the second general form is used, we act as
  though the first form were used with ~c[mp] being the function that
  ignores its argument and returns ~c[t].  The discussion below therefore
  considers only the first general form.

  Note: We are very rigid when checking that the submitted formula is
  of one of these forms.  For example, in the first form, we insist
  that all the conjuncts appear in the order shown above.  Thus,
  interchanging the two properties in the top-level conjunct or
  rearranging the hyptheses in the second conjunct both produce
  unrecognized forms.  The requirement that each ~c[fn] be proved
  well-founded at most once ensures that for each well-founded
  relation, ~c[fn], there is a unique ~c[mp] that recognizes the domain on
  which ~c[rel] is well-founded.  We impose this requirement simply so
  that ~c[rel] can be used as a short-hand when specifying the
  well-founded relations to be used in definitions; otherwise the
  specification would have to indicate which ~c[mp] was to be used.

  We also insist that the new ordering be embedded into the ordinals as handled
  by ~ilc[o-p] and ~ilc[o<] and not some into previously admitted user-defined
  well-founded set and relation.  This restriction should pose no hardship.  If
  ~c[mp] and ~c[rel] were previously shown to be well-founded via the embedding
  ~c[fn], and you know how to embed some new set and relation into ~c[mp] and
  ~c[rel], then by composing ~c[fn] with your new embedding and using the
  previously proved well-founded relation lemma you can embed the new set and
  relation into the ordinals.

  ~c[Mp] is a predicate that recognizes the objects that are supposedly
  ordered in a well-founded way by ~c[rel].  We call such an object an
  ``~c[mp]-measure'' or simply a ``measure'' when ~c[mp] is understood.
  Property 1 tells us that every measure can be mapped into an ACL2
  ordinal.  (~l[o-p].)  This mapping is performed by ~c[fn].
  Property 2 tells us that if the measure ~c[x] is smaller than the
  measure ~c[y] according to ~c[rel] then the image of ~c[x] under ~c[fn] is a smaller
  than that of ~c[y], according to the well-founded relation ~ilc[o<].
  (~l[o<].)  Thus, the general form of a
  ~c[:well-founded-relation] formula establishes that there exists a
  ~c[rel]-order preserving embedding (namely via ~c[fn]) of the ~c[mp]-measures
  into the ordinals.  We can thus conclude that ~c[rel] is well-founded on
  ~c[mp]-measures.

  Such well-founded relations are used in the admissibility test for
  recursive functions, in particular, to show that the recursion
  terminates.  To illustrate how such information may be used,
  consider a generic function definition
  ~bv[]
  (defun g (x) (if (test x) (g (step x)) (base x))).
  ~ev[]
  If ~c[rel] has been shown to be well-founded on ~c[mp]-measures, then ~c[g]'s
  termination can be ensured by finding a measure, ~c[(m x)], with the
  property that ~c[m] produces a measure:
  ~bv[]
  (mp (m x)),                                     ; Defun-goal-1
  ~ev[]
  and that the argument to ~c[g] gets smaller (when measured by ~c[m] and
  compared by ~c[rel]) in the recursion,
  ~bv[]
  (implies (test x) (rel (m (step x)) (m x))).    ; Defun-goal-2
  ~ev[]
  If ~c[rel] is selected as the ~c[:well-founded-relation] to be used in the
  definition of ~c[g], the definitional principal will generate and
  attempt to prove ~c[defun-goal-1] and ~c[defun-goal-2] to justify ~c[g].  We
  show later why these two goals are sufficient to establish the
  termination of ~c[g].  Observe that neither the ordinals nor the
  embedding, ~c[fn], of the ~c[mp]-measures into the ordinals is involved in
  the goals generated by the definitional principal.

  Suppose now that a ~c[:well-founded-relation] theorem has been proved
  for ~c[mp] and ~c[rel].  How can ~c[rel] be ``selected as the
  ~c[:well-founded-relation]'' by ~ilc[defun]?  There are two ways.
  First, an ~ilc[xargs] keyword to the ~ilc[defun] event allows the
  specification of a ~c[:well-founded-relation].  Thus, the definition
  of ~c[g] above might be written
  ~bv[]
  (defun g (x)
   (declare (xargs :well-founded-relation (mp . rel)))
   (if (test x) (g (step x)) (base x)))
  ~ev[]
  Alternatively, ~c[rel] may be specified as the
  ~c[:default-well-founded-relation] in ~ilc[acl2-defaults-table] by
  executing the event
  ~bv[]
  (set-well-founded-relation rel).
  ~ev[]
  When a ~ilc[defun] event does not explicitly specify the relation in its
  ~ilc[xargs] the default relation is used.  When ACL2 is initialized, the
  default relation is ~ilc[o<].

  Finally, though it is probably obvious, we now show that
  ~c[defun-goal-1] and ~c[defun-goal-2] are sufficient to ensure the
  termination of ~c[g] provided ~c[property-1] and ~c[property-2] of ~c[mp] and ~c[rel]
  have been proved.  To this end, assume we have proved ~c[defun-goal-1]
  and ~c[defun-goal-2] as well as ~c[property-1] and ~c[property-2] and we show
  how to admit ~c[g] under the primitive ACL2 definitional principal
  (i.e., using only the ordinals).  In particular, consider the
  definition event
  ~bv[]
  (defun g (x)
   (declare (xargs :well-founded-relation o<
                   :measure (fn (m x))))
   (if (test x) (g (step x)) (base x)))
  ~ev[]
  Proof that ~c[g] is admissible:  To admit the definition of ~c[g] above we
  must prove
  ~bv[]
  (o-p (fn (m x)))                        ; *1
  ~ev[]
  and
  ~bv[]
  (implies (test x)                               ; *2
           (o< (fn (m (step x))) (fn (m x)))).
  ~ev[]
  But *1 can be proved by instantiating ~c[property-1] to get
  ~bv[]
  (implies (mp (m x)) (o-p (fn (m x)))),
  ~ev[]
  and then relieving the hypothesis with ~c[defun-goal-1], ~c[(mp (m x))].

  Similarly, *2 can be proved by instantiating ~c[property-2] to get
  ~bv[]
  (implies (and (mp (m (step x)))
                (mp (m x))
                (rel (m (step x)) (m x)))
           (o< (fn (m (step x))) (fn (m x))))
  ~ev[]
  and relieving the first two hypotheses by appealing to two
  instances of ~c[defun-goal-1], thus obtaining
  ~bv[]
  (implies (rel (m (step x)) (m x))
           (o< (fn (m (step x))) (fn (m x)))).
  ~ev[]
  By chaining this together with ~c[defun-goal-2],
  ~bv[]
  (implies (test x)
           (rel (m (step x)) (m x)))
  ~ev[]
  we obtain *2.  Q.E.D.")

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

(deflabel built-in-clause
  :doc
  ":Doc-Section Rule-Classes

  to build a clause into the simplifier~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  A ~c[:built-in-clause]
  rule can be built from any formula other than propositional
  tautologies.  Roughly speaking, the system uses the list of built-in
  clauses as the first method of proof when attacking a new goal.  Any
  goal that is subsumed by a built in clause is proved ``silently.''~/

  ACL2 maintains a set of ``built-in'' clauses that are used to
  short-circuit certain theorem proving tasks.  We discuss this at
  length below.  When a theorem is given the rule class
  ~c[:built-in-clause] ACL2 flattens the ~ilc[implies] and ~ilc[and] structure of the
  ~c[:]~ilc[corollary] formula so as to obtain a set of formulas whose
  conjunction is equivalent to the given corollary.  It then converts
  each of these to clausal form and adds each clause to the set of
  built-in clauses.

  For example, the following ~c[:]~ilc[corollary] (regardless of the definition
  of ~c[abl])
  ~bv[]
  (and (implies (and (true-listp x)
                     (not (equal x nil)))
                (< (acl2-count (abl x))
                   (acl2-count x)))
       (implies (and (true-listp x)
                     (not (equal nil x)))
                (< (acl2-count (abl x))
                   (acl2-count x))))
  ~ev[]
  will build in two clauses,
  ~bv[]
  {(not (true-listp x))
   (equal x nil)
   (< (acl2-count (abl x)) (acl2-count x))}
  ~ev[]
  and
  ~bv[]
  {(not (true-listp x))
   (equal nil x)
   (< (acl2-count (abl x)) (acl2-count x))}.
  ~ev[]
  We now give more background.

  Recall that a clause is a set of terms, implicitly representing the
  disjunction of the terms.  Clause ~c[c1] is ``subsumed'' by clause ~c[c2] if
  some instance of ~c[c2] is a subset ~c[c1].

  For example, let ~c[c1] be
  ~bv[]
  {(not (consp l))
   (equal a (car l))
   (< (acl2-count (cdr l)) (acl2-count l))}.
  ~ev[]
  Then ~c[c1] is subsumed by ~c[c2], shown below,
  ~bv[]
  {(not (consp x))
   ; second term omitted here
   (< (acl2-count (cdr x)) (acl2-count x))}
  ~ev[]
  because we can instantiate ~c[x] in ~c[c2] with ~c[l] to obtain a subset of
  ~c[c1].

  Observe that ~c[c1] is the clausal form of
  ~bv[]
  (implies (and (consp l)
                (not (equal a (car l))))
           (< (acl2-count (cdr l)) (acl2-count l))),
  ~ev[]
  ~c[c2] is the clausal form of
  ~bv[]
  (implies (consp l)
           (< (acl2-count (cdr l)) (acl2-count l)))
  ~ev[]
  and the subsumption property just means that ~c[c1] follows trivially
  from ~c[c2] by instantiation.

  The set of built-in clauses is just a set of known theorems in
  clausal form.  Any formula that is subsumed by a built-in clause is
  thus a theorem.  If the set of built-in theorems is reasonably
  small, this little theorem prover is fast.  ACL2 uses the ``built-in
  clause check'' in four places: (1) at the top of the iteration in
  the prover -- thus if a built-in clause is generated as a subgoal it
  will be recognized when that goal is considered, (2) within the
  simplifier so that no built-in clause is ever generated by
  simplification, (3) as a filter on the clauses generated to prove
  the termination of recursively ~ilc[defun]'d functions and (4) as a
  filter on the clauses generated to verify the guards of a function.

  The latter two uses are the ones that most often motivate an
  extension to the set of built-in clauses.  Frequently a given
  formalization problem requires the definition of many functions
  which require virtually identical termination and/or guard proofs.
  These proofs can be short-circuited by extending the set of built-in
  clauses to contain the most general forms of the clauses generated
  by the definitional schemes in use.

  The attentive user might have noticed that there are some recursive
  schemes, e.g., recursion by ~ilc[cdr] after testing ~ilc[consp], that ACL2 just
  seems to ``know'' are ok, while for others it generates measure
  clauses to prove.  Actually, it always generates measure clauses but
  then filters out any that pass the built-in clause check.  When ACL2
  is initialized, the clause justifying ~ilc[cdr] recursion after a ~ilc[consp]
  test is added to the set of built-in clauses.  (That clause is ~c[c2]
  above.)

  Note that only a subsumption check is made; no rewriting or
  simplification is done.  Thus, if we want the system to ``know''
  that ~ilc[cdr] recursion is ok after a negative ~ilc[atom] test (which, by the
  definition of ~ilc[atom], is the same as a ~ilc[consp] test), we have to build
  in a second clause.  The subsumption algorithm does not ``know''
  about commutative functions.  Thus, for predictability, we have
  built in commuted versions of each clause involving commutative
  functions.  For example, we build in both
  ~bv[]
  {(not (integerp x))
   (< 0 x)
   (= x 0)
   (< (acl2-count (+ -1 x)) (acl2-count x))}
  ~ev[]
  and the commuted version
  ~bv[]
  {(not (integerp x))
   (< 0 x)
   (= 0 x)
   (< (acl2-count (+ -1 x)) (acl2-count x))}
  ~ev[]
  so that the user need not worry whether to write ~c[(= x 0)] or ~c[(= 0 x)]
  in definitions.

  ~c[:built-in-clause] rules added by the user can be enabled and
  disabled.")

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
; nonpathological example arises, but I haven't bothered to think of one.
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

(deflabel compound-recognizer
  :doc
  ":Doc-Section Rule-Classes

  make a rule used by the typing mechanism~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  An example
  ~c[:]~ilc[corollary] formula from which a ~c[:compound-recognizer] rule might be
  built is:
  ~bv[]
  Example: 
  (implies (alistp x)         When (alistp x) is assumed true,
           (true-listp x))    add the additional hypothesis that x
                              is of primitive type true-listp.~/
  ~ev[]

  Before presenting the General Forms, we start with a motivating example.  The
  following provides a nice example of a ~c[:compound-recognizer] rule that is
  built into ACL2.
  ~bv[]
  (defthm natp-compound-recognizer
    (equal (natp x)
           (and (integerp x)
                (<= 0 x)))
    :rule-classes :compound-recognizer)
  ~ev[]
  To see how this rule might be useful, consider the following (admittedly very
  simple) ~il[events].
  ~bv[]
  (defun triple (x)
    (* 3 x))

  (defthm triple-preserves-integerp
    (implies (integerp x)
             (integerp (triple x))))

  (in-theory (disable triple natp))
  ~ev[]
  If the above ~c[:compound-recognizer] rule is disabled, then the following
  trivial theorem fails as shown; we explain below.
  ~bv[]
  (thm (implies (natp x)
                (integerp (triple x)))
    :hints ((\"Goal\" :in-theory (disable natp-compound-recognizer))))
  ~ev[]

  The problem is that when ACL2 tries to rewrite the term
  ~c[(integerp (triple x))] using the ~c[:]~ilc[rewrite] rule
  ~c[triple-preserves-integerp], it needs to rewrite the hypothesis
  ~c[(integerp x)] to ~c[t], but instead what is known is ~c[(natp x)].  If we
  remove the hint, then the proof succeeds because the above
  ~c[:compound-recognizer] rule tells ACL2 that when assuming ~c[(natp x)] to
  be true, it should actually assume both ~c[(integerp x)] and ~c[(<= 0 x)] to
  be true.

  ~bv[]
  General Forms:
  (implies (fn x) concl)               ; (1)
  (implies (not (fn x)) concl)         ; (2)
  (and (implies (fn x) concl1)         ; (3)
       (implies (not (fn x)) concl2))
  (if (fn x) concl1 concl2)            ; (4)
  (iff (fn x) concl)                   ; (5)
  (equal (fn x) concl)                 ; (6)
  ~ev[]
  where ~c[fn] is a Boolean valued function of one argument, ~c[x] is a
  variable symbol, and the system can deduce some restriction on the primitive
  type of ~c[x] from the assumption that ~c[concl] holds.  The last restriction
  is vague but one way to understand it is to weaken it a little to ``and
  ~c[concl] is a non-tautological conjunction or disjunction of the primitive
  type recognizers listed below.''

  The primitive ACL2 types and a suitable primitive recognizing expression for
  each are listed below.
  ~bv[]
    type                suitable primitive recognizer

    zero                (equal x 0)
    negative integers   (and (integerp x) (< x 0))
    positive integers   (and (integerp x) (> x 0))
    negative ratio      (and (rationalp x)
                             (not (integerp x))
                             (< x 0))
    positive ratio      (and (rationalp x)
                             (not (integerp x))
                             (> x 0))
    complex rational    (complex-rationalp x)
    nil                 (equal x nil)
    t                   (equal x t)
    other symbols       (and (symbolp x)
                             (not (equal x nil))
                             (not (equal x t)))
    proper conses       (and (consp x)
                             (true-listp x))
    improper conses     (and (consp x)
                             (not (true-listp x)))
    strings             (stringp x)
    characters          (characterp x)
  ~ev[]

  Thus, a suitable ~c[concl] to recognize the naturals would be
  ~c[(or (equal x 0) (and (integerp x) (> x 0)))] but it turns out that we also
  permit ~c[(and (integerp x) (>= x 0))].  Similarly, the true-lists could be
  specified by
  ~bv[]
  (or (equal x nil) (and (consp x) (true-listp x)))
  ~ev[]
  but we in fact allow ~c[(true-listp x)].  When time permits we will document
  more fully what is allowed or implement a macro that permits direct
  specification of the desired type in terms of the primitives.

  There are essentially four forms of ~c[:compound-recognizer] rules, as the
  forms labeled (3) and (4) above are equivalent, as are those labeled (5)
  and (6).  We explain how such rules are used by considering the individual
  forms.

  Consider form (1), ~c[(implies (fn x) concl)].  The effect of such a rule is
  that when the rewriter assumes ~c[(fn x)] true, as it would while diving
  through ~c[(if (fn x) xxx ...)] to rewrite ~c[xxx], it restricts the type of
  ~c[x] as specified by ~c[concl].  For example, if ~c[concl] is the term
  ~c[(integerp x)], then when rewriting ~c[xxx], ~c[x] will be assumed to be an
  integer.  However, when assuming ~c[(fn x)] false, as necessary in
  ~c[(if (fn x) ... xxx)], the rule permits no additional assumptions about the
  type of ~c[x].  For example, if ~c[fn] is ~c[primep], i.e., the predicate
  that recognizes prime numbers, then
  ~c[(implies (primep x) (and (integerp x) (>= x 0)))] is a compound recognizer
  rule of the first form.  When ~c[(primep x)] is assumed true, the rewriter
  gains the additional information that ~c[x] is a natural number.  When
  ~c[(primep x)] is assumed false, no additional information is gained ~-[]
  since ~c[x] may be a non-prime natural or may not even be a natural.

  Form (2) is the symmetric case, when assuming ~c[(fn x)] false permits type
  restrictions on ~c[x] but assuming ~c[(fn x)] true permits no such
  restrictions.  For example, if we defined ~c[exprp] to be the recognizer for
  well-formed expressions for some language in which all symbols, numbers,
  character objects and strings were well-formed ~-[] e.g., the well-formedness
  rules only put restrictions on expressions represented by ~ilc[consp]s ~-[]
  then the theorem ~c[(implies (not (exprp x)) (consp x))] is a rule of the
  second form.  Assuming ~c[(exprp x)] true tells us nothing about the type of
  ~c[x]; assuming it false tells us ~c[x] is a ~ilc[consp].

  Forms (3) and (4), which are really equivalent, address themselves to the
  case where one type may be deduced from ~c[(fn x)] and a generally unrelated
  type may be deduced from its negation.  If we modified the expression
  recognizer above so that character objects are illegal, then rules of the
  forms (3) and (4) are
  ~bv[]
  (and (implies (exprp x) (not (characterp x)))
       (implies (not (exprp x)) (or (consp x) (characterp x)))).
  (if (exprp x) 
      (not (characterp x))
    (or (consp x) (characterp x)))
  ~ev[]

  Finally, rules of forms (5) and (6) address the case where ~c[fn] recognizes
  all and only the objects whose type is described.  In these cases, ~c[fn] is
  really just a new name for some ``compound recognizers.''  The classic
  example is ~c[(booleanp x)], which is just a handy combination of two
  primitive types:
  ~bv[]
  (iff (booleanp x) (or (equal x t) (equal x nil))).
  ~ev[]

  Often it is best to disable ~c[fn] after proving that it is a compound
  recognizer, since otherwise the term ~c[(fn x)] will be expanded and thus
  disappear.

  Every time you prove a new compound recognizer rule about ~c[fn] it overrides
  all previously proved compound recognizer rules about ~c[fn].  Thus, if you
  want to establish the type implied by ~c[(fn x)] and you want to establish
  the type implied by ~c[(not (fn x))], you must prove a compound recognizer
  rule of the third, fourth, fifth, or sixth forms.  Proving a rule of the
  first form followed by one of the second only leaves the second fact in the
  database.

  Compound recognizer rules can be disabled with the effect that older rules
  about ~c[fn], if any, are exposed.

  If you prove more than one compound recognizer rule for a function, you may
  see a ~st[warning] message to the effect that the new rule is not as
  ``restrictive'' as the old.  That is, the new rules do not give the rewriter
  strictly more type information than it already had.  The new rule is stored
  anyway, overriding the old, if enabled.  You may be playing subtle games with
  enabling or rewriting.  But two other interpretations are more likely, we
  think.  One is that you have forgotten about an earlier rule and should
  merely print it out to make sure it says what you intend, and then discard
  your new rule.  The other is that you meant to give the system more
  information and the system has simply been unable to extract the intended
  type information from the term you placed in the conclusion of the new rule.
  Given our lack of specificity in saying how type information is extracted
  from rules, you can hardly blame yourself for this problem.  Sorry.  If you
  suspect you've been burned this way, you should rephrase the new rule in
  terms of the primitive recognizing expressions above and see if the warning
  is still given.  It would also be helpful to let us see your example so we
  can consider it as we redesign this stuff.

  Compound recognizer rules are similar to ~c[:]~ilc[forward-chaining] rules in
  that the system deduces new information from the act of assuming something
  true or false.  If a compound recognizer rule were stored as a forward
  chaining rule it would have essentially the same effect as described, when it
  has any effect at all.  The important point is that
  ~c[:]~ilc[forward-chaining] rules, because of their more general and
  expensive form, are used ``at the top level'' of the simplification process:
  we forward chain from assumptions in the goal being proved.  But compound
  recognizer rules are built in at the bottom-most level of the simplifier,
  where type reasoning is done.

  All that said, compound recognizer rules are a rather fancy, specialized
  mechanism.  It may be more appropriate to create ~c[:]~ilc[forward-chaining]
  rules instead of ~c[:compound-recognizer] rules.")

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
   ((eq (access recognizer-tuple new-recog-tuple :fn)
        (access recognizer-tuple (car recognizer-alist) :fn))
    (cond
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
   (t (comment-on-new-recog-tuple1 new-recog-tuple (cdr recognizer-alist)
                                   ctx state))))

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

  (let ((pred (fcons-term* (access recognizer-tuple new-recog-tuple :fn) 'x)))
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
                                         (global-val 'recognizer-alist wrld)
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

; We construct the recongizer-tuple corresponding to term and just add
; it onto the front of the current recognizer-alist.  We used to merge
; it into the existing tuple for the same :fn, if one existed, but
; that makes disabling these rules complicated.  When we retrieve
; tuples from the alist we look for the first enabled tuple about the
; :fn in question.  So it is necessary to leave old tuples for :fn in
; place.

  (mv-let (parity fn var term1)
          (destructure-compound-recognizer term)
          (mv-let (recog-tuple ttree)
                  (make-recognizer-tuple rune nume parity fn var term1 ens
                                         wrld)
                  (declare (ignore ttree))
                  (global-set 'recognizer-alist
                              (cons recog-tuple (global-val 'recognizer-alist wrld))
                              wrld))))

;---------------------------------------------------------------------------
; Section:  :FORWARD-CHAINING Rules

(deflabel forward-chaining
  :doc
  ":Doc-Section Rule-Classes

  make a rule to forward chain when a certain trigger arises~/

  ~l[rule-classes] for a general discussion of rule classes and how they are
  used to build rules from formulas.  An example ~c[:]~ilc[corollary] formula
  from which a ~c[:forward-chaining] rule might be built is:
  ~bv[]
  Example:
  (implies (and (p x) (r x))       ; when (p a) appears in a formula to be
           (q (f x)))              ; simplified, try to establish (r a) and
                                   ; if successful, add (q (f a)) to the
                                   ; known assumptions
  ~ev[]
  To specify the triggering terms provide a non-empty list of terms
  as the value of the ~c[:trigger-terms] field of the rule class object.~/
  ~bv[]
  General Form:
  Any theorem, provided an acceptable triggering term exists.
  ~ev[]
  The structure of this documentation is as follows.  First we give a brief
  overview of forward chaining and contrast it to backchaining (rewriting).
  Then we lay out the syntactic restrictions on ~c[:forward-chaining] rules.
  Then we give more details about the process and point to a tool to assist
  you in debugging your ~c[:forward-chaining] rules.

  ~em[Overview and When to Use Forward Chaining]

  Forward chaining is performed as part of the simplification process: before
  the goal is rewritten a ~em[context] is established.  The context tells the
  theorem prover what may be assumed during the rewriting, e.g., to establish
  hypotheses of rewrite rules.  For example, if the goal is 
  ~c[(implies (and (p A) (q A)) (r A))], then when ~c[(r A)] is being
  rewritten, the context tells us we may assume ~c[(p A)] and ~c[(q A)].
  Forward chaining is used to extend the context before rewriting begins.  For
  example, the ~c[:forward-chaining] rule ~c[(implies (p x) (p1 x))] would add
  ~c[(p1 A)] to the context.

  Forward chaining and backchaining are duals.  If a rewrite rule requires that
  ~c[(p1 A)] be established and ~c[(p A)] is known, it could be done either by
  making ~c[(implies (p x) (p1 x))] a ~c[:forward-chaining] rule or a
  ~c[:rewrite] rule.  Which should you choose?
  
  As a rule of thumb, if a conclusion like ~c[(p1 A)] is expected to be
  widely needed, it is better to derive it via forward chaining because then
  it is available ``for free'' during the rewriting after paying the one-time
  cost of forward chaining.  Alternatively, if ~c[(p1 A)] is a rather
  special hypothesis of key importance to only a few rewrite rules, it is
  best to derive it only when needed.  Thus forward chaining is pro-active
  and backward chaining (rewriting) is reactive.

  ~em[Syntactic Restrictions]

  Forward chaining rules are generated from the corollary term as follows.
  First, every ~ilc[let] expression is expanded away (hence, so is every
  ~ilc[let*] and ~ilc[lambda] expression), as is every call of a so-called
  ``guard holder,'' ~ilc[mv-list] or ~ilc[return-last] (the latter resulting
  from macroexpansion of calls of ~ilc[prog2$], ~ilc[must-be-equal] or
  ~ilc[mbe]), ~ilc[ec-call], and a few others), or `~ilc[the]'.  If the
  resulting term has the form ~c[(implies hyp concl)], then ~c[concl] is
  treated as a conjunction, with one forward chaining rule with hypothesis
  ~c[hyp] created for each conjunct.  In the other case, where the corollary
  term is not an ~ilc[implies], we process it as we process the conclusion in
  the first case.

  The ~c[:trigger-terms] field of a ~c[:forward-chaining] rule class object
  should be a non-empty list of terms, if provided, and should have certain
  properties described below.  If the ~c[:trigger-terms] field is not provided,
  it defaults to the singleton list containing the ``atom'' of the first
  hypothesis of the formula.  (The atom of ~c[(not x)] is ~c[x]; the atom of
  any other term is the term itself.)  If there are no hypotheses and no
  ~c[:trigger-terms] were provided, an error is caused.

  A triggering term is acceptable if it is not a variable, a quoted constant, a
  lambda application, a ~ilc[let]- (or ~ilc[let*]-) expression, or a
  ~ilc[not]-expression, and every variable symbol in the conclusion of the
  theorem either occurs in the hypotheses or occurs in the trigger.

  ~em[More Details about Forward Chaining]

  ~c[:Forward-chaining] rules are used by the simplifier ~em[before] it begins to
  rewrite the literals of the goal.  (Forward chaining is thus carried out from
  scratch for each goal.)  If any term in the goal is an instance of a trigger
  of some forward chaining rule, we try to establish the hypotheses of that
  forward chaining theorem (from the negation of the goal).  To relieve a
  hypothesis we only use type reasoning, evaluation of ground terms, and
  presence among our known assumptions.  We do not use rewriting.  So-called
  free variables in hypotheses are treated specially; ~pl[free-variables].  If
  all hypotheses are relieved, and certain heuristics approve of the newly
  derived conclusion, we add the instantiated conclusion to our known
  assumptions.  Since this might introduce new terms into the assumptions,
  forward chaining is repeated.  Heuristic approval of each new addition is
  necessary to avoid infinite looping as would happen with the rule
  ~c[(implies (p x) (p (f x)))], which might otherwise forward chain from
  ~c[(p A)] to ~c[(p (f A))] to ~c[(p (f (f A)))], etc.

  ~em[Caution].  Forward chaining does not actually add terms to the goals
  displayed during proof attempts.  Instead, it extends an associated
  ~em[context], called ``assumptions'' in the preceding paragraph, that ACL2
  builds from the goal currently being proved.  (For insiders: forward chaining
  extends the ~c[type-alist].)  The context starts out with ``obvious''
  consequences of the negation of the goal.  For example, if the goal is
  ~bv[]
  (implies (and (p A) (q (f A)))
           (c A))
  ~ev[]
  then the context notes that ~c[(p A)] and ~c[(q (f A))] are non-~c[nil] and
  ~c[(c A)] is ~c[nil].  Forward chaining is then used to expand the context.
  For example, if a forward chaining rule has ~c[(f x)] as a trigger term and
  has body ~c[(implies (p x) (r (f x)))], then the context is extended by
  binding ~c[(r (f A))] to non-~c[nil], provided the heuristics approve of this
  extension.  Note however that since ~c[(r (f A))] is put into the context,
  not the goal, you will not see it in the goal formula.  Furthermore, the
  assumption added to the context is just the instantiation of the conclusion
  of the rule, with no simplification or rewriting applied.  Thus, for example,
  if it contains an enabled non-recursive function symbol it is unlikely ever
  to match a (rewritten) term arising during subsequent simplification of the
  goal.

  However, forward-chaining does support the linear arithmetic reasoning
  package.  For example, suppose that forward-chaining puts ~c[(< (f x) (g x))]
  into the context.  Then this inequality also goes into the linear arithmetic
  database, together with suitable instances of linear lemmas whose trigger
  term is a call of ~c[g].  ~l[linear].

  Debugging ~c[:forward-chaining] rules can be difficult since their effects
  are not directly visible on the goal being simplified.  Tools are available
  to help you discover what forward chaining has occurred
  ~pl[forward-chaining-reports].")

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
                (non-rec-fns (and warn-non-rec
                                  (non-recursive-fnnames (car terms) ens wrld)))
                (non-rec-fns-inst-hyps
                 (and warn-non-rec
                      (non-recursive-fnnames-lst
                       (strip-top-level-nots-and-forces inst-hyps) ens wrld))))
           (er-progn
            (cond
             ((and free-vars (null match-free))
              (pprogn
               (warning$ ctx "Free"
                         "When the :FORWARD-CHAINING rule generated from ~x0 ~
                          is triggered by ~x1 it contains the free ~
                          variable~#2~[ ~&2.  This variable~/s ~&2.  These ~
                          variables~] will be chosen by searching for ~#3~[an ~
                          instance~/instances~] of ~&3 among the hypotheses of ~
                          the conjecture being rewritten.  This is generally a ~
                          severe restriction on the applicability of the ~
                          forward chaining rule."
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
                         "The term ~x0 contains the non-recursive function ~
                          symbol~#1~[ ~&1.  Unless this function is~/s ~&1.  ~
                          Unless these functions are~] disabled, ~x0 is ~
                          unlikely ever to occur as a trigger for ~x2."
                         (car terms)
                         (hide-lambdas non-rec-fns)
                         name))
              (t state))
             (cond
              (non-rec-fns-inst-hyps
               (warning$ ctx ("Non-rec")
                         "As noted, when triggered by ~x0, we will instantiate ~
                          the free variable~#1~[~/s~], ~&1, of the rule ~x2, ~
                          by searching for the ~#3~[hypothesis~/set of ~
                          hypotheses~] shown above.  However, ~#3~[this ~
                          hypothesis mentions~/these hypotheses mention~] the ~
                          function symbol~#4~[ ~&4, which is~/s ~&4, which ~
                          are~] defun'd non-recursively. Unless disabled, ~
                          ~#4~[this function symbol is~/these function symbols ~
                          are~] unlikely to occur in the conjecture being ~
                          proved and hence the search for the required ~
                          ~#3~[hypothesis~/hypotheses~] will likely fail."
                         (car terms) free-vars name inst-hyps
                         (hide-lambdas non-rec-fns-inst-hyps)))
              (t state))
             (chk-triggers match-free name hyps (cdr terms)
                           hyps-vars concls-vars ctx ens wrld state)))))))

(defun destructure-forward-chaining-term (term)

; We return two lists, hyps and concls, such that term is equivalent to
; (implies (and . hyps) (and . concls)).

  (let ((term (remove-lambdas (remove-guard-holders term))))
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
   (destructure-forward-chaining-term term)
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
                           (getprop (ffn-symb (car triggers))
                                    'forward-chaining-rules nil
                                    'current-acl2-world wrld))
                     wrld)))))

(defun add-forward-chaining-rule (rune nume trigger-terms term match-free wrld)
  (mv-let
   (hyps concls)
   (destructure-forward-chaining-term term)
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

(deflabel meta
  :doc
  ":Doc-Section Rule-Classes

  make a ~c[:meta] rule (a hand-written simplifier)~/

  ~l[rule-classes] for a general discussion of rule classes and how they are
  used to build rules from formulas.  Meta rules extend the ACL2 simplifier
  with hand-written code to transform certain terms to equivalent ones.  To add
  a meta rule, the ~c[:]~ilc[corollary] formula must establish that the
  hand-written ``metafunction'' preserves the meaning of the transformed term.

  While our intention is that the set of ACL2 documentation topics is
  self-contained, readers might find it useful to see the following paper for
  an introduction to meta reasoning in ACL2.
  ~bq[]
  W. A. Hunt, Jr., R. B. Krug, M. Kaufmann, J S. Moore and E. W. Smith, ``Meta
  Reasoning in ACL2.''  TPHOLs 2005, ed. J. Hurd and T. F. Melham, LNCS 3603,
  Springer-Verlag, Berlin, 2005, pp. 163-178.~eq[]

  Example ~c[:]~ilc[corollary] formulas from which ~c[:meta] rules might be
  built are:
  ~bv[]
  Examples:
  (equal (evl x a)                  ; Modify the rewriter to use fn to
         (evl (fn x) a))            ; transform terms.  The :trigger-fns
                                    ; of the :meta rule-class specify
                                    ; the top-most function symbols of
                                    ; those x that are candidates for
                                    ; this transformation.

  (implies (and (pseudo-termp x)    ; As above, but this illustrates
                (alistp a))         ; that without loss of generality we
           (equal (evl x a)         ; may restrict x to be shaped like a
                  (evl (fn x) a)))  ; term and a to be an alist.

  (implies (and (pseudo-termp x)    ; As above (with or without the
                (alistp a)          ; hypotheses on x and a) with the
                (evl (hyp-fn x) a)) ; additional restriction that the
           (equal (evl x a)         ; meaning of (hyp-fn x) is true in
                  (evl (fn x) a)))  ; the current context.  That is, the
                                    ; applicability of the transforma-
                                    ; tion may be dependent upon some
                                    ; computed hypotheses.
  ~ev[]
  A non-~c[nil] list of function symbols must be supplied as the value
  of the ~c[:trigger-fns] field in a ~c[:meta] rule class object
  (except that a macro alias can stand in for a function symbol;
  ~pl[add-macro-alias]).~/
  ~bv[]
  General Forms:
  (implies (and (pseudo-termp x)        ; this hyp is optional
                (alistp a)              ; this hyp is optional
                (ev (hyp-fn x ...) a)   ; this hyp is optional
                ; meta-extract hyps may also be included (see below)
                )
           (equiv (ev x a)
                  (ev (fn x ...) a)))
  ~ev[]
  where ~c[equiv] is a known ~il[equivalence] relation, ~c[x] and ~c[a] are
  distinct variable names, and ~c[ev] is an evaluator function (see below), and
  ~c[fn] is a function symbol, as is ~c[hyp-fn] when provided.  The arguments
  to ~c[fn] and ~c[hyp-fn] should be identical.  In the most common case, both
  take a single argument, ~c[x], which denotes the term to be simplified.  If
  ~c[fn] and/or ~c[hyp-fn] are ~il[guard]ed, their ~il[guard]s should be
  trivially implied by ~ilc[pseudo-termp].  We say the theorem above is a
  ``metatheorem'' or ``metalemma'' and ~c[fn] is a ``metafunction'', and
  ~c[hyp-fn] is a ``hypothesis metafunction''.

  If ``~c[...]'' is empty, i.e., the metafunctions take just one argument, we
  say they are ``vanilla flavored.''  If ``~c[...]'' is non-empty, we say the
  metafunctions are ``extended.''  Extended metafunctions can access
  ~ilc[state] and context sensitive information to compute their results,
  within certain limits.  We discuss vanilla metafunctions here and recommend a
  thorough understanding of them before proceeding (at which time
  ~pl[extended-metafunctions]).

  Additional hypotheses are supported, called ``meta-extract hypotheses''.
  These allow metafunctions to depend on the validity of certain terms
  extracted from the context or the logical ~il[world].  These hypotheses
  provide a relatively advanced form of metatheorem so we explain them
  elsewhere; ~pl[meta-extract].

  One might think that metafunctions and (if supplied) hypothesis metafunctions
  must be executable: that is, not constrained (i.e., introduced in the
  ~il[signature] of ~ilc[encapsulate] ~il[events]), and not ~il[declare]d
  ~c[:]~ilc[non-executable].  After all, there is no point in installing a
  simplifier that cannot be run!  However, such a restriction is not enforced,
  because one could introduce a metafunction using ~ilc[encapsulate] and then
  use ~ilc[defattach] to attach it to an executable function; ~pl[defattach].

  We defer discussion of the case in which there is a hypothesis metafunction
  and for now address the case in which the other two hypotheses are present.

  In the discussion below, we refer to the argument, ~c[x], of ~c[fn] and
  ~c[hyp-fn] as a ``term.''  When these metafunctions are executed by the
  simplifier, they will be applied to (the quotations of) terms.  But during
  the proof of the metatheorem itself, ~c[x] may not be the quotation of a
  term.  If the ~ilc[pseudo-termp] hypothesis is omitted, ~c[x] may be any
  object.  Even with the ~ilc[pseudo-termp] hypothesis, ~c[x] may merely ``look
  like a term'' but use non-function symbols or function symbols of incorrect
  arity.  In any case, the metatheorem is stronger than necessary to allow us
  to apply the metafunctions to terms, as we do in the discussion below.  We
  return later to the question of proving the metatheorem.

  Suppose the general form of the metatheorem above is proved with the
  ~ilc[pseudo-termp] and ~ilc[alistp] hypotheses.  Then when the simplifier
  encounters a term, ~c[(h t1 ... tn)], that begins with a function symbol,
  ~c[h], listed in ~c[:trigger-fns], it applies the metafunction, ~c[fn], to
  the quotation of the term, i.e., it evaluates ~c[(fn '(h t1 ... tn))] to
  obtain some result, which can be written as ~c['val].  If ~c['val] is
  different from ~c['(h t1 ... tn)] and ~c[val] is a term, then
  ~c[(h t1 ... tn)] is replaced by ~c[val], which is then passed along for
  further rewriting.  Because the metatheorem establishes the correctness of
  ~c[fn] for all terms (even non-terms!), there is no restriction on which
  function symbols are listed in the ~c[:trigger-fns].  Generally, of course,
  they should be the symbols that head up the terms simplified by the
  metafunction ~c[fn].  ~l[term-table] for how one obtains some assistance
  towards guaranteeing that ~c[val] is indeed a term.

  The ``evaluator'' function, ~c[ev], is a function that can evaluate a certain
  class of expressions, namely, all of those composed of variables, constants,
  and applications of a fixed, finite set of function symbols, ~c[g1], ...,
  ~c[gk].  Generally speaking, the set of function symbols handled by ~c[ev] is
  chosen to be exactly the function symbols recognized and manipulated by the
  metafunctions being introduced.  For example, if ~c[fn] manipulates
  expressions in which ~c[']~ilc[equal] and ~c[']~ilc[binary-append] occur as
  function symbols, then ~c[ev] is generally specified to handle ~ilc[equal]
  and ~ilc[binary-append].  The actual requirements on ~c[ev] become clear when
  the metatheorem is proved.  The standard way to introduce an evaluator is to
  use the ACL2 macro ~ilc[defevaluator], though this is not strictly necessary.
  ~l[defevaluator] if you want details.

  [Aside for the logic-minded.] Why are we justified in using metafunctions
  this way?  Suppose ~c[(fn 'term1)] is ~c['term2].  What justifies replacing
  ~c[term1] by ~c[term2]?  The first step is to assert that ~c[term1] is
  ~c[(ev 'term1 a)], where ~c[a] is an alist that maps ~c['var] to ~c[var], for
  each variable ~c[var] in ~c[term1].  This step is incorrect, because
  ~c['term1] may contain function symbols other than the ones, ~c[g1], ...,
  ~c[gk], that ~c[ev] knows how to handle.  But we can grow ~c[ev] to a
  ``larger'' evaluator, ~c[ev*], an evaluator for all of the symbols that occur
  in ~c[term1] or ~c[term2].  We can prove that ~c[ev*] satisfies the
  ~il[constraint]s on ~c[ev], provided no ~ilc[defaxiom] events are adding
  constraints to ~c[ev] (or callers of ~c[ev], and recursively); ACL2 checks
  this additional property.  Hence, the metatheorem holds for ~c[ev*] in place
  of ~c[ev], by functional instantiation.  We can then carry out the proof of
  the ~il[equivalence] of ~c[term1] and ~c[term2] as follows: Fix ~c[a] to be
  an alist that maps the quotations of the variables of ~c[term1] and ~c[term2]
  to themselves.  Then,
  ~bv[]
  term1 = (ev* 'term1 a)      ; (1) by construction of ev* and a
        = (ev* (fn 'term1) a) ; (2) by the metatheorem for ev*
        = (ev* 'term2 a)      ; (3) by evaluation of fn
        = term2               ; (4) by construction of ev* and a
  ~ev[]
  Note that in line (2) above, where we appeal to the (functional instantiation
  of the) metatheorem, we can relieve its (optional) ~ilc[pseudo-termp] and
  ~ilc[alistp] hypotheses by appealing to the facts that ~c[term1] is a term
  and ~c[a] is an alist by construction.  [End of Aside for the logic-minded.]

  There are subtleties related to the notion of ``growing'' ~c[ev] to a
  ``larger'' evaluator, as mentioned in the paragraph just above.  For
  corresponding restrictions on ~c[:meta] rules, ~pl[evaluator-restrictions].

  Finally, we turn to the second case, in which there is a hypothesis
  metafunction.  In that case, consider as before what happens when the
  simplifier encounters a term, ~c[(h t1 ... tn)], where ~c[h] is listed in
  ~c[:trigger-fns].  This time, after it applies ~c[fn] to ~c['(h t1 ... tn)]
  to obtain the quotation of some new term, ~c['val], it then applies the
  hypothesis metafunction, ~c[hyp-fn].  That is, it evaluates
  ~c[(hyp-fn '(h t1 ... tn))] to obtain some result, which can be written as
  ~c['hyp-val].  If ~c[hyp-val] is not in fact a term, the metafunction is not
  used.  Provided ~c[hyp-val] is a term, the simplifier attempts to establish
  (by conventional backchaining) that this term is non-~c[nil] in the current
  context.  If this attempt fails, then the meta rule is not applied.
  Otherwise, ~c[(h t1...tn)] is replaced by ~c[val] as in the previous case
  (where there was no hypothesis metafunction).

  Why is it justified to make this extension to the case of hypothesis
  metafunctions?  First, note that the rule
  ~bv[]
  (implies (and (pseudo-termp x)
                (alistp a)
                (ev (hyp-fn x) a))
           (equal (ev x a)
                  (ev (fn x) a)))
  ~ev[]
  is logically equivalent to the rule
  ~bv[]
  (implies (and (pseudo-termp x)
                (alistp a))
           (equal (ev x a)
                  (ev (new-fn x) a)))
  ~ev[]
  where ~c[(new-fn x)] is defined to be ~c[(list 'if (hyp-fn x) (fn x) x)].
  (If we're careful, we realize that this argument depends on making an
  extension of ~c[ev] to an evaluator ~c[ev*] that handles ~ilc[if] and the
  functions manipulated by ~c[hyp-fn].)  If we write ~c['term] for the
  quotation of the present term, and if ~c[(hyp-fn 'term)] and ~c[(fn 'term)]
  are both terms, say ~c[hyp1] and ~c[term1], then by the previous argument we
  know it is sound to rewrite term to ~c[(if hyp1 term1 term)].  But since we
  have established in the current context that ~c[hyp1] is non-~c[nil], we may
  simplify ~c[(if hyp1 term1 term)] to ~c[term1], as desired.

  We now discuss the role of the ~ilc[pseudo-termp] hypothesis.
  ~c[(Pseudo-termp x)] checks that ~c[x] has the shape of a term.  Roughly
  speaking, it ensures that ~c[x] is a symbol, a quoted constant, or a true
  list consisting of a ~c[lambda] expression or symbol followed by some
  pseudo-terms.  Among the properties of terms not checked by
  ~ilc[pseudo-termp] are that variable symbols never begin with ampersand,
  ~c[lambda] expressions are closed, and function symbols are applied to the
  correct number of arguments.  ~l[pseudo-termp].

  There are two possible roles for ~ilc[pseudo-termp] in the development of a
  metatheorem: it may be used as the ~il[guard] of the metafunction and/or
  hypothesis metafunction and it may be used as a hypothesis of the
  metatheorem.  Generally speaking, the ~ilc[pseudo-termp] hypothesis is
  included in a metatheorem only if it makes it easier to prove.  The choice is
  yours.  (An extreme example of this is when the metatheorem is invalid
  without the hypothesis!)  We therefore address ourselves the question: should
  a metafunction have a ~ilc[pseudo-termp] ~il[guard]?  A ~ilc[pseudo-termp]
  ~il[guard] for a metafunction, in connection with other considerations
  described below, improves the efficiency with which the metafunction is used
  by the simplifier.

  To make a metafunction maximally efficient you should (a) provide it with a
  ~ilc[pseudo-termp] ~il[guard] and exploit the ~il[guard] when possible in
  coding the body of the function (~pl[guards-and-evaluation], especially the
  section on efficiency issues), (b) verify the ~il[guard]s of the metafunction
  (~pl[verify-guards]), and (c) compile the metafunction (~pl[comp]).  When
  these three steps have been taken the simplifier can evaluate ~c[(fn 'term1)]
  by running the compiled ``primary code'' (~pl[guards-and-evaluation]) for
  ~c[fn] directly in Common Lisp.  (Note however that explicit compilation may
  be suppressed; ~pl[compilation].)

  Before discussing efficiency issues further, let us review for a moment the
  general case in which we wish to evaluate ~c[(fn 'obj)] for some
  ~c[:]~ilc[logic] function.  We must first ask whether the ~il[guard]s of
  ~c[fn] have been verified.  If not, we must evaluate ~c[fn] by executing its
  logic definition.  This effectively checks the ~il[guard]s of every
  subroutine and so can be slow.  If, on the other hand, the ~il[guard]s of
  ~c[fn] have been verified, then we can run the primary code for ~c[fn],
  provided ~c['obj] satisfies the ~il[guard] of ~c[fn].  So we must next
  evaluate the ~il[guard] of ~c[fn] on ~c['obj].  If the ~il[guard] is met,
  then we run the primary code for ~c[fn], otherwise we run the logic code.

  Now in the case of a metafunction for which the three steps above have been
  followed, we know the ~il[guard] is (implied by) ~ilc[pseudo-termp] and that
  it has been verified.  Furthermore, we know without checking that the
  ~il[guard] is met (because ~c[term1] is a term and hence ~c['term1] is a
  ~ilc[pseudo-termp]).  Hence, we can use the compiled primary code directly.

  We strongly recommend that you compile your metafunctions, as well as all
  their subroutines (unless explicit compilation is suppressed;
  ~pl[compilation]).  Guard verification is also recommended.

  Finally, we present a very simple example of the use of ~c[:meta] rules,
  based on one provided by Robert Krug.  This example illustrates a trick for
  avoiding undesired rewriting after applying a metafunction or any other form
  of rewriting.  To elaborate: in general, the term ~c[t2] obtained by applying
  a metafunction to a term ~c[t1] is then handed immediately to the rewriter,
  which descends recursively through the arguments of function calls to rewrite
  ~c[t2] completely.  But if ~c[t2] shares a lot of structure with ~c[t1], then
  it might not be worthwhile to rewrite ~c[t2] immediately.  (A rewrite of
  ~c[t2] will occur anyhow the next time a goal is generated.)  The trick
  involves avoiding this rewrite by wrapping ~c[t2] inside a call of
  ~ilc[hide], which in turn is inside a call of a user-defined ``unhiding''
  function, ~c[unhide].

  ~bv[]
  (defun unhide (x)
    (declare (xargs :guard t))
    x)

  (defthm unhide-hide
    (equal (unhide (hide x))
           x)
    :hints ((\"Goal\" :expand ((hide x)))))

  (in-theory (disable unhide))

  (defun my-plus (x y)
    (+ x y))

  (in-theory (disable my-plus))

  (defevaluator evl evl-list
    ((my-plus x y)
     (binary-+ x y)
     (unhide x)
     (hide x)))

  (defun meta-fn (term)
    (declare (xargs :guard (pseudo-termp term)))
    (if (and (consp term)
             (equal (length term) 3)
             (equal (car term) 'my-plus))
        `(UNHIDE (HIDE (BINARY-+ ,(cadr term) ,(caddr term))))
      term))

  (defthm my-meta-lemma
    (equal (evl term a)
           (evl (meta-fn term) a))
    :hints ((\"Goal\" :in-theory (enable my-plus)))
    :rule-classes ((:meta :trigger-fns (my-plus))))

  ~ev[]

  Notice that in the following (silly) conjecture, ACL2 initially does only
  does the simplification directed by the metafunction; a second goal is
  generated before the commuativity of addition can be applied.  If the above
  calls of ~c[UNHIDE] and ~c[HIDE] had been stripped off, then ~c[Goal'] would
  have been the term printed in ~c[Goal''] below.

  ~bv[]
  ACL2 !>(thm
          (equal (my-plus b a)
                 ccc))

  This simplifies, using the :meta rule MY-META-LEMMA and the :rewrite
  rule UNHIDE-HIDE, to

  Goal'
  (EQUAL (+ B A) CCC).

  This simplifies, using the :rewrite rule COMMUTATIVITY-OF-+, to

  Goal''
  (EQUAL (+ A B) CCC).
  ~ev[]

  The discussion above probably suffices to make good use of this
  ~c[(UNHIDE (HIDE ...))] trick.  However, we invite the reader who wishes to
  understand the trick in depth to evaluate the following form before
  submitting the ~ilc[thm] form above.
  ~bv[]
  (trace$ (rewrite :entry (list (take 2 arglist))
                   :exit (list (car values)))
          (rewrite-with-lemma :entry (list (take 2 arglist))
                              :exit (take 2 values)))
  ~ev[]
  The following annotated subset of the trace output (which may appear a bit
  different depending on the underlying Common Lisp implementation) explains
  how the trick works.

  ~bv[]
      2> (REWRITE ((MY-PLUS B A) NIL))>
        3> (REWRITE-WITH-LEMMA
                ((MY-PLUS B A)
                 (REWRITE-RULE (:META MY-META-LEMMA)
                               1822
                               NIL EQUAL META-FN NIL META NIL NIL)))>

  We apply the meta rule, then recursively rewrite the result, which is the
  (UNHIDE (HIDE ...)) term shown just below.

          4> (REWRITE ((UNHIDE (HIDE (BINARY-+ B A)))
                       ((A . A) (B . B))))>
            5> (REWRITE ((HIDE (BINARY-+ B A))
                         ((A . A) (B . B))))>

  The HIDE protects its argument from being touched by the rewriter.

            <5 (REWRITE (HIDE (BINARY-+ B A)))>
            5> (REWRITE-WITH-LEMMA
                    ((UNHIDE (HIDE (BINARY-+ B A)))
                     (REWRITE-RULE (:REWRITE UNHIDE-HIDE)
                                   1806 NIL EQUAL (UNHIDE (HIDE X))
                                   X ABBREVIATION NIL NIL)))>

  Now we apply UNHIDE-HIDE, then recursively rewrite its right-hand
  side in an environment where X is bound to (BINARY-+ B A).

              6> (REWRITE (X ((X BINARY-+ B A))))>

  Notice that at this point X is cached, so REWRITE just returns
  (BINARY-+ B A).

              <6 (REWRITE (BINARY-+ B A))>
            <5 (REWRITE-WITH-LEMMA T (BINARY-+ B A))>
          <4 (REWRITE (BINARY-+ B A))>
        <3 (REWRITE-WITH-LEMMA T (BINARY-+ B A))>
      <2 (REWRITE (BINARY-+ B A))>
  ~ev[]")

(deflabel evaluator-restrictions

; Here is Erik Reeber's modification of his proof of nil below, but for the
; development Version of ACL2 as of early March 2007, before the fix to ACL2 for
; this problem.  [It contains a truly trivial edit we've made, not important.]
; 
;  (in-package "ACL2")
; 
;  (defun my-cancel (term)
;     (case-match term
;       (('f ('g))
;        *t*)
;       (('f2 ('g2))
;        *t*)
;       (& term)))
; 
;  (defun f2 (x)
;     (not x))
; 
;  (defun g2 ()
;     nil)
; 
;  (encapsulate
;    ((f (x) t))
; 
;    (local (defun f (x) (declare (ignore x)) t))
; 
;    (defevaluator evl evl-list
;      ((f x)
;       (f2 x)
;       (g2)))
; 
;    (defthm correctness-of-my-cancel
;      (equal (evl x a)
;             (evl (my-cancel x) a))
;      :rule-classes ((:meta :trigger-fns (f)))))
; 
;  (encapsulate
;    ()
; 
;    (local (defstub c () t))
; 
;    (local (encapsulate
;            ()
;            (local (defun g () (c)))
;            (local (in-theory (disable g (g))))
;            (local (defthm f-g
;                     (equal (f (g)) t)
;                     :rule-classes nil))
;            (defthm f-c
;              (equal (f (c)) t)
;              :hints (("Goal" :use f-g
;                       :in-theory (e/d (g) (correctness-of-my-cancel))))
;              :rule-classes nil)))
; 
;    (defthm f-t
;      (equal (f x) t)
;      :hints (("Goal" :by (:functional-instance
;                           f-c
;                           (c (lambda () x)))))
;      :rule-classes nil))
; 
;  (defun g ()
;     nil)
; 
;  ; Below is the expansion of the following defevaluator, changed slightly as
;  ; indicated by comments.
;  ; (defevaluator evl2 evl2-list ((f x) (f2 x) (g) (g2)))
; 
;  (ENCAPSULATE
;    (((EVL2 * *) => *)
;     ((EVL2-LIST * *) => *))
;    (SET-INHIBIT-WARNINGS "theory")
;    (LOCAL (IN-THEORY *DEFEVALUATOR-FORM-BASE-THEORY*))
;    (LOCAL
;     (MUTUAL-RECURSION (DEFUN EVL2 (X A)
;                         (DECLARE (XARGS :VERIFY-GUARDS NIL
;                                         :MEASURE (ACL2-COUNT X)
;                                         :WELL-FOUNDED-RELATION O<
;                                         :MODE :LOGIC))
;                         (COND ((SYMBOLP X) (CDR (ASSOC-EQ X A)))
;                               ((ATOM X) NIL)
;                               ((EQ (CAR X) 'QUOTE) (CAR (CDR X)))
;                               ((CONSP (CAR X))
;                                (EVL2 (CAR (CDR (CDR (CAR X))))
;                                      (PAIRLIS$ (CAR (CDR (CAR X)))
;                                                (EVL2-LIST (CDR X) A))))
;                               ((EQUAL (CAR X) 'F) ; changed f to f2 just below
;                                (F2 (EVL2 (CAR (CDR X)) A)))
;                               ((EQUAL (CAR X) 'F2)
;                                (F2 (EVL2 (CAR (CDR X)) A)))
;                               ((EQUAL (CAR X) 'G) (G))
;                               ((EQUAL (CAR X) 'G2) (G2))
;                               (T NIL)))
;                       (DEFUN EVL2-LIST (X-LST A)
;                         (DECLARE (XARGS :MEASURE (ACL2-COUNT X-LST)
;                                         :WELL-FOUNDED-RELATION O<))
;                         (COND ((ENDP X-LST) NIL)
;                               (T (CONS (EVL2 (CAR X-LST) A)
;                                        (EVL2-LIST (CDR X-LST) A)))))))
; 
;    (DEFTHM EVL2-CONSTRAINT-1
;      (IMPLIES (SYMBOLP X)
;               (EQUAL (EVL2 X A)
;                      (CDR (ASSOC-EQ X A)))))
;    (DEFTHM EVL2-CONSTRAINT-2
;      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'QUOTE))
;               (EQUAL (EVL2 X A) (CADR X))))
;    (DEFTHM EVL2-CONSTRAINT-3
;      (IMPLIES (AND (CONSP X) (CONSP (CAR X)))
;               (EQUAL (EVL2 X A)
;                      (EVL2 (CADDAR X)
;                            (PAIRLIS$ (CADAR X)
;                                      (EVL2-LIST (CDR X) A))))))
;    (DEFTHM EVL2-CONSTRAINT-4
;      (IMPLIES (NOT (CONSP X-LST))
;               (EQUAL (EVL2-LIST X-LST A) NIL)))
;    (DEFTHM EVL2-CONSTRAINT-5
;      (IMPLIES (CONSP X-LST)
;               (EQUAL (EVL2-LIST X-LST A)
;                      (CONS (EVL2 (CAR X-LST) A)
;                            (EVL2-LIST (CDR X-LST) A)))))
;    (DEFTHM EVL2-CONSTRAINT-6
;      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'F))
;               (EQUAL (EVL2 X A) ; changed f to f2 just below
;                      (F2 (EVL2 (CADR X) A)))))
;    (DEFTHM EVL2-CONSTRAINT-7
;      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'F2))
;               (EQUAL (EVL2 X A)
;                      (F2 (EVL2 (CADR X) A)))))
;    (DEFTHM EVL2-CONSTRAINT-8
;      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'G))
;               (EQUAL (EVL2 X A) (G))))
;    (DEFTHM EVL2-CONSTRAINT-9
;      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'G2))
;               (EQUAL (EVL2 X A) (G2)))))
; 
;  (defthm f2-t
;     (equal (f2 x) t)
;     :hints (("Goal" :by (:functional-instance
;                          f-t
;                          (f f2)
;                          (evl evl2)
;                          (evl-list evl2-list)))))
; 
;  (defthm bug-implies-nil
;     nil
;     :hints (("Goal" :use ((:instance f2-t (x t)))))
;     :rule-classes nil)

  :doc
  ":Doc-Section meta

  some restrictions on the use of evaluators in meta-level rules~/

  Note: This topic, which explains some subtleties for evaluators, can probably
  be skipped by most readers.

  Rules of class ~c[:]~ilc[meta] and of class ~c[:]~ilc[clause-processor] are
  stated using so-called ``evaluator'' functions.  Here we explain some
  restrictions related to evaluators.  Below we refer primarily to ~c[:meta]
  rules, but the discussion applies equally to ~c[:clause-processor] rules.

  In a nutshell, we require that a rule's evaluator does not support other
  functions in the rule, and we require that the evaluator not be introduced
  under a non-trivial encapsulate.  We also require that no function has an
  attachment (~pl[defattach]) that is both ancestral in the evaluator and also
  ancestral in the meta or clause-processor functions.  We explain these
  restrictions in detail below.~/

  An argument given elsewhere (~pl[meta], in particular ``Aside for the
  logic-minded'') explains that the correctness argument for applying
  metatheoretic simplifiers requires that one be able to ``grow'' an evaluator
  (~pl[defevaluator]) to handle all functions in the current ACL2 ~il[world].
  Then we may, in essence, functionally instantiate the original evaluator to
  the new (``grown'') evaluator, provided that the new evaluator satisfies all
  of the axioms of the original.  We therefore require that the evaluator
  function does not support the formula of any ~ilc[defaxiom] event.  This
  notion of ``support'' (sometimes denoted ``is an ancestor of'') is defined
  recursively as follows: a function symbol supports a formula if either it
  occurs in that formula, or else it supports the definition or constraint for
  some function symbol that occurs in that formula.  Moreover, we require that
  neither the evaluator function nor its list version support the definition or
  constraint for any other function symbol occurring in the proposed ~c[:meta]
  theorem.

  We also require that the evaluator does not support the formula of a
  ~c[:meta] rule's metafunction (nor, if there is one, hypothesis metafunction)
  or of a ~c[:clause-processor] rule's clause-processor function.  This
  requirement, along with with the analogous requirement for ~ilc[defaxiom]
  ~il[events] stated above, are necessary in order to carry out the functional
  instantiation argument alluded to above, as follows (where the reader may
  find it useful to have some familiarity with the paper ``Structured Theory
  Development for a Mechanized Logic'' (Journal of Automated Reasoning 26,
  no. 2 (2001), pages 161-203).  By the usual conservativity argument, we know
  that the rule follows logically from the axiomatic events for its supporters.
  This remains true if we functionally instantiate the evaluator with one
  corresponding to all the functions symbols of the current session, since none
  of the definitions of supporters of defaxioms or metafunctions are hit by
  that functional substitution.

  Notice though that the argument above depends on knowing that the rule is not
  itself an axiom about the evaluator!  Therefore, we also restrict evaluators
  so that they are not defined in the scope of a superior ~ilc[encapsulate]
  event with non-empty signature, in order to avoid an even more subtle
  problem.  The aforementioned correctness argument depends on knowing that the
  rule is provable from the axioms on the evaluator and metafunction (and
  hypothesis metafunction, if any).  The additional restriction avoids
  unsoundness!  The following events, if allowed, produce a proof that
  ~c[(f x)] equals ~c[t] even though, as shown below, that does not follow
  logically from the axioms introduced.
  ~bv[]
  ; Introduce our metafunction.
  (defun my-cancel (term)
    (case-match term
      (('f ('g))
       *t*)
      (& term)))

  ; Introduce our evaluator and prove our meta rule, but in the same
  ; encapsulate!
  (encapsulate
   ((f (x) t))

   (local (defun f (x) (declare (ignore x)) t))

   (defevaluator evl evl-list
     ((f x)))

   (defthm correctness-of-my-cancel
     (equal (evl x a)
            (evl (my-cancel x) a))
     :rule-classes ((:meta :trigger-fns (f)))))

  ; Prove that (f x) = t.
  (encapsulate
   ()

   (local (defstub c () t))

   (local (encapsulate
           ()
           (local (defun g () (c)))
           (local (in-theory (disable g (g))))
           (local (defthm f-g
                    (equal (f (g)) t)
                    :rule-classes nil))
           (defthm f-c
             (equal (f (c)) t)
             :hints ((\"Goal\" :use f-g
                      :in-theory (e/d (g) (correctness-of-my-cancel))))
             :rule-classes nil)))

   (defthm f-t
     (equal (f x) t)
     :hints ((\"Goal\" :by (:functional-instance
                          f-c
                          (c (lambda () x)))))
     :rule-classes nil))
  ~ev[]
  To see that the term ~c[(equal (f x) t)] does not follow logically from the
  axiomatic ~il[events] above, consider following the above definition of
  ~c[my-cancel] with the following ~il[events] instead.
  ~bv[]
  ; (defun my-cancel (term) ...) as before, then:

  (defun f (x)
    (not x))

  (defun g ()
    nil)

  (defevaluator evl evl-list
     ((f x) (g)))
  ~ev[]
  These events imply the axiomatic events above, because we still have the
  definition of ~c[my-cancel], we have a stronger ~ilc[defevaluator] event, and
  we can now prove ~c[correctness-of-my-cancel] exactly as it is stated above.
  So, the rule ~c[f-t] is a logical consequence of the chronology of the
  current session.  However, in the current session we can also prove the
  following rule, which contradicts ~c[f-t].
  ~bv[]
  (defthm f-not-t
    (equal (f t) nil)
    :rule-classes nil)
  ~ev[]
  It follows that the current session logically yields a contradiction!

  Erik Reeber has taken the above example and modified it to prove ~c[nil] in
  ACL2 Version_3.1, as follows.
  ~bv[]

  (in-package \"ACL2\")

  (defun my-cancel (term)
     (case-match term
       (('f ('g))
        *t*)
       (('f2 ('g2))
        *t*)
       (& term)))

  (defun f2 (x)
     (not x))

  (defun g2 ()
     nil)

  (encapsulate
    ((f (x) t))

    (local (defun f (x) (declare (ignore x)) t))

    (defevaluator evl evl-list
      ((f x)
       (f2 x)
       (g2)))

    (defthm correctness-of-my-cancel
      (equal (evl x a)
             (evl (my-cancel x) a))
      :rule-classes ((:meta :trigger-fns (f)))))

  (encapsulate
    ()

    (local (defstub c () t))

    (local (encapsulate
            ()
            (local (defun g () (c)))
            (local (in-theory (disable g (g))))
            (local (defthm f-g
                     (equal (f (g)) t)
                     :rule-classes nil))
            (defthm f-c
              (equal (f (c)) t)
              :hints ((\"Goal\" :use f-g
                       :in-theory (e/d (g) (correctness-of-my-cancel))))
              :rule-classes nil)))

    (defthm f-t
      (equal (f x) t)
      :hints ((\"Goal\" :by (:functional-instance
                           f-c
                           (c (lambda () x)))))
      :rule-classes nil))

  (defun g ()
     nil)

  ; Below is the expansion of the following defevaluator, changed slightly as
  ; indicated by comments.
  ; (defevaluator evl2 evl2-list ((f x) (f2 x) (g) (g2)))

  (ENCAPSULATE
    (((EVL2 * *) => *)
     ((EVL2-LIST * *) => *))
    (SET-INHIBIT-WARNINGS \"theory\")
    (LOCAL (IN-THEORY *DEFEVALUATOR-FORM-BASE-THEORY*))
    (LOCAL
     (MUTUAL-RECURSION (DEFUN EVL2 (X A)
                         (DECLARE (XARGS :VERIFY-GUARDS NIL
                                         :MEASURE (ACL2-COUNT X)
                                         :WELL-FOUNDED-RELATION O<
                                         :MODE :LOGIC))
                         (COND ((SYMBOLP X) (CDR (ASSOC-EQ X A)))
                               ((ATOM X) NIL)
                               ((EQ (CAR X) 'QUOTE) (CAR (CDR X)))
                               ((CONSP (CAR X))
                                (EVL2 (CAR (CDR (CDR (CAR X))))
                                      (PAIRLIS$ (CAR (CDR (CAR X)))
                                                (EVL2-LIST (CDR X) A))))
                               ((EQUAL (CAR X) 'F) ; changed f to f2 just below
                                (F2 (EVL2 (CAR (CDR X)) A)))
                               ((EQUAL (CAR X) 'F2)
                                (F2 (EVL2 (CAR (CDR X)) A)))
                               ((EQUAL (CAR X) 'G) (G))
                               ((EQUAL (CAR X) 'G2) (G2))
                               (T NIL)))
                       (DEFUN EVL2-LIST (X-LST A)
                         (DECLARE (XARGS :MEASURE (ACL2-COUNT X-LST)
                                         :WELL-FOUNDED-RELATION O<))
                         (COND ((ENDP X-LST) NIL)
                               (T (CONS (EVL2 (CAR X-LST) A)
                                        (EVL2-LIST (CDR X-LST) A)))))))

    (DEFTHM EVL2-CONSTRAINT-1
      (IMPLIES (SYMBOLP X)
               (EQUAL (EVL2 X A)
                      (CDR (ASSOC-EQ X A)))))
    (DEFTHM EVL2-CONSTRAINT-2
      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'QUOTE))
               (EQUAL (EVL2 X A) (CADR X))))
    (DEFTHM EVL2-CONSTRAINT-3
      (IMPLIES (AND (CONSP X) (CONSP (CAR X)))
               (EQUAL (EVL2 X A)
                      (EVL2 (CADDAR X)
                            (PAIRLIS$ (CADAR X)
                                      (EVL2-LIST (CDR X) A))))))
    (DEFTHM EVL2-CONSTRAINT-4
      (IMPLIES (NOT (CONSP X-LST))
               (EQUAL (EVL2-LIST X-LST A) NIL)))
    (DEFTHM EVL2-CONSTRAINT-5
      (IMPLIES (CONSP X-LST)
               (EQUAL (EVL2-LIST X-LST A)
                      (CONS (EVL2 (CAR X-LST) A)
                            (EVL2-LIST (CDR X-LST) A)))))
    (DEFTHM EVL2-CONSTRAINT-6
      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'F))
               (EQUAL (EVL2 X A) ; changed f to f2 just below
                      (F2 (EVL2 (CADR X) A)))))
    (DEFTHM EVL2-CONSTRAINT-7
      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'F2))
               (EQUAL (EVL2 X A)
                      (F2 (EVL2 (CADR X) A)))))
    (DEFTHM EVL2-CONSTRAINT-8
      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'G))
               (EQUAL (EVL2 X A) (G))))
    (DEFTHM EVL2-CONSTRAINT-9
      (IMPLIES (AND (CONSP X) (EQUAL (CAR X) 'G2))
               (EQUAL (EVL2 X A) (G2)))))

  (defthm f2-t
     (equal (f2 x) t)
     :hints ((\"Goal\" :by (:functional-instance
                          f-t
                          (f f2)
                          (evl evl2)
                          (evl-list evl2-list)))))

  (defthm bug-implies-nil
     nil
     :hints ((\"Goal\" :use ((:instance f2-t (x t)))))
     :rule-classes nil)
  ~ev[]

  Finally, we also require that no function has an attachment (~pl[defattach])
  that is both ancestral in the evaluator and also ancestral in the meta or
  clause-processor functions.  (If you don't use ~ilc[defattach] then you can
  ignore this condition.)  Without this restriction, the following events prove
  ~c[nil].
  ~bv[]
  (in-package \"ACL2\")
  (defstub f () t)
  (defevaluator evl evl-list
    ((f)))
  (defun my-meta-fn (x)
    (if (equal x '(f))
        (list 'quote (f))
      x))
  (defthm my-meta-fn-correct
    (equal (evl x a)
           (evl (my-meta-fn x) a))
    :rule-classes ((:meta :trigger-fns (f))))
  (defun constant-nil ()
    (declare (xargs :guard t))
    nil)
  (defattach f constant-nil)
  (defthm f-is-nil
  ; proved using my-meta-fn-correct
    (equal (f) nil)
    :rule-classes nil)
  (defthm contradiction
    nil
    :hints ((\"Goal\" :use ((:functional-instance
                           f-is-nil
                           (f (lambda () t))))))
    :rule-classes nil)
  ~ev[]
  To see why this restriction is sufficient, see a comment in the ACL2 source
  code entitled ``; Essay on Correctness of Meta Reasoning.''")

(deflabel extended-metafunctions
  :doc
  ":Doc-Section Miscellaneous

  state and context sensitive metafunctions~/

  ~bv[]
  General Form of an Extended :Meta theorem:
  (implies (and (pseudo-termp x)              ; this hyp is optional
                (alistp a)                    ; this hyp is optional
                (ev (hyp-fn x mfc state) a)   ; this hyp is optional
                ; meta-extract hyps may also be included (see below)
                )
           (equiv (ev x a)
                  (ev (fn x mfc state) a)))
  ~ev[]
  where the restrictions are as described in the ~il[documentation] for
  ~ilc[meta] and, in addition, ~c[mfc] and ~c[state] are distinct variable
  symbols (different also from ~c[x] and ~c[a]) and ~c[state] is literally the
  symbol ~c[STATE].  A ~c[:meta] theorem of the above form installs ~c[fn] as a
  metatheoretic simplifier with hypothesis function ~c[hyp-fn], exactly as for
  vanilla metafunctions.  The only difference is that when the metafunctions
  are applied, some contextual information is passed in via the ~c[mfc]
  argument and the ACL2 ~ilc[state] is made available.

  ~l[meta] for a discussion of vanilla flavored metafunctions.  This
  documentation assumes you are familiar with the simpler situation, in
  particular, how to define a vanilla flavored metafunction, ~c[fn], and its
  associated hypothesis metafunction, ~c[hyp-fn], and how to state and prove
  metatheorems installing such functions.  Defining extended metafunctions
  requires that you also be familiar with many ACL2 implementation details.
  This documentation is sketchy on these details; see the ACL2 source code or
  email the ~il[acl2-help] list if you need more help.

  Additional hypotheses are supported, called ``meta-extract hypotheses'', that
  allow metafunctions to depend on the validity of certain terms extracted from
  the context or the logical ~il[world].  These hypotheses provide a relatively
  advanced form of metatheorem so we explain them elsewhere;
  ~pl[meta-extract].~/

  The metafunction context, ~c[mfc], is a list containing many different data
  structures used by various internal ACL2 functions.  We do not document the
  form of ~c[mfc].  Your extended metafunction should just take ~c[mfc] as its
  second formal and pass it into the functions mentioned below.  The ACL2
  ~c[state] is well-documented (~pl[state]).  Below we present expressions
  below that can be useful in defining extended metafunctions.  Some of these
  expressions involve keyword arguments, ~c[:forcep] and ~c[:ttree], which are
  optional and in most cases are fine to omit, and which we explain after we
  present the useful expressions.

  ~c[(mfc-clause mfc)]: returns the current goal, in clausal form.  A clause is
  a list of ACL2 terms, implicitly denoting the disjunction of the listed
  terms.  The clause returned by ~c[mfc-clause] is the clausal form of the
  translation (~pl[trans]) of the goal or subgoal on which the rewriter is
  working.  When a metafunction calls ~c[mfc-clause], the term being rewritten
  by the metafunction either occurs somewhere in this clause or, perhaps more
  commonly, is being rewritten on behalf of some lemma to which the rewriter
  has backchained while trying to rewrite a term in the clause.

  ~c[(mfc-ancestors mfc)]: returns an alist whose keys are the negations of the
  backchaining hypotheses being pursued.  In particular,
  ~c[(null (mfc-ancestors mfc))] will be true exactly when rewriting is on part
  of the current goal.  Exception: An element of this alist whose key is of the
  form ~c[(:binding-hyp hyp unify-subst)] indicates that ~c[hyp] has been
  encountered as a hypothesis of the form ~c[(equal var term)] or
  ~c[(equiv var (double-rewrite-term))], in each case binding variable ~c[var]
  to the result of rewriting ~c[term] under ~c[unify-subst].

  ~c[(mfc-rdepth mfc)]: returns the remaining stack depth for calls of the
  rewriter (by default, ~c[*default-rewrite-stack-limit*] at the top level;
  ~pl[rewrite-stack-limit]).  When this is 0, no further calls of the rewriter
  can be made without error.

  ~c[(mfc-type-alist mfc)]: returns the type-alist governing the occurrence of
  the term, ~c[x], being rewritten by the metafunction.  A type-alist is an
  association list, each element of which is of the form ~c[(term ts . ttree)].
  Such an element means that the term ~c[term] has the ~il[type-set] ~c[ts].
  The ~c[ttree] component is probably irrelevant here.  All the terms in the
  type-alist are in translated form (~pl[trans]).  The ~c[ts] are numbers
  denoting finite Boolean combinations of ACL2's primitive types
  (~pl[type-set]).  The type-alist includes not only information gleaned from
  the conditions governing the term being rewritten but also that gleaned from
  forward chaining from the (negations of the) other literals in the clause
  returned by ~c[mfc-clause].

  ~c[(w state)]: returns the ACL2 logical ~ilc[world].

  ~c[(mfc-unify-subst mfc)]: returns the unifying substitution when evaluating
  a ~ilc[syntaxp] or ~ilc[bind-free] hypothesis, else returns ~c[nil].

  ~c[(mfc-ts term mfc state :forcep forcep :ttreep ttreep)]: returns the
  ~c[type-set] of ~c[term] in the current context; ~pl[type-set].

  ~c[(mfc-rw term obj equiv-info mfc state)]: returns the result of rewriting
  ~c[term] in the current context, ~c[mfc], with objective ~c[obj] and the
  equivalence relation described by ~c[equiv-info].  ~c[Obj] should be ~c[t],
  ~c[nil], or ~c[?], and describes your objective: try to show that ~c[term] is
  true, false, or anything.  ~c[Equiv-info] is either ~c[nil], ~c[t], a
  function symbol ~c[fn] naming a known equivalence relation, or a list of
  congruence rules.  ~c[Nil] means return a term that is ~c[equal] to ~c[term].
  ~c[T] means return a term that is propositionally equivalent (i.e., in the
  ~c[iff] sense) to ~c[term], while ~c[fn] means return a term
  ~c[fn]-equivalent to ~c[term].  The final case, which is intended only for
  advanced users, allows the specification of generated equivalence relations,
  as supplied to the ~c[geneqv] argument of ~c[rewrite].  Generally, if you
  wish to establish that ~c[term] is true in the current context, use the idiom
  ~bv[]
  (equal (mfc-rw term t t mfc state) *t*)
  ~ev[]
  The constant ~c[*t*] is set to the internal form of the constant term ~c[t],
  i.e., ~c['t].

  ~c[(mfc-rw+ term alist obj equiv-info mfc state)]: if ~c[alist] is ~c[nil]
  then this is equivalent to ~c[(mfc-rw term obj equiv-info mfc state)].
  However, the former takes an argument, ~c[alist], that binds variables to
  terms, and returns the result of rewriting ~c[term] under that ~c[alist],
  where this rewriting is as described for ~c[mfc-rw] above.  The function
  ~c[mfc-rw+] can be more efficient than ~c[mfc-rw], because the terms in the
  binding alist have generally already been rewritten, and it can be
  inefficient to rewrite them again.  For example, consider a rewrite rule of
  the following form.
  ~bv[]
  (implies (and ...
                (syntaxp (... (mfc-rw `(bar ,x) ...) ...))
                ...)
           (equal (... x ...) ...))
  ~ev[]
  Here, ~c[x] is bound in the conclusion to the result of rewriting some term,
  say, ~c[tm].  Then the above call of ~c[mfc-rw] will rewrite ~c[tm], which is
  probably unnecessary.  So a preferable form of the rule above may be as
  follows, so that ~c[tm] is not further rewritten by ~c[mfc-rw+].
  ~bv[]
  (implies (and ...
                (syntaxp (... (mfc-rw+ '(bar v) `((v . ,x)) ...) ...))
                ...)
           (equal (... x ...) ...))
  ~ev[]
  However, you may find that the additional rewriting done by ~c[mfc-rw] is
  useful in some cases.

  ~c[(mfc-ap term mfc state)]: returns ~c[t] or ~c[nil] according to whether
  linear arithmetic can determine that ~c[term] is false.  To the cognoscenti:
  returns the contradiction flag produced by linearizing ~c[term] and adding it
  to the ~c[linear-pot-lst].

  ~c[(mfc-relieve-hyp hyp alist rune target bkptr mfc state): returns ~c[t] or
  ~c[nil] according to whether the indicated hypothesis term, ~c[hyp], can be
  relieved (proved) under the giving variable bindings, ~c[alist].  Here,
  ~c[hyp] is the hypothesis of the indicated ~ilc[rune] at (one-based) position
  ~c[bkptr], and ~c[target] is an instantiated term to which ~c[rune] is being
  applied.  Note that no indication is returned for whether any assumptions
  have been generated by ~ilc[force] or ~ilc[case-split].  (If you need such a
  feature, feel free to request it of the ACL2 implementors.)

  We explain the ~c[:forcep] and ~c[:ttreep] keyword arguments provided in some
  expressions, as promised above.  Their defaults are ~c[:same] and ~c[nil],
  respectively.  A value of ~c[:same] for ~c[:forcep] means that forcing will
  be allowed if and only if it is allowed in the current rewriting environment;
  ~pl[force].  A value of ~c[t] or ~c[nil] for ~c[:forcep] overrides this
  default and allows or disallows forcing, respectively.  By default these
  functions return a single value, ~c[val], but if ~c[:ttreep] is ~c[t] then
  they return ~c[(mv val ttree)], where ~c[ttree] is the tag-tree (~pl[ttree])
  returned by the indicated operation, with an input tag-tree of ~c[nil]).

  During the execution of a metafunction by the theorem prover, the expressions
  above compute the results specified.  Typically, you should imagine that
  there are no axioms about the ~c[mfc-] function symbols: treat them as
  uninterpreted function symbols.  There is an advanced feature, meta-extract
  hypotheses, that can avoid this logical weakness in some cases when proving
  ~c[:]~ilc[meta] rules; ~pl[meta-extract].  But we assume for the rest of the
  present ~il[documentation] topic that you do not use meta-extract hypotheses.
  Thus, in the proof of the correctness of a metafunction, no information is
  available about the results of these functions: you should
  ~em[use these functions for heuristic purposes only].

  For example, your metafunction may use these functions to decide whether to
  perform a given transformation, but the transformation must be sound
  regardless of the value that your metafunction returns.  We illustrate this
  below.  It is sometimes possible to use the hypothesis metafunction,
  ~c[hyp-fn], to generate a sufficient hypothesis to justify the
  transformation.  The generated hypothesis might have already been ``proved''
  internally by your use of ~c[mfc-ts] or ~c[mfc-rw], but the system will have
  to prove it ``officially'' by relieving it.  We illustrate this below also.

  We conclude with a script that defines, verifies, and uses several extended
  metafunctions.  This script is based on one provided by Robert Krug, who was
  instrumental in the development of this style of metafunction and whose help
  we gratefully acknowledge.

  ~bv[]

  ; Here is an example.  I will define (foo i j) simply to be (+ i j).
  ; But I will keep its definition disabled so the theorem prover
  ; doesn't know that.  Then I will define an extended metafunction
  ; that reduces (foo i (- i)) to 0 provided i has integer type and the
  ; expression (< 10 i) occurs as a hypothesis in the clause.

  ; Note that (foo i (- i)) is 0 in any case.

  (defun foo (i j) (+ i j))

  (defevaluator eva eva-lst ((foo i j)
                             (unary-- i)
  
  ; I won't need these two cases until the last example below, but I
  ; include them now.
  
                             (if x y z)
                             (integerp x)))

  (set-state-ok t)

  (defun metafn (x mfc state)
    (cond
     ((and (consp x)
           (equal (car x) 'foo)
           (equal (caddr x) (list 'unary-- (cadr x))))

  ; So x is of the form (foo i (- i)).  Now I want to check some other
  ; conditions.

      (cond ((and (ts-subsetp (mfc-ts (cadr x) mfc state)
                              *ts-integer*)
                  (member-equal `(NOT (< '10 ,(cadr x))) 
                                (mfc-clause mfc)))
             (quote (quote 0)))
            (t x)))
     (t x)))

  (defthm metafn-correct
    (equal (eva x a) (eva (metafn x mfc state) a))
    :rule-classes ((:meta :trigger-fns (foo))))

  (in-theory (disable foo))

  ; The following will fail because the metafunction won't fire.
  ; We don't know enough about i.

  (thm (equal (foo i (- i)) 0))

  ; Same here.

  (thm (implies (and (integerp i) (< 0 i)) (equal (foo i (- i)) 0)))

  ; But this will work.

  (thm (implies (and (integerp i) (< 10 i))
                (equal (foo i (- i)) 0)))

  ; This won't, because the metafunction looks for (< 10 i) literally,
  ; not just something that implies it.
  
  (thm (implies (and (integerp i) (< 11 i))
                (equal (foo i (- i)) 0)))

  ; Now I will undo the defun of metafn and repeat the exercise, but
  ; this time check the weaker condition that (< 10 i) is provable
  ; (by rewriting it) rather than explicitly present.  

  (ubt 'metafn)
  
  (defun metafn (x mfc state)
    (cond
     ((and (consp x)
           (equal (car x) 'foo)
           (equal (caddr x) (list 'unary-- (cadr x))))
      (cond ((and (ts-subsetp (mfc-ts (cadr x) mfc state)
                              *ts-integer*)
                  (equal (mfc-rw `(< '10 ,(cadr x)) t t mfc state)
                         *t*))
  
  ; The mfc-rw above rewrites (< 10 i) with objective t and iffp t.  The
  ; objective means the theorem prover will try to establish it.  The
  ; iffp means the theorem prover can rewrite maintaining propositional
  ; equivalence instead of strict equality.

             (quote (quote 0)))
            (t x)))
     (t x)))

  (defthm metafn-correct
    (equal (eva x a) (eva (metafn x mfc state) a))
    :rule-classes ((:meta :trigger-fns (foo))))

  (in-theory (disable foo))

  ; Now it will prove both:

  (thm (implies (and (integerp i) (< 10 i))
                (equal (foo i (- i)) 0)))

  (thm (implies (and (integerp i) (< 11 i))
                (equal (foo i (- i)) 0)))

  ; Now I undo the defun of metafn and change the problem entirely.
  ; This time I will rewrite (integerp (foo i j)) to t.  Note that
  ; this is true if i and j are integers.  I can check this
  ; internally, but have to generate a hyp-fn to make it official.

  (ubt 'metafn)
  
  (defun metafn (x mfc state)
    (cond
     ((and (consp x)
           (equal (car x) 'integerp)
           (consp (cadr x))
           (equal (car (cadr x)) 'foo))
  
  ; So x is (integerp (foo i j)).  Now check that i and j are
  ; ``probably'' integers.

      (cond ((and (ts-subsetp (mfc-ts (cadr (cadr x)) mfc state)
                              *ts-integer*)
                  (ts-subsetp (mfc-ts (caddr (cadr x)) mfc state)
                              *ts-integer*))
             *t*)
            (t x)))
     (t x)))

  ; To justify this transformation, I generate the appropriate hyps.

  (defun hyp-fn (x mfc state)

    (declare (ignore mfc state))

  ; The hyp-fn is run only if the metafn produces an answer different
  ; from its input.  Thus, we know at execution time that x is of the
  ; form (integerp (foo i j)) and we know that metafn rewrote
  ; (integerp i) and (integerp j) both to t.  So we just produce their
  ; conjunction.  Note that we must produce a translated term; we
  ; cannot use the macro AND and must quote constants!  Sometimes you
  ; must do tests in the hyp-fn to figure out which case the metafn
  ; produced, but not in this example.
  
             `(if (integerp ,(cadr (cadr x)))
                  (integerp ,(caddr (cadr x)))
                  'nil))
    
  (defthm metafn-correct
    (implies (eva (hyp-fn x mfc state) a)
             (equal (eva x a) (eva (metafn x mfc state) a)))
    :rule-classes ((:meta :trigger-fns (integerp))))

  (in-theory (disable foo))

  ; This will not be proved.

  (thm (implies (and (rationalp x) (integerp i)) (integerp (foo i j))))

  ; But this will be.

  (thm (implies (and (rationalp x)
                     (integerp i)
                     (integerp j))
                (integerp (foo i j))))

  ~ev[]
  ")

(deflabel meta-extract
  :doc
  ":Doc-Section Miscellaneous

  meta reasoning using valid terms extracted from context or ~il[world]~/

  For this topic, we assume familiarity with metatheorems and
  metafunctions (~pl[meta]).  The capability described here ~-[] so-called
  ``meta-extract hypotheses'' for a ~c[:]~ilc[meta] or a
  ~c[:]~ilc[clause-processor] rule ~-[] provides an advanced form of meta-level
  reasoning that was largely designed by Sol Swords, who also provided a
  preliminary implementation.

  A ~c[:meta] rule may now have hypotheses, known as ``meta-extract
  hypotheses'', that take either of the following two forms.  Here ~c[evl] is
  the evaluator, ~c[obj] is an arbitrary term, ~c[mfc] is the variable used as
  the metafunction context (~pl[extended-metafunctions]), ~c[state] is
  literally the symbol ~c[STATE], ~c[a] is the second argument of ~c[evl] in
  both arguments of the conclusion of the rule, and ~c[aa] is an arbitrary
  term.
  ~bv[]
  (evl (meta-extract-contextual-fact obj mfc state) a)
  (evl (meta-extract-global-fact obj state) aa))
  ~ev[]
  The second form is legal for rules of class ~c[:meta] and also for rules of
  class ~c[:clause-processor].  However, the first form is not legal for
  ~c[:clause-processor] rules, and for ~c[:meta] rules it is only allowed if
  the metafunction is an extended metafunction.~/

  These additional hypotheses may be necessary in order to prove a proposed
  metatheorem or (for the second type of hypothesis above) clause-processor
  rule, in particular when the correctness of the metafunction depends on the
  correctness of utilities extracting formulas from the logical ~il[world] or
  (for the first type) facts from the metafunction context (mfc).  After the
  rule is proved, however, the meta-extract hypotheses have no effect on how
  the rule is applied during a proof.  An argument for correctness of using
  meta-extract hypotheses is given in the ACL2 source code within a comment
  entitled ``Essay on Correctness of Meta Reasoning''.  In the documentation
  below, we focus only on ~c[:]~ilc[meta] rules, since the use of
  ~c[meta-extract-global-fact] hypotheses in ~c[:]~ilc[clause-processor] rules
  is entirely analogous.  And for ~c[:meta] rules we focus not on the
  application of rules but, rather, on how the use of meta-extract hypotheses
  allow you to prove correctness of metafunctions that use facts from the
  logical ~il[world] or the metafunction context (mfc).

  Below we describe properties of ~c[meta-extract-contextual-fact] and
  ~c[meta-extract-global-fact], but only after we illustrate their utility with
  an example.  But even before we present that example, we first give a sense
  of how to think about these functions by showing a theorem that one can prove
  about the first of them.  If this snippet doesn't help your intuition, then
  just skip over it and start with the example.
  ~bv[]
  (defevaluator evl evl-list
    ((binary-+ x y) (typespec-check x y)))

  (thm (implies
        (not (bad-atom (cdr (assoc-equal 'x alist))))
        (equal (evl (meta-extract-contextual-fact (list :typeset 'x)
                                                  mfc
                                                  state)
                    alist)
               (not (equal 0 ; indicates non-empty intersection
                           (logand (type-set-quote ; type-set of a constant
                                    (cdr (assoc-equal 'x alist)))
                                   (mfc-ts-fn 'x mfc state nil)))))))
  ~ev[]

  The following example comes from the community book,
  ~c[books/clause-processors/meta-extract-simple-test.lisp], which presents
  very basic (and contrived) examples that nevertheless illustrate meta-extract
  hypotheses.
  ~bv[]
  (defthm plus-identity-2-meta
    (implies (and (nthmeta-ev (meta-extract-global-fact '(:formula bar-posp)
                                                        state)
                              (list (cons 'u
                                          (nthmeta-ev (cadr (cadr term))
                                                      a))))
                  (nthmeta-ev (meta-extract-contextual-fact
                               `(:typeset ,(caddr term)) mfc state)
                              a))
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (plus-identity-2-metafn term mfc state) a)))
    :rule-classes ((:meta :trigger-fns (binary-+))))
  ~ev[]
  The two hypotheses illustratate the two basic kinds of meta-extract
  hypotheses: applications of the evaluator to a call of
  ~c[meta-extract-global-fact] and to a call of
  ~c[meta-extract-contextual-fact].  Here is the definition of the metafunction
  used in the above rule, slightly simplified here from what is found in the
  above book (but adequate for proving the two events that follow it in the
  above book).
  ~bv[]
  (defun plus-identity-2-metafn (term mfc state)
    (declare (xargs :stobjs state :verify-guards nil))
    (case-match term
      (('binary-+ ('bar &) y)
       (cond
        ((equal (meta-extract-formula 'bar-posp state)
                '(POSP (BAR U)))
         (if (ts= (mfc-ts y mfc state :forcep nil)
                  *ts-character*)
             (cadr term)
           term))
        (t term)))
      (& term)))
  ~ev[]
  This metafunction returns its input term unchanged except in the case that
  the term is of the form ~c[(binary-+ (bar x) y)] and the following two
  conditions are met, in which case it returns ~c[(bar x)].
  ~bv[]
  (1)  (equal (meta-extract-formula 'bar-posp state)
              '(POSP (BAR U)))

  (2)  (ts= (mfc-ts y mfc state :forcep nil)
            *ts-character*)
  ~ev[]
  So suppose that term is ~c[(list 'binary-+ (list 'bar x) y)].  We show how
  the meta-extract hypotheses together with (1) and (2) imply that the
  conclusion of the above ~c[:meta] rule holds.  Here is that conclusion after
  a bit of simplification.
  ~bv[]
  (equal (nthmeta-ev (list 'binary-+ (list 'bar x) y) a)
         (nthmeta-ev (list 'bar x) a))
  ~ev[]
  This equality simplifies as follows using the evaluator properties of
  ~c[nthmeta-ev].
  ~bv[]
  (equal (binary-+ (bar (nthmeta-ev x a))
                   (nthmeta-ev y a))
         (bar (nthmeta-ev x a)))
  ~ev[]
  Since a positive number plus a character is that number, it clearly suffices
  to show:
  ~bv[]
  (A)  (posp (bar (nthmeta-ev x a)))

  (B)  (characterp (nthmeta-ev y a))
  ~ev[]
  It remains then to show that these follow from (1) and (2) together with the
  meta-extract hypotheses.

  First consider (A).  We show that it is just a simplification of the first
  meta-extract hypothesis.
  ~bv[]
  (nthmeta-ev (meta-extract-global-fact '(:formula bar-posp)
                                        state)
              (list (cons 'u
                          (nthmeta-ev (cadr (cadr term))
                                      a))))
  = {by our assumption that term is (list 'binary-+ (list 'bar x) y)}
  (nthmeta-ev (meta-extract-global-fact '(:formula bar-posp)
                                        state)
              (list (cons 'u
                          (nthmeta-ev x a))))
  = {by definition of meta-extract-global-fact, as discussed later}
  (nthmeta-ev (meta-extract-formula 'bar-posp state)
              (list (cons 'u
                          (nthmeta-ev x a))))
  = {by (1)}
  (nthmeta-ev '(posp (bar u))
              (list (cons 'u
                          (nthmeta-ev x a))))
  = {by evaluator properties of nthmeta-ev}
  (posp (bar (nthmeta-ev x a)))
  ~ev[]

  Now consider (B).  We show that it is just a simplification of the second
  meta-extract hypothesis.
  ~bv[]
  (nthmeta-ev (meta-extract-contextual-fact
               `(:typeset ,(caddr term)) mfc state)
              a)
  = {by our assumption that term is (list 'binary-+ (list 'bar x) y)}
  (nthmeta-ev (meta-extract-contextual-fact (list ':typeset y) mfc state)
              a)
  = {by definition of meta-extract-contextual-fact, as discussed later}
  (nthmeta-ev (list 'typespec-check
                    (list 'quote
                          (mfc-ts y mfc state :forcep nil))
                    y)
              a)
  = {by (2)}
  (nthmeta-ev (list 'typespec-check
                    (list 'quote *ts-character*)
                    y)
              a)
  = {by evaluator properties of nthmeta-ev}
  (typespec-check *ts-character* (nthmeta-ev y a))
  = {by definition of typespec-check}
  (characterp (nthmeta-ev y a))
  ~ev[]

  Note the use of ~c[:forcep nil] above.  All of the ~c[mfc-xx] functions take
  a keyword argument ~c[:forcep].  Calls of ~c[mfc-xx] functions made on behalf
  of ~c[meta-extract-contextual-fact] always use ~c[:forcep nil], so in order
  to reason about these calls in your own metafunctions, you will want to use
  ~c[:forcep nil].  We are contemplating adding a utility like
  ~c[meta-extract-contextual-fact] that allows forcing but returns a tag-tree
  (~pl[ttree]).

  Finally, we document what is provided logically by calls of
  ~c[meta-extract-global-fact] and ~c[meta-extract-contextual-fact].  Of
  course, you are invited to look at the definitions of these function in the
  ACL2 source code, or by using ~c[:]~ilc[pe].  Note that both of these
  functions are non-executable (their bodies are inside a call of
  ~ilc[non-exec]); their function is purely logical, not for execution.  The
  functions return ~c[*t*], i.e., ~c[(quote t)], in cases that they provide no
  information.

  First we consider the value of ~c[(meta-extract-global-fact obj state)] for
  various values of ~c[obj].

  ~bq[]
  Case ~c[obj] = (list :formula FN):~nl[]
  The value reduces to the value of ~c[(meta-extract-formula FN state)], which
  returns the ``formula'' of ~c[FN] in the following sense.  If ~c[FN] is a
  function symbol with formals ~c[(X1 ... Xk)], then the formula is the
  ~il[constraint] on ~c[FN] if ~c[FN] is constrained or introduced by
  ~ilc[defchoose], and otherwise is ~c[(equal (FN X1 ... Xk) BODY)], where
  ~c[BODY] is the (unsimplified) body of the definition of ~c[FN].  Otherwise,
  if ~c[FN] is the name of a theorem, the formula is just what is stored for
  that theorem.  Otherwise, the formula is ~c[*t*].

  Case ~c[obj] = (list :lemma FN N):~nl[]
  Assume ~c[N] is a natural number; otherwise, treat ~c[N] as 0.  If ~c[FN] is
  a function symbol with more than ~c[N] associated lemmas ~-[] ``associated''
  in the sense of being either a ~c[:]~ilc[definition] rule for ~c[FN] or a
  ~c[:]~ilc[rewrite] rule for ~c[FN] whose left-hand side has a top function
  symbol of ~c[FN] ~-[] then the value is the ~c[N]th such lemma (with
  zero-based indexing).  Otherwise the value is ~c[*t*].

  For any other values of ~c[obj], the value is ~c[*t*].~eq[]

  Finally, the value of ~c[(meta-extract-contextual-fact obj mfc state)] 
  is as follows for various values of ~c[obj].

  ~bq[]
  Case ~c[obj] = (list :typeset TERM ...):~nl[]
  The value is the value of ~c[(typespec-check ts TERM)], where ~c[ts] is
  the value of ~c[(mfc-ts TERM mfc state :forcep nil :ttreep nil)], and where
  ~c[(typespec-check ts val)] is defined to be true when ~c[val] has type-set
  ~c[ts].  (Exception: If ~c[val] satisfies ~c[bad-atom] then
  ~c[typespec-check] is true when ~c[ts] is negative.)

  Case ~c[obj] = (list :rw+ TERM ALIST OBJ EQUIV ...):~nl[]
  We assume below that ~c[EQUIV] is a symbol that represents an equivalence
  relation, where ~c[nil] represents ~ilc[equal], ~c[t] represents ~ilc[iff],
  and otherwise ~c[EQUIV] represents itself (an equivalence relation in the
  current logical ~il[world]).  For any other ~c[EQUIV] the value is ~c[*t*].
  Now let ~c[rhs] be the value of
  ~c[(mfc-rw+ TERM ALIST OBJ EQUIV mfc state :forcep nil :ttreep nil)].  Then
  the value is the term ~c[(list 'equv (sublis-var ALIST TERM) rhs)], where
  equv is the equivalence relation represented by ~c[EQUIV], and ~c[sublis-var]
  is defined to substitute a variable-binding alist into a term.

  Case ~c[obj] = (list :rw TERM OBJ EQUIV ...):~nl[]
  The value is the same as above but for an ~c[ALIST] of ~c[nil], i.e., for the
  case that ~c[obj] is ~c[(list :rw+ TERM nil OBJ EQUIV ...)].

  Case ~c[obj] = (list :ap TERM ...):~nl[]
  The value is ~c[(list 'not TERM)] if
  ~c[(mfc-ap TERM mfc state :forcep nil :ttreep nil)] is true, else is
  ~c[*t*].

  Case ~c[obj] = (list :relieve-hyp HYP ALIST RUNE TARGET BKPTR ...):~nl[]
  The value is ~c[(sublis-var alist hyp)] ~-[] see above for a discussion of
  ~c[sublis-var] ~-[] if the following is true.
  ~bv[]
  (mfc-relieve-hyp hyp alist rune target bkptr mfc state
                   :forcep nil :ttreep nil)
  ~ev[]
  Otherwise the value is ~c[*t*].

  If no case above applies, then the value is ~c[*t*].~eq[]~/")

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

; The clauses that describe an evaluator include an evaluator-clause
; (q.v.)  for each fn in fn-args-lst plus clauses describing evfn when
; x is a variable symbol, a quoted object, and a lambda application,
; plus clauses describing evfn-lst on nil and on conses.

; Note: The function chk-evaluator exploits the fact that if evfn is
; an evaluator, then the constraint on it will contain at least 4
; clauses.  (One of the five fixed clauses below is about only
; evfn-lst and not about evfn and hence wouldn't be among the
; constraints of evfn.)  If this changes, change chk-evaluatorp.

; The functions guess-fn-args-lst-for-evfn and guess-evfn-lst-for-evfn take the
; known constraints on an evfn and guess the evfn-lst and list of fns for which
; evfn might be an evaluator.  These functions knows the structure of the
; clauses generated here, in particular, the structure of the clause describing
; evfn-lst on a cons and the structure of the evaluator-clause for a given fn.
; If these structures change, change these two functions.

; WARNING: Don't change the clauses below without reading the Notes
; above!

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
                                  (evfn-lst (cdr x-lst) a))))))
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
; interpretted by evfn is 'if then our full-blown clausify will break
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
            (assert$ (not (eq x *unknown-constraints*))
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
                       (evaluator-clauses evfn evfn-lst fn-args-lst))))
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

(defun defevaluator-form/defthms (evfn prefix i clauses)
  (cond ((null clauses) nil)
        (t (cons (list* (if (eql i 0) 'defthmd 'defthm)
                        (genvar evfn prefix i nil)
                        (prettyify-clause (car clauses) nil nil)
                        (and (eql i 0)
                             `(:hints
                               (("Goal"
                                 :expand ((:free (x) (hide x))
                                          (,evfn x a))
                                 :in-theory (disable (:executable-counterpart
                                                      ,evfn)))))))
                 (defevaluator-form/defthms evfn prefix (1+ i)
                   (cdr clauses))))))

(defun defevaluator-form/fns-clauses (evfn fn-args-lst)

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
            (list (list 'equal '(car x) (kwote (caar fn-args-lst)))
                  (cons (caar fn-args-lst)
                        (evaluator-clause/arglist evfn
                                                  (cdar fn-args-lst)
                                                  '(cdr x))))
            (defevaluator-form/fns-clauses evfn (cdr fn-args-lst))))))

(defconst *defevaluator-form-base-theory*
  (append *definition-minimal-theory*
          '(car-cdr-elim
            car-cons cdr-cons
            o< o-finp o-first-expt o-first-coeff o-rst natp posp
            acl2-count alistp
            fix-true-list kwote kwote-lst pairlis$-fix-true-list
            (:type-prescription acl2-count))))

(defun defevaluator-form (evfn evfn-lst fn-args-lst)
  (let* ((clauses (evaluator-clauses evfn evfn-lst fn-args-lst))
         (fns-clauses (defevaluator-form/fns-clauses evfn fn-args-lst))
         (defthms (defevaluator-form/defthms
                    evfn
                    (symbol-name (pack2 evfn '-constraint-))
                    0
                    clauses)))
    `(encapsulate
      (((,evfn * *) => *)
       ((,evfn-lst * *) => *))
      (set-inhibit-warnings "theory")
      (local (in-theory *defevaluator-form-base-theory*))
      ,@(sublis
         (list (cons 'evfn evfn)
               (cons 'evfn-lst evfn-lst)
               (cons 'fns-clauses fns-clauses)
               (cons 'defthms defthms))
         '((local
            (mutual-recursion
             (defun-nx evfn (x a)
               (declare (xargs :verify-guards nil
                               :measure (acl2-count x)
                               :well-founded-relation o<
                               :mode :logic))
               (cond
                ((symbolp x)

; Before removing the conjunct of x below, see the long comment in
; evaluator-clauses about "without making a special case for x = nil".

                 (and x (cdr (assoc-eq x a))))
                ((atom x) nil)
                ((eq (car x) 'quote) (car (cdr x)))
                ((consp (car x))
                 (evfn (car (cdr (cdr (car x))))
                       (pairlis$ (car (cdr (car x)))
                                 (evfn-lst (cdr x) a))))
                .
                fns-clauses))
             (defun-nx evfn-lst (x-lst a)
               (declare (xargs :measure (acl2-count x-lst)
                               :well-founded-relation o<))
               (cond ((endp x-lst) nil)
                     (t (cons (evfn (car x-lst) a)
                              (evfn-lst (cdr x-lst) a)))))))
           (local
            (defthm eval-list-kwote-lst
              (equal (evfn-lst (kwote-lst args) a)
                     (fix-true-list args))))
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
              fn-args-lst is a true list of lists of symbols.  However, ~x0 ~
              does not have this form."
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

(defmacro defevaluator (&whole x evfn evfn-lst fn-args-lst &key skip-checks)

; Note: It might be nice to allow defevaluator to take a :DOC string, but that
; would require allowing encapsulate to take such a string!

  ":Doc-Section Events

  introduce an evaluator function~/
  ~bv[]
  Example:
  (defevaluator evl evl-list
    ((length x) (member-equal x y)))
  ~ev[]
  ~l[meta].~/
  ~bv[]
  General Form:
  (defevaluator ev ev-list
     ((g1 x1 ... xn_1)
      ...
      (gk x1 ... xn_k))
  ~ev[]
  where ~c[ev] and ~c[ev]-list are new function symbols and ~c[g1], ..., ~c[gk] are
  old function symbols with the indicated number of formals, i.e.,
  each ~c[gi] has ~c[n_i] formals.

  This function provides a convenient way to constrain ~c[ev] and ~c[ev-list]
  to be mutually-recursive evaluator functions for the symbols ~c[g1],
  ..., ~c[gk].  Roughly speaking, an evaluator function for a fixed,
  finite set of function symbols is a restriction of the universal
  evaluator to terms composed of variables, constants, lambda
  expressions, and applications of the given functions.  However,
  evaluator functions are constrained rather than defined, so that the
  proof that a given metafunction is correct vis-a-vis a particular
  evaluator function can be lifted (by functional instantiation) to a
  proof that it is correct for any larger evaluator function.
  ~l[meta] for a discussion of metafunctions.

  ~c[Defevaluator] executes an ~ilc[encapsulate] after generating the
  appropriate ~ilc[defun] and ~ilc[defthm] events.  Perhaps the easiest way to
  understand what ~c[defevaluator] does is to execute the keyword command
  ~bv[]
  :trans1 (defevaluator evl evl-list ((length x) (member-equal x y)))
  ~ev[]
  and inspect the output.  This trick is also useful in the rare case
  that the event fails because a hint is needed.  In that case, the
  output of ~c[:]~ilc[trans1] can be edited by adding hints, then
  submitted directly.

  Formally, ~c[ev] is said to be an ``evaluator function for ~c[g1],
  ..., ~c[gk], with mutually-recursive counterpart ~c[ev-list]'' iff
  ~c[ev] and ~c[ev-list] are constrained functions satisfying just the
  ~il[constraint]s discussed below.

  ~c[Ev] and ~c[ev-list] must satisfy ~il[constraint]s (0)-(4) and (k):
  ~bv[]
  (0) How to ev an arbitrary function application:
      (implies (and (consp x)
                    (syntaxp (not (equal a ''nil)))
                    (not (equal (car x) 'quote)))
               (equal (ev x a)
                      (ev (cons (car x)
                                (kwote-lst (ev-list (cdr x) a)))
                          nil)))

  (1) How to ev a variable symbol:
      (implies (symbolp x)
               (equal (ev x a) (and x (cdr (assoc-equal x a)))))

  (2) How to ev a constant:
      (implies (and (consp x)
                    (equal (car x) 'quote))
               (equal (ev x a) (cadr x)))

  (3) How to ev a lambda application:
      (implies (and (consp x)
                    (consp (car x)))
               (equal (ev x a)
                      (ev (caddar x)
                          (pairlis$ (cadar x)
                                    (ev-list (cdr x) a)))))

  (4) How to ev an argument list:
      (implies (consp x-lst)
               (equal (ev-list x-lst a)
                      (cons (ev (car x-lst) a)
                            (ev-list (cdr x-lst) a))))
      (implies (not (consp x-lst))
               (equal (ev-list x-lst a)
                      nil))

  (k) For each i from 1 to k, how to ev an application of gi,
      where gi is a function symbol of n arguments:
      (implies (and (consp x)
                    (equal (car x) 'gi))
               (equal (ev x a)
                      (gi (ev x1 a)
                          ...
                          (ev xn a)))),
      where xi is the (cad...dr x) expression equivalent to (nth i x).
  ~ev[]
  ~c[Defevaluator] defines suitable witnesses for ~c[ev] and ~c[ev-list], proves
  the theorems about them, and constrains ~c[ev] and ~c[ev-list]
  appropriately.  We expect ~c[defevaluator] to work without assistance
  from you, though the proofs do take some time and generate a lot of
  output.  The proofs are done in the context of a fixed theory,
  namely the value of the constant ~c[*defevaluator-form-base-theory*].

  (Aside: (3) above may seem surprising, since the bindings of ~c[a] are not
  included in the environment that is used to evaluate the lambda body,
  ~c[(caddar x)].  However, ACL2 lambda expressions are all ~em[closed]:
  in ~c[(lambda (v1 ... vn) body)], the only free variables in ~c[body] are
  among the ~c[vi].  ~l[term].)"

; This function executes an encapsulate that defines an evaluator
; evfn (with mutually recursive counterpart evfn-lst for lists of
; terms) that recognizes the functions in fns.

  (let ((form (defevaluator-form evfn evfn-lst fn-args-lst)))
    (cond (skip-checks form)
          (t `(progn ,(defevaluator-check-form x evfn evfn-lst fn-args-lst)
                     ,form)))))

(deflabel term-table
  :doc
  ":Doc-Section switches-parameters-and-modes

  a table used to validate meta rules~/
  ~bv[]
  Example:
  (table term-table t '((binary-+ x y) '3 'nil (car x)))
  ~ev[]~/

  ~l[table] for a general discussion of tables and the ~c[table]
  event used to manipulate tables.

  The ``~c[term-table]'' is used at the time a meta rule is checked for
  syntactic correctness.  Each proposed metafunction is run on each
  term in this table, and the result in each case is checked to make
  sure that it is a ~c[termp] in the current world.  In each case where
  this test fails, a warning is printed.

  Whenever a metafunction is run in support of the application of a
  meta rule, the result must be a term in the current world.  When the
  result is not a term, a hard error arises.  The ~c[term-table] is simply
  a means for providing feedback to the user at the time a meta rule
  is submitted, warning of the definite possibility that such a hard
  error will occur at some point in the future.

  The key used in ~c[term-table] is arbitrary.  The top-most value is
  always the one that is used; it is the entire list of terms to be
  considered.  Each must be a ~c[termp] in the current ACL2 world.~/")

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
           ((!ev ('meta-extract-contextual-fact & !mfc-symbol 'state) !a)
            (mv hs t))
           (& (mv (cons hyp hs) flg))))))))

(defun remove-meta-extract-global-hyps (hyps ev)

; Return (mv hyps' flg), where hyps' is the result of removing suitable
; meta-extract-global-fact hypotheses from hyps and flg is true if and only if
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
           ((!ev ('meta-extract-global-fact & 'state) &)
            (mv hs t))
           (& (mv (cons hyp hs) flg))))))))

(defun meta-rule-hypothesis-functions (hyp ev x a mfc-symbol)

; Here hyp is the hypothesis of the proposed meta rule (or, *t* if
; there is none).  We want to identify the hypothesis metafunction
; (see :DOC meta) of that rule.  We return nil if the hyp is
; unacceptable, t if there is no extra hypothesis, and otherwise the
; hypothesis function.  Note that we allow, but do not require, the
; hypotheses (pseudo-termp x) and (alistp a) to be among the
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
                        fn)
                       (& nil)))))
            (append (and flg1 '(meta-extract-contextual-fact))
                    (and flg2 '(meta-extract-global-fact)))))))))

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
                  (make-rcnst ens
                              wrld
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
  (or (getprop f 'siblings nil 'current-acl2-world wrld)
      (getprop f 'recursivep nil 'current-acl2-world wrld)
      (list f)))

(defun canonical-sibling (f wrld)
  (let ((sibs (getprop f 'siblings nil 'current-acl2-world wrld)))
    (cond (sibs (car sibs))
          (t (let ((sibs (getprop f 'recursivep nil 'current-acl2-world wrld)))
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

(defun immediate-canonical-ancestors (fn wrld ignore-fns rlp)

; This function is analogous to immediate-instantiable-ancestors, but it
; traffics entirely in canonical functions and is not concerned with the notion
; of instantiablep.  To see why guards are involved, see the reference to the
; Essay on Correctness of Meta Reasoning in the Essay on Defattach, which also
; explains special handling of return-last, performed here when rlp is true.

  (let ((guard-anc
         (canonical-ffn-symbs (guard fn nil wrld) wrld nil ignore-fns rlp)))
    (mv-let (name x)
            (constraint-info fn wrld)
            (cond
             ((eq x *unknown-constraints*)
              (let* ((cl-proc
                      (getprop name 'constrainedp
                               '(:error
                                 "See immediate-canonical-ancestors:  ~
                                  expected to find a 'constrainedp property ~
                                  where we did not.")
                               'current-acl2-world wrld))
                     (supporters (unknown-constraint-supporters cl-proc wrld)))
                (collect-canonical-siblings supporters wrld guard-anc
                                            ignore-fns)))
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
     ((eq constraint *unknown-constraints*)
      (er soft ctx ; see comment in defaxiom-supporters
          "The proposed ~x0 rule, ~x1, is illegal because its evaluator ~
           function symbol, ~x2, is constrained by the (unknown) theory of a ~
           dependent clause-processor, ~x3.  See :DOC clause-processor."
          rule-type
          name
          ev
          (getprop ev 'constrainedp
                   '(:error "See chk-evaluator-use-in-rule:  expected to find ~
                             a 'constrainedp property where we did not.")
                   'current-acl2-world wrld)))
     (t
      (let* ((ev-lst (ev-lst-from-ev ev wrld))
             (ev-prop (getprop ev 'defaxiom-supporter nil
                               'current-acl2-world wrld))
             (ev-lst-prop (getprop ev-lst 'defaxiom-supporter nil
                                   'current-acl2-world wrld))
             (ev-fns (list ev ev-lst))
             (meta-fn-lst (if hyp-fn
                              (list meta-fn hyp-fn)
                            (list meta-fn)))
             (meta-anc (canonical-ancestors-lst meta-fn-lst wrld))
             (extra-anc (canonical-ancestors-lst extra-fns wrld))
             (ev-anc (canonical-ancestors-lst (list ev) wrld)))
        (cond
         ((and extra-fns
               (or (getprop ev 'predefined nil 'current-acl2-world wrld)
                   (getprop ev-lst 'predefined nil 'current-acl2-world wrld)))

; See the comment below about this case in the comment in a case below, where
; we point out that extra-fns are defined in the boot-strap world.

          (er soft ctx
              "The proposed evaluator function, ~x0, was defined in the ~
               boot-strap world.  This is illegal when meta-extract hyotheses ~
               are present, because for logical reasons our implementation ~
               assumes that the evaluator is not ancestral in ~v1."
              (if (getprop ev 'predefined nil 'current-acl2-world wrld)
                  ev
                ev-lst)
              '(meta-extract-contextual-fact meta-extract-global-fact)))
         ((or ev-prop ev-lst-prop)
          (er soft ctx ; see comment in defaxiom-supporters
              "The proposed ~x0 rule, ~x1, is illegal because its evaluator ~
               function symbol, ~x2, supports the formula of the defaxiom ~
               event named ~x3.  See :DOC evaluator-restrictions."
              rule-type
              name
              (if ev-prop ev ev-lst)
              (or ev-prop ev-lst-prop)))
         ((intersectp-eq ev-fns meta-anc)

; As explained in defaxiom-supporters, we might expect also to check here that
; ev and ev-lst are not ancestral in extra-fns.  But extra-fns are defined in
; the boot-strap world while ev and ev-lst, as we check above, are not.

; It would be nice to improve the following error message by finding the
; particular function symbol in the meta or clause-processor rule for which ev
; is ancestral.

          (er soft ctx ; see comment in defaxiom-supporters
              "The proposed ~x0 rule, ~x1, is illegal because its ~
               evaluator~#2~[~/ (list)~] function symbol, ~x3, supports the ~
               definition of the rule's metafunction~#4~[~/s~], ~&4.  See ~
               :DOC evaluator-restrictions."
              rule-type
              name
              (if (member-eq ev meta-anc) 0 1)
              (if (member-eq ev meta-anc) ev ev-lst)
              meta-fn-lst))
         (t

; We would like to be able to use attachments where possible.  However, the
; example at the end of :doc evaluator-restrictions shows that this is unsound
; in general and is followed by other relevant remarks.

          (let ((bad-attached-fns-1
                 (attached-fns (intersection-eq ev-anc meta-anc) wrld))
                (bad-attached-fns-2

; Although we need bad-attached-fns-2 to be empty (see the Essay on Correctness
; of Meta Reasoning), we could at the very least store extra-anc in the world,
; based on both meta-extract-contextual-fact and meta-extract-global-fact,
; so that we don't have to compute extra-anc every time.  But that check is
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
       (case-match term
         (('implies hyp
                    (eqv (ev x a) (ev (fn x) a)))
          (mv hyp eqv ev x a fn nil))
         ((eqv (ev x a) (ev (fn x) a))
          (mv *t* eqv ev x a fn nil))
         (('implies hyp
                    (eqv (ev x a)
                         (ev (fn x mfc-symbol 'STATE)
                             a)))
          (mv hyp eqv ev x a fn mfc-symbol))
         ((eqv (ev x a)
               (ev (fn x mfc-symbol 'STATE)
                   a))
          (mv *t* eqv ev x a fn mfc-symbol))
         (& (mv *t* nil nil nil nil nil nil)))
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
        (t (add-meta-rule1 (cdr lst) rule
                           (putprop (car lst)
                                    'lemmas
                                    (cons rule
                                          (getprop (car lst)
                                                   'lemmas nil
                                                   'current-acl2-world wrld))
                                    wrld)))))

(defun maybe-putprop-lst (symb-lst key val wrld)
  (cond ((endp symb-lst)
         wrld)
        (t (let ((symb (car symb-lst)))
             (maybe-putprop-lst
              (cdr symb-lst) key val
              (cond ((getprop symb key nil 'current-acl2-world wrld)
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
            (let ((old-prop (getprop (car fns)
                                     'attachment
                                     nil
                                     'current-acl2-world
                                     wrld)))
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

(defun add-meta-rule (rune nume trigger-fns term backchain-limit wrld)
  (mv-let
   (hyp eqv ev x a fn mfc-symbol)
   (case-match term
     (('implies hyp
                (eqv (ev x a) (ev (fn x) a)))
      (mv hyp eqv ev x a fn nil))
     ((eqv (ev x a) (ev (fn x) a))
      (mv *t* eqv ev x a fn nil))
     (('implies hyp
                (eqv (ev x a)
                     (ev (fn x mfc-symbol 'STATE)
                         a)))
      (mv hyp eqv ev x a fn mfc-symbol))
     ((eqv (ev x a)
           (ev (fn x mfc-symbol 'STATE)
               a))
      (mv *t* eqv ev x a fn mfc-symbol))
     (& (mv *t* nil nil nil nil nil nil)))
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
                            :heuristic-info nil
                            :backchain-limit-lst backchain-limit)
                      (mark-attachment-disallowed
                       (if (eq hyp-fn t)
                           (list fn)
                         (list hyp-fn fn))
                       ev
                       (msg "it supports both evaluator and meta functions ~
                             used in :META rule ~x0"
                            (base-symbol rune))
                       wrld)))))))

;---------------------------------------------------------------------------
; Section:  Destructor :ELIM Rules

(deflabel elim
  :doc
  ":Doc-Section Rule-Classes

  make a destructor elimination rule~/

  ~l[rule-classes] for a general discussion of rule classes and how they are
  used to build rules from formulas.  Here we describe the class of ~c[:elim]
  rules, which is fundamentally quite different from the more common class of
  ~c[:]~ilc[rewrite] rules.  Briefly put, a ~c[:rewrite] rule replaces
  instances of its left-hand side with corresponding instances of its
  right-hand side.  But an ~c[:elim] rule, on the other hand, has the effect of
  generalizing so-called ``destructor'' function applications to variables.  In
  essence, applicability of a ~c[:rewrite] rule is based on matching its
  left-hand side, while applicability of an ~c[:elim] rule is based on the
  presence of at least one destructor term.

  For example, a conjecture about ~c[(car x)] and ~c[(cdr x)] can be replaced
  by a conjecture about new variables ~c[x1] and ~c[x2], as shown in the
  following example.  (Run the command ~c[:mini-proveall] and search for
  ~c[CAR-CDR-ELIM] to see the full proof containing this excerpt.)
  ~bv[]
  Subgoal *1/1'
  (IMPLIES (AND (CONSP X)
                (TRUE-LISTP (REV (CDR X))))
           (TRUE-LISTP (APP (REV (CDR X)) (LIST (CAR X))))).

  The destructor terms (CAR X) and (CDR X) can be eliminated by using
  CAR-CDR-ELIM to replace X by (CONS X1 X2), (CAR X) by X1 and (CDR X)
  by X2.  This produces the following goal.

  Subgoal *1/1''
  (IMPLIES (AND (CONSP (CONS X1 X2))
                (TRUE-LISTP (REV X2)))
           (TRUE-LISTP (APP (REV X2) (LIST X1)))).

  This simplifies, using primitive type reasoning, to

  Subgoal *1/1'''
  (IMPLIES (TRUE-LISTP (REV X2))
           (TRUE-LISTP (APP (REV X2) (LIST X1)))).
  ~ev[]
  The resulting conjecture is often simpler and hence more amenable to proof.

  The application of an ~c[:elim] rule thus replaces a variable by a term that
  contains applications of so-called ``destructor'' functions to that variable.
  The example above is typical: the variable ~c[x] is replaced by the term
  ~c[(cons (car x) (cdr x))], which applies a so-called ``constructor''
  function, ~ilc[cons], to applications ~c[(car x)] and ~c[(cdr x)] of
  destructor functions ~ilc[car] and ~ilc[cdr] to that same variable, ~c[x].
  But that is only part of the story.  ACL2 then generalizes the destructor
  applications ~c[(car x)] and ~c[(cdr x)] to new variables ~c[x1] and ~c[x2],
  respectively, and ultimately the result is a simpler conjecture.

  More generally, the application of an ~c[:elim] rule replaces a variable by a
  term containing applications of destructors; there need not be a clear-cut
  notion of ``constructor.''  But the situation described above is typical, and
  we will focus on it, giving full details when we introduce the ``General
  Form'' below.

  The example above employs the following built-in ~c[:elim] rule named
  ~c[car-cdr-elim].
  ~bv[]
  Example:
  (implies (consp x)                      when (car v) or (cdr v) appears
           (equal (cons (car x) (cdr x))  in a conjecture, and v is a
                  x))                     variable, consider replacing v by
                                          (cons a b), for two new variables
                                          a and b.
  ~ev[]
  Notice that the situation is complicated a bit by the fact that this
  replacement is only valid if the variable being replaced a cons structure.
  Thus, when ACL2 applies ~c[car-cdr-elim] to replace a variable ~c[v], it will
  split into two cases: one case in which ~c[(consp v)] is true, in which ~c[v]
  is replaced by ~c[(cons (car v) (cdr v))] and then ~c[(car v)] and
  ~c[(cdr v)] are generalized to new variables; and one case in which
  ~c[(consp v)] is false.  In practice, ~c[(consp v)] is often provable,
  perhaps even literally present as a hypotheses; then of course there is no
  need to introduce the second case.  That is why there is no such second case
  in the example above.

  You might find ~c[:elim] rules to be useful whenever you have in mind a data
  type that can be built up from its fields with a ``constructor'' function and
  whose fields can be accessed by corresponding ``destructor'' functions.  So
  for example, if you have a ``house'' data structure that represents a house
  in terms of its address, price, and color, you might have a rule like the
  following.
  ~bv[]
  Example:
  (implies (house-p x)
           (equal (make-house (address x)
                              (price x)
                              (color x))
                  x))
  ~ev[]
  The application of such a rule is entirely analogous to the application of
  the rule ~c[car-cdr-elim] discussed above.  We discuss such rules and their
  application more carefully below.~/

  ~bv[]
  General Form:
  (implies hyp (equiv lhs x))
  ~ev[]
  where ~c[equiv] is a known equivalence relation (~pl[defequiv]); ~c[x]
  is a variable symbol; and ~c[lhs] contains one or more terms (called
  ``destructor terms'') of the form ~c[(fn v1 ... vn)], where ~c[fn] is
  a function symbol and the ~c[vi] are distinct variable symbols,
  ~c[v1], ..., ~c[vn] include all the variable symbols in the formula,
  no ~c[fn] occurs in ~c[lhs] in more than one destructor term, and all
  occurrences of ~c[x] in ~c[lhs] are inside destructor terms.

  To use an ~c[:elim] rule, the theorem prover waits until a conjecture has
  been maximally simplified.  It then searches for an instance of some
  destructor term ~c[(fn v1 ... vn)] in the conjecture, where the instance for
  ~c[x] is some variable symbol, ~c[vi], and every occurrence of ~c[vi] outside
  the destructor terms is in an ~c[equiv]-hittable position.  If such an
  instance is found, then the theorem prover instantiates the ~c[:elim] formula
  as indicated by the destructor term matched; splits the conjecture into two
  goals, according to whether the instantiated hypothesis, ~c[hyp], holds; and
  in the case that it does hold, generalizes all the instantiated destructor
  terms in the conjecture to new variables and then replaces ~c[vi] in the
  conjecture by the generalized instantiated ~c[lhs].  An occurrence of ~c[vi]
  is ``~c[equiv]-hittable'' if sufficient congruence rules (~pl[defcong]) have
  been proved to establish that the propositional value of the clause is not
  altered by replacing that occurrence of ~c[vi] by some ~c[equiv]-equivalent
  term.

  If an ~c[:elim] rule is not applied when you think it should have been,
  and the rule uses an equivalence relation, ~c[equiv], other than ~c[equal],
  it is most likely that there is an occurrence of the variable that is not
  ~c[equiv]-hittable.  Easy occurrences to overlook are those in
  the governing hypotheses.  If you see an unjustified occurrence of the
  variable, you must prove the appropriate congruence rule to allow the
  ~c[:elim] to fire.

  Further examples of how ACL2 ~c[:elim] rules are used may be found in the
  corresponding discussion of ``Elimation of Destructors'' for Nqthm, in
  Section 10.4 of A Computational Logic Handbook.")

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
   ((getprop (ffn-symb (car dests)) 'eliminate-destructors-rule nil
             'current-acl2-world wrld)
    (er soft ctx
        "~x0 is an unacceptable destructor elimination rule because ~
         we already have a destructor elimination rule for ~x1, ~
         namely ~x2, and we do not support more than one elimination rule ~
         for the same function symbol."
        name
        (ffn-symb (car dests))
        (getprop (ffn-symb (car dests)) 'eliminate-destructors-rule nil
                 'current-acl2-world wrld)))
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

(deflabel generalize
  :doc
  ":Doc-Section Rule-Classes

  make a rule to restrict generalizations~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  An example
  ~c[:]~ilc[corollary] formula from which a ~c[:generalize] rule might be built is:
  ~bv[]
  Example:
  any theorem~/

  General Form:
  any theorem
  ~ev[]
  To use such a ~c[:generalize] rule, the system waits until it has
  decided to generalize some term, ~c[term], by replacing it with some new
  variable ~c[v].  If any ~c[:generalize] formula can be instantiated so that
  some non-variable subterm becomes ~c[term], then that instance of the
  formula is added as a hypothesis.

  At the moment, the best description of how ACL2 ~c[:generalize] rules
  are used may be found in the discussion of ``Generalize Rules,'' page
  248 of A Computational Logic Handbook, or ``Generalization,'' page
  132 of ``Computer-Aided Reasoning: An Approach.''  Also
  ~pl[introduction-to-the-theorem-prover] for detailed tutorial on using ACL2
  to prove theorems, which includes some discussion of generalization.")

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

(deflabel type-prescription
  :doc
  ":Doc-Section Rule-Classes

  make a rule that specifies the type of a term~/

  ~l[rule-classes] for a general discussion of rule classes and how they are
  used to build rules from formulas.  Some example ~c[:]~ilc[corollary]
  formulas from which ~c[:type-prescription] rules might be built are:
  ~bv[]
  Examples:
  (implies                           (nth n lst) is of type characterp
   (and (character-listp lst)        provided the two hypotheses can
        (< n (length lst)))          be established by type reasoning
   (characterp (nth n lst))).

  (implies                           (demodulize a lst 'value ans) is
   (and (atom a)                     either a nonnegative integer or
        (true-listp lst)             of the same type as ans, provided
        (member-equal a lst))        the hyps can be established by type
   (or (and                          reasoning
         (integerp
          (demodulize a lst 'value ans))
         (>= (demodulize a lst 'value ans) 0))
       (equal (demodulize a lst 'value ans) ans))).
  ~ev[]
  To specify the term whose type (~pl[type-set]) is described by the rule,
  provide that term as the value of the ~c[:typed-term] field of the rule class
  object.~/
  ~bv[]
  General Form (after preprocessing; see below):
  (implies hyps
           (or type-restriction1-on-pat
               ...
               type-restrictionk-on-pat
               (equal pat var1)
               ...
               (equal pat varj)))
  ~ev[]
  where ~c[pat] is the application of some function symbol to some arguments,
  each ~c[type-restrictioni-on-pat] is a term involving ~c[pat] and containing
  no variables outside of the occurrences of ~c[pat], and each ~c[vari] is one
  of the variables of ~c[pat].  Generally speaking, the ~c[type-restriction]
  terms ought to be terms that inform us as to the type of ~c[pat].  Ideally,
  they should be ``primitive recognizing expressions'' about ~c[pat];
  ~pl[compound-recognizer].  We describe preprocessing at the end of this
   topic.

  If the ~c[:typed-term] is not provided in the rule class object, it is
  computed heuristically by looking for a term in the conclusion whose type is
  being restricted.  An error is caused if no such term is found.

  Roughly speaking, the effect of adding such a rule is to inform the ACL2
  typing mechanism that ~c[pat] has the type described by the conclusion, when
  the hypotheses are true.  In particular, the type of ~c[pat] is within the
  union of the types described by the several disjuncts.  The ``type described
  by'' ~c[(equal pat vari)] is the type of ~c[vari].

  More operationally, when asked to determine the type of a term that is an
  instance of ~c[pat], ACL2 will first attempt to establish the hypotheses.
  ~st[This is done by type reasoning alone, not rewriting!]  However, if some
  hypothesis is a call of ~ilc[force], then forcing may occur, which may
  ultimately invoke the rewriter; ~pl[force] and ~pl[case-split].  So-called
  free variables in hypotheses are treated specially; ~pl[free-variables].
  Provided the hypotheses are established by type reasoning, ACL2 then unions
  the types described by the ~c[type-restrictioni-on-pat] terms together with
  the types of those subexpressions of ~c[pat] identified by the ~c[vari].  The
  final type computed for a term is the intersection of the types implied by
  each applicable rule.  Type prescription rules may be disabled.

  You can limit the recursive establishment of hypotheses of rules;
  ~pl[set-backchain-limit].

  Because only type reasoning is used to establish the hypotheses of
  ~c[:type-prescription] rules, some care must be taken with the hypotheses.
  Suppose, for example, that the non-recursive function ~c[my-statep] is
  defined as
  ~bv[]
    (defun my-statep (x)
      (and (true-listp x)
           (equal (length x) 2)))
  ~ev[]
  and suppose ~c[(my-statep s)] occurs as a hypothesis of a
  ~c[:type-prescription] rule that is being considered for use in the proof
  attempt for a conjecture with the hypothesis ~c[(my-statep s)].  Since the
  hypothesis in the conjecture is rewritten, it will become the conjunction of
  ~c[(true-listp s)] and ~c[(equal (length s) 2)].  Those two terms will be
  assumed to have type ~c[t] in the context in which the ~c[:type-prescription]
  rule is tried.  But type reasoning will be unable to deduce that
  ~c[(my-statep s)] has type ~c[t] in this context.  Thus, either ~c[my-statep]
  should be disabled (~pl[disable]) during the proof attempt or else the
  occurrence of ~c[(my-statep s)] in the ~c[:type-prescription] rule should be
  replaced by the conjunction into which it rewrites.

  While this example makes it clear how non-recursive predicates can cause
  problems, non-recursive functions in general can cause problems.  For
  example, if ~c[(mitigate x)] is defined to be ~c[(if (rationalp x) (1- x) x)]
  then the hypothesis ~c[(pred (mitigate s))] in the conjecture will rewrite,
  opening ~c[mitigate] and splitting the conjecture into two subgoals, one in
  which ~c[(rationalp s)] and ~c[(pred (1- x))] are assumed and the other in
  which ~c[(not (rationalp s))] and ~c[(pred x)] are assumed.  But
  ~c[(pred (mitigate s))] will not be typed as ~c[t] in either of these
  contexts.  The moral is: beware of non-recursive functions occuring in the
  hypotheses of ~c[:type-prescription] rules.

  Because of the freedom one has in forming the conclusion of a
  type-prescription, we have to use heuristics to recover the pattern, ~c[pat],
  whose type is being specified.  In some cases our heuristics may not identify
  the intended term and the ~c[:type-prescription] rule will be rejected as
  illegal because the conclusion is not of the correct form.  When this happens
  you may wish to specify the ~c[pat] directly.  This may be done by using a
  suitable rule class token.  In particular, when the token
  ~c[:type-prescription] is used it means ACL2 is to compute pat with its
  heuristics; otherwise the token should be of the form
  ~c[(:type-prescription :typed-term pat)], where ~c[pat] is the term whose
  type is being specified.

  The defun event may generate a ~c[:type-prescription] rule.  Suppose ~c[fn]
  is the name of the function concerned.  Then ~c[(:type-prescription fn)] is
  the rune given to the type-prescription, if any, generated for ~c[fn] by
  ~ilc[defun].  (The trivial rule, saying ~c[fn] has unknown type, is not
  stored, but ~ilc[defun] still allocates the rune and the corollary of this
  rune is known to be ~c[t].)

  We close with a discussion of how, before a term is parsed into a
  ~c[:type-prescription] rule, it is preprocessed.  We describe this
  preprocessing in some detail below, but first consider the following
  (contrived) example.
  ~bv[]
  (defthm append-tp-example
    (let ((result (append x y)))
      (implies (nat-listp x)
               (implies (let ((second-hyp (integer-listp y)))
                          second-hyp)
                        (true-listp result))))
    :rule-classes :type-prescription)
  ~ev[]
  This theorem is parsed into a type-prescription rule with the following
  hypotheses and conclusion.
  ~bv[]
  (nat-listp x) ; first hypothesis
  ((lambda (second-hyp) second-hyp) (integer-listp y)) ; second hypothesis
  (true-listp (binary-append x y)) ; conclusion
  ~ev[]
  Notice that the top-level ~ilc[LET] was expanded, i.e., ~c[(append x y)] was
  substituted for ~c[result] ~-[] more accurately, ~c[(binary-append x y)] was
  substituted for ~c[result], since ~ilc[append] is a macro that abbreviates
  ~ilc[binary-append].  Also notice that the two hypotheses were ``flattened''
  in the sense that they were gathered up into a list.  Finally, notice that
  the ~ilc[LET] in the second hypothesis was not expanded (it was merely
  translated to internal form, using ~c[LAMBDA]).  If you actually submit the
  theorem above, you will get warnings, which you may choose to ignore; the
  application of ~c[type-prescription] rules is somewhat subtle, so if you use
  them then you may wish to experiment to see which forms work best for you.

  Here is the detail promised above, for parsing a term into a
  ~c[:type-prescription] rule.  There are two steps.  (1) ACL2 first translates
  the term, expanding all macros (~pl[trans]) and also expanding away calls of
  all so-called ``guard holders,'' ~ilc[mv-list] and ~ilc[return-last] (the
  latter resulting for example from calls of ~ilc[prog2$], ~ilc[mbe], or
  ~ilc[ec-call]), as well as expansions of the macro `~ilc[the]'.  (2) Then the
  the translated term is traversed top-down, expanding away ~c[lambda]s
  (~ilc[let], ~ilc[let*], and ~ilc[mv-let] expressions) and flattening the
  ~ilc[IMPLIES] structure, until the conclusion is exposed; then the
  conclusion's ~c[lambda]s are also expanded away.  The simplest way to
  understand (2) may be to look at the definition of ACL2 source function
  ~c[unprettyify-tp], which implements Step (2), say by evaluating
  ~c[:]~ilc[pe]~c[ unprettyify-tp].~/")

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
        ((most-recent-enabled-recog-tuple (ffn-symb term)
                                          (global-val 'recognizer-alist wrld)
                                          ens)
         (fargn term 1))
        (t term)))

(defun type-prescription-disjunctp (var term)

; Warning: Keep this function in sync with
; subst-nil-into-type-prescription-disjunct.

; Var is a variable and term is a term.  Essentially we are answering
; the question, ``is term a legal disjunct in the conclusion of a
; type-prescription about pat'' for some term pat.  However, by this
; time all occurrences of the candidate pat in the conclusion have
; been replaced by some new variable symbol and that symbol is var.
; Furthermore, we will have already checked that the resulting
; generalized concl contains no variables other than var and the
; variables occurring in pat.  So what this function actually checks
; is that term is either (equal var other-var), (equal other-var var),
; or else is some arbitrary term whose all-vars is identically the
; singleton list containing var.

; If term is one of the two equality forms above, then we know
; other-var is a variable in pat and that term is one of the disjuncts
; that says ``pat sometimes returns this part of its input.''  If term
; is of the third form, then it might have come from a
; type-restriction on pat, e.g., (and (rationalp pat) (<= pat 0)) or
; (compound-recognizerp pat), or it might be some pretty arbitrary
; term.  However, we at least know that it contains no variables at
; all outside the occurrences of pat and that means that we can trust
; type-set-implied-by-term to tell us what this term implies about
; pat.

  (cond ((variablep term)

; This could be a type-prescription disjunct in the generalized concl
; only if term is var, i.e., the original disjunct was equivalent to
; (not (equal pat 'nil)).

         (eq term var))
        ((fquotep term) nil)
        ((flambda-applicationp term) nil)
        (t (or (and (eq (ffn-symb term) 'equal)
                    (or (and (eq var (fargn term 1))
                             (variablep (fargn term 2))
                             (not (eq (fargn term 1) (fargn term 2))))
                        (and (eq var (fargn term 2))
                             (variablep (fargn term 1))
                             (not (eq (fargn term 2) (fargn term 1))))))
               (equal (all-vars term) (list var))))))

(defun type-prescription-conclp (var concl)

; Warning: Keep this function in sync with
; subst-nil-into-type-prescription-concl.

; Var is a variable and concl is a term.  We recognize those concl
; that are the macroexpansion of (or t1 ... tk) where every ti is a
; type-prescription-disjunctp about var.

; In the grand scheme of things, concl was obtained from the
; conclusion of an alleged :TYPE-PRESCRIPTION lemma about some term,
; pat, by replacing all occurrences of pat with some new variable,
; var.  We also know that concl involves no variables other than var
; and those that occurred in pat.

  (cond ((variablep concl) (type-prescription-disjunctp var concl))
        ((fquotep concl) nil)
        ((flambda-applicationp concl) nil)
        ((eq (ffn-symb concl) 'if)
         (cond ((equal (fargn concl 1) (fargn concl 2))
                (and (type-prescription-disjunctp var (fargn concl 1))
                     (type-prescription-conclp var (fargn concl 3))))
               (t (type-prescription-disjunctp var concl))))
        (t (type-prescription-disjunctp var concl))))

(defun subst-nil-into-type-prescription-disjunct (var term)

; Warning:  Keep this function in sync with type-prescription-disjunctp.

; We assume var and term are ok'd by type-prescription-disjunctp.
; If term is of the form (equal var other-var) or (equal other-var var)
; we replace it by nil, otherwise we leave it alone.

  (cond ((variablep term) term)

; The next two cases never happen, but we leave them in just to make
; sure we copy term modulo this substitution.

        ((fquotep term) term)
        ((flambda-applicationp term) term)
        ((and (eq (ffn-symb term) 'equal)
              (or (and (eq var (fargn term 1))
                       (variablep (fargn term 2))
                       (not (eq (fargn term 1) (fargn term 2))))
                  (and (eq var (fargn term 2))
                       (variablep (fargn term 1))
                       (not (eq (fargn term 2) (fargn term 1))))))
         *nil*)
        (t term)))

(defun subst-nil-into-type-prescription-concl (var concl)

; Warning:  Keep this function in sync with type-prescription-conclp.

; We know that var and concl are ok'd by type-prescription-conclp.  So
; concl is a disjunction of terms, some of which are of the form
; (equal var other-var).  We replace each of those disjuncts in concl
; with nil so as to produce that part of concl that is a disjunct of
; type restrictions.  That is, if our answer is basic-term and vars is
; the list of all the other-vars in concl, then concl is equivalent to
; basic-term disjoined with the equality between var and each variable
; in vars.

  (cond
   ((variablep concl) (subst-nil-into-type-prescription-disjunct var concl))

; The next two cases never happen.

   ((fquotep concl) concl)
   ((flambda-applicationp concl) concl)
   ((eq (ffn-symb concl) 'if)
    (cond ((equal (fargn concl 1) (fargn concl 2))
           (let ((temp (subst-nil-into-type-prescription-disjunct var
                                                                  (fargn concl 1))))
             (fcons-term* 'if
                          temp
                          temp
                          (subst-nil-into-type-prescription-concl var
                                                                  (fargn concl 3)))))
          (t (subst-nil-into-type-prescription-disjunct var concl))))
   (t (subst-nil-into-type-prescription-disjunct var concl))))

(defun unprettyify-tp (term)

; This variant of unprettyify avoids giviing special treatment to conjunctions,
; and hence is suitable for parsing terms into type-prescription rules.  Unlike
; unprettyify, it returns (mv hyps concl).

  (case-match term
    (('implies t1 t2)
     (mv-let (hyps concl)
             (unprettyify-tp t2)
             (mv (append? (flatten-ands-in-lit t1)
                          hyps)
                 concl)))
    ((('lambda vars body) . args)
     (unprettyify-tp (subcor-var vars args body)))
    (& (mv nil (remove-lambdas term)))))

(defun destructure-type-prescription (name typed-term term ens wrld)

; Warning: Keep this in sync with the :BACKCHAIN-LIMIT-LST case of
; translate-rule-class-alist.

; Note: This function does more than "destructure" term into a
; :TYPE-PRESCRIPTION rule, it checks a lot of conditions too and
; computes type-sets.  However, it doesn't actually cause errors --
; note that state is not among its arguments -- but may return an
; error message suitable for printing with ~@.  We return many
; results.  The first is nil or an error message.  The rest are
; relevant only if the first is nil and are described below.  We code
; this way because the destructuring and checking are inextricably
; intertwined and when we destructure in order to add the rule, we do
; not have state around.

; We determine whether term is a suitable :TYPE-PRESCRIPTION lemma
; about the term typed-term.  Term is suitable as a :TYPE-
; PRESCRIPTION lemma about typed-term if the conclusion of term,
; concl, is a disjunction of type-prescription disjuncts about
; typed-term.  Each disjunct must either be an equality between
; typed-term and one of the variables occurring in typed-term, or else
; must be some term, such as (and (rationalp typed-term) (<=
; typed-term 0)) or (compound-recognizerp typed-term), that mentions
; typed-term and contains no variables outside those occurrences of
; typed-term.

; If term is unsuitable we return an error msg and nils.  Otherwise we
; return nil and four more things: the list of hyps, a basic type
; set, a list of variables, and a ttree.  In that case, term implies
; that when hyps are true, the type-set of typed-term is the union of the
; basic type-set together with the type-sets of the variables listed.
; The ttree records our dependencies on compound recognizers or other
; type-set lemmas in wrld.  The ttree returned contains no 'assumption
; tags.

  (let ((term (remove-guard-holders term)))
    (mv-let
     (hyps concl)
     (unprettyify-tp term)
     (cond
      ((or (variablep typed-term)
           (fquotep typed-term)
           (flambda-applicationp typed-term))
       (mv (msg "The :TYPED-TERM, ~x0, provided in the :TYPE-PRESCRIPTION ~
                 rule class for ~x1 is illegal because it is a variable, ~
                 constant, or lambda application.  See :DOC type-prescription."
                typed-term name)
           nil nil nil nil nil))
      ((dumb-occur-lst typed-term hyps)
       (mv (msg "The :TYPED-TERM, ~x0, of the proposed :TYPE-PRESCRIPTION ~
                 rule ~x1 occurs in the hypotheses of the rule.  This would ~
                 cause ``infinite backchaining'' if we permitted ~x1 as a ~
                 :TYPE-PRESCRIPTION.  (Don't feel reassured by this check:  ~
                 infinite backchaining may occur anyway since it can be ~
                 caused by the combination of several rules.)"
                typed-term
                name)
           nil nil nil nil nil))
      (t
       (let ((all-vars-typed-term (all-vars typed-term))
             (all-vars-concl (all-vars concl)))
         (cond
          ((not (subsetp-eq all-vars-concl all-vars-typed-term))
           (mv (msg "~x0 cannot be used as a :TYPE-PRESCRIPTION rule as ~
                     described by the given rule class because the ~
                     :TYPED-TERM, ~x1, does not contain the ~#2~[variable ~&2 ~
                     which is~/variables ~&2 which are~] mentioned in the ~
                     conclusion.  See :DOC type-prescription."
                    name
                    typed-term
                    (set-difference-eq all-vars-concl all-vars-typed-term))
               nil nil nil nil nil))
          (t (let* ((new-var (genvar (find-pkg-witness typed-term)
                                     "TYPED-TERM" nil all-vars-typed-term))
                    (concl1 (subst-expr new-var typed-term concl)))
               (cond
                ((not (type-prescription-conclp new-var concl1))
                 (mv (msg "~x0 is an illegal :TYPE-PRESCRIPTION lemma of the ~
                           class indicated because its conclusion is not a ~
                           disjunction of type restrictions about the ~
                           :TYPED-TERM ~x1.  See :DOC type-prescription."
                          name typed-term)
                     nil nil nil nil nil))
                (t (let ((vars (remove1-eq new-var (all-vars concl1)))
                         (basic-term
                          (subst-nil-into-type-prescription-concl new-var concl1)))

; Once upon a time, briefly, we got the type-set implied by (and hyps
; basic-term), thinking that we might need hyps to extract type
; information from basic-term.  But the only var in basic-term is new
; so the hyps don't help much.  The idea was to permit lemmas like
; (implies (rationalp x) (<= 0 (* x x))).  Note that the guard for <=
; is satisfied only if we know that the product is rational, which we
; can deduce from the hyp.  But when we try to process that lemma, the
; typed-term in generalized away, e.g., (implies (rationalp x) (<= 0
; Z)).  Thus, the hyps don't help: the only var in basic-term is
; new-var.  You could conjoin hyps and concl1 and THEN generalize the
; typed-term to new-var, thereby linking the occurrences of typed-term
; in the hyps to those in the concl.  But this is very unhelpful
; because it encourages the creation of lemmas that contain the
; typed-term in the hyps.  That is bad because type-set then
; infinitely backchains.  In the face of these difficulties, we have
; reverted back to the simplest treatment of type-prescription lemmas.

                     (mv-let
                      (ts ttree)
                      (type-set-implied-by-term new-var nil basic-term ens wrld
                                                nil)
                      (cond ((ts= ts *ts-unknown*)
                             (mv (msg "~x0 is a useless :TYPE-PRESCRIPTION ~
                                       lemma because we can deduce no type ~
                                       restriction about its :TYPED-TERM ~
                                       (below represented by ~x1) from the ~
                                       generalized conclusion, ~p2.  See :DOC ~
                                       type-prescription."
                                      name
                                      new-var
                                      (untranslate concl1 t wrld))
                                 nil nil nil nil nil))
                            ((not (assumption-free-ttreep ttree))

; If type-set-implied-by-term requires that we force some assumptions,
; it is not clear what to do.  For example, it is possible that the
; assumptions involve new-var, which makes no sense in the context of
; an application of this rule.  My intuition tells me this error will
; never arise because for legal concls, basic-term is guard free.  If
; there are :TYPE-PRESCRIPTION lemmas about the compound recognizers
; in it, they could have forced hyps.  I think it unlikely, since the
; recognizers are Boolean.  Well, I guess I could add a
; :TYPE-PRESCRIPTION lemma that said that under some forced hyp the
; compound-recognizer was actually t.  In that case, the forced hyp
; would necessarily involve new-var, since that is the only argument
; to a compound recognizer.  It would be interesting to see a living
; example of this situation.

                             (mv
                              (if (tagged-objectsp 'fc-derivation ttree)
                                  (er hard
                                      "Somehow an 'fc-derivation, ~x0, has ~
                                       found its way into the ttree returned ~
                                       by type-set-implied-by-term."
                                      (car (tagged-objects 'fc-derivation
                                                           ttree)))
                                (msg "~x0 is an illegal :TYPE-PRESCRIPTION ~
                                      lemma because in determining the ~
                                      type-set implied for its :TYPED-TERM, ~
                                      ~x1, by its conclusion the ~
                                      ~#2~[assumption ~&2 was~/assumptions ~
                                      ~&2 were~] and our :TYPE-PRESCRIPTION ~
                                      preprocessor, ~
                                      CHK-ACCEPTABLE-TYPE-PRESCRIPTION-RULE, ~
                                      does not know how to handle this ~
                                      supposedly unusual situation.  It would ~
                                      be very helpful to report this error to ~
                                      the authors."
                                     name typed-term
                                     (tagged-objects 'assumption ttree)))
                              nil nil nil nil nil))
                            (t (mv nil hyps concl ts vars ttree))))))))))))))))

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
;   ACL2 !>(car (getprop 'my-equal 'type-prescriptions t 'current-acl2-world (w state)))
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
                    (getprop (ffn-symb typed-term)
                             'type-prescriptions
                             nil
                             'current-acl2-world
                             wrld))
              wrld)))))

(defun strong-compound-recognizer-p (fn recognizer-alist ens)
  (cond ((endp recognizer-alist) nil)
        ((let ((recog-tuple (car recognizer-alist)))
           (and (eq fn (access recognizer-tuple recog-tuple :fn))
                (access recognizer-tuple recog-tuple :strongp)
                (enabled-numep (access recognizer-tuple recog-tuple :nume)
                               ens)))
         t)
        (t (strong-compound-recognizer-p fn (cdr recognizer-alist) ens))))

(defun warned-non-rec-fns-for-tp (term recognizer-alist ens wrld)
  (cond ((or (variablep term)
             (fquotep term))
         nil)
        ((flambdap (ffn-symb term))
         (cons (ffn-symb term)
               (non-recursive-fnnames-lst (fargs term) ens wrld)))
        ((eq (ffn-symb term) 'if)

; Type-set and assume-true-false explore the top-level IF structure in such a
; way that NOT and strong compound recognizers aren't problems.

         (union-equal
          (warned-non-rec-fns-for-tp
           (fargn term 1) recognizer-alist ens wrld)
          (union-equal
           (warned-non-rec-fns-for-tp
            (fargn term 2) recognizer-alist ens wrld)
           (warned-non-rec-fns-for-tp
            (fargn term 3) recognizer-alist ens wrld))))
        ((eq (ffn-symb term) 'not)
         (warned-non-rec-fns-for-tp (fargn term 1) recognizer-alist ens wrld))
        ((strong-compound-recognizer-p (ffn-symb term) recognizer-alist ens)
         (non-recursive-fnnames-lst (fargs term) ens wrld))
        (t (non-recursive-fnnames term ens wrld))))

(defun warned-non-rec-fns-tp-hyps1 (hyps recognizer-alist ens wrld acc)
  (cond ((endp hyps) acc)
        (t (warned-non-rec-fns-tp-hyps1
            (cdr hyps)
            recognizer-alist ens wrld
            (let ((hyp (if (and (nvariablep (car hyps))
;                               (not (fquotep (car hyps))) ; implied by:
                                (member-eq (ffn-symb (car hyps))
                                           '(force case-split)))
                           (fargn (car hyps) 1)
                         (car hyps))))
              (cond (acc (union-equal (warned-non-rec-fns-for-tp
                                       hyp recognizer-alist ens wrld)
                                      acc))
                    (t (warned-non-rec-fns-for-tp
                        hyp recognizer-alist ens wrld))))))))

(defun warned-non-rec-fns-tp-hyps (hyps ens wrld)
  (warned-non-rec-fns-tp-hyps1 hyps
                               (global-val 'recognizer-alist wrld)
                               ens wrld nil))

(defun chk-acceptable-type-prescription-rule (name typed-term term
                                                   backchain-limit-lst
                                                   ctx ens wrld state)

; Like all individual rule checkers, we either cause an error or
; return a ttree that records our dependencies on lemmas.

  (mv-let
   (erp hyps concl ts vars ttree)
   (destructure-type-prescription name typed-term term ens wrld)
   (declare (ignore ts vars))
   (cond
    (erp (er soft ctx "~@0" erp))
    (t (let* ((weakp

; We avoid calling weak-type-prescription-rulep if we are going to ignore the
; warning anyhow.  Otherwise, we construct a temporary world using 

               (and (not (warning-disabled-p "Type prescription"))
                    (let* ((nume (get-next-nume wrld))
                           (rune (list :type-prescription name))
                           (wrld2 (add-type-prescription-rule
                                   rune nume typed-term term
                                   backchain-limit-lst
                                   ens wrld nil)))
                      (mv-let
                       (ts ttree)
                       (type-set term nil t nil ens wrld2 nil nil nil)
                       (or (not (assumption-free-ttreep ttree))
                           (ts-intersectp ts *ts-nil*)))))))
         (pprogn
          (cond
           (weakp
            (warning$ ctx ("Type prescription")
                      "The :type-prescription rule generated for ~x0 may be ~
                       weaker than you expect.  Note that the conclusion of a ~
                       :type-prescription rule is stored as a type rather ~
                       than a term.  It so happens that~|  ~p1~|is not ~
                       provable using type-set reasoning in the extension of ~
                       the current world by that rule.  Because information ~
                       has been lost, this rule probably does not have the ~
                       strength that it appears to have.~@2"
                      name
                      (untranslate term t wrld)
                      (if (ffnnamep '< concl)
                          "  The conclusion of this rule contains a call of ~
                           function symbol < (or a macro <=, >, or >=), so it ~
                           may be worth considering making a :linear rule; ~
                           see :DOC linear."
                        "")))
           (t state))
          (let* ((warned-non-rec-fns
                  (and (not (warning-disabled-p "Non-rec"))
                       (warned-non-rec-fns-tp-hyps hyps ens wrld)))
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
              (warned-non-rec-fns
               (warning$ ctx ("Non-rec")
                         "The hypothesis of the :type-prescription rule ~
                          generated from ~x0 contains the non-recursive ~
                          function symbol~#1~[~/s~] ~&1.  Since the ~
                          hypotheses of :type-prescription rules are relieved ~
                          by type reasoning alone (and not rewriting) ~
                          ~#1~[this function is~/these functions are~] liable ~
                          to make the rule inapplicable.  See :DOC ~
                          type-prescription."
                         name (hide-lambdas warned-non-rec-fns)))
              (t state))
             (cond
              (warned-free-vars
               (warning$ ctx ("Free")
                         "The :type-prescription rule generated from ~x0 ~
                          contains the free variable~#1~[ ~&1.  This ~
                          variable~/s ~&1.  These variables~] will be chosen ~
                          by searching for instances of ~&2 among the ~
                          hypotheses of conjectures being rewritten.  This is ~
                          generally a severe restriction on the applicability ~
                          of the :type-prescription rule."
                         name warned-free-vars inst-hyps))
              (t state))
             (cond
              ((and warned-free-vars
                    (forced-hyps inst-hyps))
               (warning$ ctx ("Free")
                         "For the forced ~#0~[hypothesis~/hypotheses~], ~&1, ~
                          used to instantiate free variables we will search ~
                          for ~#0~[an instance of the argument~/instances of ~
                          the arguments~] rather than ~#0~[an ~
                          instance~/instances~] of the FORCE or CASE-SPLIT ~
                          ~#0~[term itself~/terms themselves~].  If a search ~
                          fails for such a hypothesis, we will cause a case ~
                          split on the partially instantiated hypothesis.  ~
                          Note that this case split will introduce a ``free ~
                          variable'' into the conjecture.  While sound, this ~
                          will establish a goal almost certain to fail since ~
                          the restriction described by this apparently ~
                          necessary hypothesis constrains a variable not ~
                          involved in the problem.  To highlight this oddity, ~
                          we will rename the free variables in such forced ~
                          hypotheses by prefixing them with ~
                          ``UNBOUND-FREE-''.  This is not guaranteed to ~
                          generate a new variable but at least it generates ~
                          an unusual one.  If you see such a variable in a ~
                          subsequent proof (and did not introduce them ~
                          yourself) you should consider the possibility that ~
                          the free variables of this type-prescription rule ~
                          were forced into the conjecture."
                         (if (null (cdr (forced-hyps inst-hyps))) 0 1)
                         (forced-hyps inst-hyps)))
              (t state))
             (value ttree)))))))))

;---------------------------------------------------------------------------
; Section:  :EQUIVALENCE Rules

(deflabel equivalence
  :doc
  ":Doc-Section Rule-Classes

  mark a relation as an equivalence relation~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  An example
  ~c[:]~ilc[corollary] formula from which a ~c[:equivalence] rule might be built is
  as follows.  (We assume that ~c[r-equal] has been defined.)
  ~bv[]
  Example:
  (and (booleanp (r-equal x y))
       (r-equal x x)
       (implies (r-equal x y) (r-equal y x))
       (implies (and (r-equal x y)
                     (r-equal y z))
                (r-equal x z))).
  ~ev[]
  Also ~pl[defequiv].~/
  ~bv[]
  General Form:
  (and (booleanp (equiv x y))
       (equiv x x)
       (implies (equiv x y) (equiv y x))
       (implies (and (equiv x y)
                     (equiv y z))
                (equiv x z)))
  ~ev[]
  except that the order of the conjuncts and terms and the choice of
  variable symbols is unimportant.  The effect of such a rule is to
  identify ~c[equiv] as an equivalence relation.  Note that only Boolean
  2-place function symbols can be treated as equivalence relations.
  ~l[congruence] and ~pl[refinement] for closely related
  concepts.

  The macro form ~c[(defequiv equiv)] is an abbreviation for a ~ilc[defthm] of
  rule-class ~c[:equivalence] that establishes that ~c[equiv] is an
  equivalence relation.  It generates the formula shown above.
  ~l[defequiv].

  When ~c[equiv] is marked as an equivalence relation, its reflexivity,
  symmetry, and transitivity are built into the system in a deeper way
  than via ~c[:]~ilc[rewrite] rules.  More importantly, after ~c[equiv] has been
  shown to be an equivalence relation, lemmas about ~c[equiv], e.g.,
  ~bv[]
  (implies hyps (equiv lhs rhs)),
  ~ev[]
  when stored as ~c[:]~ilc[rewrite] rules, cause the system to rewrite certain
  occurrences of (instances of) ~c[lhs] to (instances of) ~c[rhs].  Roughly
  speaking, an occurrence of ~c[lhs] in the ~c[kth] argument of some
  ~c[fn]-expression, ~c[(fn ... lhs' ...)], can be rewritten to produce
  ~c[(fn ...  rhs' ...)], provided the system ``knows'' that the value
  of ~c[fn] is unaffected by ~c[equiv]-substitution in the ~c[kth]
  argument.  Such knowledge is communicated to the system via
  ``congruence lemmas.''

  For example, suppose that ~c[r-equal] is known to be an equivalence
  relation.  The ~c[:]~ilc[congruence] lemma
  ~bv[]
  (implies (r-equal s1 s2)
           (equal (fn s1 n) (fn s2 n)))
  ~ev[]
  informs the rewriter that, while rewriting the first argument of
  ~c[fn]-expressions, it is permitted to use ~c[r-equal] rewrite-rules.
  ~l[congruence] for details about ~c[:]~ilc[congruence] lemmas.
  Interestingly, congruence lemmas are automatically created when an
  equivalence relation is stored, saying that either of the
  equivalence relation's arguments may be replaced by an equivalent
  argument.  That is, if the equivalence relation is ~c[fn], we store
  congruence rules that state the following fact:
  ~bv[]
  (implies (and (fn x1 y1)
                (fn x2 y2))
           (iff (fn x1 x2) (fn y1 y2)))
  ~ev[]
  Another aspect of equivalence relations is that of ``refinement.''
  We say ~c[equiv1] ``refines'' ~c[equiv2] iff ~c[(equiv1 x y)] implies
  ~c[(equiv2 x y)].  ~c[:]~ilc[refinement] rules permit you to establish such
  connections between your equivalence relations.  The value of
  refinements is that if the system is trying to rewrite something
  while maintaining ~c[equiv2] it is permitted to use as a ~c[:]~ilc[rewrite]
  rule any refinement of ~c[equiv2].  Thus, if ~c[equiv1] is a
  refinement of ~c[equiv2] and there are ~c[equiv1] rewrite-rules
  available, they can be brought to bear while maintaining ~c[equiv2].
  ~l[refinement].

  The system initially has knowledge of two equivalence relations,
  equality, denoted by the symbol ~ilc[equal], and propositional
  equivalence, denoted by ~ilc[iff].  ~ilc[Equal] is known to be a refinement of
  all equivalence relations and to preserve equality across all
  arguments of all functions.

  Typically there are five steps involved in introducing and using a
  new equivalence relation, equiv.~bq[]

  (1) Define ~c[equiv],

  (2) prove the ~c[:equivalence] lemma about ~c[equiv],

  (3) prove the ~c[:]~ilc[congruence] lemmas that show where ~c[equiv] can be used
  to maintain known relations,

  (4) prove the ~c[:]~ilc[refinement] lemmas that relate ~c[equiv] to known
  relations other than equal, and

  (5) develop the theory of conditional ~c[:]~ilc[rewrite] rules that drive
  equiv rewriting.

  ~eq[]More will be written about this as we develop the techniques.  For
  now, here is an example that shows how to make use of equivalence
  relations in rewriting.

  Among the theorems proved below is
  ~bv[]
  (defthm insert-sort-is-id 
    (perm (insert-sort x) x))
  ~ev[]
  Here ~c[perm] is defined as usual with ~c[delete] and is proved to be an
  equivalence relation and to be a congruence relation for ~ilc[cons] and
  ~ilc[member].

  Then we prove the lemma
  ~bv[]
  (defthm insert-is-cons
    (perm (insert a x) (cons a x)))
  ~ev[]
  which you must think of as you would ~c[(insert a x) = (cons a x)].

  Now prove ~c[(perm (insert-sort x) x)].  The base case is trivial.  The
  induction step is
  ~bv[]
     (consp x)
   & (perm (insert-sort (cdr x)) (cdr x))

  -> (perm (insert-sort x) x).
  ~ev[]
  Opening ~c[insert-sort] makes the conclusion be
  ~bv[]
     (perm (insert (car x) (insert-sort (cdr x))) x).
  ~ev[]
  Then apply the induction hypothesis (rewriting ~c[(insert-sort (cdr x))]
  to ~c[(cdr x)]), to make the conclusion be
  ~bv[]
  (perm (insert (car x) (cdr x)) x)
  ~ev[]
  Then apply ~c[insert-is-cons] to get ~c[(perm (cons (car x) (cdr x)) x)].
  But we know that ~c[(cons (car x) (cdr x))] is ~c[x], so we get ~c[(perm x x)]
  which is trivial, since ~c[perm] is an equivalence relation.

  Here are the events.
  ~bv[]
  (encapsulate (((lt * *) => *))
    (local (defun lt (x y) (declare (ignore x y)) nil))
    (defthm lt-non-symmetric (implies (lt x y) (not (lt y x)))))

  (defun insert (x lst)
    (cond ((atom lst) (list x))
          ((lt x (car lst)) (cons x lst))
          (t (cons (car lst) (insert x (cdr lst))))))

  (defun insert-sort (lst)
    (cond ((atom lst) nil)
          (t (insert (car lst) (insert-sort (cdr lst))))))

  (defun del (x lst)
    (cond ((atom lst) nil)
          ((equal x (car lst)) (cdr lst))
          (t (cons (car lst) (del x (cdr lst))))))

  (defun mem (x lst)
    (cond ((atom lst) nil)
          ((equal x (car lst)) t)
          (t (mem x (cdr lst)))))

  (defun perm (lst1 lst2)
    (cond ((atom lst1) (atom lst2))
          ((mem (car lst1) lst2)
           (perm (cdr lst1) (del (car lst1) lst2)))
          (t nil)))

  (defthm perm-reflexive
    (perm x x))

  (defthm perm-cons
    (implies (mem a x)
             (equal (perm x (cons a y))
                    (perm (del a x) y)))
    :hints ((\"Goal\" :induct (perm x y))))

  (defthm perm-symmetric
    (implies (perm x y) (perm y x)))

  (defthm mem-del
    (implies (mem a (del b x)) (mem a x)))

  (defthm perm-mem
    (implies (and (perm x y)
                  (mem a x))
             (mem a y)))

  (defthm mem-del2
    (implies (and (mem a x)
                  (not (equal a b)))
             (mem a (del b x))))

  (defthm comm-del
    (equal (del a (del b x)) (del b (del a x))))

  (defthm perm-del
    (implies (perm x y)
             (perm (del a x) (del a y))))

  (defthm perm-transitive
    (implies (and (perm x y) (perm y z)) (perm x z)))

  (defequiv perm)

  (in-theory (disable perm
                      perm-reflexive
                      perm-symmetric
                      perm-transitive))

  (defcong perm perm (cons x y) 2)

  (defcong perm iff (mem x y) 2)

  (defthm atom-perm
    (implies (not (consp x)) (perm x nil))
    :rule-classes :forward-chaining
    :hints ((\"Goal\" :in-theory (enable perm))))

  (defthm insert-is-cons
    (perm (insert a x) (cons a x)))

  (defthm insert-sort-is-id 
    (perm (insert-sort x) x))

  (defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))

  (defun rev (x)
    (if (consp x) (app (rev (cdr x)) (list (car x))) nil))

  (defcong perm perm (app x y) 2)

  (defthm app-cons
    (perm (app a (cons b c)) (cons b (app a c))))

  (defthm app-commutes
    (perm (app a b) (app b a)))

  (defcong perm perm (app x y) 1
    :hints ((\"Goal\" :induct (app y x))))

  (defthm rev-is-id (perm (rev x) x))

  (defun == (x y)
    (if (consp x)
        (if (consp y)
            (and (equal (car x) (car y))
                 (== (cdr x) (cdr y)))
            nil)
        (not (consp y))))

  (defthm ==-reflexive (== x x))

  (defthm ==-symmetric (implies (== x y) (== y x)))

  (defequiv ==)

  (in-theory (disable ==-symmetric ==-reflexive))

  (defcong == == (cons x y) 2)

  (defcong == iff (consp x) 1)

  (defcong == == (app x y) 2)

  (defcong == == (app x y) 1)

  (defthm rev-rev (== (rev (rev x)) x))
  ~ev[]~/")

; For a rule to acceptable as an :EQUIVALENCE rule, it must state the
; Boolean-ness, reflexivity, symmetry, and transitivity of a 2-place
; function symbol.  We make the user type in the desired formula and
; then check that he typed a suitable one.  This way we can define a
; simple macro that generates a suitable defthm event (rather than
; have to produce a new event type with all the prove-level hint
; passing mechanism).  To check that the formula is suitable we
; generate a cannonical formula and check that the given one subsumes
; it.  To add an :EQUIVALENCE rule we add a 'coarsenings property to
; the function symbol and also set up an initial 'congruences property
; for it.

; Some of the simple functions below anticipate the day we allow n-ary
; equivalences (n>2) but don't be fooled into thinking we allow it
; today!

(defun boolean-fn (fn)

; The name boolean is not usable for definitions in Allegro, because
; it's in the COMMON-LISP package.  So, we'd better not use that name
; here.

  `(booleanp (,fn x y)))

(defun reflexivity (fn)

; In this function we expect fn to have arity 2.

  `(,fn x x))

(defun symmetry (fn)

; This function expects fn to have arity 2.

  `(implies (,fn x y)
            (,fn y x)))

(defun transitivity (fn)

; This function expects fn to have arity 2.

  `(implies (and (,fn x y)
                 (,fn y z))
            (,fn x z)))

(defun equivalence-relation-condition (fn)

; This function expects fn to have arity 2.  We generate a formula that states
; that fn is Boolean, reflexive, symmetric, and transitive.

; There are at least two reasons we require equivalence relations to be
; Boolean.  One is to simplify assume-true-false.  When we assume (fn x y)
; true, we pair it with *ts-t* rather than its full type-set take away
; *ts-nil*.  The other is that from reflexivity and Boolean we get than fn is
; commutative and so can freely use (fn y x) for (fn x y).  If we did not have
; the Boolean condition we would have to be more careful about, say,
; commutative unification.

  `(and ,(boolean-fn fn)
        ,(reflexivity fn)
        ,(symmetry fn)
        ,(transitivity fn)))

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
         ((eqv-cond (translate (equivalence-relation-condition fn)
                               t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)

         (let ((eqv-clauses (shallow-clausify eqv-cond)))

; In the first test below we open-code a call of equivalence-relationp,
; avoiding special treatment for iff since we want (defequiv iff) to succeed
; during initialization.

           (cond
            ((or (eq fn 'equal)
                 (and (not (flambdap fn))
                      (getprop fn 'coarsenings nil 'current-acl2-world wrld)))
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
                            (getprop fn 'lemmas nil 'current-acl2-world wrld)))))
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
                            for the :EQUIVALENCE lemma ~x0 for funcction ~
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
              (append (getprop 'equal 'coarsenings nil
                               'current-acl2-world wrld)
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
                             (getprop fn 'congruences nil
                                      'current-acl2-world
                                      wrld))
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

(deflabel refinement
  :doc
  ":Doc-Section Rule-Classes

  record that one equivalence relation refines another~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  An example
  ~c[:]~ilc[corollary] formula from which a ~c[:refinement] rule might be built is:
  ~bv[]
  Example:
  (implies (bag-equal x y) (set-equal y x)).
  ~ev[]
  Also ~pl[defrefinement].~/
  ~bv[]
  General Form:
  (implies (equiv1 x y) (equiv2 x y))
  ~ev[]
  ~c[Equiv1] and ~c[equiv2] must be known equivalence relations.  The effect
  of such a rule is to record that ~c[equiv1] is a refinement of ~c[equiv2].
  This means that ~c[equiv1] ~c[:]~ilc[rewrite] rules may be used while trying to
  maintain ~c[equiv2].  ~l[equivalence] for a general discussion of
  the issues.

  The macro form ~c[(defrefinement equiv1 equiv2)] is an abbreviation for
  a ~ilc[defthm] of rule-class ~c[:refinement] that establishes that ~c[equiv1] is a
  refinement of ~c[equiv2].  ~l[defrefinement].

  Suppose we have the ~c[:]~ilc[rewrite] rule
  ~bv[]
  (bag-equal (append a b) (append b a))
  ~ev[]
  which states that ~ilc[append] is commutative modulo bag-equality.
  Suppose further we have established that bag-equality refines
  set-equality.  Then when we are simplifying ~ilc[append] expressions while
  maintaining set-equality we use ~ilc[append]'s commutativity property,
  even though it was proved for bag-equality.

  Equality is known to be a refinement of all equivalence relations.
  The transitive closure of the refinement relation is maintained, so
  if ~c[set-equality], say, is shown to be a refinement of some third
  sense of equivalence, then ~c[bag-equality] will automatially be known
  as a refinement of that third equivalence.

  ~c[:refinement] lemmas cannot be disabled.  That is, once one
  equivalence relation has been shown to be a refinement of another,
  there is no way to prevent the system from using that information.
  Of course, individual ~c[:]~ilc[rewrite] rules can be disabled.

  More will be written about this as we develop the techniques.")

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

  (let ((all-equivs (getprop 'equal 'coarsenings nil
                             'current-acl2-world wrld)))
    (pairlis$ all-equivs
              (getprop-x-lst all-equivs 'coarsenings wrld))))

(defun putprop-coarsenings (alist wrld)

; Alist pairs equiv relations with their new 'coarsenings property.
; Put each property, provided it is different from its current value
; in wrld.

  (cond ((null alist) wrld)
        ((equal (getprop (caar alist) 'coarsenings nil
                         'current-acl2-world wrld)
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
                    (append (getprop equiv1 'coarsenings nil
                                     'current-acl2-world wrld)
                            (list equiv2))
                    (collect-coarsenings wrld)))
     wrld)))

;---------------------------------------------------------------------------
; Section:  :CONGRUENCE Rules

(deflabel congruence
  :doc
  ":Doc-Section Rule-Classes

  the relations to maintain while simplifying arguments~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.  An example
  ~c[:]~ilc[corollary] formula from which a ~c[:congruence] rule might be built is:
  ~bv[]
  Example:
  (implies (set-equal x y)
           (iff (memb e x) (memb e y))).
  ~ev[]
  Also ~pl[defcong] and ~pl[equivalence].~/
  ~bv[]
  General Form:
  (implies (equiv1 xk xk-equiv)
           (equiv2 (fn x1... xk       ...xn)
                   (fn x1... xk-equiv ...xn)))
  ~ev[]
  where ~c[equiv1] and ~c[equiv2] are known equivalence relations, ~c[fn] is an
  ~c[n-ary] function symbol and the ~c[xi] and ~c[xk-equiv] are all distinct
  variables.  The effect of such a rule is to record that the
  ~c[equiv2]-equivalence of ~c[fn]-expressions can be maintained if, while
  rewriting the ~c[kth] argument position, ~c[equiv1]-equivalence is
  maintained.  ~l[equivalence] for a general discussion of the
  issues.  We say that ~c[equiv2], above, is the ``outside equivalence''
  in the rule and ~c[equiv1] is the ``inside equivalence for the ~c[k]th
  argument''

  The macro form ~c[(defcong equiv1 equiv2 (fn x1 ... x1) k)] is an
  abbreviation for a ~ilc[defthm] of rule-class ~c[:congruence] that attempts to
  establish that ~c[equiv2] is maintained by maintaining ~c[equiv1] in ~c[fn]'s
  ~c[k]th argument.  The ~ilc[defcong] macro automatically generates the general
  formula shown above.  ~l[defcong].

  The ~c[memb] example above tells us that ~c[(memb e x)] is propositionally
  equivalent to ~c[(memb e y)], provided ~c[x] and ~c[y] are ~c[set-equal].  The
  outside equivalence is ~ilc[iff] and the inside equivalence for the second
  argument is ~c[set-equal].  If we see a ~c[memb] expression in a
  propositional context, e.g., as a literal of a clause or test of an
  ~ilc[if] (but not, for example, as an argument to ~ilc[cons]), we can rewrite
  its second argument maintaining ~c[set-equality].  For example, a rule
  stating the commutativity of ~ilc[append] (modulo set-equality) could be
  applied in this context.  Since equality is a refinement of all
  equivalence relations, all equality rules are always available.
  ~l[refinement].

  All known ~c[:congruence] rules about a given outside equivalence and ~c[fn]
  can be used independently.  That is, consider two ~c[:congruence] rules
  with the same outside equivalence, ~c[equiv], and about the same
  function ~c[fn].  Suppose one says that ~c[equiv1] is the inside equivalence
  for the first argument and the other says ~c[equiv2] is the inside
  equivalence for the second argument.  Then ~c[(fn a b)] is ~c[equiv]
  ~c[(fn a' b')] provided ~c[a] is ~c[equiv1] to ~c[a'] and ~c[b] is ~c[equiv2]
  to ~c[b'].  This is an easy consequence of the transitivity of
  ~c[equiv].  It permits you to think independently about the inside
  equivalences.

  Furthermore, it is possible that more than one inside equivalence
  for a given argument slot will maintain a given outside equivalence.
  For example, ~c[(length a)] is equal to ~c[(length a')] if ~c[a] and ~c[a'] are
  related either by ~c[list-equal] or by ~ilc[string-equal].  You may prove two
  (or more) ~c[:congruence] rules for the same slot of a function.  The
  result is that the system uses a new, ``generated'' equivalence
  relation for that slot with the result that rules of both (or all)
  kinds are available while rewriting.

  ~c[:Congruence] rules can be disabled.  For example, if you have two
  different inside equivalences for a given argument position and you
  find that the ~c[:]~ilc[rewrite] rules for one are unexpectedly preventing the
  application of the desired rule, you can disable the rule that
  introduced the unwanted inside equivalence.

  ~em[Remark on Replacing IFF by EQUAL.] You may encounter a warning suggesting
  that a congruence rule ``can be strengthened by replacing the second
  equivalence relation, IFF, by EQUAL.''  Suppose for example that this warning
  occurs when you submit the following rule:

  ~bv[]
  (defcong equiv1 iff (fn x y) 2)
  ~ev[]
  which is shorthand for the following:
  ~bv[]
  (defthm equiv1-implies-iff-fn-2
         (implies (equiv1 y y-equiv)
                  (iff (fn x y) (fn x y-equiv)))
         :rule-classes (:congruence))
  ~ev[]
  The warning is telling you that ACL2 was able to deduce that ~c[fn] always
  returns a Boolean, and hence a trivial but useful consequence is obtained by
  replacing ~ilc[iff] by ~ilc[equal] ~-[]
  ~bv[]
  (defcong equiv1 equal (fn x y) 2)
  ~ev[]
  ~-[] which is shorthand for the following:
  ~bv[]
  (defthm equiv1-implies-equal-fn-2
         (implies (equiv1 y y-equiv)
                  (equal (fn x y) (fn x y-equiv)))
         :rule-classes (:congruence))
  ~ev[]
  If you have difficulty proving the latter directly, you can derive it from
  the former by giving a suitable hint, minimally as follows.
  ~bv[]
  (defcong equiv1 equal (fn x y) 2
    :hints ((\"Goal\"
             :use equiv1-implies-iff-fn-2
             :in-theory
             (union-theories '((:type-prescription fn))
                             (theory 'minimal-theory)))))
  ~ev[]
  By heeding this warning, you may avoid unnecessary ~ilc[double-rewrite]
  warnings later.  We now explain why, but ~pl[double-rewrite] for relevant
  background material.

  For example, suppose you have proved the ``~c[iff]'' version of the
  congruence rule above, and later you submit the following rewrite rule.
  ~bv[]
  (defthm equal-list-perm
    (implies (equiv1 x y)
             (fn x y)))
  ~ev[]
  Since ~c[fn] is known to return a Boolean, ACL2 performs an optimization that
  stores this rule as though it were the following.
  ~bv[]
  (defthm equal-list-perm
    (implies (equiv1 x y)
             (equal (fn x y) t)))
  ~ev[]
  Thus, if ACL2's rewriter sees a term ~c[(fn a b)] in a context where the
  equivalence relation ~ilc[iff] is not being maintained, then it cannot use
  rule ~c[equiv1-implies-iff-fn-2], so it rewrites argument ~c[a] without the
  benefit of knowing that it suffices to maintain ~c[equiv1]; and then it
  caches the result.  When ACL2 subsequently attempts to relieve the hypothesis
  ~c[(equiv1 x y)], it will rewrite ~c[x] simply by returning the rewritten
  value of ~c[a] from the result cache.  This is unfortunate if ~c[a] could
  have been rewritten more completely under maintainance of the equivalence
  relation ~c[equiv1] ~-[] which is legal in the hypothesis since ~c[a] is an
  argument of ~c[equiv1], which is an ~il[equivalence] relation.  The user who
  observes the warning from rule ~c[equiv1-implies-iff-fn-2], and replaces it
  with ~c[equiv1-implies-equal-fn-2], will avoid this unfortunate case.")

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

(defun interpret-term-as-congruence-rule (name term wrld)

; This function recognizes terms that are :CONGRUENCE lemmas.  We
; return two results.  The first is a flag that indicates whether or
; not the term is a :CONGRUENCE lemma.  If the term is a congruence
; lemma, the second result is a 4-tuple, (fn equiv1 k equiv2), which
; means term states that ``equiv2 is preserved by equiv1 in the kth
; argument of fn.''  If the term is not a :CONGRUENCE rule, the second
; is a tilde-@ message explaining why.  See the essay on equivalence,
; refinements, and congruence-based rewriting for details.

; :CONGRUENCE lemmas are of the form

; (implies (equiv1 xk yk)
;          (equiv2 (fn x1 ... xk ... xn) (fn x1 ... yk ... xn)))

; where fn is a function symbol, all the xi and yk are distinct
; variables and equiv1 and the equiv2 are equivalence relations.
; Such a lemma is read as ``equiv2 is preserved by equiv1 in the kth
; argument of fn.''

; We do not actually cause an error because this function is sometimes
; called when STATE is unavailable.  We combine the recognition of the
; :CONGRUENCE lemma with the construction of the 4-tuple describing it
; because the two are so intermingled that it seemed dubious to
; separate them into two functions.

  (let ((pairs (unprettyify (remove-guard-holders term)))
        (hyp-msg   "~x0 is an unacceptable :CONGRUENCE rule.  The ~
                    single hypothesis of a :CONGRUENCE rule must be a ~
                    term of the form (equiv x y), where equiv has ~
                    been proved to be an equivalence relation and x ~
                    and y are distinct variable symbols.  The ~
                    hypothesis of ~x0, ~x1, is not of this form.")

        (concl-msg "~x0 is an unacceptable :CONGRUENCE rule.  The ~
                    conclusion of an acceptable rule must be of the ~
                    form (equiv (fn x1 ... xk ... xn) (fn x1 ... yk ~
                    ... xn)) where equiv has been proved to be an ~
                    equivalence relation, fn is a function symbol, ~
                    the xi are distinct variable symbols, xk is ~x1, ~
                    yk is ~x2, and ~x2 does not occur among the xi.  ~
                    The conclusion of ~x0, ~x3, is not of this form."))
    (cond
     ((and (int= (length pairs) 1)
           (int= (length (caar pairs)) 1))
      (let ((hyp (caaar pairs))
            (concl (cdar pairs)))
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
               ((and (equivalence-relationp equiv2 wrld)
                     (symbolp fn)
                     (all-variablep args1)
                     (no-duplicatesp-equal args1)
                     (member-eq xk args1)
                     (corresponding-args-eq-except args1 args2 xk yk))
                (mv t (list fn equiv1
                            (1+ (- (length args1) (length (member-eq xk args1))))
                            equiv2)))
               (t (mv nil (msg concl-msg name xk yk concl)))))
             (& (mv nil (msg concl-msg name xk yk concl)))))
           (t (mv nil (msg hyp-msg name hyp)))))
         (& (mv nil (msg hyp-msg name hyp))))))
     (t (mv nil (msg "~x0 is an unacceptable :CONGRUENCE rule.  When ~
                      an acceptable :CONGRUENCE rule is ~
                      propositionally flattened, only one conjunct is ~
                      produced and it is of the form (implies (equiv1 ~
                      xk yk) (equiv2 (fn ... xk ...) (fn ... yk ~
                      ...))), where equiv1 and equiv2 are equivalence ~
                      relations.  ~x0 is not of this form."
                     name))))))

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

; We check that term is of the form
; (implies (equiv1 xk yk)
;          (equiv2 (fn ... xk ...) (fn ... yk ...)))

; We print a warning message if we already know that equiv2 is
; preserved by equiv1 in the kth slot of fn.  We are not so much
; watching out for the possibility that equiv1 literally occurs in the
; list in the kth slot -- though that could happen and the old rule be
; disabled so the user is unaware that it exists.  We are more
; concerned about the possibility that equiv1 is some refinement of a
; relation already in the kth slot.

  (mv-let
   (flg x)
   (interpret-term-as-congruence-rule name term wrld)
   (cond
    ((not flg) (er soft ctx "~@0" x))
    (t (let ((fn (car x))
             (equiv1 (cadr x))
             (k (caddr x))
             (equiv2 (cadddr x)))
         (let ((temp (nth k
                          (assoc-eq equiv2
                                    (getprop fn 'congruences nil
                                             'current-acl2-world wrld)))))
           (cond
            ((some-congruence-rule-same equiv1 temp)
             (er soft ctx
                 "The previously added :CONGRUENCE lemma, ~x0, ~
                  establishes that ~x1 preserves ~x2 in the ~n3 slot ~
                  of ~x4.  Thus, ~x5 is unnecessary."
                 (base-symbol
                  (access congruence-rule
                          (some-congruence-rule-same equiv1 temp)
                          :rune))
                 equiv1 equiv2 (cons k 'th) fn name))
            ((some-congruence-rule-has-refinement equiv1 temp wrld)
             (er soft ctx
                 "The previously added :CONGRUENCE lemma, ~x0, ~
                  establishes that ~x1 preserves ~x2 in the ~n3 slot ~
                  of ~x4.  But we know that ~x5 is a refinement of ~
                  ~x1.  Thus, ~x6 is unnecessary."
                 (base-symbol
                  (access congruence-rule
                          (some-congruence-rule-has-refinement equiv1 temp wrld)
                          :rune))
                 (access congruence-rule
                         (some-congruence-rule-has-refinement equiv1 temp wrld)
                         :equiv)
                 equiv2 (cons k 'th) fn equiv1 name))
            (t (pprogn
                (cond ((eq equiv1 'equal)
                       (warning$ ctx "Equiv"
                                 "The :CONGRUENCE rule ~x0 will have no effect ~
                                  on proofs because ACL2 already knows that ~
                                  ~x1 refines every equivalence relation, ~
                                  including ~x2."
                                 name 'equal equiv2))
                      ((and (eq equiv2 'iff)
                            (mv-let
                             (ts ttree)
                             (type-set (cons-term fn (formals fn wrld))
                                       nil nil nil (ens state) wrld
                                       nil nil nil)
                             (declare (ignore ttree))
                             (ts-subsetp ts *ts-boolean*)))
                       (warning$ ctx "Equiv"
                                 "The :CONGRUENCE rule ~x0 can be ~
                                  strengthened by replacing the second ~
                                  equivalence relation, ~x1, by ~x2.  See ~
                                  :DOC congruence, in particular (near the ~
                                  end) the Remark on Replacing IFF by EQUAL."
                                 name 'iff 'equal))
                      (t state))
                (value nil))))))))))

(defun putnth (val n lst)
  (declare (xargs :guard (and (true-listp lst)
                              (integerp n)
                              (<= 0 n))))
  (cond ((int= n 0) (cons val (cdr lst)))
        (t (cons (car lst) (putnth val (1- n) (cdr lst))))))

(defun add-congruence-rule-to-congruence (rule k congruence)

; Congruence is an element of the 'congruence property of some n-ary
; function fn.  As such, it is of the form (equiv geneqv1 ... geneqvk
; ... geneqvn), where equiv is some equivalence relation and each of
; the geneqvi is a list of congruence-rule records.  We add rule to
; geneqvk.

  (putnth (cons rule (nth k congruence)) k congruence))

(defun add-congruence-rule (rune nume term wrld)

; Suppose term states that equiv2 is preserved by equiv1 in the kth
; argument of fn.  Then we add a new :CONGRUENCE rule to the
; 'congruences property of fn recording this fact.  The new rule is
; added as the first rule tried for the kth argument of fn while
; maintaining equiv2.  In addition, the entry for equiv2 is moved to
; the front of the list of congruences for fn so that when we rewrite
; fn maintaining some equiv3, where equiv2 is a refinement of equiv3,
; we will try equiv2 first.  This idea of moving the equiv2 entry to
; the front is not motivated by any example -- this code has not yet
; seen action -- it is just the first-cut design.

  (mv-let (flg x)
          (interpret-term-as-congruence-rule (base-symbol rune) term wrld)
          (declare (ignore flg))
          (let ((fn (car x))
                (equiv1 (cadr x))
                (k (caddr x))
                (equiv2 (cadddr x)))
            (let* ((temp (assoc-eq equiv2
                                   (getprop fn 'congruences nil
                                            'current-acl2-world wrld)))
                   (equiv2-congruence
                    (or temp
                        (cons equiv2 (make-list-ac (arity fn wrld) nil nil))))
                   (rst (if temp
                            (remove1-equal temp
                                           (getprop fn 'congruences nil
                                                    'current-acl2-world wrld))
                            (getprop fn 'congruences nil 'current-acl2-world wrld))))
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
                       wrld)))))

;---------------------------------------------------------------------------
; Section:  :DEFINITION rules

(deflabel definition
  :doc
  ":Doc-Section Rule-Classes

  make a rule that acts like a function definition~/

  ~l[rule-classes] for a general discussion of rule classes and how they are
  used to build rules from formulas.  An example ~c[:]~ilc[corollary] formula
  from which a ~c[:definition] rule might be built is:
  ~bv[]
  Example:
  (implies (true-listp x)
           (equal (len x)
                  (if (null x)
                      0
                      (if (null (cdr x))
                          1
                          (+ 2 (len (cddr x)))))))~/

  General Form:
  (implies hyp (equiv (fn a1 ... an) body))
  ~ev[]
  where ~c[equiv] is an equivalence relation and ~c[fn] is a function symbol
  other than ~ilc[if], ~ilc[hide], ~ilc[force] or ~ilc[case-split].  Such rules
  allow ``alternative'' definitions of ~c[fn] to be proved as theorems but used
  as definitions.  These rules are not true ``definitions'' in the sense that
  they (a) cannot introduce new function symbols and (b) do not have to be
  terminating recursion schemes.  They are just conditional rewrite rules that
  are controlled the same way we control recursive definitions.  We call these
  ``definition rules'' or ``generalized definitions''.

  Consider the general form above.  Generalized definitions are stored among
  the ~c[:]~ilc[rewrite] rules for the function ``defined,'' ~c[fn] above, but
  the procedure for applying them is a little different.  During rewriting,
  instances of ~c[(fn a1 ... an)] are replaced by corresponding instances of
  ~c[body] provided the ~c[hyp]s can be established as for a ~c[:]~ilc[rewrite]
  rule and the result of rewriting ~c[body] satisfies the criteria for function
  expansion.  There are two primary criteria, either of which permits
  expansion.  The first is that the ``recursive'' calls of ~c[fn] in the
  rewritten body have arguments that already occur in the goal conjecture.  The
  second is that the ``controlling'' arguments to ~c[fn] are simpler in the
  rewritten body.

  The notions of ``recursive call'' and ``controllers'' are complicated by the
  provisions for mutually recursive definitions.  Consider a ``clique'' of
  mutually recursive definitions.  Then a ``recursive call'' is a call to any
  function defined in the clique and an argument is a ``controller'' if it is
  involved in the measure that decreases in all recursive calls.  These notions
  are precisely defined by the definitional principle and do not necessarily
  make sense in the context of generalized definitional equations as
  implemented here.

  But because the heuristics governing the use of generalized definitions
  require these notions, it is generally up to the user to specify which calls
  in body are to be considered recursive and what the controlling arguments
  are.  This information is specified in the ~c[:clique] and
  ~c[:controller-alist] fields of the ~c[:definition] rule class.

  The ~c[:clique] field is the list of function symbols to be considered
  recursive calls of ~c[fn].  In the case of a non-recursive definition, the
  ~c[:clique] field is empty; in a singly recursive definition, it should
  consist of the singleton list containing ~c[fn]; otherwise it should be a
  list of all of the functions in the mutually recursive clique with this
  definition of ~c[fn].

  If the ~c[:clique] field is not provided it defaults to ~c[nil] if ~c[fn]
  does not occur as a function symbol in ~c[body] and it defaults to the
  singleton list containing ~c[fn] otherwise.  Thus, ~c[:clique] must be
  supplied by the user only when the generalized definition rule is to be
  treated as one of several in a mutually recursive clique.

  The ~c[:controller-alist] is an alist that maps each function symbol in the
  ~c[:clique] to a mask specifying which arguments are considered controllers.
  The mask for a given member of the clique, ~c[fn], must be a list of ~c[t]'s
  and ~c[nil]'s of length equal to the arity of ~c[fn].  A ~c[t] should be in
  each argument position that is considered a ``controller'' of the recursion.
  For a function admitted under the principle of definition, an argument
  controls the recursion if it is one of the arguments measured in the
  termination argument for the function.  But in generalized definition rules,
  the user is free to designate any subset of the arguments as controllers.
  Failure to choose wisely may result in the ``infinite expansion'' of
  definitional rules but cannot render ACL2 unsound since the rule being
  misused is a theorem.

  If the ~c[:controller-alist] is omitted it can sometimes be defaulted
  automatically by the system.  If the ~c[:clique] is ~c[nil], the
  ~c[:controller-alist] defaults to ~c[nil].  If the ~c[:clique] is a singleton
  containing ~c[fn], the ~c[:controller-alist] defaults to the controller alist
  computed by ~c[(defun fn args body)].  (The user can obtain some control over
  this analysis by setting the default ruler-extenders;
  ~pl[ruler-extenders].)  If the ~c[:clique] contains more than one function,
  the user must supply the ~c[:controller-alist] specifying the controllers for
  each function in the clique.  This is necessary since the system cannot
  determine and thus cannot analyze the other definitional equations to be
  included in the clique.

  For example, suppose ~c[fn1] and ~c[fn2] have been defined one way and it is
  desired to make ``alternative'' mutually recursive definitions available to
  the rewriter.  Then one would prove two theorems and store each as a
  ~c[:definition] rule.  These two theorems would exhibit equations
  ``defining'' ~c[fn1] and ~c[fn2] in terms of each other.  No provision is
  here made for exhibiting these two equations as a system of equations.  One
  is proved and then the other.  It just so happens that the user intends them
  to be treated as mutually recursive definitions.  To achieve this end, both
  ~c[:definition] rules should specify the ~c[:clique] ~c[(fn1 fn2)] and should
  specify a suitable ~c[:controller-alist].  If, for example, the new
  definition of ~c[fn1] is controlled by its first argument and the new
  definition of ~c[fn2] is controlled by its second and third (and they each
  take three arguments) then a suitable ~c[:controller-alist] would be
  ~c[((fn1 t nil nil) (fn2 nil t t))].  The order of the pairs in the alist is
  unimportant, but there must be a pair for each function in the clique.

  Inappropriate heuristic advice via ~c[:clique] and ~c[:controller-alist] can
  cause ``infinite expansion'' of generalized definitions, but cannot render
  ACL2 unsound.

  Note that the actual definition of ~c[fn1] has the runic name
  ~c[(:definition fn1)].  The runic name of the alternative definition is
  ~c[(:definition lemma)], where ~c[lemma] is the name given to the event that
  created the generalized ~c[:definition] rule.  This allows theories to switch
  between various ``definitions'' of the functions.

  By default, a ~c[:definition] rule establishes the so-called ``body'' of a
  function.  The body is used by ~c[:expand] ~il[hints], and it is also used
  heuristically by the theorem prover's preprocessing (the initial
  simplification using ``simple'' rules that is controlled by the
  ~c[preprocess] symbol in ~c[:do-not] ~il[hints]), induction analysis, and the
  determination for when to warn about non-recursive functions in rules.  The
  body is also used by some heuristics involving whether a function is
  recursively defined, and by the ~c[expand], ~c[x], and ~c[x-dumb] commands of
  the ~il[proof-checker].

  ~l[rule-classes] for a discussion of the optional field ~c[:install-body] of
  ~c[:definition] rules, which controls whether a ~c[:definition] rule is used
  as described in the paragraph above.  Note that even if ~c[:install-body nil]
  is supplied, the rewriter will still rewrite with the ~c[:definition] rule;
  in that case, ACL2 just won't install a new body for the top function symbol
  of the left-hand side of the rule, which for example affects the application
  of ~c[:expand] hints as described in the preceding paragraph.  Also
  ~pl[set-body] and ~pl[show-bodies] for how to change the body of a function
  symbol.

  Note only that if you prove a definition rule for function ~c[foo], say,
  ~c[foo-new-def], you will need to refer to that definition as ~c[foo-new-def]
  or as ~c[(:DEFINITION foo-new-def)].  That is because a ~c[:definition] rule
  does not change the meaning of the symbol ~c[foo] for ~c[:use] ~il[hints],
  nor does it change the meaning of the symbol ~c[foo] in theory expressions;
  ~pl[theories], in particular the discussion there of runic designators.
  Similarly ~c[:]~ilc[pe] ~c[foo] and ~c[:]~ilc[pf] ~c[foo] will still show the
  original definition of ~c[foo].

  The definitional principle, ~ilc[defun], actually adds ~c[:definition] rules.
  Thus the handling of generalized definitions is exactly the same as for
  ``real'' definitions because no distinction is made in the implementation.
  Suppose ~c[(fn x y)] is ~ilc[defun]'d to be ~c[body].  Note that ~ilc[defun]
  (or ~ilc[defuns] or ~ilc[mutual-recursion]) can compute the clique for ~c[fn]
  from the syntactic presentation and it can compute the controllers from the
  termination analysis.  Provided the definition is admissible, ~ilc[defun]
  adds the ~c[:definition] rule ~c[(equal (fn x y) body)].~/")

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
     ((member-eq fn *definition-minimal-theory*)

; This restriction is to allow us to assume that calls of (body fn t wrld),
; which occur in several places in the source code, refer to the original
; normalized body of fn, which excuses us from tracking the corresponding rune.

      (er soft ctx
          "~@0 the function symbol being called on the left-hand side, ~x1, ~
           must not be among the following built-in functions:  ~&2.~@3  ~
           Please contact the implementors if you feel that this is an ~
           encumbrance to you."
          er-preamble
          fn
          *definition-minimal-theory*
          install-body-msg))
     ((not (arglistp args))
      (er soft ctx
          "~@0 the arguments on the left-hand side of the rule must be a list ~
           of distinct variables, unlike ~x1.~@2  See :DOC definition."
          er-preamble
          args
          install-body-msg))
     ((not (eq equiv 'equal))
      (er soft ctx
          "~@0 the equivalence relation on the left-hand side of the rule ~
           must be ~x1, unlike ~x2.~@3  See :DOC definition."
          er-preamble
          'equal
          equiv
          install-body-msg))
     ((free-varsp-member-lst hyps args)
      (er soft ctx
          "~@0 the hypotheses must not contain free variables that are not ~
           among the variables on its left-hand side.  The ~#1~[variable ~&1 ~
           violates~/variables ~&1 violate~] this requirement.~@2  See :DOC ~
           definition."
          er-preamble
          (set-difference-eq (all-vars1-lst hyps nil) args)
          install-body-msg))
     ((free-varsp-member body args)
      (er soft ctx
          "~@0 the right-hand side of a :DEFINITION rule must not contain free ~
           variables that are not among the variables on its left-hand side.  ~
           The ~#1~[variable ~&1 violates~/variables ~&1 violate~] this ~
           requirement.~@2  See :DOC definition."
          er-preamble
          (set-difference-eq (all-vars body) args)
          install-body-msg))
     (t (value nil)))))

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
                  :hyps (preprocess-hyps hyps)
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

(deflabel induction
  :doc
  ":Doc-Section Rule-Classes

  make a rule that suggests a certain induction~/
  ~bv[]
  Example:
  (:induction :corollary t  ; the theorem proved is irrelevant!
              :pattern (* 1/2 i)
              :condition (and (integerp i) (>= i 0))
              :scheme (recursion-by-sub2 i))
  ~ev[]~/

  In ACL2, as in Nqthm, the functions in a conjecture ``suggest'' the
  inductions considered by the system.  Because every recursive
  function must be admitted with a justification in terms of a measure
  that decreases in a well-founded way on a given set of
  ``controlling'' arguments, every recursive function suggests a dual
  induction scheme that ``unwinds'' the function from a given
  application.

  For example, since ~ilc[append] (actually ~ilc[binary-append], but we'll ignore
  the distinction here) decomposes its first argument by successive
  ~ilc[cdr]s as long as it is a non-~c[nil] true list, the induction scheme
  suggested by ~c[(append x y)] has a base case supposing ~c[x] to be either
  not a true list or to be ~c[nil] and then has an induction step in which
  the induction hypothesis is obtained by replacing ~c[x] by ~c[(cdr x)].
  This substitution decreases the same measure used to justify the
  definition of ~ilc[append].  Observe that an induction scheme is suggested
  by a recursive function application only if the controlling actuals
  are distinct variables, a condition that is sufficient to ensure
  that the ``substitution'' used to create the induction hypothesis is
  indeed a substitution and that it drives down a certain measure.  In
  particular, ~c[(append (foo x) y)] does not suggest an induction
  unwinding ~ilc[append] because the induction scheme suggested by
  ~c[(append x y)] requires that we substitute ~c[(cdr x)] for ~c[x] and
  we cannot do that if ~c[x] is not a variable symbol.

  Once ACL2 has collected together all the suggested induction schemes
  it massages them in various ways, combining some to simultaneously
  unwind certain cliques of functions and vetoing others because they
  ``flaw'' others.  We do not further discuss the induction heuristics
  here; the interested reader should see Chapter XIV of A
  Computational Logic (Boyer and Moore, Academic Press, 1979) which
  represents a fairly complete description of the induction heuristics
  of ACL2.

  However, unlike Nqthm, ACL2 provides a means by which the user can
  elaborate the rules under which function applications suggest
  induction schemes.  Such rules are called ~c[:induction] rules.  The
  definitional principle automatically creates an ~c[:induction] rule,
  named ~c[(:induction fn)], for each admitted recursive function, ~c[fn].  It
  is this rule that links applications of ~c[fn] to the induction scheme
  it suggests.  Disabling ~c[(:induction fn)] will prevent ~c[fn] from
  suggesting the induction scheme derived from its recursive
  definition.  It is possible for the user to create additional
  ~c[:induction] rules by using the ~c[:induction] rule class in ~ilc[defthm].

  Technically we are ``overloading'' ~ilc[defthm] by using it in the
  creation of ~c[:induction] rules because no theorem need be proved to
  set up the heuristic link represented by an ~c[:induction] rule.
  However, since ~ilc[defthm] is generally used to create rules and
  rule-class objects are generally used to specify the exact form of
  each rule, we maintain that convention and introduce the notion of
  an ~c[:induction] rule.  An ~c[:induction] rule can be created from any
  lemma whatsoever.
  ~bv[]
  General Form of an :induction Lemma or Corollary:
  T

  General Form of an :induction rule-class:
  (:induction :pattern pat-term
              :condition cond-term
              :scheme scheme-term)
  ~ev[]
  where ~c[pat-term], ~c[cond-term], and ~c[scheme-term] are all terms, ~c[pat-term]
  is the application of a function symbol, ~c[fn], ~c[scheme-term] is the
  application of a function symbol, ~c[rec-fn], that suggests an
  induction, and, finally, every free variable of ~c[cond-term] and
  ~c[scheme-term] is a free variable of ~c[pat-term].  We actually check that
  ~c[rec-fn] is either recursively defined ~-[] so that it suggests the
  induction that is intrinsic to its recursion ~-[] or else that another
  ~c[:induction] rule has been proved linking a call of ~c[rec-fn] as the
  ~c[:pattern] to some scheme.

  The induction rule created is used as follows.  When an instance of
  the ~c[:pattern] term occurs in a conjecture to be proved by induction
  and the corresponding instance of the ~c[:condition] term is known to be
  non-~c[nil] (by type reasoning alone), the corresponding instance of the
  ~c[:scheme] term is created and the rule ``suggests'' the induction, if
  any, suggested by that term.  (Analysis of that term may further involve
  induction rules, though the applied rule is removed from consideration during
  that further analysis, in order to avoid looping.)  If ~c[rec-fn] is
  recursive, then the suggestion is the one that unwinds that recursion.

  Consider, for example, the example given above,
  ~bv[]
  (:induction :pattern (* 1/2 i)
              :condition (and (integerp i) (>= i 0))
              :scheme (recursion-by-sub2 i)).
  ~ev[]
  In this example, we imagine that ~c[recursion-by-sub2] is the
  function:
  ~bv[]
  (defun recursion-by-sub2 (i)
    (if (and (integerp i)
             (< 1 i))
        (recursion-by-sub2 (- i 2))
        t))
  ~ev[]
  Observe that this function recursively decomposes its integer
  argument by subtracting ~c[2] from it repeatedly and stops when the
  argument is ~c[1] or less.  The value of the function is irrelevant; it
  is its induction scheme that concerns us.  The induction scheme
  suggested by ~c[(recursion-by-sub2 i)] is
  ~bv[]
  (and (implies (not (and (integerp i) (< 1 i)))   ; base case
                (:p i))
       (implies (and (and (integerp i) (< 1 i))    ; induction step
                     (:p (- i 2)))
                (:p i)))
  ~ev[]
  We can think of the base case as covering two situations.  The
  first is when ~c[i] is not an integer.  The second is when the integer ~c[i]
  is ~c[0] or ~c[1].  In the base case we must prove ~c[(:p i)] without further
  help.  The induction step deals with those integer ~c[i] greater than ~c[1],
  and inductively assumes the conjecture for ~c[i-2] while proving it for
  ~c[i].  Let us call this scheme ``induction on ~c[i] by twos.''

  Suppose the above ~c[:induction] rule has been added.  Then an
  occurrence of, say, ~c[(* 1/2 k)] in a conjecture to be proved by
  induction would suggest, via this rule, an induction on ~c[k] by twos,
  provided ~c[k] was known to be a nonnegative integer.  This is because
  the induction rule's ~c[:pattern] is matched in the conjecture, its
  ~c[:condition] is satisfied, and the ~c[:scheme] suggested by the rule is
  that derived from ~c[(recursion-by-sub2 k)], which is induction on ~c[k] by
  twos.  Similarly, the term ~c[(* 1/2 (length l))] would suggest no
  induction via this rule, even though the rule ``fires'' because it
  creates the ~c[:scheme] ~c[(recursion-by-sub2 (length l))] which suggests no
  inductions unwinding ~c[recursion-by-sub2] (since the controlling
  argument of ~c[recursion-by-sub2] in this ~c[:scheme] is not a variable
  symbol).

  Continuing this example one step further illustrates the utility of
  ~c[:induction] rules.  We could define the function ~c[recursion-by-cddr]
  that suggests the induction scheme decomposing its ~ilc[consp] argument
  two ~ilc[cdr]s at a time.  We could then add the ~c[:induction] rule linking
  ~c[(* 1/2 (length x))] to ~c[(recursion-by-cddr x)] and arrange for
  ~c[(* 1/2 (length l))] to suggest induction on ~c[l] by ~ilc[cddr].

  Observe that ~c[:induction] rules require no proofs to be done.  Such a
  rule is merely a heuristic link between the ~c[:pattern] term, which may
  occur in conjectures to be proved by induction, and the ~c[:scheme]
  term, from which an induction scheme may be derived.  Hence, when an
  ~c[:induction] rule-class is specified in a ~ilc[defthm] event, the theorem
  proved is irrelevant.  The easiest theorem to prove is, of course,
  ~c[t].  Thus, we suggest that when an ~c[:induction] rule is to be created,
  the following form be used:
  ~bv[]
  (defthm name T
    :rule-classes ((:induction :pattern pat-term
                               :condition cond-term
                               :scheme scheme-term)))
  ~ev[]
  The name of the rule created is ~c[(:induction name)].  When that rune
  is disabled the heuristic link between ~c[pat-term] and ~c[scheme-term] is
  broken.")

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
                   (getprop fn 'induction-rules nil
                            'current-acl2-world wrld))
             wrld)))

;---------------------------------------------------------------------------
; Section:  :TYPE-SET-RECOGNIZER-TERM Rules

(deflabel type-set-inverter
  :doc
  ":Doc-Section Rule-Classes

  exhibit a new decoding for an ACL2 type-set~/

  ~l[rule-classes] for a general discussion of rule classes and
  how they are used to build rules from formulas.
  ~bv[]
  Example Rule Class:
  (:type-set-inverter 
    :corollary (equal (and (counting-number x) (not (equal x 0)))
                      (and (integerp x) (< x 0)))
    :type-set 2)~/

  General Forms of Rule Class:
  :type-set-inverter, or
  (:type-set-inverter :type-set n)

  General Form of Theorem or Corollary:
  (EQUAL new-expr old-expr)
  ~ev[]
  where ~c[n] is a ~ilc[type-set] (~pl[type-set]) and ~c[old-expr] is the term
  containing ~c[x] as a free variable that ACL2 currently uses to
  recognize ~ilc[type-set] ~c[n].  For a given ~c[n], the exact form of ~c[old-expr] is
  generated by
  ~bv[]
  (convert-type-set-to-term 'x n (ens state) (w state) nil)].
  ~ev[]

  If the ~c[:]~ilc[type-set] field of the rule-class is omitted, we attempt to
  compute it from the right-hand side, ~c[old-expr], of the corollary.
  That computation is done by ~c[type-set-implied-by-term]
  (~pl[type-set]).  However, it is possible that the type-set we
  compute from ~c[lhs] does not have the required property that when
  inverted with ~c[convert-type-set-to-term] the result is ~c[lhs].  If you
  omit ~c[:]~ilc[type-set] and an error is caused because ~c[lhs] has the incorrect
  form, you should manually specify both ~c[:]~ilc[type-set] and the ~c[lhs]
  generated by ~c[convert-type-set-to-term].

  The rule generated will henceforth make ~c[new-expr] be the term used by
  ACL2 to recognize type-set ~c[n].  If this rule is created by a ~ilc[defthm]
  event named ~c[name] then the rune of the rule is
  ~c[(:type-set-inverter name)] and by disabling that rune you can
  prevent its being used to decode type-sets.

  Type-sets are inverted when forced assumptions are turned into
  formulas to be proved.  In their internal form, assumptions are
  essentially pairs consisting of a context and a goal term, which was
  forced.  Abstractly a context is just a list of hypotheses which may
  be assumed while proving the goal term.  But actually contexts are
  alists which pair terms with type-sets, encoding the current
  hypotheses.  For example, if the original conjecture contained the
  hypothesis ~c[(integerp x)] then the context used while working on that
  conjecture will include the assignment to ~c[x] of the type-set
  ~c[*ts-integer*].")

(defun chk-acceptable-type-set-inverter-rule (name ts term ctx ens wrld state)
  (let* ((vars (all-vars term)))
    (cond
     ((not (and (nvariablep term)
                (not (fquotep term))
                (eq (ffn-symb term) 'equal)
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

(deflabel clause-processor
  :doc
  ":Doc-Section Rule-Classes

  make or apply a ~c[:clause-processor] rule (goal-level simplifier)~/

  Also ~pl[define-trusted-clause-processor] for documentation of an analogous
  utility that does not require the clause-processor to be proved correct.  But
  please read the present documentation before reading about that utility.
  Both utilities designate functions ``clause-processors''.  Such functions
  must be executable ~-[] hence not constrained by virtue of being introduced
  in the ~il[signature] of an ~ilc[encapsulate] ~-[] and must respect
  ~il[stobj] and output arity restrictions.  For example, something like 
  ~c[(car (mv ...))] is illegal; also ~pl[signature].

  We begin this documentation with an introduction, focusing on an example, and
  then conclude with details.  You might find it most useful simply to look at
  the examples in community books directory ~c[books/clause-processors/]; see
  file ~c[Readme.lsp] in that directory.

  A ~c[:clause-processor] rule installs a simplifier at the level of goals,
  where a goal is represented as a ~em[clause]: a list of ~il[term]s that is
  implicitly viewed as a disjunction (the application of ~ilc[OR]).  For
  example, if ACL2 prints a goal in the form ~c[(implies (and p q) r)], then
  the clause might be the one-element list containing the internal
  representation of this term ~-[] ~c[(implies (if p q 'nil) r)] ~-[] but more
  likely, the corresponding clause is ~c[((not p) (not q) r)].  Note that the
  members of a clause are ~em[translated] terms; ~pl[term].  For example, they
  do not contains calls of the macro ~c[AND], and constants are quoted.

  Note that clause-processor simplifiers are similar to metafunctions, and
  similar efficiency considerations apply.  ~l[meta], in particular the
  discussion on how to ``make a metafunction maximally efficient.''

  Unlike rules of class ~c[:]~ilc[meta], rules of class ~c[:clause-processor]
  must be applied by explicit ~c[:clause-processor] ~il[hints]; they are not
  applied automatically (unless by way of computed hints; ~pl[computed-hints]).
  But ~c[:clause-processor] rules can be useful in situations for which it is
  more convenient to code a simplifier that manipulates the entire goal clause
  rather than individual subterms of terms in the clause.

  We begin with a simple illustrative example: a clause-processor that assumes
  an alleged fact (named ~c[term] in the example) and creates a separate goal
  to prove that fact.  We can extend the hypotheses of the current goal (named
  ~c[cl] in the example) with a term by adding the negation of that term to the
  clause (disjunctive) representation of that goal.  So the following returns
  a list of two clauses: the result of adding ~c[term] as a hypothesis to the
  input clause, as just described, and a second clause consisting only of that
  term.  This list of two clauses can be viewed as the conjunction of the first
  clause and the second clause (where again, each clause is viewed as a
  disjunction).
  ~bv[]

  (defun note-fact-clause-processor (cl term)
    (declare (xargs :guard t)) ; optional, for better efficiency
    (list (cons (list 'not term)
                cl)
          (list term)))

  ~ev[]
  As with ~c[:]~ilc[meta] rules, we need to introduce a suitable evaluator;
  ~pl[defevaluator] if you want details.  Since we expect to reason about the
  function ~ilc[NOT], because of its role in ~c[note-fact-clause-processor] as
  defined above, we include ~c[NOT] in the set of functions known to this
  evaluator.  We also include ~c[IF], as is often a good idea.
  ~bv[]

  (defevaluator evl0 evl0-list
    ((not x) (if x y z)))

  ~ev[]
  ACL2 can now prove the following theorem automatically.  (Of course,
  ~c[:clause-processor] rules about clause-processor functions less trivial
  than ~c[note-fact-clause-processor] may require lemmas to be proved first!)
  The function ~c[disjoin] takes a clause and returns its disjunction (the
  result of applying ~ilc[OR] to its members), and ~c[conjoin-clauses] applies
  ~c[disjoin] to every element of a given list of clauses and then conjoins
  (applies ~c[AND]) to the corresponding list of resulting terms.
  ~bv[]

  (defthm correctness-of-note-fact-clause-processor
    (implies (and (pseudo-term-listp cl)
                  (alistp a)
                  (evl0 (conjoin-clauses
                         (note-fact-clause-processor cl term))
                        a))
             (evl0 (disjoin cl) a))
    :rule-classes :clause-processor)

  ~ev[]
  Now let us submit a silly but illustrative example theorem to ACL2, to show
  how a corresponding ~c[:clause-processor] hint is applied.  The hint says to
  apply the clause-processor function, ~c[note-fact-clause-processor], to the
  current goal clause and a ``user hint'' as the second argument of that
  function, in this case ~c[(equal a a)].  Thus, a specific variable,
  ~c[clause], is always bound to the current goal clause for the evaluation of
  the ~c[:clause-processor] hint, to produce a list of clauses.  Since two
  subgoals are created below, we know that this list contained two clauses.
  Indeed, these are the clauses returned when ~c[note-fact-clause-processor] is
  applied to two arguments:  the current clause, which is the one-element list
  ~c[((equal (car (cons x y)) x))], and the user hint, ~c[(equal a a)].
  ~bv[]

  ACL2 !>(thm (equal (car (cons x y))
                     x)
              :hints
              ((\"Goal\"
                :clause-processor
                (note-fact-clause-processor clause '(equal a a)))))

  [Note:  A hint was supplied for our processing of the goal above. 
  Thanks!]

  We now apply the verified :CLAUSE-PROCESSOR function NOTE-FACT-CLAUSE-
  PROCESSOR to produce two new subgoals.

  Subgoal 2
  (IMPLIES (EQUAL A A)
           (EQUAL (CAR (CONS X Y)) X)).

  But we reduce the conjecture to T, by the :executable-counterpart of
  IF and the simple :rewrite rule CAR-CONS.

  Subgoal 1
  (EQUAL A A).

  But we reduce the conjecture to T, by primitive type reasoning.

  Q.E.D.

  Summary
  Form:  ( THM ...)
  Rules: ((:EXECUTABLE-COUNTERPART IF)
          (:EXECUTABLE-COUNTERPART NOT)
          (:FAKE-RUNE-FOR-TYPE-SET NIL)
          (:REWRITE CAR-CONS))
  Warnings:  None
  Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

  Proof succeeded.
  ACL2 !>
  ~ev[]~/

  That concludes our introduction to clause-processor rules and hints.  We turn
  now to detailed documentation.

  The ~il[signature] of a clause-processor function, ~c[CL-PROC], must have
  one of the following forms.  Here, each ~c[st_i] is a ~il[stobj] (possibly
  ~c[state]) while the other parameters and results are not stobjs
  (~pl[stobj]).  Note that there need not be input stobjs in [3] ~-[] i.e.,
  ~c[k] can be 0 ~-[] and even if there are, there need not be output stobjs.
  ~bv[]
  [1]  ((CL-PROC cl) => cl-list)

  [2]  ((CL-PROC cl hint) => cl-list)

  [3]  ((CL-PROC cl hint st_1 ... st_k) => (mv erp cl-list st_i1 ... st_in))
  ~ev[]
  In [3], we think of the first component of the result as an error flag.
  Indeed, a proof will instantly abort if that error flag is not ~c[nil].

  We next discuss the legal forms of ~c[:clause-processor] rules, followed
  below by a discussion of ~c[:clause-processor] ~il[hints].  In the discussion
  below, we use lower-case names to represent specific symbols, for example
  ~c[implies], and we use upper-case names to represent more arbitrary pieces
  of syntax (which we will describe), for example, ~c[CL].

  If a ~c[:]~ilc[rule-classes] specification includes ~c[:clause-processor],
  then the corresponding term must have the following form.  (Additional
  ``meta-extract'' hypotheses'', not shown or discussed below, may be included
  as desired in order to use facts from the logical ~ilc[world] to help prove
  the rule; ~pl[meta-extract] for explanation of this advanced feature.)
  ~bv[]
  (implies (and (pseudo-term-listp CL)
                (alistp A)
                (EVL (conjoin-clauses <CL-LIST>)
                      B))
           (EVL (disjoin CL) A))
  ~ev[]
  Here ~c[EVL] is a known evaluator; ~c[CL] and ~C[A] are distinct non-stobj
  variables; and ~c[<CL-LIST>] is an expression representing the clauses
  returned by the clause-processor function ~c[CL-PROC], whose form depends on
  the ~il[signature] of that function, as follows.  Typically ~c[B] is ~c[A],
  but it can be any term (useful when generalization is occurring; see the
  example ``Test generalizing alist'' in community book
  ~c[books/clause-processors/basic-examples.lisp]).  For cases [1] and [2]
  above, ~c[<CL-LIST>] is of the form ~c[(CL-PROC CL)] or
  ~c[(CL-PROC CL HINT)], respectively, where in the latter case ~c[HINT] is a
  non-stobj variable distinct from the variables ~c[CL] and ~c[A].  For case
  [3], ~c[<CL-LIST>] is of the form
  ~bv[]
  (clauses-result (CL-PROC CL HINT st_1 ... st_k))
  ~ev[]
  where the ~c[st_i] are the specific stobj names mentioned in [3].  Logically,
  ~c[clauses-result] returns the ~ilc[cadr] if the ~ilc[car] is ~c[NIL], and
  otherwise (for the error case) returns a list containing the empty (false)
  clause.  So in the non-error case, ~c[clauses-result] picks out the second 
  result, denoted ~c[cl-list] in [3] above, and in the error case the
  implication above trivially holds.

  In the above theorem, we are asked to prove ~c[(EVL (disjoin CL) A)] assuming
  that the conjunction of all clauses produced by the clause processor
  evaluates to a non-~c[nil] value under some alist ~c[B].  In fact, we can
  choose ~c[B] so as to allow us to assume evaluations of the generated clauses
  over many different alists.  This technique is discussed in the community
  book ~c[books/clause-processors/multi-env-trick.lisp], which introduces some
  macros that may be helpful in accomplishing proofs of this type.

  The clause-processor function, ~c[CL], must have a guard that ACL2 can
  trivially prove from the hypotheses that the first argument of ~c[CL] is
  known to be a ~c[pseudo-term-listp] and any ~il[stobj] arguments are assumed
  to satisfy their stobj predicates.

  Next we specify the legal forms for ~c[:clause-processor] ~il[hints].  These
  depend on the signature as described in [1] through [3] above.  Below, as
  above, ~c[CL-PROC] is the clause-processor function, and references to
  ``~c[clause]'' refer to that exact variable (not, for example, to ~c[cl]).
  In each of the three cases, the forms shown for that case are equivalent; in
  particular, the ~c[:function] syntax is simply a convenience for the final
  form in each case.

  Signature [1], ~c[((cl-proc cl) => cl-list)]:
  ~bv[]
  :clause-processor CL-PROC
  :clause-processor (:function CL-PROC)
  :clause-processor (CL-PROC clause)
  ~ev[]
  or any term macroexpanding to ~c[(CL-PROC clause)].

  Signature [2], ((cl-proc cl hint) => cl-list):
  ~bv[]
  :clause-processor (:function CL-PROC :hint HINT)
  :clause-processor (CL-PROC clause HINT)
  ~ev[]
  or any term macroexpanding to ~c[(CL-PROC clause HINT)], where ~c[HINT] is
  any term with at most ~c[CLAUSE] free.

  Signature [3], ((CL-PROC cl hint ...) => (mv erp cl-list ...))
  ~bv[]
  :clause-processor (:function CL-PROC :hint HINT)
  :clause-processor (CL-PROC clause HINT st_1 ... st_k)
  ~ev[]
  or any term macroexpanding to ~c[(CL-PROC clause HINT st_1 ... st_k)], where
  ~c[HINT] is any term with at most ~c[CLAUSE] free.

  A ~c[:clause-processor] hint causes the proof to abort if the result returned
  by evaluating the suitable ~c[CL-PROC] call, as above, is not a list of
  clauses, i.e., a list of (translated) ~il[term] lists.  The proof also aborts
  if in case [3] the first (~c[erp]) value returned is not ~c[nil], in which
  case ~c[erp] is used for printing an error message as follows: if it is a
  string, then that string is printed; but if it is a non-empty true list whose
  first element is a string, then it is printed as though by
  ~c[(fmt ~~@0 (list (cons #\\0 erp)) ...)] (~pl[fmt]).  Otherwise, a
  non-~c[nil] ~c[erp] value causes a generic error message to be printed.

  If there is no error as above, but the ~c[CL-PROC] call returns clause list
  whose single element is equal to the input clause, then the hint is ignored
  since we are left with the goal with which we started.  In that case, the
  other prover processes are then applied as usual.

  You can see all current ~c[:clause-processor] rules by issuing the following
  command: ~c[(print-clause-processor-rules)].

  The following paper discusses ACL2 clause-processors at a high level suitable
  for a non-ACL2 audience:~bq[]

  M. Kaufmann, J S. Moore, S. Ray, and E. Reeber, ``Integrating External
  Deduction Tools with ACL2.''  ~em[Journal of Applied Logic] (Special Issue:
  Empirically Successful Computerized Reasoning), Volume 7, Issue 1, March
  2009, pp. 3--25.  Also published online (DOI ~c[10.1016/j.jal.2007.07.002]).
  Preliminary version in: Proceedings of the 6th International Workshop on the
  Implementation of Logics (IWIL 2006) (C. Benzmueller, B. Fischer, and
  G. Sutcliffe, editors), CEUR Workshop Proceedings Vol. 212, Phnom Penh,
  Cambodia, pp. 7-26, November 2006, ~url[http://ceur-ws.org/Vol-212/].~eq[]")

(defun tilde-@-illegal-clause-processor-sig-msg (cl-proc stobjs-in stobjs-out)

; A clause-processor should have signature of the form
; (cl-proc cl) => cl-list
; or
; (cl-proc cl hint) => cl-list
; or
; (cl-proc cl hint st_1 ... st_k) => (erp cl-list st_i1 ... st_in)

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
   ((and ; the final (third) class of signatures above
     (null (car stobjs-in))
     (cdr stobjs-in)
     (null (cadr stobjs-in))
     (not (member-eq nil (cddr stobjs-in)))
     (null (car stobjs-out))
     (cdr stobjs-out)
     (null (cadr stobjs-out))
     (not (member-eq nil (cddr stobjs-out))))
    nil)
   (t
    (msg "both the arguments and results of ~x0 in this case are expected to ~
          contain stobjs in exactly all positions other than the first two"
         cl-proc))))

(defun destructure-clause-processor-rule (term)
  (case-match term
    (('implies hyp
               (ev ('disjoin clause) alist))
     (mv-let
      (hyps meta-extract-flg)
      (remove-meta-extract-global-hyps
       (remove1-equal (fcons-term* 'pseudo-term-listp clause)
                      (remove1-equal (fcons-term* 'alistp alist)
                                     (flatten-ands-in-lit hyp)))
       ev)
      (case-match hyps
        (((ev ('conjoin-clauses cl-result)
              &))
         (case-match cl-result
           (('clauses-result (cl-proc !clause . rest-args))
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
                                              '(meta-extract-global-fact))
                                         :clause-processor
                                         ev ctx wrld state)
              (chk-rule-fn-guard "clause-processor" :clause-processor cl-proc
                                 ctx wrld state)
              (chk-evaluator ev wrld ctx state))))))))))))

(defun add-clause-processor-rule (name term wrld)

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
     t

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

(defun trusted-clause-processor-table-guard (key val wrld)

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
                 define-trusted-clause-processor.")
        (ctx 'trusted-clause-processor-table-guard))
    (cond
     ((not (or (ttag wrld)
               (global-val 'boot-strap-flg wrld)))
      (er hard ctx er-msg
          "there is not an active ttag (also see :DOC ttag)"))
     ((not (symbolp key))
      (er hard ctx er-msg
          (msg "the clause-processor must be a symbol, unlike ~x0"
               key)))
     ((not (function-symbolp key wrld))
      (er hard ctx er-msg
          (msg "the clause-processor must be a function symbol, unlike ~x0"
               key)))
     ((not (and (consp val)
                (all-function-symbolps (car val) wrld)))
      (cond ((not (symbol-listp (car val)))
             (er hard ctx er-msg
                 "the indicated supporters list is not a true list of symbols"))
            (t (er hard ctx er-msg
                   (msg "the indicated supporter~#0~[ ~&0 is not a function ~
                         symbol~/s ~&0 are not function symbols~] in the ~
                         current ACL2 world"
                        (non-function-symbols (car val) wrld))))))
     ((and (cdr val)
           (not (eql (length (non-trivial-encapsulate-ee-entries
                              (global-val 'embedded-event-lst wrld)))
                     1)))
      (let  ((ee-entries (non-trivial-encapsulate-ee-entries
                          (global-val 'embedded-event-lst wrld))))
        (cond
         ((null ee-entries)
          (er hard ctx er-msg
              "there is no promised encapsulate to associate with this ~
               dependent clause-processor"))
         (t
          (er hard ctx er-msg
              (msg "there is not a unique encapsulate for the promised ~
                    encapsulate to associate with this dependent ~
                    clause-processor.  In particular, an enclosing ~
                    encapsulate introduces function ~x0, while an encapsulate ~
                    superior to that introduces function ~x1"
                   (caar (cadr (car ee-entries)))
                   (caar (cadr (cadr ee-entries)))))))))
     (t
      (let ((failure-msg (tilde-@-illegal-clause-processor-sig-msg
                          key
                          (stobjs-in key wrld)
                          (stobjs-out key wrld))))
        (cond
         (failure-msg
          (er hard ctx er-msg
              (msg failure-msg key)))
         (t t)))))))

(table trusted-clause-processor-table nil nil
       :guard
       (trusted-clause-processor-table-guard key val world))

(defmacro define-trusted-clause-processor
  (clause-processor supporters
                    &key
                    label          ;;; optional, but required if doc is non-nil
                    doc            ;;; optional
                    partial-theory ;;; optional
                    ttag           ;;; optional; nil is same as missing
                    )

; We could mention that unlike trusted clause-processors, no supporters need to
; be specified for a verified clause-processor, as such a rule is guaranteed to
; be a theorem even in if local events have been removed.  But that probably
; would distract more than it would enlighten.

  ":Doc-Section Events

  define a trusted (unverified) goal-level simplifier~/

  This ~il[documentation] assumes familiarity with ~c[:clause-processor] rules;
  ~pl[clause-processor].  Briefly put, a ~em[clause-processor] is a
  user-defined function that takes as input the ACL2 representation of a goal
  ~-[] a ~em[clause] ~-[] and returns a list of goals (i.e., a list of
  clauses).  A ~c[:clause-processor] rule is a way to inform ACL2 that a
  clause-processor has been proved correct and now may be specified in
  ~c[:clause-processor] ~il[hints].

  Here we describe a utility, ~c[define-trusted-clause-processor], that
  provides another way to inform ACL2 that a function is to be considered a
  clause-processor that can be specified in a ~c[:clause-processor] hint.  You
  can find examples of correct and incorrect use of this utility in community
  book ~c[books/clause-processors/basic-examples].

  Consider the simple example already presented for ~c[:clause-processor] rules
  (again, ~pl[clause-processor]), for a simple clause-processor named
  ~c[note-fact-clause-processor].  Instead of introducing an evaluator and
  proving a correctness theorem with ~c[:rule-classes :clause-processor], we
  can simply inform ACL2 that we trust the function
  ~c[note-fact-clause-processor] to serve as a clause-processor.
  ~bv[]
  (define-trusted-clause-processor
    note-fact-clause-processor
    nil
    :ttag my-ttag)
  ~ev[]
  A non-nil ~c[:ttag] argument generates a ~ilc[defttag] event in order to
  acknowledge the dependence of the ACL2 session on the (unproved) correctness
  of this clause-processor.  That argument can be omitted if there is currently
  an active trust tag.  ~l[defttag].  Because we are trusting this
  clause-processor, rather than having proved it correct, we refer to it as a
  ``trusted'' clause-processor to contrast with a proved-correct, or
  ``verified'', clause-processor.

  Now that the event displayed above has established
  ~c[note-fact-clause-processor] as a (trusted) clause-processor, we can use it
  in a ~c[:clause-processor] hint, for example as follows.  Notice that the output
  is identical to that for the corresponding example presented for the verified
  case (~pl[clause-processor]), except that the word ``verified'' has been
  replaced by the word ``trusted''.
  ~bv[]
  ACL2 !>(thm (equal (car (cons x y))
                     x)
              :hints
              ((\"Goal\"
                :clause-processor
                (note-fact-clause-processor clause '(equal a a)))))

  [Note:  A hint was supplied for our processing of the goal above. 
  Thanks!]

  We now apply the trusted :CLAUSE-PROCESSOR function NOTE-FACT-CLAUSE-
  PROCESSOR to produce two new subgoals.

  Subgoal 2
  (IMPLIES (EQUAL A A)
           (EQUAL (CAR (CONS X Y)) X)).

  But we reduce the conjecture to T, by the :executable-counterpart of
  IF and the simple :rewrite rule CAR-CONS.

  Subgoal 1
  (EQUAL A A).

  But we reduce the conjecture to T, by primitive type reasoning.

  Q.E.D.

  Summary
  Form:  ( THM ...)
  Rules: ((:EXECUTABLE-COUNTERPART IF)
          (:EXECUTABLE-COUNTERPART NOT)
          (:FAKE-RUNE-FOR-TYPE-SET NIL)
          (:REWRITE CAR-CONS))
  Warnings:  None
  Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

  Proof succeeded.
  ACL2 !>
  ~ev[]
  Indeed, if one runs this example first and subsequently verifies the
  clause-processor, one will see the word ``trusted'' change to ``verified''.~/

  The general form is as follows.
  ~bv[]
  (define-trusted-clause-processor
    cl-proc           ;;; clause-processor function
    supporters        ;;; see below
    &key
    label             ;;; optional, but required if doc is non-nil
    doc               ;;; optional
    ttag              ;;; discussed above
    partial-theory    ;;; optional encapsulate event
    )
  ~ev[]
  If a ~c[:label] ~c[LAB] is supplied, then a subsidiary ~ilc[deflabel] event
  will be generated with name ~c[LAB], which will enable you to to undo this
  ~c[define-trusted-clause-processor] event using: ~c[:]~ilc[ubt]~c[ LAB].  If
  you supply a ~c[:label] then you may supply a ~c[:doc] argument to use with
  that generated ~ilc[deflabel] event.  We discussed the ~c[:ttag] argument
  above.  The entire form is considered redundant (skipped) if it is identical
  to one already executed in the current ACL2 world; but if it is not
  redundant, then ~c[cl-proc] must not already have been similarly designated
  as a trusted clause-processor.

  Note that ~c[cl-proc] may be defined either in ~c[:program]-mode or
  ~c[:logic]-mode.

  The ~c[supporters] argument should be a true list of function symbols in the
  current ACL2 world.  It is important that this list include user-defined
  functions whose definitions support the correctness of the clause-processor
  function.  Otherwise, ~ilc[local] definitions of those missing supporters can
  render the use of this clause-processor unsound, as discussed in the paper
  referenced at the end of the ~il[clause-processor] documentation topic.
  Moreover, ACL2 assumes for dependent clause-processors (discussed below) that
  every function symbol constrained by the ``promised encapsulate'' of that
  event is either among those ~c[supporters] or ancestral in one of them
  (i.e. a supporter of a supporter, a supporter of one of those, etc.).

  ~st[Dependent clause-processors and promised encapsulates]: The
  ~c[:partial-theory] argument

  Suppose you want to introduce a clause-processor to reason about a complex
  hardware simulator that is implemented outside ACL2.  Sawada and Reeber had
  just such a problem, as reported in their FMCAD 2006 paper.  Indeed, they
  used ~ilc[sys-call] to implement a ~c[:]~ilc[program]-mode function in ACL2
  that can invoke that simulator.  In principle one could code the simulator
  directly in ACL2; but it would be a tremendous amount of work that has no
  practical purpose, given the interface to the external simulator.  So: In
  what sense can we have a clause-processor that proves properties about a
  simulator when that simulator is not fully axiomatized in ACL2?  Our answer,
  in a nutshell, is this: The above ~c[:partial-theory] argument provides a way
  to write merely some of the ~il[constraint]s on the external tool (or even no
  constraints at all), with the understanding that such constraints are present
  implicitly in a stronger ``promised'' ~c[encapsulate], for example by
  exporting the full definition.

  If a trusted clause-processor is introduced with a ~c[:partial-theory]
  argument, we call it a ``dependent'' clause-processor, because its
  correctness is dependent on the constraints implicitly introduced by the
  ~c[:partial-theory] ~c[encapsulate] form.  The implicit constraints should
  logically imply the constraints actually introduced by the explicit
  ~c[encapsulate], but they should also be sufficient to justify every possible
  invocation of the clause-processor in a ~c[:clause-processor] hint.  The user
  of a ~c[define-trusted-clause-processor] form is making a guarantee ~-[] or,
  is relying on a guarantee provided by the writer of that form ~-[] that in
  principle, there exists a so-called ``promised encapsulate'': an
  ~c[encapsulate] form with the same ~il[signature] as the ~c[:partial-theory]
  ~c[encapsulate] form associated with the trusted clause-processor, but whose
  constraints introduced are the aforementioned implicit constraints.

  There are several additional requirements on a ~c[:partial-theory] argument.
  First, it must be an ~ilc[encapsulate] event with non-empty ~il[signature].
  Moreover, the functions introduced by that event must be exactly those
  specified in the signature, and no more.  And further still, the
  ~c[define-trusted-clause-processor] form cannot be executed inside any
  ~ilc[encapsulate] form with non-empty ~il[signature]; we can think of this
  situation as attempting to associate more than one ~c[encapsulate]
  with the functions introduced in the inner ~c[encapsulate].

  The ~c[:partial-theory] event will (in essence) be executed as part of the
  evaluation of the ~c[define-trusted-clause-processor] form.  Again, a
  critical obligation rests on the user who provides a ~c[:partial-theory]:
  there must exist (in principle at least) a corresponding promised encapsulate
  form with the same ~il[signature] that could logically be admitted, whenever
  the above ~c[define-trusted-clause-processor] form is evaluated successfully,
  that justifies the designation of ~c[cl-proc] as a clause-processor.  See
  also the paper mentioned above for more about promised encapsulates.  A key
  consequence is that the ~il[constraint]s are unknown for the functions
  introduced in (the signature of) a ~c[:partial-theory] ~ilc[encapsulate]
  form.  Thus, functional instantiation (~pl[functional-instantiation-example])
  is disabled for function in the signature of a ~c[:partial-theory] form.

  ~st[A remark on the underlying implementation]

  You can see all of the current trusted clause-processors by issuing the
  command ~c[(table trusted-clause-processor-table)].  Those that are dependent
  clause-processors will be associated in the resulting association list with a
  pair whose ~c[car] is the list of supporters and whose ~c[cdr] is ~c[t],
  i.e., with ~c[(supporters . t)]; the others will be associated just with
  ~c[(supporters)].

  Thus, ~c[define-trusted-clause-processor] is actually a macro that generates
  (among other things) a ~c[table] event for a table named
  ~c[trusted-clause-processor-table]; ~pl[table].  You are invited to use
  ~c[:]~ilc[trans1] to see expansions of calls of this macro.

  ~st[A technique for using raw Lisp to define a trusted clause-processor]

  The following code is intended to give an idea for how one might define the
  ``guts'' of a trusted clause-processor in raw Lisp.  The idea is to stub out
  functions, such as ~c[acl2-my-prove below], that you want to define in raw
  Lisp; and then, load a raw Lisp file to overwrite any such function with the
  real code.  But then we make any such overwritten function untouchable.
  (This last step is important because otherwise, one can prove ~c[nil] using a
  ~c[:functional-instance] ~c[:use] hint, by exploiting the fact that this
  function has executable code for which there is no corresponding definitional
  axiom.)

  ~bv[]
  (defstub acl2-my-prove (term hint) t)

  (program)

  (defttag :my-cl-proc)

  (progn

  ; We wrap everything here in a single progn, so that the entire form is
  ; atomic.  That's important because we want the use of push-untouchable to
  ; prevent anything besides my-clause-processor from calling acl2-my-prove.

    (progn!

     (set-raw-mode-on state)

     (load \"my-hint-raw.lsp\") ; defines my-prove in raw Lisp

     (defun acl2-my-prove (term hint)
       (my-prove term hint)))

    (defun my-clause-processor (cl hint)
      (declare (xargs :guard (pseudo-term-listp cl)
                      :mode :program))
      (if (acl2-my-prove (disjoin cl) hint)
          (disjoin-clause-segments-to-clause
           (pairlis$ (hint-to-termlist hint) nil)
           cl)
        (prog2$ (cw \"~~|~~%NOTE: Unable to prove goal with ~~
                    my-clause-processor and indicated hint.~~|\")
                (list cl))))

    (push-untouchable acl2-my-prove t)
    )
  ~ev[]"

  (let* ((ctx 'define-trusted-clause-processor)
         (er-msg "The proposed use of define-trusted-clause-processor is ~
                  illegal because ~@0.  See :DOC ~
                  define-trusted-clause-processor.")
         (assert-check
          `(assert-event
            (not (assoc-eq ',clause-processor
                           (table-alist 'trusted-clause-processor-table
                                        (w state))))
            :msg (msg "The function ~x0 is already indicated as a trusted ~
                       clause-processor."
                      ',clause-processor)
            :on-skip-proofs t))
         (ttag-extra (and ttag `((defttag ,ttag))))
         (label-extra (and label
                           (cond (doc
                                  `((deflabel ,label
                                      :doc ,doc)))
                                 (t `((deflabel ,label))))))
         (extra (append ttag-extra label-extra)))
    (cond
     ((not (symbol-listp supporters))
      (er hard ctx er-msg
          "the second (supporters) argument must be a true list of symbols"))
     ((not (symbolp clause-processor)) ; expansion will do stronger check
      (er hard ctx er-msg
          "the first argument must be a symbol (in fact, must be a defined ~
           function symbol in the current ACL2 world)"))
     ((and doc (not label))
      (er hard ctx er-msg
          "a non-nil :label argument is required when a non-nil :doc argument ~
           is supplied"))
     (t
      (case-match partial-theory
        (nil
         `(encapsulate
           ()
           ,assert-check
           ,@extra
           (table trusted-clause-processor-table ',clause-processor
                  '(,supporters))))
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
               (table trusted-clause-processor-table ',clause-processor
                      '(,supporters . t))))))
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

; Now we stub out the proof checker's sense of "instructions."

(defun primitive-instructionp (instr state)
  (let* ((cmd (car (make-official-pc-instr instr)))
         (typ (pc-command-type cmd)))
    (and (member-eq typ '(primitive atomic-macro))
         (acl2-system-namep
          (intern-in-package-of-symbol (symbol-name cmd) 'acl2-pc::induct)
          (w state)))))

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

(defun loop-stopper-alist-p (x wrld)
  (cond
   ((consp x)
    (and (true-listp (car x))
         (<= 2 (length (car x)))
         (legal-variablep (caar x))
         (legal-variablep (cadar x))
         (not (eq (caar x) (cadar x)))
         (all-function-symbolps (cddar x) wrld)
         (loop-stopper-alist-p (cdr x) wrld)))
   (t
    (eq x nil))))

(defun guess-controller-alist-for-definition-rule (names formals body ctx wrld
                                                         state)

; Names is a singleton list containing a function name to be used as the clique
; for a :definition rule with the indicated formals and body.  We guess a
; :controller-alist or cause an error.

  (let ((t-machine (termination-machine names body nil nil
                                        (default-ruler-extenders wrld))))
    (er-let*
     ((m (guess-measure (car names) nil formals 0 t-machine ctx wrld state)))
     (value (list (cons (car names)
                        (make-controller-pocket formals
                                                (all-vars m))))))))

(defun chk-legal-linear-trigger-terms1 (term lst name ctx state)
  (cond ((null lst) (value nil))
        ((subsetp-eq (set-difference-eq (all-vars (cdar lst))
                                        (all-vars1-lst (caar lst) nil))
                     (all-vars term))
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
; that each trigger is legal for every rule generated from the unprettified
; corollary.  Here, terms is a true-list of terms proposed as triggers and lst
; is the unprettification of the corollary, i.e., a list of pairs of the form
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
                     (destructure-forward-chaining-term corollary)
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
                                               (not (fquotep (car hyps)))
                                               (or (eq (ffn-symb (car hyps))
                                                       'force)
                                                   (eq (ffn-symb (car hyps))
                                                       'case-split)))
                                          (fargn (car hyps) 1)
                                        (car hyps)))
                                     (trigger-term
                                      (if (and (nvariablep first-hyp)
                                               (not (fquotep first-hyp))
                                               (eq (ffn-symb first-hyp) 'not))
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
              (unprettyify-tp (remove-guard-holders corollary))
              (declare (ignore hyps))
              (let ((pat (cond ((and (not (variablep concl))
                                     (not (fquotep concl))
                                     (eq (ffn-symb concl) 'implies))
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
                   for the :CLIQUE consisting of ~&1.  See :DOC definition."
                  controller-alist
                  clique)))))))
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
                       "The variables occuring freely in the :CONDITION term ~
                        of an :INDUCTION rule class must be a subset of those ~
                        occuring freely in the :PATTERN term.  But the ~
                        condition term ~x0 mentions ~&1, which ~#1~[does~/do~] ~
                        not occur in the pattern term ~x2.  Thus the ~
                        :INDUCTION rule class specified for ~x3 is illegal."
                       cond-term
                       (set-difference-eq cond-vars pat-vars)
                       pat-term
                       name))
                  ((not (subsetp-eq scheme-vars pat-vars))
                   (er soft ctx
                       "The variables occuring freely in the :SCHEME term ~
                        of an :INDUCTION rule class must be a subset of those ~
                        occuring freely in the :PATTERN term.  But the ~
                        scheme term ~x0 mentions ~&1, which ~#1~[does~/do~] ~
                        not occur in the pattern term ~x2.  Thus the ~
                        :INDUCTION rule class specified for ~x3 is illegal."
                       scheme-term
                       (set-difference-eq scheme-vars pat-vars)
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
                         "It is illegal to supply both :HINTS and :INSTRUCTIONS ~
                       in a rule class.  Hence, ~x0 is illegal.  See :DOC ~
                       rule-classes."
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
                       Thus, ~x0 is illegal.  See :DOC forward-chaining and ~
                       :DOC meta."
                         x))
                    ((not (eq token :META))
                     (er soft ctx
                         ":TRIGGER-FNS can only be specified for :META rules.  ~
                       Thus, ~x0 is illegal.  See :DOC ~@1."
                         x
                         (symbol-name token)))
                    ((atom (cadr alist))
                     (er soft ctx
                         "The :TRIGGER-FNS component of a :META rule class must ~
                       be a non-empty true-list of function symbols.  But ~x0 ~
                       is empty.  See :DOC meta."
                         (cadr alist)))
                    ((eq (car (cadr alist)) 'quote)
                     (er soft ctx
                         "The :TRIGGER-FNS component of a :META rule class must ~
                       be a non-empty true-list of function symbols.  You ~
                       specified ~x0 for this component, but the list is not ~
                       to be quoted.~@1  See :DOC meta."
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
                                          "The :TRIGGER-FNS component of a :META ~
                                        rule class must be a non-empty ~
                                        true-list of function symbols, but ~
                                        ~x0 ~@1.  See :DOC meta."
                                          (cadr alist) lst))
                                     (t (value lst)))))))
                  (:TRIGGER-TERMS
                   (cond
                    ((eq token :META)
                     (er soft ctx
                         "The :META rule class may specify :TRIGGER-FNS but may ~
                       not specify :TRIGGER-TERMS.  Thus, ~x0 is illegal.  ~
                       See :DOC meta and :DOC forward-chaining."
                         x))
                    ((not (true-listp (cadr alist)))
                     (er soft ctx
                         "The :TRIGGER-TERMS must be a list true list.  Thus the ~
                       rule class ~x0 proposed for ~x1 is illegal."
                         x name))
                    ((eq token :LINEAR)

; We allow but do not require :TRIGGER-TERMS to be provided for :LINEAR rules.
; The whole idea of :TRIGGER-TERMS specified at the rule-class level is a
; little jarring in the case of linear rules because we generate a linear rule
; for each unprettified branch through the COROLLARY of the rule class and the
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
                           list of :TRIGGER-TERMS.  This is illegal.  If you ~
                           wish to cause ACL2 to compute the trigger terms, ~
                           omit the :TRIGGER-TERMS field entirely.  See :DOC ~
                           linear."
                             name))
                        (t
                         (let ((terms (remove-guard-holders-lst terms)))
                           (er-progn
                            (chk-legal-linear-trigger-terms
                             terms
                             (unprettyify (remove-guard-holders corollary))
                             name ctx state)
                            (value terms)))))))
                    ((eq token :FORWARD-CHAINING)
                     (er-let*
                         ((terms (translate-term-lst (cadr alist)
                                                     t t t ctx wrld state)))
                       (cond ((null terms)
                              (er soft ctx
                                  ":FORWARD-CHAINING rules must have at least one ~
                               trigger.  Your rule class, ~x0, specifies ~
                               none.  See :DOC forward-chaining."
                                  x))
                             (t (value (remove-guard-holders-lst terms))))))
                    (t
                     (er soft ctx
                         ":TRIGGER-TERMS can only be specified for ~
                       :FORWARD-CHAINING and :LINEAR rules.  Thus, ~x0 is ~
                       illegal.  See :DOC ~@1."
                         x
                         (symbol-name token)))))
                  (:TYPED-TERM
                   (cond
                    ((not (eq token :TYPE-PRESCRIPTION))
                     (er soft ctx
                         "Only :TYPE-PRESCRIPTION rule classes are permitted to ~
                       have a :TYPED-TERM component.  Thus, ~x0 is illegal.  ~
                       See :DOC ~@1."
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
                              (unprettyify-tp (remove-guard-holders corollary))
                              (list (cons hyps concl))))
                            (otherwise
                             (unprettyify (remove-guard-holders corollary))))))
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
                         rules have different hypothesis lists.  You should ~
                         split the corollary of ~x0 into parts and specify a ~
                         limit for each."
                           x))
                      (t
                       (let ((hyps (car (car hyps-concl-pairs))))
                         (cond
                          ((null hyps)
                           (er soft ctx
                               "There are no hypotheses, so :BACKCHAIN-LIMIT-LST ~
                             makes no sense.  See :DOC RULE-CLASSES."))
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
                             rules of class :META are nil or a non-negative ~
                             integer.  See :DOC RULE-CLASSES."))
                          ((and (backchain-limit-listp (cadr alist))
                                (eql (length (cadr alist)) (length hyps)))
                           (value (cadr alist)))
                          (t
                           (er soft ctx
                               "The legal values of :BACKCHAIN-LIMIT-LST are ~
                             nil, a non-negative integer, or a list of these ~
                             of the same length as the flattened hypotheses.  ~
                             In this case the list of flattened hypotheses, ~
                             of length ~x0, is:~%  ~x1.~%See :DOC ~
                             RULE-CLASSES."
                               (length hyps) hyps))))))))
                  (:MATCH-FREE
                   (cond
                    ((not (member-eq token '(:REWRITE :LINEAR :FORWARD-CHAINING)))
                     (er soft ctx
                         "Only :REWRITE, :FORWARD-CHAINING, and :LINEAR rule ~
                       classes are permitted to have a :MATCH-FREE component.  ~
                       Thus, ~x0 is illegal.  See :DOC free-variables."
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
                         "Only :DEFINITION rule classes are permitted to have a ~
                       :CLIQUE component.  Thus, ~x0 is illegal.  See :DOC ~
                       ~@1."
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
                                       "The :CLIQUE of a :DEFINITION must be a ~
                                     truelist of function symbols (containing ~
                                     no duplications) or else a single ~
                                     function symbol.  ~x0 is neither.~@1  ~
                                     See :DOC definition."
                                       (cadr alist)
                                       (cond ((eq flg :error) "")
                                             (t (msg "  Note that it is illegal ~
                                                   to use ~v0 here, because ~
                                                   we require function ~
                                                   symbols, not merely macros ~
                                                   that are aliases for ~
                                                   function symbols (see :DOC ~
                                                   macro-aliases-table)."
                                                     (set-difference-equal
                                                      (cadr alist)
                                                      lst)))))))
                                 ((and (ffnnamep fn body)
                                       (not (member-eq fn clique)))
                                  (er soft ctx
                                      "The :CLIQUE of a :DEFINITION must contain ~
                                    the defined function, ~x0, if the body ~
                                    calls the function.  See :DOC definition."
                                      fn))
                                 ((and clique
                                       (not (member-eq fn clique)))
                                  (er soft ctx
                                      "The :CLIQUE of a :DEFINITION, when ~
                                    non-nil, must contain the function ~
                                    defined.  ~x0 does not contain ~x1.  See ~
                                    :DOC definition."
                                      (cadr alist)
                                      fn))
                                 (t (value clique)))))))))
                  (:CONTROLLER-ALIST
                   (cond
                    ((not (eq token :DEFINITION))
                     (er soft ctx
                         "Only :DEFINITION rule classes are permitted to have a ~
                       :CONTROLLER-ALIST component.  Thus, ~x0 is illegal.  ~
                       See :DOC ~@1."
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
                         "Only :DEFINITION rule classes are permitted to have an ~
                       :INSTALL-BODY component.  Thus, ~x0 is illegal.  ~
                       See :DOC ~@1."
                         x
                         (symbol-name token)))
                    ((not (member-eq (cadr alist)
                                     '(t nil :NORMALIZE)))
                     (er soft ctx
                         "The :INSTALL-BODY component of a  :DEFINITION rule ~
                       class must have one of the values ~v0.  Thus, ~x1 is ~
                       illegal.  See :DOC ~@2."
                         '(t nil :NORMALIZE)
                         (cadr alist)
                         (symbol-name token)))
                    (t 
                     (value (cadr alist)))))
                  (:LOOP-STOPPER
                   (cond
                    ((not (eq token :REWRITE))
                     (er soft ctx
                         "Only :REWRITE rule classes are permitted to have a ~
                       :LOOP-STOPPER component.  Thus, ~x0 is illegal.  See ~
                       :DOC rule-classes."
                         x))
                    ((not (loop-stopper-alist-p (cadr alist) wrld))
                     (er soft ctx
                         "The :LOOP-STOPPER for a rule class must be a list ~
                       whose elements have the form (variable1 variable2 . ~
                       fns), where variable1 and variable2 are distinct ~
                       variables and fns is a list of function symbols, but ~
                       ~x0 does not have this form.  Thus, ~x1 is illegal.  ~
                       See :DOC rule-classes."
                         (cadr alist)
                         x))
                    ((not (subsetp-eq (union-eq (strip-cars (cadr alist))
                                                (strip-cadrs (cadr alist)))
                                      (all-vars corollary)))
                     (let ((bad-vars (set-difference-eq
                                      (union-eq (strip-cars (cadr alist))
                                                (strip-cadrs (cadr alist)))
                                      (all-vars corollary))))
                       (er soft ctx
                           "The variables from elements (variable1 variable2 . ~
                         fns) of a :LOOP-STOPPER specified for a rule class ~
                         must all appear in the :COROLLARY theorem for that ~
                         rule class.  However, the ~#0~[variables ~&1 ~
                         do~/variable ~&1 does~] not appear in ~p2.  Thus, ~
                         ~x3 is illegal.  See :DOC rule-classes."
                           (if (cdr bad-vars) 0 1)
                           bad-vars
                           (untranslate corollary t wrld)
                           x)))
                    (t
                     (value (cadr alist)))))
                  (:PATTERN
                   (cond
                    ((not (eq token :INDUCTION))
                     (er soft ctx
                         "Only :INDUCTION rule classes are permitted to have a ~
                       :PATTERN component.  Thus, ~x0 is illegal.  See :DOC ~
                       ~@1."
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
                               "The :PATTERN term of an :INDUCTION rule class may ~
                            not be a variable symbol, constant, or the ~
                            application of a lambda expression.  Thus ~x0 is ~
                            illegal.  See :DOC induction."
                               x))
                          (t (value term)))))))
                  (:CONDITION
                   (cond
                    ((not (eq token :INDUCTION))
                     (er soft ctx
                         "Only :INDUCTION rule classes are permitted to have a ~
                       :CONDITION component.  Thus, ~x0 is illegal.  See :DOC ~
                       ~@1."
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
                         "Only :INDUCTION rule classes are permitted to have a ~
                       :SCHEME component.  Thus, ~x0 is illegal.  See :DOC ~
                       ~@1."
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
                               "The :SCHEME term of an :INDUCTION rule class may ~
                            not be a variable symbol, constant, or the ~
                            application of a lambda expression.  Thus ~x0 is ~
                            illegal.  See :DOC induction."
                               x))
                          ((not (or (getprop (ffn-symb term) 'induction-machine
                                             nil 'current-acl2-world wrld)
                                    (getprop (ffn-symb term) 'induction-rules
                                             nil 'current-acl2-world wrld)))
                           (er soft ctx
                               "The function symbol of the :SCHEME term of an ~
                            :INDUCTION rule class must, at least sometimes, ~
                            suggest an induction and ~x0 does not.  See :DOC ~
                            induction."
                               (ffn-symb term)))
                          (t (value term)))))))
                  (:TYPE-SET
                   (cond
                    ((not (eq token :TYPE-SET-INVERTER))
                     (er soft ctx
                         "Only :TYPE-SET-INVERTER rule classes are permitted to ~
                       have a :TYPE-SET component.  Thus ~x0 is illegal.  See ~
                       :DOC ntype-set-inverter."
                         x))
                    ((not (and (integerp (cadr alist))
                               (<= *min-type-set* (cadr alist))
                               (<= (cadr alist) *max-type-set*)))
                     (er soft ctx
                         "The :TYPE-SET of a :TYPE-SET-INVERTER rule must be a ~
                       type-set, i.e., an integer between ~x0 and ~x1, ~
                       inclusive.  ~x2 is not a type-set.  See :DOC type-set ~
                       and :DOC type-set-inverter."
                         *min-type-set*
                         *max-type-set*
                         (cadr alist)))
                    (t (value (cadr alist)))))
                  (otherwise
                   (er soft ctx
                       "The key ~x0 is unrecognized as a rule class component.  ~
                     See :DOC rule-classes."
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
; found in (deflabel rule-classes ...).  It is hygenic to compare periodically
; the setting below to the form described there.

  (let ((rule-tokens '(:REWRITE
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
          "Uh oh, it was a keyword-value-listp after all!!"))
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

; X is an untranslated rule class.  For example, x may be :REWRITE or
; (:META :TRIGGER-FNS (fn1 ... fnk)) or even (:REWRITE :COROLLARY
; (IMPLIES p q) :HINTS ...).  We either translate x into a "fully
; elaborated" rule class or else cause an error.  A fully elaborated
; rule class starts with one of the rule class keywords, token,
; followed by an alternating keyword/value list.  Every fully
; elaborated class has a :COROLLARY component.  In addition, every
; :META class has a :TRIGGER-FNS component, every :FORWARD-CHAINING
; class has a :TRIGGER-TERMS component, and every :TYPE-PRESCRIPTION
; has a :TYPED-TERM component.  No keyword is bound twice in the list
; and the values associated with each keyword is syntactically correct
; in a local sense, e.g., alleged function symbols are really function
; symbols, alleged terms are translated terms, alleged hints are
; translated hints, etc.  We do not make the non-local checks, such as
; that the :COROLLARY of a :TYPE-PRESCRIPTION rule actually prescribes
; the type of the :TYPED-TERM.  Those checks are made by the
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
           (chk-acceptable-rewrite-rule name
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
            (cadr (assoc-keyword :BACKCHAIN-LIMIT-LST (cdr class)))
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

; The classes have already been translated, so we do not need to worry
; about unrecognized classes.  Each class contains a :COROLLARY which
; is a translated term.  We check that the :COROLLARY term can be used
; as a rule of the class indicated.  We either cause an error or
; return a ttree justifying whatever pre/post-processing is done to
; store the rules.  If we are not doing proofs we skip the checks.

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

                (collect-keys-eq '(:meta :clause-processor) classes))
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
           (add-rewrite-rule rune nume
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
                          term
                          (cadr (assoc-keyword :BACKCHAIN-LIMIT-LST
                                               (cdr class)))
                          wrld))
          (:CLAUSE-PROCESSOR
           (add-clause-processor-rule (base-symbol rune) term wrld))
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
                                       (cadr (assoc-keyword
                                              :BACKCHAIN-LIMIT-LST
                                              (cdr class)))
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

(defun redundant-theoremp (name term classes wrld)

; We know name is a symbol, but it may or may not be new.  We return t
; if name is already defined as the name of the theorem term with the
; given rule-classes.  If we are booting, no theorem is redundant.

  (and (equal term (getprop name 'theorem 0 'current-acl2-world wrld))
       (equal (truncate-classes classes term)
              (getprop name 'classes 0 'current-acl2-world wrld))))

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
                      (proof-checker nil (untranslate goal t wrld)
                                     goal nil instructions
                                     wrld state))
                     (t (prove goal
                               (make-pspv ens
                                          wrld
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
; signalling the successful proof of all the corollaries.

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
                        `((:meta-fn ,lhs)
                          (:hyp-fn  ,(or hyps :none) hyps))
                      `((:lhs  ,(untranslate lhs nil wrld) lhs)
                        (:rhs  ,(untranslate rhs nil wrld) rhs)
                        (:hyps ,(untranslate-hyps hyps wrld) hyps)))
                  (:equiv               ,equiv)
                  (:backchain-limit-lst ,backchain-limit-lst)
                  (:subclass            ,subclass)
                  ,@(cond ((eq subclass 'backchain)
                           `((:loop-stopper ,heuristic-info)))
                          ((eq subclass 'definition)
                           `((:clique           ,(car heuristic-info))
                             (:controller-alist ,(cdr heuristic-info))))
                          (t
                           nil)))
                (info-for-lemmas (cdr lemmas) numes ens wrld))
        (info-for-lemmas (cdr lemmas) numes ens wrld)))))

(defun world-to-next-event (wrld)
  (cond ((null wrld) nil)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value))
         nil)
        (t (cons (car wrld)
                 (world-to-next-event (cdr wrld))))))

(defun assoc-eq-eq (x y alist)

; We look for a pair on alist of the form (x y . val) where we compare with x
; and y using eq.  We return the pair or nil.

  (cond ((endp alist) nil)
        ((and (eq (car (car alist)) x)
              (eq (car (cdr (car alist))) y))
         (car alist))
        (t (assoc-eq-eq x y (cdr alist)))))

(defun actual-props (props seen acc)

; Props is a list whose elements have the form (sym key . val), where val could
; be *acl2-property-unbound*.  Seen is the list containing some (sym key . &)
; for each pair (sym key) that has already been seen.

  (cond
   ((null props)
    (reverse acc))
   ((assoc-eq-eq (caar props) (cadar props) seen)
    (actual-props (cdr props) seen acc))
   ((eq (cddr (car props)) *acl2-property-unbound*)
    (actual-props (cdr props) (cons (car props) seen) acc))
   (t
    (actual-props (cdr props)
                  (cons (car props) seen)
                  (cons (car props) acc)))))

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
                      (list :term      (untranslate term nil wrld)
                            term)
                      (list :hyps      (untranslate-hyps hyps wrld)
                            hyps)
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
      (recognizer-alist
       (info-for-compound-recognizer-rules val numes ens wrld))
      (generalize-rules
       (info-for-generalize-rules val numes ens wrld))
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
      (coarsenings
       (info-for-coarsenings val numes ens wrld))
      (forward-chaining-rules
       (info-for-forward-chaining-rules val numes ens wrld))
      (type-prescriptions
       (info-for-type-prescriptions val numes ens wrld))
      (induction-rules
       (info-for-induction-rules val numes ens wrld))
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
                          (t (fmt1 " ~q1"
                                   (list (cons #\0 14)
                                         (cons #\1 (caar vals)))
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
                   (ens state)
                   wrld)
   (standard-co state)
   state))

(defun pr-fn (name state)
  (cond ((and (symbolp name)
              (not (keywordp name)))
         (let* ((wrld (w state))
                (name (deref-macro-name name (macro-aliases wrld)))
                (numes (strip-cars (getprop name 'runic-mapping-pairs nil
                                            'current-acl2-world wrld)))
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

  ":Doc-Section History

  print the rules stored by the event with the given name~/
  ~bv[]
  Examples:

  :pr fn ; prints the rules from the definition of fn (including any
         ; :type-prescription rule and :definition rule)

  :pr assoc-append ; if assoc-append is a rewrite rule, prints that rule
  ~ev[]~/

  Also ~pl[pr!], which is similar but works at the command level
  instead of at the event level, and ~pl[pl], which displays all
  rewrite rules for calls of ~c[fn], not just those introduced at
  definition time.

  ~c[Pr] takes one argument, a logical name, and prints the rules
  associated with it.  In each case it prints the rune, the current
  enabled/disabled status, and other appropriate fields from the rule.
  It may be helpful to read the documentation for various kinds of
  rules in order to understand the information printed by this
  command.  For example, the information printed for a linear rule
  might be:
  ~bv[]
    Rune:     (:LINEAR ABC)
    Enabled:  T
    Hyps:     ((CONSP X))
    Concl:    (< (ACL2-COUNT (CAR X)) (ACL2-COUNT X))
    Max-term: (ACL2-COUNT (CAR X))
    Backchain-limit-lst:    (3)
  ~ev[]
  The ~c[hyps] and ~c[concl] fields for this rule are fairly
  self-explanatory, but it is useful to ~pl[linear] to learn about
  maximal terms (which, as one might guess, are stored under
  ``Max-term'').

  Currently, this function does not print congruence rules or
  equivalence rules.

  The expert user might also wish to use ~ilc[find-rules-of-rune].
  ~l[find-rules-of-rune].~/"

  (list 'pr-fn name 'state))

(defmacro pr! (cd)

  ":Doc-Section History

  print rules stored by the command with a given command descriptor~/
  ~bv[]
  Examples:

  :pr! fn ; prints the rules from the definition of fn (including any
          ; :type-prescription rule and :definition rule), as well as all other
          ; rules created by the command that created by fn (which could be
          ; many rules if, for example, fn was defined by an include-book
          ; command).

  :pr! :max ; prints all the rules stored by the most recent command
  ~ev[]~/

  Also ~pl[pr], which is similar but works at the event level
  instead of at the command level.

  ~ilc[Pr] takes one argument, a command descriptor, and prints the rules
  created by the corresponding event.  In each case it prints the
  rune, the current enabled/disabled status, and other appropriate
  fields from the rule.  ~l[pr] for further details.~/"

  (list 'pr!-fn cd 'state))

(defun disabledp-fn-lst (runic-mapping-pairs ens)
  (cond ((null runic-mapping-pairs) nil)
        ((enabled-numep (caar runic-mapping-pairs) ens)
         (disabledp-fn-lst (cdr runic-mapping-pairs) ens))
        (t (cons (cdar runic-mapping-pairs)
                 (disabledp-fn-lst (cdr runic-mapping-pairs) ens)))))

(defun disabledp-fn (name ens wrld)
  (declare (xargs :guard t))
  (cond ((symbolp name)
         (let ((name2 (if (symbolp name)
                          (deref-macro-name name (macro-aliases wrld))
                        name)))
           (cond ((and (not (eq name2 :here))
                       name2
                       (logical-namep name2 wrld))
                  (disabledp-fn-lst (getprop name2 'runic-mapping-pairs nil
                                             'current-acl2-world wrld)
                                    ens))
                 (t (er hard 'disabledp
                        "Illegal call of disabledp on symbolp argument ~x0.  ~
                         See :DOC disabledp."
                        name)))))
        ((runep name wrld)
         (not (enabled-runep name ens wrld)))
        (t (er hard 'disabledp
               "Illegal call of disabledp on non-symbol, non-rune argument ~
                ~x0.  See :DOC disabledp."
               name))))

(defmacro disabledp (name)

  ":Doc-Section Miscellaneous

  determine whether a given name or rune is disabled~/
  ~bv[]
  Examples:

  :disabledp foo   ; returns a list of all disabled runes whose base
                   ; symbol is foo (~pl[rune])
  (disabledp 'foo) ; same as above (i.e., :disabledp foo)
  :disabledp (:rewrite bar . 1) ; returns t if the indicated rune is
                                ; disabled, else nil
  (disabledp (:rewrite bar . 1)); same as immediately above
  ~ev[]~/

  Also ~pl[pr], which gives much more information about the rules associated
  with a given event.

  ~c[Disabledp] takes one argument, an event name (~pl[events]) other than
  ~c[nil] or a ~il[rune].  In the former case it returns the list of disabled
  runes associated with that name, in the sense that the rune's ``base symbol''
  is that name (~pl[rune]) or, if the event named is a ~ilc[defmacro] event,
  then the list of disabled runes associated with the function corresponding to
  that macro name, if any (~pl[macro-aliases-table]).  In the latter case,
  where the argument is a ~il[rune], ~c[disabledp] returns ~c[t] if the rune is
  disabled, and ~c[nil] otherwise.~/"

  `(disabledp-fn ,name (ens state) (w state)))

(defun access-x-rule-rune (x rule)

; Given a rule object, rule, of record type x, we return the :rune of rule.
; This is thus ``(access x rule :rune).''

; Note: We include with every case the rule-class tokens that create this rule
; so that we can search for any such tokens and find this function when adding
; a new, similar, rule-class.

; There is no record object generated only by        ;;; :refinement
;                                                    ;;; :tau-system
  (case x
        (recognizer-tuple                            ;;; :compound-recognizer
         (access recognizer-tuple rule :rune))
        (type-prescription                           ;;; :type-prescription
         (access type-prescription rule :rune))
        (congruence-rule                             ;;; :congruence
                                                     ;;; :equivalence
         (access congruence-rule rule :rune))
        (rewrite-rule                                ;;; :rewrite
                                                     ;;; :meta
                                                     ;;; :definition
         (access rewrite-rule rule :rune))
        (well-founded-relation-rule                  ;;; :well-founded-relation
; No such record type, but we pretend!
         (cddr rule))
        (linear-lemma                                ;;; :linear
         (access linear-lemma rule :rune))
        (forward-chaining-rule                       ;;; :forward-chaining
         (access forward-chaining-rule rule :rune))
        (built-in-clause                             ;;; :built-in-clause
         (access built-in-clause rule :rune))
        (elim-rule                                   ;;; :elim
         (access elim-rule rule :rune))
        (generalize-rule                             ;;; :generalize
         (access generalize-rule rule :rune))
        (induction-rule                              ;;; :induction
         (access induction-rule rule :rune))
        (type-set-inverter-rule                      ;;; :type-set-inverter
         (access type-set-inverter-rule rule :rune))
        (otherwise (er hard 'access-x-rule-rune
                       "Unrecognized rule class, ~x0."
                       x))))

(defun collect-x-rules-of-rune (x rune lst ans)

; Lst is a list of rules of type x.  We collect all those elements of lst
; with :rune rune.

  (cond ((null lst) ans)
        ((equal rune (access-x-rule-rune x (car lst)))
         (collect-x-rules-of-rune x rune (cdr lst)
                                  (add-to-set-equal (car lst) ans)))
        (t (collect-x-rules-of-rune x rune (cdr lst) ans))))

(defun collect-congruence-rules-of-rune-in-geneqv-lst (geneqv-lst rune ans)

; A geneqv is a list of congruence rules.  Geneqv-lst, above, is a list of
; geneqvs.  We scan every congruence rule in geneqv-lst and collect those with
; the :rune rune.

  (cond
   ((null geneqv-lst) ans)
   (t (collect-congruence-rules-of-rune-in-geneqv-lst
       (cdr geneqv-lst) rune
       (collect-x-rules-of-rune 'congruence-rule rune (car geneqv-lst) ans)))))

(defun collect-congruence-rules-of-rune (congruences rune ans)

; The 'congruences property of an n-ary function symbol is a list of tuples,
; each of which is of the form (equiv geneqv1 ... geneqvn), where each geneqvi
; is a list of congruence rules.  Congruences is the 'congruences property of
; some function.  We scan it and collect every congruence rule in it that has
; :rune rune.

  (cond
   ((null congruences) ans)
   (t (collect-congruence-rules-of-rune
       (cdr congruences) rune
       (collect-congruence-rules-of-rune-in-geneqv-lst (cdr (car congruences))
                                                       rune ans)))))

(defun find-rules-of-rune2 (rune sym key val ans)

; (sym key . val) is a member of wrld.  We collect all the rules in val with
; :rune rune.  This function is patterned after info-for-x-rules.

; Wart: If key is 'eliminate-destructors-rule, then val is a single rule, not a
; list of rules.  We handle this case specially below.

; Warning: Keep this function in sync with info-for-x-rules.  In that spirit,
; note that tau rules never store runes and hence are completely ignored
; here, as in info-for-x-rules.

  (let ((token (car rune)))

; As an efficiency, we do not look for rune in places where it cannot occur.
; For example, if token is :elim then there is no point in searching through
; the 'lemmas properties.  In general, each case below insists that token is of
; the appropriate class.  Sometimes there are more than one.  For example, the
; 'lemmas property may contain :rewrite, :definition, and :meta runes, all of
; which are stored as REWRITE-RULEs.

    (cond
     ((eq key 'global-value)
      (case sym
            (well-founded-relation-alist
             (if (eq token :well-founded-relation)
                 (collect-x-rules-of-rune 'well-founded-relation-rule rune
                                          val ans)
                 ans))
            (built-in-clauses
             (if (eq token :built-in-clause)
                 (collect-x-rules-of-rune 'built-in-clause rune val ans)
                 ans))
            (type-set-inverter-rules
             (if (eq token :type-set-inverter)
                 (collect-x-rules-of-rune 'type-set-inverter-rule rune
                                          val ans)
                 ans))
            (recognizer-alist
             (if (eq token :compound-recognizer)
                 (collect-x-rules-of-rune 'recognizer-tuple rune val ans)
                 ans))
            (generalize-rules
             (if (eq token :generalize)
                 (collect-x-rules-of-rune 'generalize-rule rune val ans)
                 ans))
            (otherwise ans)))
     (t
      (case key
            (lemmas
             (if (member-eq token '(:rewrite :meta :definition))
                 (collect-x-rules-of-rune 'rewrite-rule rune val ans)
                 ans))
            (linear-lemmas
             (if (eq token :linear)
                 (collect-x-rules-of-rune 'linear-lemma rune val ans)
                 ans))
            (eliminate-destructors-rule
             (if (eq token :elim)
                 (collect-x-rules-of-rune 'elim-rule rune (list val) ans)
                 ans))
            (congruences
             (if (member-eq token '(:congruence :equivalence))
                 (collect-congruence-rules-of-rune val rune ans)
                 ans))
            (coarsenings

; :Refinement rules add to the 'coarsenings property.  If equiv1 is a
; refinement of equiv2, then equiv2 is a coarsening of equiv1 and the lemma
; establishing that fact adds equiv2 to the 'coarsenings property of equiv1.
; There is no rule object corresponding to this fact.  Hence, even if rune is
; the :refinement rune responsible for adding some equiv2 to this list, we
; won't find a rule object here by the name rune.

; Similar comments apply to :equivalence rules.  They add to the 'coarsenings
; property but no rule object exists.  It should be noted that some congruence
; rules are added by lemmas of class :equivalence and those rules are named by
; :equivalence runes and are found among the 'congruences properties.

             ans)
            (forward-chaining-rules
             (if (eq token :forward-chaining)
                 (collect-x-rules-of-rune 'forward-chaining-rule rune val ans)
                 ans))
            (type-prescriptions
             (if (eq token :type-prescription)
                 (collect-x-rules-of-rune 'type-prescription rune val ans)
                 ans))
            (induction-rules
             (if (eq token :induction)
                 (collect-x-rules-of-rune 'induction-rule rune val ans)
                 ans))
            (otherwise ans))))))

(defun find-rules-of-rune1 (rune props ans)

; Props is a list of triples and can be considered a segment of some wrld.  (It
; is not only because duplicates have been removed.)  We visit every property
; and collect all the rules with :rune rune.

  (cond ((null props) ans)
        ((eq (cddar props) *acl2-property-unbound*)
         (find-rules-of-rune1 rune (cdr props) ans))
        (t (find-rules-of-rune1 rune (cdr props)
                                (find-rules-of-rune2 rune
                                                     (caar props)
                                                     (cadar props)
                                                     (cddar props)
                                                     ans)))))

(defun find-rules-of-rune (rune wrld)

  ":Doc-Section Miscellaneous

  find the rules named rune~/
  ~bv[]
  General Form:
  (find-rules-of-rune rune wrld)
  ~ev[]~/

  This function finds all the rules in ~c[wrld] with ~c[:]~ilc[rune] rune.  It
  returns a list of rules in their internal form (generally as
  described by the corresponding ~c[defrec]).  Decyphering these rules is
  difficult since one cannot always look at a rule object and decide
  what kind of record it is without exploiting many system invariants
  (e.g., that ~c[:]~ilc[rewrite] runes only name rewrite-rules).

  At the moment this function returns ~c[nil] if the rune in question is a
  ~c[:]~ilc[refinement] rune, because there is no object representing
  ~c[:]~ilc[refinement] rules.  (~c[:]~ilc[refinement] rules cause changes in the
  ~c['coarsenings] properties.)  In addition, if the rune is an
  ~c[:]~ilc[equivalence] rune, then congruence rules with that rune will be
  returned ~-[] because ~c[:]~ilc[equivalence] lemmas generate some congruence
  rules ~-[] but the fact that a certain function is now known to be an
  equivalence relation is not represented by any rule object and so no
  such rule is returned.  (The fact that the function is an
  equivalence relation is encoded entirely in its presence as a
  ~c['coarsening] of ~ilc[equal].)"

; Find all the rules in wrld with :rune rune.  We do this by first obtaining
; that segment of wrld consisting of the properties stored by the event
; named by the base symbol of rune.  Then we collect every rule mentioned
; in the segment, provided the rule has :rune rune.

  (declare (xargs :guard (and (plist-worldp wrld)
                              (runep rune wrld))))
  (let ((wrld-tail (decode-logical-name (base-symbol rune) wrld)))
    (find-rules-of-rune1 rune
                         (actual-props
                          (world-to-next-event (cdr wrld-tail))
                          nil
                          nil)
                         nil)))

(defun collect-non-backchain-subclass (rules)

; Rules is a list of REWRITE-RULEs.  We collect all those that are not
; of :subclass 'backchain.

  (cond ((null rules) nil)
        ((eq (access rewrite-rule (car rules) :subclass) 'backchain)
         (collect-non-backchain-subclass (cdr rules)))
        (t (cons (car rules) (collect-non-backchain-subclass (cdr rules))))))

(defun chk-acceptable-monitor (rune expr ctx state)

; We check that rune is a breakable rune and expr is a suitable
; conditional expression.  We either cause an error or return
; the translation of expr.

  (cond
   ((not (runep rune (w state)))
    (er soft ctx "~x0 is not a rune." rune))
   ((not (member-eq (car rune) '(:rewrite :definition)))
    (er soft ctx
        "Only :REWRITE and :DEFINITION runes may be monitored.  We cannot ~
         break ~x0."
        rune))
   (t (er-let*
          ((term (translate-break-condition expr ctx state)))
          (cond
           ((eq (car rune) :rewrite)

; The checks below can be extremely expensive when dealing with a :definition
; rule for a function that is part of a large mutual recursion nest.  We have
; seen the call of actual-props in find-rules-of-rune take over a minute for a
; function defined in a mutual-recursion nest of several thousand functions.
; So we restrict the check to :rewrite rules.

            (let* ((rules (find-rules-of-rune rune (w state)))
                   (bad-rewrite-rules (collect-non-backchain-subclass rules)))

; Observe that we collect all the non-backchain rules but then claim to the
; user that they are all abbreviation rules.  That is because we believe that
; there are only four subclasses of rewrite rules: backchain, abbreviation,
; definition, and meta and the latter two have runes beginning with the tokens
; :definition and :meta instead of :rewrite.

              (pprogn
               (cond
                ((null rules)
                 (prog2$
                  (er hard ctx
                      "Implementation error (please contact the ACL2 ~
                       implementors): Although ~x0 is a runep, ~
                       find-rules-of-rune fails to find any rules for it."
                      rune)
                  state))
                ((equal (length bad-rewrite-rules) (length rules))
                 (warning$ ctx "Monitor"
                           "The rune ~x0 only names ~#1~[a simple ~
                            abbreviation rule~/~n2 simple abbreviation ~
                            rules~].  Monitors can be installed on ~
                            abbreviation rules, but will not fire during ~
                            preprocessing, so you may want to supply the hint ~
                            :DO-NOT '(PREPROCESS); see :DOC hints.  For an ~
                            explanation of what a simple abbreviation rule ~
                            is, see :DOC simple.  Also, see :DOC monitor."
                           rune
                           bad-rewrite-rules
                           (length bad-rewrite-rules)))
                (bad-rewrite-rules
                 (warning$ ctx "Monitor"
                           "Among the ~n0 rules named ~x1 ~#2~[is a simple ~
                            abbreviation rule~/are ~n3 simple abbreviation ~
                            rules~].  Such rules can be monitored, but will ~
                            not fire during preprocessing, so you may want to ~
                            supply the hint :DO-NOT '(PREPROCESS); see :DOC ~
                            hints,  For an explanation of what a simple ~
                            abbreviation rule is, see :DOC simple.  Also, see ~
                            :DOC monitor."
                           (length rules)
                           rune
                           bad-rewrite-rules
                           (length bad-rewrite-rules)))
                (t state))
               (value term))))
           (t (value term)))))))

(defun chk-acceptable-monitors (lst ctx state)

; We check that lst is an acceptable value for the brr-global
; 'brr-monitored-runes.  We return the translation of lst or cause an
; error.

  (cond ((null lst) (value nil))
        ((not (and (consp (car lst))
                   (consp (cdr (car lst)))
                   (null (cddr (car lst)))))
         (er soft ctx
             "Every element of brr-monitored-runes must be a doublet of the ~
              form (rune term) and ~x0 is not."
             (car lst)))
        (t (er-let*
            ((term (chk-acceptable-monitor (car (car lst))
                                              (cadr (car lst))
                                              ctx state))
             (rlst (chk-acceptable-monitors (cdr lst) ctx state)))
            (value (cons (list (car (car lst)) term) rlst))))))

(defun monitor1 (rune form ctx state)

; The list of monitored runes modified by this function is a brr-global.
; Thus, this function should only be evaluated within a wormhole.  The macro
; monitor can be called in either a wormhole state or a normal state.

  (er-let*
   ((term (chk-acceptable-monitor rune form ctx state)))
   (prog2$
    (or (f-get-global 'gstackp state)
        (cw "Note: Enable break-rewrite with :brr t.~%"))
    (pprogn
     (f-put-global 'brr-monitored-runes
                   (put-assoc-equal rune (list term)
                                    (get-brr-global 'brr-monitored-runes
                                                         state))
                   state)
     (value (get-brr-global 'brr-monitored-runes state))))))

(defun unmonitor1 (rune ctx state)
  (cond
   ((assoc-equal rune (get-brr-global 'brr-monitored-runes state))
    (pprogn
     (f-put-global 'brr-monitored-runes
                   (remove1-equal
                    (assoc-equal rune
                                 (get-brr-global 'brr-monitored-runes state))
                    (get-brr-global 'brr-monitored-runes state))
                   state)
     (prog2$
      (cond ((and (f-get-global 'gstackp state)
                  (null (get-brr-global 'brr-monitored-runes state)))
             (cw "Note:  No runes are being monitored.  Disable break-rewrite ~
                  with :brr nil.~%"))
            (t nil))
      (value (get-brr-global 'brr-monitored-runes state)))))
   (t (er soft ctx "~x0 is not monitored." rune))))

(defun monitor-fn (rune expr state)

; If we are not in a wormhole, get into one.  Then we set brr-monitored-runes
; appropriately.  We always print the final value of brr-monitored-runes to the
; comment window and we always return (value :invisible).

  (cond
   ((eq (f-get-global 'wormhole-name state) 'brr)
    (er-progn
     (monitor1 rune expr 'monitor state)
     (prog2$
      (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil)
      (value :invisible))))
   (t (prog2$
       (brr-wormhole
        '(lambda (whs)
           (set-wormhole-entry-code whs :ENTER))
        nil
        `(er-progn
          (monitor1 ',rune ',expr 'monitor state)
          (prog2$
           (cw "~Y01~|" (get-brr-global 'brr-monitored-runes state) nil)
           (value nil)))
        nil)
       (value :invisible)))))

(defun unmonitor-fn (rune ctx state)
  (cond
   ((eq (f-get-global 'wormhole-name state) 'brr)
    (er-progn
     (cond ((eq rune :all)
            (pprogn (f-put-global 'brr-monitored-runes nil state)
                    (value nil)))
           ((and (consp rune)
                 (keywordp (car rune)))
            (unmonitor1 rune ctx state))
           (t (er soft ctx
                  "The only legal arguments to UNMONITOR are runes
                   and :ALL, but ~x0 is neither.  See :DOC unmonitor ~
                   for a more precise explanation of the requirements."
                  rune)))
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
        (cond ((eq ',rune :all)
               (pprogn (f-put-global 'brr-monitored-runes nil state)
                       (value nil)))
              ((and (consp ',rune)
                    (keywordp (car ',rune)))
               (unmonitor1 ',rune ',ctx state))
              (t (er soft ',ctx
                     "The only legal arguments to UNMONITOR are runes ~
                      and :ALL, but ~x0 is neither.  See :DOC ~
                      unmonitor for a more precise explanation of the ~
                      requirements."
                     ',rune)))
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

(defun brr-fn (flg state)
  (cond
   (flg
    (pprogn
     (f-put-global 'gstackp t state)
     (prog2$
      (cw "Use :a! to exit break-rewrite.~|See :DOC set-evisc-tuple to ~
           control suppression of details when printing.~|~%The monitored ~
           runes are:~%")
      (er-progn
       (monitored-runes-fn state)
       (value t)))))
   (t (pprogn (f-put-global 'gstackp nil state)
              (value nil)))))

(defmacro brr (flg)

  ":Doc-Section Break-Rewrite

  to enable or disable the breaking of rewrite rules~/
  ~bv[]
  Example:
  :brr t       ; enable
  :brr nil     ; disable~/

  General Form:
  (brr flg)
  ~ev[]
  where ~c[flg] evaluates to ~c[t] or ~c[nil].  This function modifies
  ~ilc[state] so that the attempted application of certain rewrite rules are
  ``broken.'' ``~c[Brr]'' stands for ``break-rewrite'' and can be thought of as
  a mode with two settings.  The normal mode is ``disabled.''

  When ~c[brr] mode is ``enabled'' the ACL2 rewriter monitors the attempts to
  apply certain rules and advises the user of those attempts by entering an
  interactive wormhole break.  From within this break the user can watch
  selected application attempts.  ~l[break-rewrite].  The user can also
  interact with the system during ~c[brr] breaks via ~ilc[brr-commands].

  The rules monitored are selected by using the ~ilc[monitor] and
  ~ilc[unmonitor] commands.  It is possible to break a rune ``conditionally''
  in the sense that an interactive break will occur only if a specified
  predicate is true of the environment at the time of the attempted
  application.  ~l[monitor] and ~pl[unmonitor].

  Even if a non-empty set of rules has been selected, no breaks will occur
  unless ~c[brr] mode is enabled.  Thus, the first time in a session that you
  wish to monitor a rewrite rule, use ~c[:brr] ~c[t] to enable ~c[brr] mode.
  Thereafter you may select runes to be monitored with ~ilc[monitor] and
  ~ilc[unmonitor] with the effect that whenever monitored rules are tried (and
  their break conditions are met) an interactive break will occur.  Be advised
  that when ~c[brr] mode is enabled the rewriter is somewhat slower than
  normal.  Furthermore, that sluggishness persists even if no runes are
  monitored.  You may regain normal performance ~-[] regardless of what runes
  are monitored ~-[] by disabling ~c[brr] mode with ~c[:brr] ~c[nil].

  Why isn't ~c[brr] mode disabled automatically when no runes are monitored?
  More generally, why does ACL2 have ~c[brr] mode at all?  Why not just test
  whether there are monitored runes?  If you care about the answers,
  ~pl[why-brr].

  BRR Mode and Console Interrupts: If the system is operating in ~c[brr] mode
  and you break into raw Lisp (as by causing a console interrupt or happening
  upon a signalled Lisp error; ~pl[breaks]), you can return to the ACL2
  top-level, outside any ~c[brr] environment, by executing
  ~c[(]~ilc[abort!]~c[)].  Otherwise, the normal way to quit from such a break
  (for example ~c[:q] in GCL, ~c[:reset] in Allegro CL, and ~c[q] in CMU CL)
  will return to the innermost ACL2 read-eval-print loop, which may or may not
  be the top-level of your ACL2 session!  In particular, if the break happens
  to occur while ACL2 is within the ~c[brr] environment (in which it is
  preparing to read ~ilc[brr-commands]), the abort will merely return to that
  ~c[brr] environment.  Upon exiting that environment, normal theorem proving
  is continued (and the ~c[brr] environment may be entered again in response to
  subsequent monitored rule applications).  Before returning to the ~c[brr]
  environment, ACL2 ``cleans up'' from the interrupted ~c[brr] processing.
  However, it is not possible (given the current implementation) to clean up
  perfectly.  This may have two side-effects.  First, the system may
  occasionally print the self-explanatory ``Cryptic BRR Message 1'' (or 2),
  informing you that the system has attempted to recover from an aborted
  ~c[brr] environment.  Second, it is possible that subsequent ~c[brr] behavior
  in that proof will be erroneous because the cleanup was done incorrectly.
  The moral is that you should not trust what you learn from ~c[brr] if you
  have interrupted and aborted ~c[brr] processing during the proof.  These
  issues do not affect the behavior or soundness of the theorem prover."

  `(brr-fn ,flg state))

(deflabel why-brr
  :doc
  ":Doc-Section Miscellaneous

  an explanation of why ACL2 has an explicit ~ilc[brr] mode~/

  Why isn't ~ilc[brr] mode automatically disabled when there are no
  monitored runes?  The reason is that the list of monitored runes is
  kept in a wormhole state.~/

  ~l[wormhole] for more information on wormholes in general.  But
  the fundamental property of the wormhole function is that it is a
  logical ~c[no-op], a constant function that does not take state as an
  argument.  When entering a wormhole, arbitrary information can be
  passed in (including the external state).  That information is used
  to construct a near copy of the external state and that ``wormhole
  state'' is the one with respect to which interactions occur during
  breaks.  But no information is carried by ACL2 out of a wormhole ~-[]
  if that were allowed wormholes would not be logical no-ops.  The
  only information carried out of a wormhole is in the user's head.

  ~ilc[Break-rewrite] interacts with the user in a wormhole state because
  the signature of the ACL2 rewrite function does not permit it to
  modify ~ilc[state].  Hence, only wormhole interaction is possible.  (This
  has the additional desirable property that the correctness of the
  rewriter does not depend on what the user does during interactive
  breaks within it; indeed, it is logically impossible for the user to
  affect the course of ~ilc[rewrite].)

  Now consider the list of monitored runes.  Is that kept in the
  external state as a normal state global or is it kept in the
  wormhole state?  If it is in the external state then it can be
  inspected within the wormhole but not changed.  This is
  unacceptable; it is common to change the ~il[monitor]ed rules as the
  proof attempt progresses, installing monitors when certain rules are
  about to be used in certain contexts.  Thus, the list of monitored
  runes must be kept as a wormhole variable.  Hence, its value cannot
  be determined outside the wormhole, where the proof attempt is
  ongoing.

  This raises another question: If the list of monitored runes is
  unknown to the rewriter operating on the external state, how does
  the rewriter know when to break?  The answer is simple: it breaks
  every time, for every rune, if ~ilc[brr] mode is enabled.  The wormhole is
  entered (silently), computations are done within the wormhole state
  to determine if the user wants to see the break, and if so,
  interactions begin.  For unmonitored runes and runes with false
  break conditions, the silent wormhole entry is followed by a silent
  wormhole exit and the user perceives no break.

  Thus, the penalty for running with ~ilc[brr] mode enabled when there are
  no monitored runes is high: a wormhole is entered on every
  application of every rune and the user is simply unware of it.  The
  user who has finally unmonitored all runes is therefore strongly
  advised to carry this information out of the wormhole and to do ~c[:]~ilc[brr]
  ~c[nil] in the external state when the next opportunity arises.")

(defmacro brr@ (sym)
  ":Doc-Section Break-Rewrite

  to access context sensitive information within ~ilc[break-rewrite]~/
  ~bv[]
  Example:
  (brr@ :target)      ; the term being rewritten
  (brr@ :unify-subst) ; the unifying substitution~/

  General Form:
  (brr@ :symbol)
  ~ev[]
  where ~c[:symbol] is one of the following keywords.  Those marked with
  ~c[*] probably require an implementor's knowledge of the system to use
  effectively.  They are supported but not well documented.  More is
  said on this topic following the table.
  ~bv[]
  :symbol             (brr@ :symbol)
  -------             ---------------------

  :target             the term to be rewritten.  This term is an
                      instantiation of the left-hand side of the
                      conclusion of the rewrite-rule being broken.
                      This term is in translated form!  Thus, if
                      you are expecting (equal x nil) -- and your
                      expectation is almost right -- you will see
                      (equal x 'nil); similarly, instead of (cadr a)
                      you will see (car (cdr a)).  In translated
                      forms, all constants are quoted (even nil, t,
                      strings and numbers) and all macros are
                      expanded.

  :unify-subst        the substitution that, when applied to :target,
                      produces the left-hand side of the rule being
                      broken.  This substitution is an alist pairing
                      variable symbols to translated (!) terms.

  :wonp               t or nil indicating whether the rune was
                      successfully applied.  (brr@ :wonp) returns
                      nil if evaluated before :EVALing the rule.

  :rewritten-rhs      the result of successfully applying the rule
                      or else nil if (brr@ :wonp) is nil.  The result
                      of successfully applying the rule is always a
                      translated (!) term and is never nil.

  :failure-reason     some non-nil lisp object indicating why the rule 
                      was not applied or else nil.  Before the rule is
                      :EVALed, (brr@ :failure-reason) is nil.  After
                      :EVALing the rule, (brr@ :failure-reason) is nil
                      if (brr@ :wonp) is t.  Rather than document the
                      various non-nil objects returned as the failure
                      reason, we encourage you simply to evaluate
                      (brr@ :failure-reason) in the contexts of interest.
                      Alternatively, study the ACL2 function tilde-@-
                      failure-reason-phrase.

  :lemma           *  the rewrite rule being broken.  For example,
                      (access rewrite-rule (brr@ :lemma) :lhs) will
                      return the left-hand side of the conclusion
                      of the rule.

  :type-alist      *  a display of the type-alist governing :target.
                      Elements on the displayed list are of the form
                      (term type), where term is a term and type
                      describes information about term assumed to hold
                      in the current context.  The type-alist may be
                      used to determine the current assumptions, e.g.,
                      whether A is a CONSP.

  :ancestors       *  a stack of frames indicating the backchain history
                      of the current context.  The theorem prover is in
                      the process of trying to establish each hypothesis
                      in this stack.  Thus, the negation of each hypothesis
                      can be assumed false.  Each frame also records the
                      rules on behalf of which this backchaining is being
                      done and the weight (function symbol count) of the
                      hypothesis.  All three items are involved in the
                      heuristic for preventing infinite backchaining.
                      Exception:  Some frames are ``binding hypotheses''
                      (equal var term) or (equiv var (double-rewrite term))
                      that bind variable var to the result of rewriting
                      term.

  :gstack          *  the current goal stack.  The gstack is maintained
                      by rewrite and is the data structure printed as the
                      current ``path.''  Thus, any information derivable
                      from the :path brr command is derivable from gstack.
                      For example, from gstack one might determine that
                      the current term is the second hypothesis of a
                      certain rewrite rule.
  ~ev[]
  In general ~c[brr@-expressions] are used in break conditions, the
  expressions that determine whether interactive breaks occur when
  ~il[monitor]ed ~il[rune]s are applied.  ~l[monitor].  For example, you
  might want to break only those attempts in which one particular term
  is being rewritten or only those attempts in which the binding for
  the variable ~c[a] is known to be a ~ilc[consp].  Such conditions can be
  expressed using ACL2 system functions and the information provided
  by ~c[brr@].  Unfortunately, digging some of this information out of the
  internal data structures may be awkward or may, at least, require
  intimate knowledge of the system functions.  But since conditional
  expressions may employ arbitrary functions and macros, we anticipate
  that a set of convenient primitives will gradually evolve within the
  ACL2 community.  It is to encourage this evolution that ~c[brr@] provides
  access to the ~c[*]'d data."

  (declare (xargs :guard (member-eq sym '(:target
                                          :unify-subst
                                          :wonp
                                          :rewritten-rhs
                                          :failure-reason
                                          :lemma
                                          :type-alist
                                          :ancestors
                                          :gstack))))
  (case sym
        (:target '(get-brr-local 'target state))
        (:unify-subst '(get-brr-local 'unify-subst state))
        (:wonp '(get-brr-local 'wonp state))
        (:rewritten-rhs '(get-brr-local 'rewritten-rhs state))
        (:failure-reason '(get-brr-local 'failure-reason state))
        (:lemma '(get-brr-local 'lemma state)) 
        (:type-alist '(get-brr-local 'type-alist state))
        (:ancestors '(get-brr-local 'ancestors state))
        (otherwise '(get-brr-global 'brr-gstack state))))

(defmacro monitor (rune expr)

  ":Doc-Section Break-Rewrite

  to monitor the attempted application of a rule name~/
  ~bv[]
  Example:
  (monitor '(:rewrite assoc-of-app) 't)
  :monitor (:rewrite assoc-of-app) t
  :monitor (:definition app) (equal (brr@ :target) '(app c d))~/

  General Form:
  (monitor rune term)
  ~ev[]
  where ~c[rune] is a ~il[rune] and ~c[term] is a term, called the ``break
  condition.'' ~c[Rune] must be either a ~c[:rewrite] ~il[rune] or a
  ~c[:definition] ~il[rune].

  When a ~il[rune] is ~il[monitor]ed any attempt to apply it may result in an
  interactive break in an ACL2 ``~il[wormhole] ~il[state].'' There you will get
  a chance to see how the application proceeds.
  ~l[break-rewrite] for a description of the interactive loop
  entered.  Whether an interactive break occurs depends on the value
  of the break condition expression associated with the ~il[monitor]ed
  ~il[rune].

  NOTE: Some ~c[:rewrite] rules are considered ``simple abbreviations'';
  ~pl[simple].  These can be be monitored, but only at certain times during the
  proof.  Monitoring is carried out by code inside the rewriter but
  abbreviation rules may be applied by a special purpose simplifier inside the
  so-called ~em[preprocess] phase of a proof.  If you desire to monitor an
  abbreviation rule, a warning will be printed suggesting that you may want to
  supply the hint ~c[:DO-NOT '(PREPROCESS)]; ~pl[hints].  Without such a hint,
  an abbreviation rule can be applied during the preprocess phase of a proof,
  and no such application will cause an interactive break.

  To remove a ~il[rune] from the list of ~il[monitor]ed ~il[rune]s, use ~c[unmonitor].
  To see which ~il[rune]s are ~il[monitor]ed and what their break conditions
  are, evaluate ~c[(monitored-runes)].

  ~c[Monitor], ~c[unmonitor] and ~c[monitored-runes] are macros that expand
  into expressions involving ~c[state].  While these macros appear to return
  the list of ~il[monitor]ed ~il[rune]s this is an illusion.  They all print
  ~il[monitor]ed ~il[rune] information to the comment window and then return
  error triples (~pl[error-triples]) instructing ~c[ld] to print nothing.  It
  is impossible to return the list of ~il[monitor]ed ~il[rune]s because it
  exists only in the ~il[wormhole] ~il[state] with which you interact when a
  break occurs.  This allows you to change the ~il[monitor]ed ~il[rune]s and
  their conditions during the course of a proof attempt without changing the
  ~il[state] in which the the proof is being constructed.

  Unconditional break points are obtained by using the break condition
  ~c[t].  We now discuss conditional break points.  The break condition,
  ~c[expr], must be a term that contains no free variables other than
  ~c[state] and that returns a single non-~c[state] result.  In fact, the
  result should be ~c[nil], ~c[t], or a true list of commands to be fed to the
  resulting interactive break.  Whenever the system attempts to use
  the associated rule, ~c[expr] is evaluated in the ~il[wormhole] interaction
  ~il[state].  A break occurs only if the result of evaluating ~c[expr] is
  non-~c[nil].  If the result is a true list, that list is appended to the
  front of ~c[standard-oi] and hence is taken as the initial user commands
  issued to the interactive break.

  In order to develop effective break conditions it must be possible
  to access context sensitive information, i.e., information about the
  context in which the ~il[monitor]ed ~il[rune] is being tried.  The ~c[brr@] macro
  may be used in break conditions to access such information as the
  term being rewritten and the current governing assumptions.  This
  information is not stored in the proof ~il[state] but is transferred into
  the ~il[wormhole] ~il[state] when breaks occur.  The macro form is ~c[(brr@ :sym)]
  where ~c[:sym] is one of several keyword symbols, including ~c[:target] (the
  term being rewritten), ~c[:unify-subst] (the substitution that
  instantiates the left-hand side of the conclusion of the rule so
  that it is the target term), and ~c[:type-alist] (the governing
  assumptions).  ~l[brr@].

  For example,
  ~bv[]
  ACL2 !>:monitor (:rewrite assoc-of-app) 
                  (equal (brr@ :target) '(app a (app b c)))
  ~ev[]
  will monitor ~c[(:rewrite assoc-of-app)] but will cause an interactive
  break only when the target term, the term being rewritten, is
  ~c[(app a (app b c))].

  Because break conditions are evaluated in the interaction
  environment, the user developing a break condition for a given ~il[rune]
  can test candidate break conditions before installing them.  For
  example, suppose an unconditional break has been installed on a
  ~il[rune], that an interactive break has occurred and that the user has
  determined both that this particular application is uninteresting
  and that many more such applications will likely occur.  An
  appropriate response would be to develop an expression that
  recognizes such applications and returns ~c[nil].  Of course, the hard
  task is figuring out what makes the current application
  uninteresting.  But once a candidate expression is developed, the
  user can evaluate it in the current context simply to confirm that
  it returns ~c[nil].

  Recall that when a break condition returns a non-~c[nil] true list that
  list is appended to the front of ~c[standard-oi].  For example,
  ~bv[]
  ACL2 !>:monitor (:rewrite assoc-of-app) '(:go)
  ~ev[]
  will cause ~c[(:rewrite assoc-of-app)] to be ~il[monitor]ed and will make
  the break condition be ~c['(:go)].  This break condition always
  evaluates the non-~c[nil] true list ~c[(:go)].  Thus, an interactive break
  will occur every time ~c[(:rewrite assoc-of-app)] is tried.  The break
  is fed the command ~c[:go].  Now the command ~c[:go] causes ~c[break-rewrite] to
  (a) evaluate the attempt to apply the lemma, (b) print the result of
  that attempt, and (c) exit from the interactive break and let the
  proof attempt continue.  Thus, in effect, the above ~c[:monitor] merely
  ``traces'' the attempted applications of the ~il[rune] but never causes
  an interactive break requiring input from the user.

  It is possible to use this feature to cause a conditional break
  where the effective break condition is tested ~st[after] the lemma has
  been tried.  For example:
  ~bv[]
  ACL2 !>:monitor (:rewrite lemma12) 
                  '(:unify-subst
                    :eval$ nil
                    :ok-if (or (not (brr@ :wonp))
                               (not (equal (brr@ :rewritten-rhs) '(foo a))))
                    :rewritten-rhs)
  ~ev[]
  causes the following behavior when ~c[(:rewrite lemma12)] is tried.  A
  break always occurs, but it is fed the commands above.  The first,
  ~c[:unify-subst], causes ~c[break-rewrite] to print out the unifying
  substitution.  Then in response to ~c[:eval$] ~c[nil] the lemma is tried but
  with all ~il[rune]s temporarily ~il[unmonitor]ed.  Thus no breaks will occur
  during the rewriting of the hypotheses of the lemma.  When the
  attempt has been made, control returns to ~c[break-rewrite] (which will
  print the results of the attempt, i.e., whether the lemma was
  applied, if so what the result is, if not why it failed).  The next
  command, the ~c[:ok-if] with its following expression, is a conditional
  exit command.  It means exit ~c[break-rewrite] if either the attempt was
  unsuccessful, ~c[(not (brr@ :wonp))], or if the result of the rewrite is
  any term other than ~c[(foo a)].  If this condition is met, the break is
  exited and the remaining break commands are irrelevant.  If this
  condition is not met then the next command, ~c[:rewritten-rhs], prints
  the result of the application (which in this contrived example is
  known to be ~c[(foo a)]).  Finally, the list of supplied commands is
  exhausted but ~c[break-rewrite] expects more input.  Therefore, it
  begins prompting the user for input.  The end result, then, of the
  above ~c[:monitor] command is that the ~il[rune] in question is elaborately
  traced and interactive breaks occur whenever it rewrites its target
  to ~c[(foo a)].

  We recognize that the above break condition is fairly arcane.  We
  suspect that with experience we will develop some useful idioms.
  For example, it is straightforward now to define macros that monitor
  ~il[rune]s in the ways suggested by the following names:  ~c[trace-rune],
  ~c[break-if-target-is], and ~c[break-if-result-is].  For example, the last
  could be defined as
  ~bv[]
  (defmacro break-if-result-is (rune term)
    `(monitor ',rune
              '(quote (:eval :ok-if
                             (not (equal (brr@ :rewritten-rhs) ',term))))))
  ~ev[]
  (Note however that the submitted term must be in translated form.)

  Since we don't have any experience with this kind of control on
  lemmas we thought it best to provide a general (if arcane) mechanism
  and hope that the ACL2 community will develop the special cases that
  we find most convenient."

  `(monitor-fn ,rune ,expr state))

(defmacro unmonitor (rune)

  ":Doc-Section Break-Rewrite

  to stop monitoring a rule name~/
  ~bv[]
  Examples:
  (unmonitor '(:rewrite assoc-of-app))
  :unmonitor (:rewrite assoc-of-app)
  :unmonitor :all~/

  General Forms:
  (unmonitor rune)
  (unmonitor :all)
  ~ev[]
  Here, ~c[rune] is a ~il[rune] that is currently among those with break points
  installed.  This function removes the break.

  Subtle point:  Because you may want to unmonitor a ``~il[rune]'' that is
  no longer a ~il[rune] in the current ACL2 ~il[world], we don't actually check
  this about ~il[rune].  Instead, we simply check that ~il[rune] is a ~c[consp]
  beginning with a ~c[keywordp].  That way, you'll know you've made a
  mistake if you try to ~c[:unmonitor binary-append] instead of
  ~c[:unmonitor (:definition binary-append)], for example."

  `(unmonitor-fn ,rune 'unmonitor state))

(defmacro monitored-runes ()

  ":Doc-Section Break-Rewrite

  print the ~il[monitor]ed ~il[rune]s and their break conditions~/
  ~bv[]
  Example and General Form:
  :monitored-runes
  ~ev[]~/

  This macro prints a list, each element of which is of the form
  ~c[(rune expr)], showing each ~il[monitor]ed ~il[rune] and its current break
  condition."

  `(monitored-runes-fn state))

(defun proceed-from-brkpt1 (action runes ctx state)

; Action may be 
; silent - exit brr with no output except the closing parenthesis
; print -  exit brr after printing results of attempted application
; break -  do not exit brr

; Runes is allegedly either t or a list of runes to be used as brr-monitored-runes
; after pairing every rune with *t*.  If it is t, it means use the same
; brr-monitored-runes.  Otherwise, we check that they are all legal.  If not, we
; warn and do not exit.  We may wish someday to provide the capability of
; proceeding with conditions other than *t* on the various runes, but I haven't
; seen a nice design for that yet.

  (er-let*
   ((lst (if (eq runes t)
             (value nil)
             (chk-acceptable-monitors (pairlis-x2 runes (list *t*))
                                      ctx state))))
   (pprogn
    (put-brr-local 'saved-standard-oi
                   (f-get-global 'standard-oi state)
                   state)
    (put-brr-local 'saved-brr-monitored-runes
                   (get-brr-global 'brr-monitored-runes state)
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

  ":Doc-Section Break-Rewrite

  conditional exit from ~c[break-rewrite]~/
  ~bv[]
  Example Form:
  :ok-if (null (brr@ :wonp))~/

  General Form:
  :ok-if expr
  ~ev[]
  where ~c[expr] is a term involving no free variables other than ~c[state] and
  returning one non-~c[state] result which is treated as Boolean.  This form is
  intended to be executed from within ~c[break-rewrite]
  (~pl[break-rewrite]).

  Consider first the simple situation that the ~c[(ok-if term)] is a command
  read by ~c[break-rewrite].  Then, if the term is non-~c[nil],
  ~c[break-rewrite] exits and otherwise it does not.

  More generally, ~c[ok-if] returns an ACL2 error triple
  ~c[(mv erp val state)].  (~l[ld] or ~pl[programming-with-state] for more on
  error triples.)  If any form being evaluated as a command by
  ~c[break-rewrite] returns the triple returned by ~c[(ok-if term)] then the
  effect of that form is to exit ~il[break-rewrite] if term is non-~c[nil].
  Thus, one might define a function or macro that returns the value of
  ~c[ok-if] expressions on all outputs and thus create a convenient new way to
  exit ~c[break-rewrite].

  The exit test, ~c[term], generally uses ~c[brr@] to access context sensitive
  information about the attempted rule application.  ~l[brr@].  ~c[Ok-if] is
  useful inside of command sequences produced by break conditions.
  ~l[monitor].  ~c[:ok-if] is most useful after an ~c[:eval] command has caused
  ~c[break-rewrite] to try to apply the rule because in the resulting break
  environment ~c[expr] can access such things as whether the rule succeeded, if
  so, what term it produced, and if not, why.  There is no need to use
  ~c[:ok-if] before ~c[:eval]ing the rule since the same effects could be
  achieved with the break condition on the rule itself.  Perhaps we should
  replace this concept with ~c[:eval-and-break-if]?  Time will tell."

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

 ; Then when we (conceptually at least) functionally instantiate a :meta or
; :clause-processor rule using a functional substitution of the form ((evl
; evl') (evl-list evl'-list)), we need to know that the above proof obligations
; are met.

; ACL2 insists (in function chk-evaluator-use-in-rule) that the evaluator of a
; proposed :meta or :clause-processor rule is not ancestral in any defaxiom or
; in the definition of, or constraint on, the rule's metafunctions, nor is the
; evaluator ancestral in meta-extract-global-fact and
; meta-extract-contextual-fact if they are used in the rule.  Thus, when we
; imagine functionally instantiating the rule as discussed above, at the point
; of its application, the only relevant theorems for (i) above are the
; constraints on the evaluator, and there are no relevant theorems for (ii)
; above.  We can use our usual computation of "ancestral", which does not
; explore below functions that are not instantiablep, since (presumably!)
; non-instantiablep functions are primitives in which no evaluator functions is
; ancestral.

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

(defun defaxiom-fn (name term state rule-classes doc event-form)

; Important Note: Don't change the formals of this function without reading the
; *initial-event-defmacros* discussion in axioms.lisp.

  (when-logic
   "DEFAXIOM"
   (with-ctx-summarized
    (if (output-in-infixp state) event-form (cons 'defaxiom name))
    (let ((wrld (w state))
          (ens (ens state))
          (event-form (or event-form
                          (list* 'defaxiom name term
                                 (append (if (not (equal rule-classes
                                                         '(:REWRITE)))
                                             (list :rule-classes rule-classes)
                                           nil)
                                         (if doc
                                             (list :doc doc)
                                           nil))))))
      (er-progn
       (chk-all-but-new-name name ctx nil wrld state)
       (er-let* ((tterm (translate term t t t ctx wrld state))
; known-stobjs = t (stobjs-out = t)
                 (supporters (defaxiom-supporters tterm name ctx wrld state))
                 (classes (translate-rule-classes name rule-classes tterm ctx
                                                  ens wrld state)))
         (cond
          ((redundant-theoremp name tterm classes wrld)
           (stop-redundant-event ctx state))
          (t

; Next we implement Defaxiom Restriction for Defattach from The Essay on
; Defattach: no ancestor (according to the transitive closure of the
; immediate-supporter relation) of a defaxiom event has an attachment.  Since
; this is all about logic, we remove guard-holders from term before doing this
; check.

           (let ((attached-fns
                  (attached-fns (canonical-ancestors-lst
                                 (all-ffn-symbs (remove-guard-holders tterm)
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
                    ((ttree1 (chk-acceptable-rules name classes ctx ens wrld state))
                     (wrld1 (chk-just-new-name name 'theorem nil ctx wrld state))
                     (doc-pair (translate-doc name doc ctx state))
                     (ttree3
                      (cond ((ld-skip-proofsp state)
                             (value nil))
                            (t 
                             (prove-corollaries name tterm classes ens wrld1 ctx
                                                state)))))
                  (let* ((wrld2
                          (update-doc-database
                           name doc doc-pair
                           (add-rules name classes tterm term ens wrld1 state)))
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
                                     state)))))))))))))))))


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

;; RAG - this trio of functions adds the hypothesis "(standardp x)"
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

(defun defthm-fn1 (name term state
                        rule-classes
                        instructions
                        hints
                        otf-flg
                        doc
                        event-form
                        #+:non-standard-analysis std-p)
  (with-ctx-summarized
   (if (output-in-infixp state) event-form (cons 'defthm name))
   (let ((wrld (w state))
         (ens (ens state))
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
                                          nil)
                                        (if doc
                                            (list :doc doc)
                                          nil)))))
         (ld-skip-proofsp (ld-skip-proofsp state)))
     (pprogn
      (warn-on-inappropriate-defun-mode ld-skip-proofsp event-form ctx state)
      #+acl2-par
      (erase-acl2p-checkpoints-for-summary state)
      (with-waterfall-parallelism-timings
       name
       (er-progn
        (chk-all-but-new-name name ctx nil wrld state)
        (er-let*
         ((tterm0 (translate term t t t ctx wrld state))
; known-stobjs = t (stobjs-out = t)
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

           (translate-rule-classes name rule-classes tterm0 ctx ens wrld
                                   state)))
         (cond
          ((redundant-theoremp name tterm0 classes wrld)
           (stop-redundant-event ctx state))
          (t
           (enforce-redundancy
            event-form ctx wrld
            (er-let*
             ((ttree1 (chk-acceptable-rules name classes ctx ens wrld
                                            state))
              (wrld1 (chk-just-new-name name 'theorem nil ctx wrld state)))
             (er-let*
              ((instructions (if (or (eq ld-skip-proofsp 'include-book)
                                     (eq ld-skip-proofsp 'include-book-with-locals)
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
               (doc-pair (translate-doc name doc ctx state))
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
; proof-checker, and then absent-mindedly somehow suffixed "-std" on to the
; car, defthm, of that form.

                                   (er soft ctx
                                       ":INSTRUCTIONS are not supported for ~
                                        defthm-std events.")
                                 (value nil))
                               (proof-checker name term
                                              tterm classes instructions
                                              wrld1 state)))
                             (t (prove tterm
                                       (make-pspv ens wrld1
                                                  :displayed-goal term
                                                  :otf-flg otf-flg)
                                       hints ens wrld1 ctx state))))
               (ttree3 (cond (ld-skip-proofsp (value nil))
                             (t (prove-corollaries name tterm0 classes ens wrld1
                                                   ctx state)))))
              (let ((wrld2
                     (update-doc-database
                      name doc doc-pair
                      (add-rules name classes tterm0 term ens wrld1 state)))
                    (ttree4 (cons-tag-trees ttree1
                                            (cons-tag-trees ttree2 ttree3))))
                (er-progn
                 (chk-assumption-free-ttree ttree4 ctx state)
                 (print-rule-storage-dependencies name ttree1 state)
                 (install-event name
                                event-form
                                'defthm
                                name
                                ttree4
                                nil :protect ctx wrld2
                                state)))))))))))))))

(defun defthm-fn (name term state
                       rule-classes
                       instructions
                       hints
                       otf-flg
                       doc
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
     doc
     event-form
     #+:non-standard-analysis std-p)))

(defmacro thm (term &key hints otf-flg doc)

  ":Doc-Section Other

  prove a theorem~/
  ~bv[]
  Example:
  (thm (equal (app (app a b) c)
              (app a (app b c))))
  ~ev[]
  Also ~pl[defthm].  Unlike ~ilc[defthm], ~c[thm] does not create an
  event; it merely causes the theorem prover to attempt a proof.~/

  ~bv[]
  General Form:
  (thm term
       :hints        hints
       :otf-flg      otf-flg
       :doc          doc-string)
  ~ev[]
  where ~c[term] is a term alleged to be a theorem, and ~ilc[hints],
  ~ilc[otf-flg] and ~ilc[doc-string] are as described in the corresponding
  ~c[:]~ilc[doc] entries.  The three keyword arguments above are all
  optional.~/"

  (list 'thm-fn
        (list 'quote term)
        'state
        (list 'quote hints)
        (list 'quote otf-flg)
        (list 'quote doc)))

(defun thm-fn (term state hints otf-flg doc)
  (er-progn
   (with-ctx-summarized
    (if (output-in-infixp state)
        (list* 'THM term (if (or hints otf-flg doc) '(irrelevant) nil))
        "( THM ...)")
    (let ((wrld (w state))
          (ens (ens state)))
      (er-let* ((hints (translate-hints+ 'thm
                                         hints
                                         (default-hints wrld)
                                         ctx wrld state))
                (doc-pair (translate-doc nil doc ctx state)))
               (er-let* ((tterm (translate term t t t ctx wrld state))
; known-stobjs = t (stobjs-out = t)
                         (ttree (prove tterm
                                       (make-pspv ens wrld
                                                  :displayed-goal term
                                                  :otf-flg otf-flg)
                                       hints ens wrld ctx state)))
                        (value nil)))))
   (pprogn (io? prove nil state
                nil
                (fms "Proof succeeded.~%" nil
                     (proofs-co state) state nil))
           (value :invisible))))

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

(defun gen-new-name-in-package-of-symbol1 (char-lst cnt pkgsym wrld)

; This function generates a symbol in the same package as pkgsym that
; is guaranteed to be a new-namep in wrld.  We form a symbol by
; concatenating char-lst and the decimal representation of the natural
; number cnt (separated by a hyphen).  Clearly, for some sufficiently
; large cnt that symbol is a new name.

  (let ((sym (intern-in-package-of-symbol
              (coerce
               (append char-lst
                       (cons #\- (explode-nonnegative-integer cnt 10 nil)))
               'string)
              pkgsym)))
    (cond ((new-namep sym wrld)
           sym)
          (t
           (gen-new-name-in-package-of-symbol1 char-lst (1+ cnt) pkgsym
                                               wrld)))))

(defun gen-new-name-in-package-of-symbol (sym pkgsym wrld)

; We generate a symbol, sym', in the same package as pkgsym, such that
; (new-namep sym' wrld).  If sym itself will not do, we start trying
; the extension of sym with successive integers, e.g., sym-0, sym-1,
; sym-2, ...

  (let ((sym1 (if (equal (symbol-package-name sym)
                         (symbol-package-name pkgsym))
                  sym
                  (intern-in-package-of-symbol
                   (symbol-name sym)
                   pkgsym))))
    (cond ((new-namep sym1 wrld) sym1)
          (t (gen-new-name-in-package-of-symbol1
              (coerce (symbol-name sym) 'list)
              0
              pkgsym
              wrld)))))

(defmacro defequiv (equiv
                    &key (rule-classes '(:EQUIVALENCE))
                    instructions
                    hints
                    otf-flg
                    event-name
                    doc)

  ":Doc-Section Events

  prove that a function is an ~il[equivalence] relation~/
  ~bv[]
  Example:
  (defequiv set-equal)

  is an abbreviation for
  (defthm set-equal-is-an-equivalence
    (and (booleanp (set-equal x y))
         (set-equal x x)
         (implies (set-equal x y) (set-equal y x))
         (implies (and (set-equal x y)
                       (set-equal y z))
                  (set-equal x z)))
    :rule-classes (:equivalence))
  ~ev[]
  ~l[equivalence].~/
  ~bv[]
  General Form:
  (defequiv fn
    :rule-classes rule-classes
    :instructions instructions
    :hints hints
    :otf-flg otf-flg
    :event-name event-name
    :doc doc)
  ~ev[]
  where ~c[fn] is a function symbol of arity 2, ~c[event-name], if supplied,
  is a symbol, and all other arguments are as specified in the
  documentation for ~ilc[defthm].  The ~c[defequiv] macro expands into a call
  of ~c[defthm].  The name of the ~c[defthm] is ~c[fn-is-an-equivalence], unless
  ~c[event-name] is supplied, in which case ~c[event-name] is the name used.
  The term generated for the ~c[defthm] event states that ~c[fn] is Boolean,
  reflexive, symmetric, and transitive.  The rule-class
  ~c[:equivalence] is added to the ~il[rule-classes] specified, if it is not
  already there.  All other arguments to the generated ~c[defthm] form
  are as specified by the other keyword arguments above."

  `(defthm ,(or event-name
                (intern-in-package-of-symbol
                 (coerce (packn1 (list equiv "-IS-AN-EQUIVALENCE")) 'string)
                 equiv))
     ,(equivalence-relation-condition equiv)
     :rule-classes
     ,(extend-rule-classes :equivalence rule-classes)
     ,@(if instructions (list :instructions instructions) nil)
     ,@(if hints (list :hints hints) nil)
     ,@(if otf-flg (list :otf-flg otf-flg) nil)
     ,@(if doc (list :doc doc) nil)))

(defmacro defrefinement (equiv1 equiv2
                                &key (rule-classes '(:REFINEMENT))
                                instructions
                                hints
                                otf-flg
                                event-name
                                doc)

  ":Doc-Section Events

  prove that ~c[equiv1] refines ~c[equiv2]~/
  ~bv[]
  Example:
  (defrefinement equiv1 equiv2)

  is an abbreviation for
  (defthm equiv1-refines-equiv2
    (implies (equiv1 x y) (equiv2 x y))
    :rule-classes (:refinement))
  ~ev[]
  ~l[refinement].~/
  ~bv[]
  General Form:
  (defrefinement equiv1 equiv2
    :rule-classes rule-classes
    :instructions instructions
    :hints hints
    :otf-flg otf-flg
    :event-name event-name
    :doc doc)
  ~ev[]
  where ~c[equiv1] and ~c[equiv2] are known ~il[equivalence] relations,
  ~c[event-name], if supplied, is a symbol and all other arguments are as
  specified in the documentation for ~ilc[defthm].  The ~c[defrefinement]
  macro expands into a call of ~c[defthm].  The name supplied is
  ~c[equiv1-refines-equiv2], unless ~c[event-name] is supplied, in which case
  it is used as the name.  The term supplied states that ~c[equiv1]
  refines ~c[equiv2].  The rule-class ~c[:refinement] is added to the
  ~c[rule-classes] specified, if it is not already there.  All other
  arguments to the generated ~c[defthm] form are as specified by the other
  keyword arguments above."

  `(defthm
     ,(or event-name
          (intern-in-package-of-symbol
           (coerce (packn1 (list equiv1 "-REFINES-" equiv2)) 'string)
           equiv1))
     (implies (,equiv1 x y) (,equiv2 x y))
     :rule-classes
     ,(extend-rule-classes :REFINEMENT rule-classes)
     ,@(if instructions (list :instructions instructions) nil)
     ,@(if hints (list :hints hints) nil)
     ,@(if otf-flg (list :otf-flg otf-flg) nil)
     ,@(if doc (list :doc doc) nil)))

(defmacro defcong (&whole x
                          equiv1 equiv2 fn-args k
                          &key (rule-classes '(:CONGRUENCE))
                          instructions
                          hints
                          otf-flg
                          event-name
                          doc)

  ":Doc-Section Events

  prove ~il[congruence] rule~/
  ~bv[]
  ~c[Defcong] is used to prove that one ~il[equivalence] relation preserves
  another in a given argument position of a given function.
  Example:
  (defcong set-equal iff (memb x y) 2)

  is an abbreviation for
  (defthm set-equal-implies-iff-memb-2
    (implies (set-equal y y-equiv)
             (iff (memb x y) (memb x y-equiv)))
    :rule-classes (:congruence))
  ~ev[]
  ~l[congruence] and also ~pl[equivalence].~/
  ~bv[]
  General Form:
  (defcong equiv1 equiv2 term k
    :rule-classes rule-classes
    :instructions instructions
    :hints hints
    :otf-flg otf-flg
    :event-name event-name
    :doc doc)
  ~ev[]
  where ~c[equiv1] and ~c[equiv2] are known ~il[equivalence] relations, ~c[term] is a
  call of a function ~c[fn] on the correct number of distinct variable
  arguments ~c[(fn x1 ... xn)], ~c[k] is a positive integer less than or equal
  to the arity of ~c[fn], and other arguments are as specified in the
  documentation for ~ilc[defthm].  The ~c[defcong] macro expands into a call
  of ~ilc[defthm].  The name of the ~ilc[defthm] event is
  ~c[equiv1-implies-equiv2-fn-k] unless an ~c[:event-name] keyword argument is
  supplied for the name.  The term of the theorem is
  ~bv[]
  (implies (equiv1 xk yk)
           (equiv2 (fn x1... xk ...xn)
                   (fn x1... yk ...xn))).
  ~ev[]
  The rule-class ~c[:]~ilc[congruence] is added to the ~ilc[rule-classes] specified,
  if it is not already there.  All other arguments to the generated
  ~ilc[defthm] form are as specified by the keyword arguments above."

  (cond
   ((not (and (symbolp equiv1)
              (symbolp equiv2)
              (integerp k)
              (< 0 k)
              (symbol-listp fn-args)
              (no-duplicatesp-equal (cdr fn-args))
              (< k (length fn-args))))
    `(er soft 'defcong
         "The form of a defcong event is (defcong equiv1 equiv2 term k ...), ~
          where equiv1 and equiv2 are symbols and k is a positive integer less ~
          than the length of term, where term should be a call of a function ~
          symbol on distinct variable arguments.  However, ~x0 does not have ~
          this form.  See :DOC defcong."
         ',x))
   (t
    (let ((sym (if (equal (symbol-package-name equiv1)
                          *main-lisp-package-name*)
                   (pkg-witness "ACL2")
                 equiv1)))
      `(defthm
         ,(or event-name
              (intern-in-package-of-symbol
               (coerce (packn1 (list equiv1 "-IMPLIES-"
                                     equiv2 "-" (car fn-args) "-" k)) 'string)
               sym))
         ,(let ((arg-k-equiv (intern-in-package-of-symbol
                              (coerce (packn1 (list (nth k fn-args) '-equiv))
                                      'string)
                              sym)))
            `(implies (,equiv1 ,(nth k fn-args)
                               ,arg-k-equiv)
                      (,equiv2 ,fn-args
                               ,(putnth arg-k-equiv k fn-args))))
         :rule-classes
         ,(extend-rule-classes :CONGRUENCE rule-classes)
         ,@(if instructions (list :instructions instructions) nil)
         ,@(if hints (list :hints hints) nil)
         ,@(if otf-flg (list :otf-flg otf-flg) nil)
         ,@(if doc (list :doc doc) nil))))))
