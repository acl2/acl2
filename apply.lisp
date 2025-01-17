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

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

; See the Essay on the APPLY$ Integration in apply-prim.lisp for an overview.

; Outline

; 1. Badges
;    Partially define BADGE, which returns the badge of a symbol.  By
;    ``partially define'' we mean ``define in terms of a constrained
;    function.''

; 2. Tameness
;    Partially define tameness: tame lambdas, tame expressions, tame functions,
;    lists of tame things, in terms of BADGE.

; 3. Definition of APPLY$ and EV$
;    Partially define APPLY$ and EV$.

; 4. Executable Versions of BADGE and TAMEP
;    Define :PROGRAM mode functions to recover the badge of a previously
;    warranted function and to determine whether expressions, etc., are tame.
;    These functions will be used by defwarrant to infer badges which
;    maintains a data structure containing previously inferred badges.

; 5. BADGER and the Badge-Table
;    Define the :PROGRAM mode function BADGER, which infers the badge (if any)
;    of a defined function.  The key routine in BADGER is a :PROGRAM mode
;    iterative inference mechanism called GUESS-ILKS-ALIST.

; 6. Essay on CHECK-ILKS
;    For purposes of reassurance only, we locally convert GUESS-ILKS-ALIST to a
;    :LOGIC mode function and prove that when it returns non-erroneously the
;    badge has certain key properties, (b)-(e), which are enumerated when we
;    discuss BADGER.  These properties are not immediately obvious from the
;    defun of GUESS-ILKS-ALIST because it is iterative and is full of error
;    messages.  To state this theorem we will define the :LOGIC mode function
;    CHECK-ILKS.  But the sources and the model differ in when they they do
;    this.  In the sources, we just leave the essay to remind us that
;    guess-ilks-alist is known to imply properties (b)-(e) and we don't
;    actually define CHECK-ILKS.  That is done during :acl2-devel, during
;    certification of books/system/apply.  In the model, we define CHECK-ILKS
;    and do the proof, but only locally.

; 7. Functional Equivalence
;    Define the functional equivalence relation and prove that it is a
;    congruence relation for APPLY$.  Defwarrant will prove the appropriate
;    congruence rules for each :FN formal of newly badged functions.

; 8. DEFWARRANT and DEFBADGE
;    Define DEFWARRANT and DEFBADGE.

; 9. DEFUN$
;    Define DEFUN$.

; Historical Note:  Once upon a time we had

;    10. The LAMB Hack
;        Define (LAMB vars body) to be `(LAMBDA ,vars ,body) to provide a
;        rewrite target for functional-equivalence lemmas.  Since ACL2 doesn't
;        rewrite constants, we won't even try to simplify a lambda object.  We
;        are not satisfied with the treatment of functional equivalence yet and
;        LAMB is sort of a reminder and placeholder for future work.

; However, we have removed that from the sources because we are not yet
; convinced it is a good way to address the problem of rewriting equivalent
; lambda objects.  We plan to experiment with solutions in the user-maintained
; books.  As of Version_8.0, our best shot is in books/projects/apply/base.lisp
; (formerly apply-lemmas.lisp), but this may change.

; The next two items are not reflected in the model except as noted below.

; 11. The Defattach
;     We attach ``magic'' functions to badge-userfn and apply$-userfn to
;     support top-level evaluation of ground apply$ expressions.  These magic
;     functions are defined in the source file apply-raw.lisp.  This is done in
;     the ACL2 sources but not in the model of apply$.  (However, other files
;     in the model work demonstrate the attachments and carry out the requisite
;     proofs.)

; 12. Loop$ Scions
;     Define the loop$ scions.  See the Essay on Loop$ in translate.lisp.
;     (This is not done in the model, just the sources.)

; Note: This entire file is processed only in pass 2, fundamentally because
; apply$-primp and apply$-prim are only defined in pass 2.

(when-pass-2

; -----------------------------------------------------------------
; 1. Badges

(defun badge (fn)
  (declare (xargs :guard t

; Badge, apply$-primp, and apply$ all come up in :program mode in #+acl2-devel
; builds.  These all depend on functions in *system-verify-guards-alist-1*,
; which are in :program mode in #+acl2-devel builds (see the discussion in
; *system-verify-guards-alist*).

                  :mode :program))
  (cond
   ((apply$-primp fn) (badge-prim fn))
   ((eq fn 'BADGE) *generic-tame-badge-1*)
   ((eq fn 'TAMEP) *generic-tame-badge-1*)
   ((eq fn 'TAMEP-FUNCTIONP) *generic-tame-badge-1*)
   ((eq fn 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*)
   ((eq fn 'APPLY$) *apply$-badge*)
   ((eq fn 'EV$) *ev$-badge*)
; Otherwise, badge is undefined unless a warrant tells us what it is.
   (t (badge-userfn fn))))

#-acl2-devel
(in-theory (disable apply$-primp badge-prim))

; -----------------------------------------------------------------
; 2. Tameness

; These functions are defined for speed, not clarity.  Aside from the obvious
; logical requirements of tameness -- roughly speaking, every function is
; either tame or is tame when supplied with quoted tame functions in the right
; argument positions.  We want (tamep x) to imply that x is either a symbol or
; a true-listp and to imply that every function call in x is supplied with the
; right number of arguments (at least with respect to the arities reported by
; badge), and we want tamep guard verified with a guard of t.

(defabbrev tamep-lambdap (fn)

; Fn is allegedly a lambda object.  We know it's a consp!  We check that it has
; just enough structure to allow guard checking of the tamep clique.  This does
; not actually assure us that the lambda object is well formed.  We don't
; check, for example, that the lambda formals are distinct or that the
; lambda-body is a termp with no other free vars.  The weakness of this
; definition just means that apply$ and ev$ assign meaning to some lambda
; object applications that ACL2 would reject.  That's ok as long as we don't
; try to evaluate those applications directly, e.g., by compiling them.
; Finally, we define this as an abbreviation because we use it several times in
; the tamep clique and don't want to introduce another function into the mutual
; recursion.

; See executable-tamep-lambdap for a discussion of an executable version of
; this ``function,'' including an equivalent alternative definition using
; case-match that is perhaps more perspicuous.

; This function is one of the ways of recognizing a lambda object.  See the end
; of the Essay on Lambda Objects and Lambda$ for a discussion of the various
; recognizers and their purposes.

  (and (lambda-object-shapep fn)
       (symbol-listp (lambda-object-formals fn))
       (tamep (lambda-object-body fn))))

(mutual-recursion

(defun tamep (x)
  (declare (xargs :measure (acl2-count x)
                  :guard t
                  :mode :program))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((bdg (badge (car x))))
           (cond
            ((null bdg) nil)
            ((eq (access apply$-badge bdg :ilks) t)
             (suitably-tamep-listp (access apply$-badge bdg :arity)
                                   nil
                                   (cdr x)))
            (t (suitably-tamep-listp (access apply$-badge bdg :arity)
                                     (access apply$-badge bdg :ilks)
                                     (cdr x))))))
        ((consp (car x))
         (let ((fn (car x)))
           (and (tamep-lambdap fn)
                (suitably-tamep-listp (length (cadr fn))
; Given (tamep-lambdap fn), (cadr fn) = (lambda-object-formals fn).
                                      nil
                                      (cdr x)))))
        (t nil)))

(defun tamep-functionp (fn)
  (declare (xargs :measure (acl2-count fn)
                  :guard t))
  (if (symbolp fn)
      (let ((bdg (badge fn)))
        (and bdg (eq (access apply$-badge bdg :ilks) t)))
    (and (consp fn)
         (tamep-lambdap fn))))

(defun suitably-tamep-listp (n flags args)

; We take advantage of the fact that (car nil) = (cdr nil) = nil.

  (declare (xargs :measure (acl2-count args)
                  :guard (and (natp n)
                              (true-listp flags))))
  (cond
   ((zp n) (null args))
   ((atom args) nil)
   (t (and
       (let ((arg (car args)))
         (case (car flags)
           (:FN
            (and (consp arg)
                 (eq (car arg) 'QUOTE)
                 (consp (cdr arg))
                 (null (cddr arg))
                 (tamep-functionp (cadr arg))))
           (:EXPR
            (and (consp arg)
                 (eq (car arg) 'QUOTE)
                 (consp (cdr arg))
                 (null (cddr arg))
                 (tamep (cadr arg))))
           (otherwise
            (tamep arg))))
       (suitably-tamep-listp (- n 1) (cdr flags) (cdr args))))))
)

; -----------------------------------------------------------------
; 3. Definition of APPLY$ and EV$

(mutual-recursion

(defun apply$ (fn args)
  (declare (xargs :guard (apply$-guard fn args)
                  :guard-hints (("Goal" :do-not-induct t))
                  :mode :program))
  (cond
   ((consp fn)
    (apply$-lambda fn args))
   ((apply$-primp fn)
    (apply$-prim fn args))
   ((eq fn 'BADGE)
    (badge (car args)))
   ((eq fn 'TAMEP)
    (tamep (car args)))
   ((eq fn 'TAMEP-FUNCTIONP)
    (tamep-functionp (car args)))
   ((eq fn 'SUITABLY-TAMEP-LISTP)
    (ec-call (suitably-tamep-listp (car args) (cadr args) (caddr args))))
   ((eq fn 'APPLY$)

; The tamep-functionp test below prevents us from APPLY$ing 'APPLY$ except to
; tame functions.  In particular, you can't apply$ 'apply$ to 'apply$.  We
; discuss some ramifications of this in the Essay on Applying APPLY$ below.  A
; cheaper version of this test that works (in the sense that allows both the
; termination and guard proofs) would be (if (symbolp (car args)) (not
; (member-eq (car args) '(apply$ ev$))) (consp (car args))) though that is less
; succinct and might actually ruin the doppelganger construction in the model
; (we haven't tried) because in that construction there are other symbols
; besides APPLY$ and EV$ you can't apply.  But the reason we keep the full
; blown tamep-functionp test is more aesthetic: it makes the tameness
; conditions in the ``warrant for apply$'' (which doesn't actually exist but
; which is embodied in the lemma apply$-APPLY$ proved in
; books/projects/apply/base.lisp) exactly analogous to the tameness conditions
; for user-defined mapping functions like COLLECT.  There is a similar
; ``warrant for ev$'' embodied in apply$-EV$.

    (if (tamep-functionp (car args))
        (ec-call (APPLY$ (car args) (cadr args)))
      (untame-apply$ fn args)))
   ((eq fn 'EV$)
    (if (tamep (car args))
        (EV$ (car args) (cadr args))
      (untame-apply$ fn args)))
   (t (apply$-userfn fn args))))

(defun apply$-lambda (fn args)

; This is the logical definition of apply$-lambda, which is evaluated under the
; superior call of when-pass-2.  Keep this in sync with the raw Lisp
; definition, which is in apply-raw.lisp.

  (declare (xargs :guard (apply$-lambda-guard fn args)
                  :guard-hints (("Goal" :do-not-induct t))))
  (apply$-lambda-logical fn args))

(defun ev$ (x a)
  (declare (xargs :guard t))
  (cond
   ((not (tamep x))
    (untame-ev$ x a))
   ((variablep x)
    (ec-call (cdr (ec-call (assoc-equal x a)))))
   ((fquotep x)
    (cadr x))
   ((eq (car x) 'if)
    (if (ev$ (cadr x) a)
        (ev$ (caddr x) a)
      (ev$ (cadddr x) a)))
   ((eq (car x) 'APPLY$)

; Note: the (not (tamep x)) test at the top of this cond is critical to the
; measure of (cadr (cadr x)) being smaller than that of x: we need to know that
; (cdr x) is a consp and it is if x is tamep and starts with 'apply$!.

    (apply$ 'APPLY$
            (list (cadr (cadr x)) (EV$ (caddr x) a))))
   ((eq (car x) 'EV$)
    (apply$ 'EV$ (list (cadr (cadr x)) (EV$ (caddr x) a))))
   (t
    (APPLY$ (car x)
            (EV$-LIST (cdr x) a)))))

(defun ev$-list (x a)
  (declare (xargs :guard t))
  (cond
   ((atom x) nil)
   (t (cons (EV$ (car x) a)
            (EV$-LIST (cdr x) a)))))
)

; Historical Note:

; We tried to put ``reasonable'' guards on the apply$ clique and failed.  For
; example, the reasonable guard on (ev$ x a) is that x is a pseudo-termp and a
; is a symbol-alistp.  But consider the recursive call (ev$ (car args) (cadr
; args)) in apply$.  The governing test (tamep (car args)) might give us the
; former, but there's nothing that can give us the second because, when ev$
; calls itself as it interprets an 'EV$ call, the second actual is the result
; of a recursive evaluation.  So that not only makes the guard proof reflexive
; but puts non-syntactic requirements on the args.

; So we have decided to go with :guard t, except for apply$ where we insist
; (true-listp args) and apply$-lambda where we additionally know that fn and
; args satisfy the pretty weak (apply$-guard fn args).

; Essay on Applying APPLY$

; Suppose collect and collect* are defined as

; (defun$ collect (lst fn)
;   (cond ((endp lst) nil)
;         (t (cons (apply$ fn (list (car lst)))
;                  (collect (cdr lst) fn)))))

; (defun$ collect* (lst fn)
;   (if (endp lst)
;       nil
;       (cons (apply$ fn (car lst))
;             (collect* (cdr lst) fn))))

; Warning: Don't confuse these symbols with the loop$ scions collect$ and
; collect$+ which take the fn argument first.  We define these symbols this way
; here merely for historical reasons: they're defined that way in the original
; apply$ paper.

; (thm ; [1]
;  (implies (apply$-warrant-collect)
;           (equal (apply$ 'collect '((1 2 3) (lambda (x) (binary-+ '3 x))))
;                  '(4 5 6))))

; BTW: The warrant below is required because otherwise we don't know
; COLLECT is NOT tame (it is ``almost tame'').

;  (thm ; [2]
;   (implies (apply$-warrant-collect)
;            (equal (apply$ 'apply$
;                           '(collect ((1 2 3) (lambda (x) (binary-+ '3 x)))))
;                   (untame-apply$
;                    'apply$
;                    '(collect ((1 2 3) (lambda (x) (binary-+ '3 x)))))))
;   :hints
;   (("Goal"
;     :expand
;     ((apply$ 'apply$
;              '(collect ((1 2 3) (lambda (x) (binary-+ '3 x)))))))))

; Note that the left-hand sides of the conclusions of [1] and [2] are sort of
; similar but [1] is more direct than [2].  One might wish that if we can
; reduce (apply$ 'collect ...) to a constant we could reduce (apply$ 'apply$
; '(collect ...)) to the same constant but that is not true.  In fact [2] tells
; us that (apply$ 'apply$ '(collect ...)) is in some sense undefined since it
; is proved equal to an undefined expression.

; For what it is worth, we can do this:

; (thm ; [3]
;  (implies (apply$-warrant-collect)
;           (equal (apply$ 'apply$
;                          '((lambda (lst)
;                              (collect lst '(lambda (x) (binary-+ '3 x))))
;                            ((1 2 3))))
;                  '(4 5 6)))
;  :hints
;  (("Goal" :expand ((apply$ 'apply$
;                            '((lambda (lst)
;                                (collect lst '(lambda (x) (binary-+ '3 x))))
;                              ((1 2 3))))))))

; One's reaction to [3] could be similar to the scene in "Six Days and Seven
; Nights"... the plane has crashed on the beach of a deserted island...

; Robin: Whoa. What happened?
; Quinn: It crumpled the landing gear when we hit.
; Robin: Well, aren't you gonna fix it? I mean can't we, can't we reattach
;        it somehow?
; Quinn: Sure, we'll, like, glue it back on.
; Robin: Aren't you one of those guys?
; Quinn: What guys?
; Robin: Those guy guys, you know, those guys with skills.
; Quinn: Skills?
; Robin: Yeah. You send them into the wilderness with a pocket knife and a
;        Q-tip and they build you a shopping mall. You can't do that?
; Quinn: No, I can't do that, but I can do this:
;        [Pops finger out of the side of his mouth]

; The reason [3] is relevant is that it's really like [2] except we package the
; collect and the tame lambda object into a tame lambda object and apply it
; successfully.  Not exactly a shopping mall, but maybe a convenience store...
; and certainly better than a popping noise!

; Perhaps more interestingly, we can do such things as

; (thm ; [4]
;  (implies (apply$-warrant-collect)
;           (equal (collect* '(((1 2 3) (lambda (x) (binary-+ '3 x)))
;                              ((10 20 30) (lambda (x) (binary-+ '3 x))))
;                            'collect)
;                  '((4 5 6) (13 23 33))))
;  :hints (("Goal" :in-theory (disable (collect*)))))

; [4] is interesting because we are mapping with a mapping function.  One might
; think that since we can't apply$ a mapping function this wouldn't work.  But
; it's more subtle.  The defun of collect* expands to introduce
; (apply$ 'collect '((1 2 3) (lambda (x) (binary-+ '3 x)))).
; Then the warrant for collect checks that its functional arg is tame,
; so that expands to (collect '(1 2 3) '(lambda (x) (binary-+ '3 x))).

; Now you might think, ``But why can't we force the expansion of the apply$ on
; the untame collect to get an untame-apply error?''  The reason is that
; there's no such clause in the defun of apply$.  The clause you're thinking
; about only works for (apply$ 'apply$ ...) not (apply$ 'collect ...).  The
; meaning of (apply$ 'collect ...) is, by the defun of apply$, whatever
; apply$-userfn says it is, which is controlled by the warrant for collect.

; About the definition of APPLY$-LAMBDA:

; The only reason we define APPLY$-LAMBDA is so that we can attach a concrete
; executable counterpart to it in the ACL2 source code.  We'd prefer not to
; have the function occur in our proofs and so we will always expand it away.
; (See apply$-lambda-opener in books/projects/apply/base.lisp).

; About the definition of EV$:

; In books/projects/apply/base.lisp (and in the model) we prove a simpler
; version of the defun of EV$, conditioned by the hypothesis that x is tamep.
; (This simpler definition, called ev$-def is LOCAL to that book but is used to
; prove ev$-opener which embodies the definition in an effective way.)  So why
; do we define EV$ as we do above?  In the two clauses dealing with calls of
; APPLY$ and EV$ we apply$ the relevant function symbol rather than just
; calling it, e.g., we write (apply$ 'apply$ ...)  instead of (apply$ ...).  We
; do it this way so that we can more easily prove that in all cases, ev$
; handles function calls by calling apply$ on the ev$-list of the arguments.
; But note that we don't write it quite that way because we need to prove
; termination.  That is, instead of calling ev$-list we actually write an
; explicit list of the two arguments (list (cadr (cadr x)) (EV$ (caddr x) a)).
; Note in particular that we do not ev$ the first argument but just take its
; cadr!  This ensures termination and is equivalent to (ev$ (cadr x) a)
; PROVIDED the argument is tame, because tameness guarantees that the first
; argument is quoted!  Note also that we could have called (ev$-list (cdr x) a)
; had we known (cdr x) was suitably tame but that would require admitting this
; clique as a reflexive function: the fact that (ev$ (cadr x) a) is smaller
; than (cadr x) when (cadr x) is tame requires reasoning about ev$ before it is
; admitted.

; -----------------------------------------------------------------
; 4. Executable Versions of BADGE and TAMEP

; In order to infer badges of new functions as will be done in defwarrant we
; must be able to determine the badges of already-badged functions.  Similarly,
; we must be able to determine that certain quoted expressions are tame.  So we
; define executable versions of badge and tamep that look at data structures
; maintained by defwarrant.

; At one time the definitions were here for executable-badge,
; executable-tamep-lambdap, executable-tamep, executable-tamep-functionp, and
; executable-suitably-tamep-listp.  These definitions are now in
; translate.lisp.

; -----------------------------------------------------------------
; 5. BADGER and the Badge-Table

; Recall (from constraints.lisp) that three categories of functions have
; badges: the ~800 apply$ primitives, the 6 apply$ boot functions, and all the
; user-defined functions on which defwarrant succeeded.  The last category of
; badges are stored in the badge-table under the key :badge-userfn-structure.
; Given a function fn, (executable-badge fn wrld) returns the badge, or nil.

; We are here primarily interested in the badge-table, which is maintained by
; defwarrant.  Defwarrant infers badges (and builds warrants with them) by
; recursively inspecting the body of defun'd functions.  It uses
; executable-badge to acquire badges of subroutines.

; Here are some terms we use below:

; ilk: one of the symbols NIL, :FN, or :EXPR; if a variable or argument
;  position has ilk NIL we sometimes say it is ``vanilla'' or ``ordinary.''  If
;  a variable or argument position has ilk :FN we say it is ``functional'' and
;  if it has ilk :EXPR we say it is ``expressional.''  The badge inference
;  mechanism uses two more pseudo-ilks, :unknown and :unknown*, which never get
;  out of that inference mechanism and should not be confused with ilks.

; ilks: a true list of ilk (or in badge inference, pseudo-ilk) symbols or T
;  denoting a list of as many NILs as we'll need.  The ilks associated with a
;  function symbol fn with formals v1, ..., vn, has length n, and successive
;  formals have the corresponding ilk in ilks.  For example, if ilks is (NIL
;  :FN :EXPR) and the formals are (X Y Z), then X is vanilla, Y is functional
;  and Z is expressional.

; badge: a defrec record structure object associated with a function symbol fn.

;  The badge has name APPLY$-BADGE and three fields:
;  :arity - arity of fn
;  :out-arity - number of output values
;  :ilks - ilks (of length equal to the arity of fn) corresponding to the
;    formals of fn, or else T denoting a list of nils of the appropriate
;    length.

;   For example, the function COLLECT (mentioned in a comment above) has badge
;   (APPLY$-BADGE 2            ; = :arity
;                 1            ; = :out-arity
;                 . (NIL :FN)) ; first formal is ordinary, second formal is
;                              ; treated like a function

;   If a function fn with formals v1, ..., vn, has a badge with :arity n,
;   :out-arity k and :ilks T or (c1 ... cn) then fn takes n arguments and
;   returns k values, and

;   - if fn is an apply$ primitive, then ilks is T

;   - if fn is an apply$ boot function, then the ilks are as given below:

;     fn                      ilks
;     BADGE                   T
;     TAMEP                   T
;     TAMEP-FUNCTIONP         T
;     SUITABLY-TAMEP-LISTP    T
;     APPLY$                  (:FN NIL)
;     EV$                     (:EXPR NIL)

;    - otherwise, fn is a user-defined function successfully processed by
;      defwarrant and thus:

;      Fn is a defined :logic mode function, its justification is ``pre-apply$
;      definable,'' meaning that the measure, well-founded relation, and domain
;      are ancestrally independent of apply$-userfn, and is either in class
;      (G1) or (G2) as described below:

;      (G1) fn's body is ancestrally independent of apply$-userfn and
;           ancestrally independent of inapplicative functions, like sys-call.
;           (This odd extra condition is necessary because we don't actually
;           require that fn's body be fully badged.  If fn could only call
;           badged functions, then we wouldn't have to check that such
;           functions as sys-call are not involved.)

;      (G2) fn's body is ancestrally dependent on apply$-usefn and

;        (a) one of these conditions hold:
;            * fn is not recursively defined, or

;            * fn is recursively defined with a natural number measure and
;              well-founded relation O<, and domain O-P, or

;            * fn is recursively defined with a measure that is the
;              macroexpansion of an LLIST expression, well-founded relation L<,
;              and domain LEXP

;            Recall from above that we also know justification is pre-apply$
;            definable.

;        (b) Every function called in the body of fn, except fn itself, has a
;            badge (and thus cannot be one of the inapplicable primitives)

;        (c) Every formal of ilk :FN is only passed into :FN slots and every
;            :FN slot in the body is either occupied by a formal of ilk :FN or
;            by a quoted tame function symbol other than fn itself, or a quoted
;            well-formed (fully translated and closed), tame lambda expression
;            that does not call fn.

;        (d) Every formal of ilk :EXPR is only passed into :EXPR slots and
;            every :EXPR slot in the body is either occupied by a formal of ilk
;            :EXPR or by a quoted, well-formed (fully translated), tame term
;            that does not call fn.

;        (e) If formal vi has ilk :FN or :EXPR then vi is passed unchanged into
;            the ith slot of every recursive call of fn in the body.

; These conditions are important to our model construction.

; TODO: We cannot analyze mutually recursive defuns yet!  We have not yet tried
; to extend the modeling process to accommodate mutually recursive mapping
; functions into the clique with APPLY$ and EV$.

; Note about Inferring Ilks

; We actually beta reduce all ACL2 lambda applications in the body before we
; begin inferring ilks.  We discuss this decision further below but for the
; moment just imagine that the body contains no lambda applications.

; If every function symbol mentioned in a (beta-reduced) term has a
; badge then we can tag every occurrence of every subterm in term with an ilk
; of NIL, :FN or :EXPR, as follows: tag the top-level occurrence of the term
; with NIL and then, for each subterm occurring as the nth actual to some call
; of a function, g, tag that occurrence of the subterm with the nth ilk of g.

; We call these the ``occurrence ilks'' of the body of fn, to distinguish them
; from the ilks assigned to the formals of fn by the badge of fn.  If a subterm
; occurrence has an occurrence ilk of :ilk, then we say the subterm ``occurs in
; an :ilk slot.''

; For example, consider the top-level term: (apply$ x (cons y (ev$ u v))).  The
; occurrence ilks are then:

;  occurrence                         ilk

; (apply$ x (cons y (ev$ u v)))       NIL
; x                                   :FN
; (cons y (ev$ u v))                  NIL
; y                                   NIL
; (ev$ u v)                           NIL
; u                                   :EXPR
; v                                   NIL

; For example, the subterm (ev$ u v) occurs in a NIL slot and u occurs in an
; :EXPR slot.  The occurrence ilk of each formal variable is its ilk and each
; formal variable has a single ilk.  That is, every occurrence of a formal must
; have the same occurrence ilk.

; The basic algorithm for inferring is as follows: in an alist, provisionally
; assign the pseudo-ilk :unknown to each formal, and explore the body keeping
; track of the occurrence ilk of each subterm we encounter, and accumulating
; into the alist the occurrence ilks of each use of each formal or signalling
; an error when a formal with an already known ilk is misused.  Of course, we
; do not yet know the ilks of the slots in recursive calls so some uses of a
; formal may not actually tell us anything about its ilk.

; As we explore the body we also enforce the rules (b)-(e) above; rule (a) is
; assured before we start.  These checks are sort of scattered since we are
; recursing through a term maintaining occurrence ilks.  For example, consider
; (c).  The first part of (c) says that every :FN formal is only used in :FN
; slots; the second part says that every :FN slot is occupied either by a :FN
; formal or by a quoted tame object (satisfying still other requirements).  The
; first part is checked whenever we encounter a variable: we check that its
; assigned ilk is identical to its occurrence ilk.  The second part is checked
; in three places: when we encounter a variable (as just stated), when we
; encounter a quote with occurrence ilk :FN, and when we encounter anything
; else with occurrence ilk :FN.

; Because we may process some recursive calls before we know the ilks of
; everything, we make a second pass confirming that the rules all hold.  We
; detect and signal many errors along the way, which obscures the code.

; Finally, because we're checking many things and signalling ``helpful'' error
; messages, the code is pretty obscure!  But see the Essay on CHECK-ILKS below.

; Note about Lambda Applications

; To infer the ilks of formals we first beta reduce all ACL2 lambda
; applications in the body.  That is, when we say we analyze the body of a
; function we really mean we analyze the body after beta reducing all lambda
; applications in it.  [Important distinction: We really do mean we beta reduce
; the ACL2 lambda applications, not ``apply$'s of lambda objects''.  Just as we
; distinguish ``ACL2 lambda expressions'' from ``lambda objects,'' -- the
; former being ordinary first class ACL2 terms and the latter being quoted
; constants -- one must distinguish ``ACL2 lambda applications,'' which are
; just ordinary first-class terms, from ``apply$'s of lambda objects.''  Here
; we're talking just about expanding all of the former, i.e., getting rid of
; LET's, LET*'s, etc!]

; To illustrate the problem, consider

; (defun fn (x y)
;   ((lambda (u v) (apply$ u v)) x y))

; Note that to determine that x is of ilk :FN we must follow x into the lambda
; via u.  This is just the idea of beta reduction.  Rather than do it
; repeatedly every time we encounter a given lambda application we just expand
; them all before inferring ilks.

; Alternatively, we could recursively determine that the ilks of the lambda
; formals are :FN and NIL respectively, and then treat the lambda application
; like an ordinary function call with a known badge.

; This idea seems more compositional but is complicated by the fact that we
; might run into recursive calls of fn inside the body of that lambda and they
; will not contribute (initially) to the ilks of the slots.  So we would have
; to replace our simple alist, mentioned above and used to track the ilks
; determined so far for the formals of fn, with something more complicated that
; keeps track of local variables within lambdas or ilks for each lambda object
; or something.  In any case, the presence of recursive calls both inside the
; lambdas and outside the lambdas complicates the inductive inference.  It is
; clearly simpler to just get rid of the lambda applications!

; Warning: One might dismiss the possibility that the body of the lambda
; involves recursion on fn -- mistakenly thinking that recursion is not allowed
; inside lambdas as per restriction (c) above.  But one would be confused!
; (One often is!)  ACL2 lambda expressions may well involve recursive calls of
; the fn being defined -- it happens whenever a recursively defun'd function
; starts with a LET.

(mutual-recursion

(defun quick-check-for-tamenessp (name term wrld)

; We return t or nil according to whether every function symbol mentioned in
; term (except name) is badged as tame.  Note that if every function in the
; body is tame except fn, and fn is defined to be body, then fn is tame.  So
; this is really a computational induction argument that says if the recursive
; calls and all subroutines are tame then fn is tame.  Note that fn might be
; tame even if some subroutines aren't.  For example, the following fn is tame:
; (defun fn (x y) (apply$ 'binary-+ (list x y))).  But this function won't
; detect that.

  (declare (xargs :mode :program))
  (cond ((variablep term) t)
        ((fquotep term) t)
        (t (let ((fn (ffn-symb term)))
             (cond
              ((flambdap fn)
               (and (quick-check-for-tamenessp name (lambda-body fn) wrld)
                    (quick-check-for-tamenessp-listp name (fargs term) wrld)))
              ((eq name fn)
               (quick-check-for-tamenessp-listp name (fargs term) wrld))
              (t (let ((bdg (executable-badge fn wrld)))
                   (and bdg
                        (eq (access apply$-badge bdg :ilks) t)
                        (quick-check-for-tamenessp-listp name (fargs term) wrld)))))))))

(defun quick-check-for-tamenessp-listp (name terms wrld)
  (declare (xargs :mode :program))
  (cond
   ((endp terms) t)
   (t (and (quick-check-for-tamenessp name (car terms) wrld)
           (quick-check-for-tamenessp-listp name (cdr terms) wrld)))))
)

(defun accumulate-ilk (var ilk alist)

; Var has occurred in an ilk slot.  If ilk is :UNKNOWN, then this occurrence
; tells us nothing and we return (mv nil alist).  Else, ilk is one of NIL, :FN,
; or :EXPR.  If var is not bound in alist, then let alist' be alist with the
; new binding (var . ilk) and return (mv nil alist').  If var is bound in alist
; then confirm that the binding is the same as ilk (returning (mv nil alist)),
; or cause an error by returning (mv msg nil).

  (declare (xargs :mode :program))
  (let ((temp (assoc-eq var alist)))
    (cond
     ((null temp)
      (if (eq ilk :unknown)
          (mv nil alist)
          (mv nil
              (cons (cons var ilk)
                    alist))))
     ((eq ilk :unknown)
      (mv nil alist))
     ((eq ilk (cdr temp)) (mv nil alist))
     (t (mv (msg "The variable ~x0 is used both as ~#1~[a function (ilk = ~
                  :FN)~/an expression (ilk = :EXPR)~/an ordinary object (ilk ~
                  = NIL)~] and as ~#2~[a function (ilk = :FN)~/an expression ~
                  (ilk = :EXPR)~/an ordinary object (ilk = NIL)~]."
                 var
                 (cond
                  ((eq (cdr temp) :FN) 0)
                  ((eq (cdr temp) :EXPR) 1)
                  (t 2))
                 (cond
                  ((eq ilk :FN) 0)
                  ((eq ilk :EXPR) 1)
                  (t 2)))
            nil)))))

(defun convert-ilk-alist-to-ilks1 (formals alist)

; Return the ilks of the formals, as recorded in alist, defaulting unbound
; formals to ilk NIL.  E.g., if given formals (X Y Z) and alist ((X . NIL) (Y
; . :FN)) we return (NIL :FN NIL).

  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        (t (cons (cdr (assoc-eq (car formals) alist))
                 (convert-ilk-alist-to-ilks1 (cdr formals) alist)))))

(defun convert-ilk-alist-to-ilks (formals alist)

; Convert an alist, mapping some formals to ilks, to the value of the :ilks
; field of an apply$-badge.  This assigns unassigned formals the ilk NIL and
; returns T if the result is all nils.

  (declare (xargs :mode :program))
  (let ((temp (convert-ilk-alist-to-ilks1 formals alist)))
    (if (all-nils temp)
        t
        temp)))

(defun changed-functional-or-expressional-formalp (formals ilks actuals)

; If there is a formal, vi, of ilk :FN or :EXPR whose corresponding actual is
; not identical to vi, we return the first such (formal ilk actual) triple.
; Else nil.  We know formals, ilks, and actuals are all the same length.  (Ilks
; = T is handled before calling this function.)

  (declare (xargs :mode :program))
  (cond
   ((endp formals) nil)
   ((and (or (eq (car ilks) :FN)
             (eq (car ilks) :EXPR))
         (not (eq (car formals) (car actuals))))
    (list (car formals) (car ilks) (car actuals)))
   (t (changed-functional-or-expressional-formalp (cdr formals)
                                                  (cdr ilks)
                                                  (cdr actuals)))))

(defun weak-well-formed-lambda-objectp (x wrld)

; Check that x is (lambda vars body) or (lambda vars dcl body) where vars is a
; list of distinct legal variable names, body is a well-formed term wrt wrld,
; and the free vars of body are a subset of vars.  We omit the checks involving
; dcl and the tameness check for body.

; This function is one of the ways of recognizing a lambda object.  See the end
; of the Essay on Lambda Objects and Lambda$ for a discussion of the various
; recognizers and their purposes.

  (declare (xargs :mode :program))
  (case-match x
    (('LAMBDA formals body)
     (and (arglistp formals)
          (termp body wrld)
          (subsetp-eq (all-vars body) formals)
          ))
    (('LAMBDA formals dcl body)
     (declare (ignore dcl))
     (and (arglistp formals)
          (termp body wrld)
          (subsetp-eq (all-vars body) formals)
          ))
    (& nil)))

(mutual-recursion

(defun guess-ilks-alist (fn new-badge term ilk wrld alist)

; Fn is the name of a function being defined.  New-badge is either nil or a
; proposed badge for fn and term is a term (initially the body of fn) occurring
; in a slot of ilk ilk.  Note: term contains no ACL2 lambda applications!  We
; try to determine the ilks of the free vars in term, extending alist to record
; what we find.  We return (mv msg alist'), where either msg is an error
; message and alist' is nil, or msg is nil and alist' is extension of alist
; assigning ilks to free vars occurring in term.

; Foreshadowing: We will call this function twice on every name being badged:
; the first time new-badge is nil and the initial alist is nil, and the
; resulting ilks are used to construct a proposed badge and a complete alist
; that binds every formal to the ilk specified by new-badge, then we call the
; function a second time with these new values.  The second pass is different
; because there are no unknowns and we have a proposed badge for fn, which
; means we can check recursive calls.  Only if the second pass completes
; without error and returns exactly the same alist do we accept the badge.

; We offer an informal but partially mechanically checked proof, below, that
; this rather complicated function is correct.  See the Essay on Check-Ilks
; after the defun of badger, which is the function that manages the
; pre-conditions and two passes of this function.  The function is more
; complicated than its spec because we try to generate good error messages.

; A few details:

; All ACL2 lambda applications in the body of the function being analyzed
; should be expanded away before this function is called.  There may still be
; lambda objects used as arguments to scions, but no ACL2 lambda applications.
; Lambda objects need not be well-formed.  All free variables encountered in
; term are formals of the function being analyzed!

; Ilk is the ``occurrence ilk'' of the current occurrence of term; however, it
; is one of the values: NIL, :FN, :EXPR, or :UNKNOWN.  The last means the
; occurrence of term is as an actual in a call of fn whose ilks are being
; computed.  If term is a variable with :UNKNOWN ilk and the body does not
; definitively assign an ilk to term, we will assign the ilk NIL at the end of
; pass 1.  One way this could happen is while trying to determine ilks for:

; (defun fn (x y z) (if (endp x) nil (fn (cdr x) z y))).

; Alist maps the variables we've seen so far to one of the three known ilks,
; NIL, :FN, or :EXPR.  If a variable is not bound in alist, it it as though it
; is bound to :UNKNOWN.  Thus, the nil alist is the appropriate initial value.
; When we're done with the first pass we complete the alist by assigning nil to
; all variables not otherwise bound.  Once the alist binds every formal to a
; known ilk (as is always the case on the second pass) then any conflicting ilk
; will cause an error.

  (declare (xargs :mode :program))
  (cond
   ((variablep term)
    (accumulate-ilk term ilk alist))
   ((fquotep term)

; Every exit from this clause is either an error or (mv nil alist).  We are
; just very particular about which error message we generate.

    (cond
     ((eq ilk :FN)

; The evg must be a tame function.  We could call executable-tamep-functionp
; but we want to check some additional properties and signal appropriate errors,
; so we consider lambda objects separately from quoted symbols...

      (cond
       ((symbolp (cadr term))
        (cond
         ((and (eq fn (cadr term))
               (not (executable-badge fn wrld)))

; Note that we avoid the error by testing whether (executable-badge fn wrld) is
; non-nil.  This means fn was admitted with :LOOP$-RECURSION.  But at the
; moment, a loop like (loop$ for x in lst collect (fn x)) translates to
; (collect$ (lambda$ (x)(fn x)) lst), not (collect$ 'fn lst), so technically
; loop$ recursion has not occurred!  But the user who knows what is going on
; could well type (collect$ 'fn lst) if she wanted to, since it is logically
; equivalent to the loop$ translation and more succinct!  So we allow it.

          (mv (msg "~x0 cannot be badged because a :FN slot in its body is ~
                    occupied by a quoted reference to ~x0 itself; recursion ~
                    through APPLY$ is not permitted except when the function ~
                    was admitted with XARGS :LOOP$-RECURSION T, which only ~
                    permits such recursion in LOOP$s."
                   fn)
              nil))
         ((executable-tamep-functionp (cadr term) wrld)
          (mv nil alist))
         (t (mv (msg "~x0 cannot be badged because a :FN slot in its ~
                      body is occupied by a quoted symbol, ~x1, that is not a ~
                      tame function."
                     fn
                     term)
                nil))))
       ((consp (cadr term))
        (cond ((weak-well-formed-lambda-objectp (cadr term) wrld)

; See the Essay on Lambda Objects and Lambda$, in particular, item (2) of the
; ``confusing variety of concepts'' for recognizing lambda objects.  The check
; above ensures that the formals of the object are legal distinct variables and
; that the body is a term.  The dcl, if any, is unchecked and tameness and
; closure are unchecked.

               (cond
                ((and (ffnnamep fn (lambda-object-body (cadr term)))
                      (not (executable-badge fn wrld)))
                 (mv (msg "~x0 cannot be badged because a :FN slot in its ~
                           body is occupied by a lambda object, ~x1, that ~
                           recursively calls ~x0; recursion through APPLY$ is ~
                           not permitted unless the function was admitted ~
                           with XARGS :LOOP$-RECURSION T, which only permits ~
                           such recursion in LOOP$s."
                          fn
                          term)
                     nil))
                ((executable-tamep-lambdap (cadr term) wrld)

; See item (3) of the above mentioned discussion.

                 (mv nil alist))
                (t (mv (msg "~x0 cannot be badged because a :FN slot in ~
                             its body is occupied by a lambda object, ~x1, ~
                             whose body is not tame."
                            fn
                            term)
                       nil))))
              (t (mv (msg "~x0 will not be badged because a :FN slot in ~
                           its body is occupied by a quoted cons object, ~x1, ~
                           that is not a well-formed, fully-translated, ~
                           closed lambda object.  The default behavior of ~
                           APPLY$ on ill-formed input is nonsensical, e.g., ~
                           unquoted numbers are treated like variables and ~
                           macros are treated like undefined functions.  It ~
                           is unwise to exploit this default behavior!"
                          fn
                          term)
                     nil))))
       (t (mv (msg "~x0 cannot be badged because a :FN slot in its ~
                    body is occupied by a quoted constant, ~x1, that does not ~
                    denote a tame function symbol or lambda object."
                   fn
                   term)
              nil))))
     ((eq ilk :EXPR)
      (cond
       ((termp (cadr term) wrld)

        (cond ((ffnnamep fn (cadr term))

; We don't even allow fns admitted with :LOOP$-RECURSION T because we don't
; think the user will ever explicitly type a call of EV$!

               (mv (msg "~x0 cannot be badged because an :EXPR slot ~
                         in its body is occupied by a quoted term, ~x1, that ~
                         calls ~x0; recursion through EV$ is not permitted!"
                        fn
                        term)
                   nil))
              ((executable-tamep (cadr term) wrld)
               (mv nil alist))
              (t (mv (msg "~x0 cannot be badged because an :EXPR ~
                           slot in its body is occupied by a quoted term, ~
                           ~x1, that is not tame."
                          fn
                          term)
                     nil))))
       (t (mv (msg "~x0 will not be badged because an :EXPR slot in its ~
                    body is occupied by a quoted object, ~x1, that is not a ~
                    well-formed, fully-translated ACL2 term.  The default ~
                    behavior of EV$ on ill-formed input is nonsensical, e.g., ~
                    unquoted numbers are treated like variables and macros ~
                    are treated like undefined functions.  It is unwise to ~
                    exploit this default behavior!"
                   fn
                   term)
              nil))))
     (t (mv nil alist))))
   ((flambdap (ffn-symb term))
    (mv (msg "There are not supposed to be any ACL2 lambda applications in ~
              the term being analyzed by guess-ilks-alist, but we have ~
              encountered ~x0!  This really indicates a coding error in ACL2 ~
              and is not your fault!  Please tell the implementors."
            term)
        nil))
   ((or (eq ilk :FN)
        (eq ilk :EXPR))
    (mv (msg "~x0 cannot be badged because ~#1~[a :FN~/an :EXPR~] slot in ~
              its body is occupied by a call of ~x2.  All :FN and :EXPR slots ~
              must be occupied by either variable symbols or quoted constants ~
              denoting tame functions."
             fn
             (if (eq ilk :FN) 0 1)
             (ffn-symb term))
        nil))
   ((eq fn (ffn-symb term))
    (cond
     (new-badge
; This is a recursive call and we now ``know'' the ilks of the args.  So we
; compute the ilks of the arguments according to this badge and then check
; a few more things.
      (mv-let (msg alist1)
        (guess-ilks-alist-list fn new-badge
                               (fargs term)
                               (access apply$-badge new-badge :ilks)
                               wrld
                               alist)

; Since the alist is complete on the formals during the second pass (when
; new-badge is non-nil) and since alist1 is an extension of alist and since any
; discrepancy between the old ilk assignment and the new would signal an error
; msg instead of changing the alist, we don't see any way alist1 can differ
; from alist!  But we still check and have a special part of the error message
; to handle that possibility.

        (cond
         ((or msg
              (not (equal alist1 alist)))
          (mv (msg "The first pass of the badger on ~x0 produced the proposed ~
                    badge ~x1, but when we ran the second pass -- in which ~
                    recursive calls of ~x0 are assumed to have that badge -- ~
                    we ~#2~[got this error message:  ~@3~/the badger posited ~
                    a different alist mapping formals to ilks, namely ~x4.~]"
                   fn
                   new-badge
                   (if msg 0 1)
                   msg
                   alist1)
              nil))
         ((not (eq (access apply$-badge new-badge :ilks) t))
          (let ((triple (changed-functional-or-expressional-formalp
                         (formals fn wrld)
                         (access apply$-badge new-badge :ilks)
                         (fargs term))))
            (cond
             (triple (mv (msg "The first pass of the badger on ~x0 produced ~
                               the proposed badge ~x1, but during the second ~
                               pass -- in which recursive calls of ~x0 are ~
                               assumed to have that badge -- we found that ~
                               the formal parameter ~x2, which was assigned ~
                               ilk ~x3, was not passed identically into a ~
                               recursive call of ~x0.  Instead, the actual ~
                               ~x4 was passed for the new value of ~x2.  No ~
                               warrant can be issued for ~x0."
                              fn
                              new-badge
                              (car triple)   ; formal
                              (cadr triple)  ; ilk
                              (caddr triple) ; actual
                              )
                         nil))
             (t (mv nil alist)))))
         (t (mv nil alist)))))
     (t (guess-ilks-alist-list fn new-badge
                               (fargs term)
                               :UNKNOWN*
                               wrld
                               alist))))
   (t (let ((bdg (executable-badge (ffn-symb term) wrld)))
        (cond
         ((null bdg)
          (mv (msg "~x0 calls the function ~x1 which does not have a badge.  ~
                    You may be able to remedy this by executing ~x2 but then ~
                    again it is possible you've done that already and ~x1 ~
                    cannot be badged, in which case neither can ~x0."
                   fn
                   (ffn-symb term)
                   `(defbadge ,(ffn-symb term)))
              nil))
         (t (guess-ilks-alist-list fn new-badge
                                   (fargs term)
                                   (access apply$-badge bdg :ilks)
                                   wrld
                                   alist)))))))

(defun guess-ilks-alist-list (fn new-badge terms ilks wrld alist)

; Terms a list of n terms and ilks is generally a list of n known ilks, e.g.,
; each ilk is NIL, :FN, or :EXPR.  But ilks = NIL is interpreted as a list of n
; nils, and ilks = :UNKNOWN* is interpreted as a list of n :UNKNOWNs.  We
; guess-ilks-alist each term in terms with its corresponding ilk and accumulate the
; resulting alists.  We return (mv msg alist').

  (declare (xargs :mode :program))
  (cond
   ((endp terms) (mv nil alist))
   (t (mv-let (msg alist1)
        (guess-ilks-alist fn new-badge
                          (car terms)
                          (cond ((eq ilks :unknown*)
                                 :unknown)
                                ((eq ilks T) nil)
                                (t (car ilks)))
                          wrld
                          alist)
        (cond
         (msg (mv msg nil))
         (t (guess-ilks-alist-list fn new-badge
                                   (cdr terms)
                                   (cond ((eq ilks :unknown*)
                                          :unknown*)
                                         ((eq ilks T) T)
                                         (t (cdr ilks)))
                                   wrld
                                   alist1)))))))
 )

(defun nonsensical-justification-term (fn wrld)

; Let m, rel, and mp be the measure term, the well-founded relation, and the
; domain predicate used in the justification of fn.  We return the essentially
; meaningless term (rel m (mp X)).  This term has the property that if g is
; ancestral in it, then g is correspondingly ancestral in
; m, or in the definition of rel, or in the definition of mp.

  (declare (xargs :mode :program))
  (let ((just (getpropc fn 'justification nil wrld)))
    (if just
        (let ((m (access justification just :measure))
              (rel (access justification just :rel))
              (mp (access justification just :mp)))
          (fcons-term* rel m (fcons-term* mp 'x)))
        *t*)))

(defun bad-ancestor1 (flg jflg x bad-fns wrld seen)

; With the proper settings of the first two flag arguments, this function
; determines whether any function symbol listed in bad-fns is ancestral in term
; x.

; This is a flagged mutual recursion where flg = t means x is a list of terms;
; else x is a term.  When jflg=t causes the function to also check the measure,
; well-founded relation, and domain predicate used to admit fn.  Otherwise, we
; just check the body.

; We walk through the relevant term(s) and consider every function symbol
; called.  If we find a call of a function listed in bad-fns, we return the
; first such fn found.  Otherwise, we return the list of all functions seen so
; far.  We need to accumulate the list of functions seen to avoid loops
; (through recursive calls) and redundant explorations of functions already
; explored.  So the final answer is either a non-nil symbol, meaning we found
; that particular bad function, or else is a list (nil or cons) meaning we did
; not.

  (declare (xargs :mode :program))
  (cond
   ((and seen (symbolp seen))
    seen)
   (flg ; x is a list of terms
    (cond ((null x) seen)
          (t (bad-ancestor1
              nil
              jflg
              (car x)
              bad-fns
              wrld
              (bad-ancestor1 t jflg (cdr x) bad-fns wrld seen)))))
   ((variablep x) seen)
   ((fquotep x) seen)
   ((flambda-applicationp x)
    (bad-ancestor1
     nil
     jflg
     (lambda-body (ffn-symb x))
     bad-fns
     wrld
     (bad-ancestor1 t jflg (cdr x) bad-fns wrld seen)))
   ((member-eq (ffn-symb x) bad-fns) (ffn-symb x))
   ((member-eq (ffn-symb x) seen)
    (bad-ancestor1 t jflg (fargs x) bad-fns wrld seen))
   (jflg
    (bad-ancestor1
     nil
     jflg
     (body (ffn-symb x) nil wrld)
     bad-fns
     wrld
     (bad-ancestor1
      t
      jflg
      (fargs x)
      bad-fns
      wrld
      (bad-ancestor1
       nil
       jflg
       (nonsensical-justification-term (ffn-symb x) wrld)
       bad-fns
       wrld
       (cons (ffn-symb x) seen)))))
   (t
    (bad-ancestor1
     nil
     jflg
     (body (ffn-symb x) nil wrld)
     bad-fns
     wrld
     (bad-ancestor1
      t
      jflg
      (fargs x)
      bad-fns
      wrld
      (cons (ffn-symb x) seen))))))

(defun bad-ancestor (jflg term bad-fns wrld)

; We return the first element of bad-fns that is ancestral in term, or nil if
; none is.  Jflg determines whether the ancestral sweep includes justifications
; or not.

  (declare (xargs :mode :program))
  (let ((ans (bad-ancestor1 nil jflg term bad-fns wrld nil)))
    (if (and ans (symbolp ans))
        ans
        nil)))

(defun not-pre-apply$-definable (fnp x wrld)

; If fnp, then x is a function symbol; else it is a term.  We return nil if the
; function symbol x (or every function symbol in term x, as per fnp) can be
; defined before apply$ (actually, before apply$-userfn).  Otherwise we return
; a symbol, g, naming a ``bad'' function that is ancestral (in the jflg=t
; sense) in fn.  G is always some element of *apply$-userfn-callers* and is
; just used in an error about why we can't issue a warrant.

  (declare (xargs :mode :program))
  (bad-ancestor t
                (if fnp
                    (fcons-term x (formals x wrld))
                    x)
                *apply$-userfn-callers*
                wrld))

(defun lex-measure-terms (term)

; If term is (the translation of) an LLIST term, (llist t1 ... tk), we return
; (t1 ... tk), the list of components.  Otherwise we return nil.

; We assume that term is not initially NIL.  Technically, nil is the
; translation of (llist); if that were some function's measure it would mean
; the function was non-recursive.  But we assume that condition is detected
; before this function is called and so we are free to return nil as the signal
; that term is not an LLIST term.

  (declare (xargs :mode :program))
  (cond
   ((variablep term) nil)
   ((fquotep term)
; If term is NIL, we've reached the end of a successful parse of an LLIST.  We
; return T to signal that, as opposed to returning NIL which here means that
; the original term is not an LLIST.
    (cond ((equal term acl2::*nil*) T)
          (t nil)))
   ((and (eq (ffn-symb term) 'CONS)
         (acl2::nvariablep (fargn term 1))
         (not (fquotep (fargn term 1)))
         (eq (ffn-symb (fargn term 1)) 'NFIX))
    (let ((temp (lex-measure-terms (fargn term 2))))
      (cond ((null temp) nil)
            (t (cons (fargn term 1)
                     (if (eq temp t) nil temp))))))
   (t nil)))

(defun g2-justification (fn ens wrld)

; Fn is a defined function symbol being considered for a warrant and we know
; that fn's measure, if fn is recursive, is not ancestrally dependent on
; apply$-userfn, but that fn's body is ancestrally dependent on apply$-userfn.
; So fn will become a G2 function if we warrant it.  But that means its
; justification is either (1) a natp-valued measure with well-founded relation
; O< and domain O-P, or (2) a lexp-valued measure with well-founded relation L<
; and domain LEXP.  We explain why we impose these restrictions below.

; Here we only do a type-set check of the natp criteria.  Fn's justification
; may fail our check but still be warrantable if a (natp m) can be proved.
; Here are the possible answers we return.

; * (mv t nil)
;   fn's justification is ok

; * (mv t events)
;   fn's justification is ok if the events in events can be admitted.
;   However, our caller knows that when events is non-nil it consists
;   of exactly two events.  The first is just an observation, packaged up
;   like an event, to explain what we're doing, and the second is a
;   defthm.

; * (mv nil msg)
;   fn's justification is not ok, as explained by msg

; The reasons we impose restrictions on G2 measures are:

; * We don't care about the measures of G1 functions as long as they're not
; dependent on apply$.  The model construction can order the G1 definitions
; (and any relevant unwarranted definitions) in the user's chronological order
; and admit them all.

; * We insist that G2 functions have measures independent of apply$ so we
; don't complicate the admission of the mutually recursive clique involving
; apply$ and all G2 functions.  To weaken this restriction will require a
; meta-level argument that a function in the clique can be used as the measure
; of another one -- a reflexive situation we're not sure we can handle and so
; don't!

; * We limit the acceptable measures to either natural numbers or non-empty
; lists of naturals, which is what lexp checks.  The model construction's
; measure for the doppelganger clique is o<-lst, which is a well-founded
; lexicographic relation on ordinals below omega^omega.  Actually, the clique's
; measure is of length 5 and the 4th slot is devoted to the ordinal
; corresponding (via lsttoo) to the measure of each G2 function in the clique.
; If each G2 function has a lexp measure then its ordinal is less than
; omega^omega.

; We could clearly allow larger bounded measures for G2 functions but lexp
; feels good enough for now.  We can imagine allowing an arbitrary ordinal
; measure (independent of apply$) but that requires another meta-level proof
; based on the structured theory paper's universal evaluator to
; non-constructively define a recursion counter.  We haven't worked out the
; details of this proof.

  (declare (xargs :mode :program))
  (cond
   ((not (recursivep fn nil wrld))
    (mv t nil))
   (t (let ((just (getpropc fn 'justification nil wrld)))
        (cond
         ((null just)
          (mv (er hard 'warranted-justification
                  "~x0 is marked with a non-nil RECURSIVEP property but its ~
                   JUSTIFICATION property is nil!"
                  fn)
              nil))
         (t (let* ((m (access justification just :measure))
                   (rel (access justification just :rel))
                   (mp (access justification just :mp)))
              (cond
               ((eq rel 'o<)
; Then m must satisfy natp and mp must be o-p.
                (mv-let (ts ttree)
                  (type-set m
                            nil ; force-flg
                            nil ; dwp
                            nil ; type-alist
                            ens
                            wrld
                            nil ; ttree
                            nil ; pot-lst
                            nil ;pt
                            )
                  (declare (ignore ttree))
                  (cond
                   ((ts-subsetp ts *ts-non-negative-integer*)
                    (cond
                     ((not (eq mp 'O-P))
                      (mv nil
                          (msg "~x0 cannot be warranted because its ~
                                justification's domain is ~x1 instead of O-P ~
                                as required for its natural-number measure."
                               fn
                               mp)))
                     (t (mv t nil))))
                   (t

; In this case, fn can be warranted if we can prove (natp m).  We return (mv t
; events), where events is exactly two events: an observation explaining what
; we're doing and a defthm.

                      (let ((defthm-event
                              `(defthm
                                ,(packn-pos (list "NATP-MEASURE-OF-" fn)
                                            fn)
                                (natp ,m)
                                :rule-classes nil)))
                        (mv t
                            `((make-event
                               (pprogn
                                (observation
                                 (cons 'defwarrant ',fn)
                                 "Since ~x0 is justified with O<, defwarrant ~
                                  insists that ~x0's measure, ~x1, satisfy ~
                                  NATP.  Syntactic considerations fail to ~
                                  establish this.  So to warrant ~x0 we must ~
                                  prove~%~%~X23~%~%"
                                 ',fn
                                 ',m
                                 ',defthm-event
                                 nil)
                                (value '(value-triple :invisible))))
                              ,defthm-event)))))))
               ((eq rel 'l<)
                (cond
                 ((not (eq mp 'ACL2::LEXP))
                  (mv nil
                      (msg "~x0 cannot be warranted because its ~
                            justification's domain is ~x1 but defwarrant ~
                            requires that when the well-founded relation is ~
                            l< the domain be lexp."
                           fn
                           mp)))
                 (t

; If rel is L< and mp is LEXP then defun proved (LEXP m) when fn was admitted.
; So we don't need to prove it now.

                  (mv t nil))))
               (t (mv nil
                      (msg "~x0 cannot be warranted because it was justified ~
                            with well-founded relation ~x1.  Defwarrant ~
                            requires that the justification use either O< (on ~
                            domain O-P) or L< (on domain LEXP) and that in ~
                            the O< case the measure must return a natural ~
                            number, not a larger ordinal."
                           fn
                           rel)))))))))))

; -----------------------------------------------------------------
; REDEF+ HACK: Now I redefine badger properly.  If and when this is all
; working, figure out how to make badger available to defuns-fn legitimately!

; (redef+)
; (logic)

; -----------------------------------------------------------------

(defun badger (fn wrld)

; We infer the badge for fn, or else indicate an error.  We return
; (mv msg badge).

  (declare (xargs :mode :program))
  (let ((formals (formals fn wrld))
        (body (expand-all-lambdas (body fn nil wrld))))
    (mv-let (msg alist0)
      (guess-ilks-alist fn nil body :unknown wrld nil) ; Pass 1
      (cond
       (msg (mv msg nil))
       (t (let* ((new-ilks
                  (convert-ilk-alist-to-ilks formals alist0))
                 (alist1
                  (pairlis$ formals
                            (if (eq new-ilks t) nil new-ilks)))
                 (new-badge
                  (make apply$-badge
                        :arity (arity fn wrld)
                        :out-arity
                        (length (getpropc fn 'stobjs-out nil wrld))
                        :ilks new-ilks)))
            (mv-let (msg alist2)

; We suspect that if new-ilks (the :ilks of new-badge) is t then there is no
; need to do Pass 2: The only parts of the body that get different treatments
; are newly discovered :FN and :EXPR slots.  In fact, we could probably get
; away without Pass 2 if we just checked that all recursive calls pass :FN and
; :EXPR formals without changing them.  But we decided it is simpler just to
; run guess-ilks-alist again... and we've got the proof in the essay below to
; confirm that pass 2 is adequate, so we are not much motivated to change it.

              (guess-ilks-alist fn ; Pass 2
                                new-badge
                                body
                                nil
                                wrld
                                alist1)
              (cond
               (msg (mv msg nil))
               ((equal alist1 alist2)

; If we get here, we know that (check-ilks fn new-badge body nil (w state)).
; See the Essay on Check-Ilks below.

                (mv nil new-badge))
               (t

; We believe it is impossible to get here because of guess-ilks-alist-lemma
; shown in the Essay on Check-Ilks below.

                (mv
                 (er hard 'badger
                     "The second pass of the badger produced a different alist ~
                     than the first!  The (completed) alist produced by the ~
                     first pass is ~x0 but the alist produced by the second ~
                     pass is ~x1.  This must be some kind of coding error in ~
                     ACL2.  Please report this to the implementors."
                     alist1 alist2)
                 nil))))))))))

; Essay on the Badge Table Guard

; There are only two legal operations on the :badge-userfn-structure:
; * :new     - add a new tuple to the front of the existing value
; * :changed - change the warrantp field of the tuple of one fn from NIL to T

; Unfortunately, the guard for the table can only see the proposed new value,
; rather than which operation was used to create it.  So we must recognize the
; operation from a comparison of the old and newly proposed values.  We do some
; fast minimal checking during this recognition phase and return the op and
; new/changed tuple.  If neither op explains the new value we cause a hard
; error -- we can't cause soft errors because we can't have state because we're
; in a table guard.

; We recognize op :new when the cdr of the new value is equal to the old value.
; We recognize op :changed by scanning down both looking for the first tuple
; that is different.  However, even after finding that changed tuple we insist
; that the fn fields are the same, the warrantp fields of the old (new) version
; was NIL (T), that the badge fields are the same, and that the remaining
; tuples in the two lists are equal.  This guarantees that the change was
; merely flipping the warrantp flag of an existing function from nil to t.  The
; recognition phase ends non-erroneously by returning the op token and the
; tuple in question.

; The more sophisticated checks are then done depending on the op.  If the op
; is :new, we confirm that the fn of the changed tuple is a function symbol
; that was not bound in the old alist, that the warrantp field is boolean and,
; if warrantp=t, that there is a warrant function for fn, and that the badge is
; correct.  If the op is :changed, we confirm that there is a warrant function
; for fn.  The checks on the existence of a warrant function and correctness of
; the badge are the sophisticated parts: we generate the defining event for the
; warrant and see if it's in the world and we infer the correct badge from
; scratch and compare it to the new one.

; Note that if the check succeeds, we know, among many other things, that the
; warrant for fn is named as created by (warrant-name fn).

(defun recognize-badge-userfn-structure-op1 (new-lst old-lst)

; We know the only legal op is going to be :changed.  We look for the changed
; tuple and classify several error cases.

  (declare (xargs :mode :program))
  (cond
   ((endp new-lst)
    (cond
     ((endp old-lst)
      (mv (er hard 'badge-table-guard
              "~@0we found no changed tuple."
              *badge-table-guard-msg*)
          nil))
     (t (mv (er hard 'badge-table-guard
                "~@0the new value doesn't include all the function symbols in ~
                 the old one.  The first omitted tuple from the old list is ~
                 ~x1."
                *badge-table-guard-msg*
                (car old-lst))
            nil))))
   ((endp old-lst)
    (mv (er hard 'badge-table-guard
            "~@0the new value contains a new tuple, ~x1, that is not at the ~
             front of the list."
            *badge-table-guard-msg*
            (car new-lst))
        nil))
   ((equal (car new-lst) (car old-lst))
    (recognize-badge-userfn-structure-op1 (cdr new-lst) (cdr old-lst)))
   ((weak-badge-userfn-structure-tuplep (car new-lst))
    (let* ((new-tuple (car new-lst))
           (old-tuple (car old-lst))
           (new-fn (car new-tuple))
           (new-warrantp
            (access-badge-userfn-structure-tuple-warrantp new-tuple))
           (new-badge
            (access-badge-userfn-structure-tuple-badge new-tuple))
           (old-fn (car old-tuple))
           (old-warrantp
            (access-badge-userfn-structure-tuple-warrantp old-tuple))
           (old-badge
            (access-badge-userfn-structure-tuple-badge old-tuple)))
      (cond
       ((and (eq old-fn new-fn)
             (eq old-warrantp nil)
             (eq new-warrantp t)
             (equal old-badge new-badge)
             (equal (cdr old-lst) (cdr new-lst)))
        (mv :changed new-tuple))
       (t (mv (er hard 'badge-table-guard
                  "~@0the first changed tuple does not just flip the ~
                   warrantp flag.  The proposed new tuple is ~x1 and the ~
                   corresponding old tuple is ~x2."
                  *badge-table-guard-msg*
                  new-tuple
                  old-tuple)
              nil)))))
   (t (mv (er hard 'badge-table-guard
              "~@0the first changed element was ill-formed.  The proposed new ~
               element is ~x1 and the corresponding old tuple is ~x2."
              *badge-table-guard-msg*
              (car new-lst)
              (car old-lst))
          nil))))

(defun recognize-badge-userfn-structure-op (new-lst old-lst)

; We return (mv op tuple) where op is :new, :changed, or one of several error
; tokens.  In the non-erroneous cases, tuple is the tuple we must inspect more
; closely.  In the erroneous cases, tuple is just something specific to the
; error and is only used in reporting.

  (declare (xargs :mode :program))
  (cond ((and (consp new-lst)
              (equal (cdr new-lst) old-lst))
         (cond ((weak-badge-userfn-structure-tuplep (car new-lst))
                (mv :new (car new-lst)))
               (t (mv (er hard 'badge-table-guard
                          "~@0the proposed new element, ~x1, is ill-formed."
                          *badge-table-guard-msg*
                          (car new-lst))
                      nil))))
        (t (recognize-badge-userfn-structure-op1 new-lst old-lst))))

(defun get-defun-body (fn ctx wrld)
  (declare (xargs :mode :program))
  (let ((body (car (last (get-defun-event fn wrld)))))
    (and body
         (mv-let (erp tbody)
           (translate-cmp body t nil t ctx wrld
                          (default-state-vars nil
                            :temp-touchable-vars t
                            :temp-touchable-fns t))
           (cond ((null erp) tbody)
                 (t (er hard ctx
                        "An attempt to translate the body of function symbol ~
                         ~x0 failed unexpectedly."
                        fn)))))))

(defun ok-defbadge (fn wrld)

; We determine whether it is ok to call defbadge on fn.  We return (mv msg flg
; badge).  If msg is non-nil, it is an error message and the other results are
; irrelevant.  If msg is nil, flg is t iff we found that fn already has a badge
; stored in the system (either because it's built in or because, for example,
; fn was warranted earlier).  In either case of flg, badge is the badge for fn
; (which we either retrieved from the world or we inferred).  Note that a
; non-erroneous return with flg = nil means some higher event should store
; badge in the badge-table for fn.

; Note: This function is to defbadge what chk-acceptable-defwarrant is to
; defwarrant.  That is, it does all the checks necessary for a syntactically
; successful defbadge.  But, why then didn't we call it
; chk-acceptable-defbadge?  The reason is that the chk functions almost always
; take STATE and cause errors or return useful things computed during the
; checking.  But this function must be used in badge-table-guard, where state
; is unavailable.  So it can't take state and can't cause errors, just prepare
; the messages.

; At one time we disallowed badges for all functions that traffic in stobjs.
; We removed that restriction to support stobjs in DO loop$ expressions,
; without yet supporting the general use of apply$ on functions that traffic in
; stobjs.  This of course presents no new problems for logic-mode functions in
; contexts such as theorems, where one translates without stobj restrictions,
; because one can already call logic-mode functions that take and/or return
; stobjs in theorems.  Such calls in code also do not present problems for a
; different reason (ignoring stobj creators, which we'll discuss shortly): such
; calls can't occur, because any such function takes at least one stobj
; argument, and code cannot produce an argument list for the second argument of
; apply$ that contains a stobj.  Finally, returning to stobj creators, note
; that apply$ will call their *1* functions, which always throw; and this
; already prevents them from creating live stobjs, for example during proofs.

  (declare (xargs :mode :program))
  (let ((bdg (and (symbolp fn)
                  (get-badge fn wrld)))
        (body (and (symbolp fn)
                   (or (body fn nil wrld)
                       (get-defun-body fn 'defbadge wrld)))))
    (cond
     (bdg (mv nil t bdg))
     ((not (and (symbolp fn)
                (arity fn wrld)
                body))

; Note: Defbadge requires fn to be defined.  But fn might be in :program mode!

      (mv (msg "Only defined function symbols can be badged and ~x0 is not one."
               fn)
          nil nil))
     ((untouchable-fn-p fn wrld nil)

; Note: The nil above is the value for temp-touchable-fns.  That is stored in
; state and we don't have access to state here.  Furthermore, we can't because
; this function is called from badge-table-guard1 (to check that badges added
; to the badge-table are valid).  The bottom line: because of this nil,
; defbadge won't allow a function to be badged if the function is on
; untouchable-fns but has been put temporarily on temp-touchable-fns.

      (mv (msg "~x0 has been declared untouchable and so cannot be badged."
               fn)
          nil nil))
     ((member-eq fn *blacklisted-apply$-fns*)

; No blacklisted function has a badge.  Functions like SYS-CALL, HONS-CLEAR!,
; and HONS-WASH! require active trust tags to call and we'd rather not
; complicate the whole apply$ story by relaxing this requirement.  It doesn't
; seem worth the bother to make such exceptions; after all, with a trust tag
; one can redefine *blacklisted-apply$-fns*!

; The following message could be made more specific for the case that fn
; belongs to the list *avoid-oneify-fns*.  But a more specific message would
; probably be too low-level, and this one is still accurate, since CL behavior
; differs from logical behavior with respect to handling of state.

          (mv (msg "~x0 cannot be badged because apply$ is prohibited from ~
                    calling it.  This is generally because its Common Lisp ~
                    behavior is different from its logical behavior."
                   fn)
              nil nil))
     ((null (bad-ancestor
             nil ; j-flg (we do not care about the justification)
             body
             *apply$-userfn-callers*
             wrld))

; If fn is not ancestrally dependent on apply$ we can badge it, even if it's
; part of a mutually recursive clique and/or some of its subfunctions are not
; badged.

      (mv nil nil
          (make apply$-badge
                :arity (arity fn wrld)
                :out-arity (length (getpropc fn 'stobjs-out nil wrld))
                :ilks t)))
     ((cdr (getpropc fn 'recursivep nil wrld))
      (mv (msg "~x0 cannot be badged because it is mutually recursive clique ~
                with ~&1.  Unfortunately, we cannot yet analyze such cliques."
               fn
               (remove1-eq fn (getpropc fn 'recursivep nil wrld)))
          nil nil))
     ((quick-check-for-tamenessp fn body wrld)
      (mv nil nil
          (make apply$-badge
                :arity (arity fn wrld)
                :out-arity
                (length (getpropc fn 'stobjs-out nil wrld))
                :ilks t)))
     (t (mv-let (msg badge)
          (badger fn wrld)
          (cond (msg (mv msg nil nil))
                (t (mv nil nil badge))))))))

(defun chk-acceptable-defwarrant1 (fn ens wrld)

; See chk-acceptable-defwarrant.

; In the error case we return (mv t msg), where msg is a msgp to be printed.
; Otherwise we return (mv nil val), where either val is t to indicate that fn
; is built-in so adding a warrant is inappropriate, or else val is a list of
; events for the encapsulate generated by defwarrant.

  (declare (xargs :mode :program))
  (cond
   ((or (apply$-primp fn)
        (assoc-eq fn *apply$-boot-fns-badge-alist*))

; We formerly included one more disjunct: (get-warrantp fn wrld).  But in that
; case we could get an error when including identical certified books in the
; example shown just below, because for bk2.lisp, the defwarrant event had a
; different expansion at include-book time (after having included bk1) then at
; certification time, resulting in a redefinition error.

;   (in-package "ACL2")
;   (include-book "projects/apply/top" :dir :system)
;   (defun foo (x) x)
;   (defwarrant foo)

    (mv nil t))
   ((eq (getpropc fn 'symbol-class nil wrld)
        :PROGRAM)
    (mv t (msg "Defwarrant expects a defined, :logic mode function symbol as ~
                its argument and ~x0 is not one."
               fn)))

; Next, we need to find out if the justification of fn, if any, is dependent on
; apply$-userfn.  If so, fn can't be warranted UNLESS fn is do$!

   (t (let ((bad-fn
             (if (eq fn 'do$) ;;; Do$ Wart
                 nil
               (not-pre-apply$-definable
                nil
                (nonsensical-justification-term fn wrld)
                wrld))))
        (cond
         (bad-fn

; A dependence on apply$-userfn was found in the justification of fn.

          (mv t (msg "~x0 cannot be warranted because some part of its ~
                      justification (i.e., its measure, well-founded ~
                      relation, or domain predicate) ancestrally calls or is ~
                      justified in terms of ~x1."
                     fn
                     bad-fn)))
         (t
          (let ((body (body fn nil wrld)))

; At this point we know fn is a candidate for either G1 or G2.  It is G1 if its
; body doesn't depend on apply$-userfn.  Otherwise, it is G2 if it meets
; certain constraints.

            (cond
             ((null (bad-ancestor
                     nil ; j-flg (we no longer care about the justification)
                     body
                     *apply$-userfn-callers*
                     wrld))

; Fn is in G1, so we warrant it.

              (mv nil nil)) ; no events necessary

; Fn will be in G2 if we warrant it.  But its justification must fit within
; the model's justification of the apply clique.

             (t
              (mv-let
                (flg val)
                (g2-justification fn ens wrld)

; If flg is t, val is either nil or a list of two events that must be admitted
; to justify warranting fn.  If flg nil, val is an error msg and we signal a
; soft error.

                (cond
                 (flg (mv nil val)) ; two events to admit
                 (t (mv t val)))))))))))))

(defun badge-table-guard1 (new-lst old-lst ens wrld)

; In normal ACL2 usage, this function is called only when the badge-table is to
; be modified by defwarrant or defbadge.  The user could however attempt to
; extend that table directly, in which case chk-acceptable-defwarrant would not
; be called and the checks made there by chk-acceptable-defwarrant1 would thus
; be skipped.  Therefore we call chk-acceptable-defwarrant1 below.  Although
; chk-acceptable-defwarrant also calls chk-acceptable-defwarrant1, that
; supports nicer error messages.  If one calls table directly to modify
; badge-table, one still deserves accurate error messages but not necessarily
; pretty ones, and one should tolerate the hard error produced below (note that
; table guards do not return state) instead of the soft error returned by
; defwarrant.

; Note on Checking Badges

; Consider the following sequence of two events, concluding in a horrible
; encapsulate.

;   (include-book "projects/apply/top" :dir :system)
;   (encapsulate ((stub (x fx) t))
;     (local (defun$ stub (x fx) (declare (ignore fx)) (cons x x)))
;     (defun$ mapstub (lst fn)
;       (if (endp lst)
;           nil
;           (cons (stub (car lst) (apply$ fn (list (car lst))))
;                 (mapstub (cdr lst) fn))))
;     (defthm constraint
;       (implies (and (true-listp lst)
;                     (not (equal lst nil)))
;                (< (acl2-count lst) (acl2-count (mapstub lst fn)))))
;     )

; Note that mapstub ancestrally uses stub (not subversively).  Note that
; mapstub is used in the constraint.  Finally, note that both stub and mapstub
; are introduced with DEFUN$, so both expand to DEFUNs followed by
; DEFWARRANTs.

; During first pass, stub is tame (more precisely, its witness is tame).  It
; gets the badge (APPLY$-BADGE 2 1 . T).  The next event, the defun$ of
; mapstub, analyzes the body and announces that mapstub is a mapping function
; with badge (APPLY$-BADGE 2 1 NIL :FN).

; The successful badging of mapstub implicitly depends on stub having a badge.

; But during the second pass, stub is just declared.  The local defun$ is
; skipped.  Stub gets no badge.

; But the expansion of the (defwarrant mapstub) records the pass 1 badge of
; mapstub, so in the second pass mapstub gets the old -- now inappropriate --
; badge.  But badge-table-guard will cause the necessary error.

; Why might it be bad to allow mapstub to be badged while it calls the unbadged
; stub?  The simplest answer is that it violates one of our Assurances on
; Badged Functions, namely ``(G2)(b) Every function called in its body has a
; badge.''  (Note that apply$ is ancestral in mapstub, so mapstub is in G2.)
; But that begs the question.  Why do we care?

; It is worrying because of functional instantiation.  There is no logical
; recording of the badge of stub.  It could be functionally instantiated with a
; function that is not tame, for example.  Perhaps this could be fixed, e.g.,
; by having a constraint on stub that says (badge 'stub) = '(APPLY$-BADGE 2 1
; . T) or something.  Even if we solve that problem, there is the problem of
; elaborating the evaluation theory story for mapping functions, especially as
; it concerns the idea of using defattach to make stub executable.  But this
; whole issue -- allowing constrained functions into mapping functions -- we
; just haven't considered a high enough priority to think about!

; Calling badge-table-guard is inefficient, since it re-does checks done by
; defwarrant or defbadge.  But efficiency does not seem to be a big concern
; here, so we will wait until users complain about performance.

  (declare (xargs :mode :program))
  (cond
   ((null new-lst)

; It is legal simply to abandon all userfn badges and warrants!  But generally
; this is only done during bootstrapping to initialize the table.

    t)
   (t (mv-let (op tuple)
        (recognize-badge-userfn-structure-op new-lst old-lst)
        (let ((fn (car tuple))
              (warrantp
               (access-badge-userfn-structure-tuple-warrantp tuple))
              (badge
               (access-badge-userfn-structure-tuple-badge tuple)))

; We now do the sophisticated checks on the tuple.  BTW: If the recognizer
; didn't cause a hard error, op is either :new or :changed.  But we check that
; just to be sure!  If op = :new, we confirm that the fn of the changed tuple
; is a function symbol that was not bound in the old alist, that the warrantp
; field is boolean, if warrantp=t there there is a warrant function for fn, and
; that the badge is correct.  If the op is :changed, we confirm that there is a
; warrant function for fn.  To avoid code duplication, we check for the warrant
; function in code shared for the two ops.

          (and
           (or (eq op :new)
               (eq op :changed)
               (er hard 'badge-table-guard
                   "Recognize-badge-userfn-structure-op returned op = ~x0 when ~
                  it is supposed be either :NEW or :CHANGED."
                   op))
           (if (eq op :new)
               (and (symbolp fn)
                    (arity fn wrld)
                    (not (assoc-eq fn old-lst))
                    (booleanp warrantp)
                    (mv-let
                      (msg flg correct-badge)
                      (ok-defbadge fn wrld)
                      (declare (ignore flg))
                      (cond
                       (msg (er hard 'badge-table-guard
                                "~@0the badge proposed for ~x1 was ~x2, but ~
                                 badger reports: ~@3"
                                *badge-table-guard-msg*
                                fn badge msg))
                       ((not (equal badge correct-badge))
                        (er hard 'badge-table-guard
                            "~@0the badge proposed for ~x1 was ~x2 but the ~
                             actual badge computed by the badger is ~x3"
                            *badge-table-guard-msg*
                            fn badge correct-badge))
                       (t t))))
             t)
; At this point we know badge = correct-badge.  Now we check the warrant if
; warrantp = t, whether op is :new or :changed.  Note that if the check
; succeeds, we know, among many other things, that the warrant for fn is really
; named by (warrant-name fn).

           (if (eq warrantp t)
               (and (or (equal (get-event (warrant-name fn) wrld)
                               (make-apply$-warrant-defun-sk fn
                                                             (formals fn wrld)
                                                             badge
                                                             t))
                        (er hard 'badge-table-guard
                            "~@0it is claimed that ~x1 has a warrant but ~
                             ~#2~[there is no event introducing a function ~
                             named ~x3~/the event introducing the name ~x3 is ~
                             ~x4 and should be ~x5~]."
                            *badge-table-guard-msg*
                            fn
                            (if (get-event (warrant-name fn) wrld)
                                1 0)
                            (warrant-name fn)
                            (get-event (warrant-name fn) wrld)
                            (make-apply$-warrant-defun-sk fn
                                                          (formals fn wrld)
                                                          badge
                                                          t)))
                    (mv-let (erp val)
                      (chk-acceptable-defwarrant1 fn ens wrld)
                      (cond
                       (erp (er hard (cons 'defwarrant fn) "~@0" val))
                       ((eq val t)
                        (er hard (cons 'defwarrant fn)
                            "The function ~x0 is built-in and already has a ~
                             warrant when ACL2 starts up.  It is illegal to ~
                             attempt to ~#1~[add an entry to~/update an entry ~
                             in~] the badge-table for ~x0 in this case.~|~%"
                            fn
                            (if (eq op :new) 0 1)))
                       (t t))))
             t)))))))

(defun badge-table-guard (key val ens wrld)

; See the Essay on the Badge Table Guard.

; See the comment in defwarrant about speeding up this function by using a
; checker version of badger.  (That checker would need to be written.)

  (declare (xargs :mode :program))
  (cond
   ((not (eq key :badge-userfn-structure)) ; no need to protect for other keys
    t)
   (t (badge-table-guard1 val
                          (cdr (assoc-eq :badge-userfn-structure
                                         (table-alist 'badge-table wrld)))
                          ens
                          wrld))))

(set-table-guard badge-table
                 (badge-table-guard key val ens world)
                 :topic defbadge
                 :show t)

(table badge-table
       :badge-userfn-structure
       nil)

; -----------------------------------------------------------------
; 6. Essay on CHECK-ILKS

; The computation above is messy both because we're inferring ilks (using two
; pseudo ``ilks'' :UNKNOWN and :UNKNOWN*) and we're generating ``helpful''
; error messages, cluttering the code.  We therefore would like to know that
; when badger returns no error msg and a purported badge that the badge is
; actually ``correct,'' where correctness is as succinctly stated as we can
; manage.  To that end we have written a checker (in
; books/system/apply/apply.lisp), proved (during the :acl2-devel certification
; process) the key property mechanically, and can then put together an informal
; proof of the correctness of badger.  We give that informal proof here and do
; the mechanical checking part during the :acl2-devel certification.

; Unfortunately, the definition of check-ilks is pretty complicated so we will
; paraphrase it here, in Assurances on Badged Functions, below, for future
; reference.  These assurances are exploited in our construction demonstrating
; that we can model all mapping functions (by defining them
; mutually-recursively with APPLY$).

; But first we make a few observations.

; First, when we use the word ``badge'' below we mean something satisfying
; apply$-badgep, which means in particular that the :ilks is either T (denoting
; a list of NILs) or a true list that is a subset of (NIL :FN :EXPR).  In
; particular, we never mention the strange ``ilks'' :UNKNOWN or :UNKNOWN*.

; Second, we explore the beta reduced body as previously noted.

; Third, we keep track of ``occurrence ilks'' as we walk the body.

; Fourth, inspection of badger above shows that it signals an error unless fn
; is a defined (not constrained) :logic mode function symbol that has a
; natural-number valued measure that decreases according to o<.

; Fifth, when badger returns non-erroneously, the badge is constructed with
; make apply$-badge with obviously correct settings for :arity and :out-arity.
; The only question is whether :ilks is set correctly.

; Assurances on Badged Functions (recapitulation)

; If badger assigns new-badge as the badge of fn with (beta-reduced) body,
; body, then we know fn is a defined :logic mode function, its justification is
; pre-apply$ definable as above and fn is either in class (G1) or (G2).

; (G1) fn's body is ancestrally independent of apply$-userfn and ancestrally
;      independent of inapplicative functions, like sys-call.

; (G2) fn's body is ancestrally dependent on apply$-usefn and

;  (a) one of these conditions hold:
;      * fn is not recursively defined, or

;      * fn is recursively defined with a natural number measure and
;        well-founded relation O<, and domain O-P, or

;      * fn is recursively defined with a measure that is the
;        macroexpansion of an LLIST expression, well-founded relation L<,
;        and domain LEXP

;      Recall from above that we also know justification is pre-apply$
;      definable.

;  (b) Every function called in body has a badge (including fn if we consider
;      new-badge the badge of fn).

;  (c) Every formal of ilk :FN is only passed into :FN slots, and
;      every :FN slot in the body is occupied by
;      * a formal variable of ilk :FN in new-badge, or
;      * a quoted tame function symbol other than fn, or
;      * a quoted, well-formed (fully translated and closed), tame lambda
;        object that does not call fn.

;  (d) Every formal of ilk :EXPR is only passed into :EXPR slots, and
;      every :EXPR slot in the body is occupied by
;      * a formal variable of ilk :EXPR in new-badge, or
;      * a quoted, well-formed (fully translated), tame term that does not call
;        fn.

;  (e) If the nth formal, vn, of fn has ilk :FN or :EXPR then vn is passed
;      unchanged into the nth slot of every recursive call of fn.

; To establish this we first inspect badger and see that it quite literally
; checks that fn is in :logic mode, its justification is pre-apply$ definable,
; and it is either in class (G1) or (G2).  It then goes on to check the
; additional properties imposed on (G2) functions.  One need only pay attention
; to the non-erroneous exits, e.g., (mv nil ...).  It is the third (last)
; non-erroneous exit that is potentially problematic.

; Briefly reviewing the code in badger leading to the second non-erroneous
; return we see that it guesses an alist0 assigning ilks to the vars of body,
; then it produces a proposed new-badge and alist1 from alist0.  Alist1 is just
; alist0 completed on all the formals, by assigning an ilk of NIL to any
; unassigned formal.  New-badge just lists those completed ilks in formals
; order.  We then see that badger tests that (guess-ilks-alist fn new-badge
; body nil wrld alist1) is non-erroneous.  Only if that test succeeds do we
; return new-badge.

; Check-ilks, defined in books/system/apply/apply.lisp, checks (b), (c), (d)
; and (e); as noted, (a) is obvious.  We encourage you to read the defun of
; check-ilks to confirm that if it returns t then (b)-(e) hold.

; We could change badger to call check-ilks as with (check-ilks <fn>
; <new-badge> <beta-reduced-body> nil <(w state)>) and cause an error if it
; fails, but there is no need.  We can prove that check-ilks will succeed when
; badger returns from the second non-erroneous exit.  (We enclose the arguments
; to check-ilks above in brackets, e.g., <fn>, ..., <(w state)>, to denote the
; values of those expressions at the second non-erroneous exit above.)

; In particular, consider this theorem from books/system/apply/apply.lisp:

; (defthm guess-ilks-alist-correct
;   (implies (and (null                                                ; hyp 1
;                  (mv-nth 0 (guess-ilks-alist fn new-badge term
;                                              ilk wrld alist)))
;                 (alist-okp term formals new-badge alist wrld)        ; hyp 2
;                 (badge-table-okp                                     ; hyp 3
;                  (cdr (assoc-equal :badge-userfn-structure
;                                    (table-alist 'badge-table wrld))))
;                 (apply$-badgep new-badge)                            ; hyp 4
;                 (member ilk '(nil :fn :expr))                        ; hyp 5
;                 (termp term wrld))                                   ; hyp 6
;            (check-ilks fn formals new-badge term ilk wrld))
;   ...)

; Instantiate it with the values passed to guess-ilks-alist in Pass 2:
; ((fn <fn>)
;  (new-badge <new-badge>)
;  (term <beta-reduced-body>)
;  (ilk nil)
;  (wrld <(w state)>)
;  (alist <alist1>)
;  (formals (formals <fn> <(w state)>)))

; This gives the conclusion we desire but we must confirm that the hypotheses
; are true.  Hyp 1 is true by the Pass 2 test in badger.  Hyp 2 requires that
; every variable in <beta-reduced-body> be a member of (formals <fn> <(w
; state)>) and have the same ilk in new-badge as assigned in alist1; the
; membership is obviously true and the ilk requirement is true by construction
; of <new-badge> and <alist1>.  Hyp 3 requires that the 'BADGE-TABLE in <(w
; state)> is well-formed and we know we maintain that invariant.  Hyp 4
; requires that <new-badge> be an APPLY$-BADGEP and it is by construction.  Hyp
; 5 is obviously true because ilk is nil.  And Hyp 6 is obviously true:
; <beta-reduced-body> is a term in <(w state)>.

; This ``proof'' has to be made informally unless we formalize a great deal of
; the properties of (w state) and the invariants maintained by defwarrant.

; -----------------------------------------------------------------
; 7. Functional Equivalence

; We now develop the notion of two functions being equivalent.  The basic idea
; is that fn1 is functionally equivalent to fn2 if they are both tame and
; apply$ cannot distinguish them.  We define fn-equal to be this concept, but
; first need the quantified statement that apply$ cannot distinguish the two.

; See boot-strap-pass-2-b.lisp for the definitions of apply$-equivalence and
; fn-equal, which are :logic mode functions dependent on apply$ and hence must
; wait for (system-verify-guards).  But the definitions are exactly:

; (defun-sk apply$-equivalence (fn1 fn2)
;   (declare (xargs :guard t))
;   (forall (args)

; We use ec-call to support guard verification in "make proofs".

;    (equal (ec-call (apply$ fn1 args))
;           (ec-call (apply$ fn2 args)))))

; (defun fn-equal (fn1 fn2)
;   (declare (xargs :guard t))
;   (if (equal fn1 fn2)
;       t
;       (and (tamep-functionp fn1)
;            (tamep-functionp fn2)
;            (apply$-equivalence fn1 fn2))))

(defun defcong-fn-equal-equal-events (term i c1-cn)
  (declare (xargs :guard (and (natp i)
                              (true-listp c1-cn))))
  (cond
   ((endp c1-cn) nil)
   ((eq (car c1-cn) :FN)
    (cons `(defcong fn-equal equal ,term ,i
             :package :legacy
             :hints
             (("Goal" :in-theory (disable (:executable-counterpart force)))))
          (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn))))
   (t (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn)))))

; -----------------------------------------------------------------
; 8. DEFWARRANT and DEFBADGE

; Suppose AP is defined (with defun$) to be a tame function of two arguments
; returning one result.  Then defun$ will also do something equivalent to the
; following (modulo the note below):

; (defun-sk apply$-warrant-AP nil
;   (forall (args) (and (equal (badge 'AP) '(APPLY$-BADGE 2 1 . T))
;                       (equal (apply$ 'AP args)
;                              (ap (car args) (cadr args))))))

; (defthm apply$-AP
;   (implies (force (apply$-warrant-AP))
;            (and (equal (badge 'AP) '(APPLY$-BADGE 2 1 . T))
;                 (equal (apply$ 'AP args)
;                        (ap (car args) (cadr args))))))

; (in-theory (disable apply$-warrant-AP))

; which will mean that if we have the hypothesis (apply$-warrant-AP), we will
; rewrite (badge 'AP) to the given badge of ap and rewrite (apply$ 'AP args) to
; the appropriate call of ap.

; Note: the actual warrant is phrased in terms of badge-userfn and
; apply$-userfn, not badge and apply$, as shown above; but the rewrite rule
; apply$-AP indeed deals with badge and apply$.  We deal with this later.

(defun forced-warrant-fn (names)

; This is a helper function for the macro warrant.  Given (a b ...) we return
; ((FORCE (APPLY$-WARRANT-a)) (FORCE (APPLY$-WARRANT-b)) ...)

  (declare (xargs :mode :logic ; :program mode may suffice, but this is nice
                  :guard (symbol-listp names)))
  (cond ((endp names) nil)
        ((or (assoc-eq (car names) *badge-prim-falist*)
             (assoc-eq (car names) *apply$-boot-fns-badge-alist*))
; Primitives and apply$ boot functions do not have or need warrants.
         (forced-warrant-fn (cdr names)))
        (t (cons (list 'FORCE (list (warrant-name (car names))))
                 (forced-warrant-fn (cdr names))))))

(defmacro warrant (&rest names)

; This implements the abbreviation (warrant a b c) for:
; (AND (APPLY$-WARRANT-a) (APPLY$-WARRANT-b) (APPLY$-WARRANT-c))

  (declare (xargs :guard (symbol-listp names)))
  `(AND ,@(forced-warrant-fn names)))

; The warrant for AP, illustrated above, is particularly simple because AP is
; tame.  All of its formals are vanilla.  The warrant for a mapping function
; like COLLECT has a tameness condition imposed by the non-vanilla ilks, here
; assumed to be (NIL :FN), e.g.,

; (defun-sk apply$-warrant-COLLECT nil
;   (forall (args)
;     (and (equal (badge 'COLLECT) '(APPLY$-BADGE 2 1 NIL :FN))
;          (implies (tamep-functionp (cadr args)) ; tameness-conditions
;                   (equal (apply$ 'COLLECT args)
;                          (collect (car args)     ; successive-cadrs
;                                   (cadr args))))))
;   :constrain t)

; (BTW: The actual warrant is a defun-sk phrased in terms of badge-userfn and
; apply$-userfn, not badge and apply$, as shown above; but the rewrite rule
; indeed deals with badge and apply$.  We deal with this later.)

; We originally introduced defwarrant-event here, preceded by supporting
; functions tameness-conditions, successive-cadrs, and necc-name-ARGS-instance.
; However, we moved it to other-events because at one time it was needed there
; in the implementation of defattach.  It does not appear to be needed there
; anymore and perhaps could be moved back here.

(defun chk-acceptable-defwarrant (fn ctx ens wrld state)

; We cause an error if (defwarrant fn) is unacceptable; otherwise, we return
; (via an error-triple) either T, meaning fn is already warranted or needs no
; warrant, or else a doublet (events badge).  Events is either nil or a list of
; exactly two events (an observation and a defthm) which must be admitted in
; order to warrant fn.  In any case badge is the badge (either looked up or
; inferred).

; Among other things we guarantee that fn is a defined :logic mode function,
; that it is not blacklisted, that its justification is independent of apply$
; (but see warning below), that either (a) the body is independent of apply$,
; or (b) the body is not independent of apply$ but is singly-recursive (well,
; at least, not mutually recursive) and that the justification is suitably
; lexicographic (in the sense that we can insert it into the model's measure of
; the apply$ clique).

  (declare (xargs :mode :program))
  (mv-let (msg storedp badge)
    (ok-defbadge fn wrld)
    (declare (ignore storedp))
    (cond
     (msg (er soft ctx "~@0" msg))
     (t

; If ok-defbadge didn't indicate an error we know fn is a defined function
; symbol with the other properties necessary for defbadge to succeed.

; It is important to call chk-acceptable-defwarrant1 here even though it is
; also called by badge-table-guard1.  One reason is that the code below can
; produce a soft error instead of the uglier hard error from a table guard
; violation.  Another reason is to avoid the possibility of getting a less
; user-friendly error when evaluating events from the encapsulate generated by
; the make-event (e.g., from a defattach failure).

      (mv-let (erp val)
        (chk-acceptable-defwarrant1 fn ens wrld)
        (cond
         (erp (er soft ctx "~@0" val))
         ((eq val t) (value t))
         (t (value (list val badge)))))))))

(defun confirm-apply-books (state)
  (declare (xargs :mode :program))
  (let ((wrld (w state))
        (apply-lemmas-book-name *projects/apply/base-sysfile*))
    (cond
     ((and (not (global-val 'projects/apply/base-includedp wrld))
           (not (equal apply-lemmas-book-name
                       (active-book-name wrld state)))
           (not (global-val 'boot-strap-flg wrld)))

; In order to succeed, defwarrant needs base.lisp to have been included.  That
; is because defwarrant tries to prove congruence rules and at the very least
; needs the lemmas establishing that fn-equal is an equivalence and a
; congruence for apply$.  So we tell the user to load top (which includes base)
; unless base has already been loaded or we're currently including or
; certifying base itself (which, naturally enough, explicitly proves all the
; lemmas it needs to do the defwarrants it tries).

; We make an exception for the boot-strap, where we take responsibility for the
; necessary verification.

      (er soft 'confirm-apply-books
          "Please execute~%~x0~|before the first defun$, defbadge, or ~
           defwarrant.  See :DOC defwarrant."
          '(include-book "projects/apply/top" :dir :system)))
     (t (value nil)))))

(defun defwarrant-fn1 (fn state)
  (declare (xargs :mode :program))
  (let ((wrld (w state)))
    (er-progn
     (confirm-apply-books state)
     (er-let* ((doublet-or-t
                (chk-acceptable-defwarrant fn
                                           (cons 'defwarrant fn)
                                           (ens state)
                                           wrld
                                           state)))
; Doublet-or-t is either t meaning fn is already warranted (or doesn't
; need a warrant) or else it's ((observation defthm) badge), i.e., a list of
; two events and fn's badge.

       (cond
        ((eq doublet-or-t t)
         (pprogn

; Keep this case in sync with the corresponding case in defbadge-fn1.

; Some functions are warranted in boot-strap-pass-2-b.lisp and without this
; check of the boot-strap-flg the build prints a bunch of misleading messages
; about how, for example, mempos is already warranted (but it wasn't until
; (defwarrant mempos) was executed in boot-strap-pass-2b.

          (if (global-val 'boot-strap-flg wrld)
              state
            (observation
             (cons 'defwarrant fn)
             "The function ~x0 is built-in and already has a warrant when ~
              ACL2 starts up.  This event thus has no effect.~|~%"
             fn))
          (value `(with-output
                    :stack :pop
                    (value-triple nil)))))
        (t
         (let ((events (car doublet-or-t))
               (badge (cadr doublet-or-t)))
           (value

; We know that events is either nil or a list of exactly two events: an
; observation explaining why we're about to prove a theorem and a defthm for
; that theorem.  We use two events so we can control the output below.

; WARNING: Be sure no event under this (encapsulate () ...) is local!  At one
; time we used (progn ...) instead.  However, we found that defwarrant events
; were never redundant because of the defattach below.

            `(encapsulate ; Read the warning above before changing to progn.
               ()
               ,@(if (eq events nil)
                     nil
                   `((with-output     ; First we lay down the observation
                       :stack :pop    ; explaining that we're about to
                       :off summary   ; prove a defthm that fn's measure
                       ,(car events)) ; is a natp.

                     (with-output ; Then we lay down the defthm.
                       :stack :pop ,(cadr events))))
               ,@(defwarrant-events fn (formals fn wrld) badge)
               (table badge-table
                      :badge-userfn-structure
                      (put-badge-userfn-structure-tuple-in-alist
                       (make-badge-userfn-structure-tuple
                        ',fn T ',badge)
                       (cdr (assoc :badge-userfn-structure
                                   (table-alist 'badge-table world)))
                       'defwarrant)
                      :put)
               ,(if (getpropc fn 'predefined nil wrld)
                    `(defattach (,(warrant-name fn)
                                 true-apply$-warrant)
                       :system-ok t)
                  `(defattach ,(warrant-name fn) true-apply$-warrant))
               ,@(if (eq (access apply$-badge badge :ilks) t)
                     nil
                   (defcong-fn-equal-equal-events
                     (cons fn (formals fn wrld))
                     1
                     (access apply$-badge badge :ilks)))
               (progn ,(if (global-val 'boot-strap-flg wrld)
                           `(with-output
                              :stack :pop
                              (value-triple
                               (prog2$
                                (cw "~%~x0 is now warranted by ~x1, with badge ~x2.~%~%"
                                    ',fn
                                    ',(warrant-name fn)
                                    ',badge)
                                :warranted)))
                         `(side-effect-event
                           (if (or (eq (ld-skip-proofsp state)
                                       'include-book)
                                   (eq (ld-skip-proofsp state)
                                       'include-book-with-locals)
                                   (eq (ld-skip-proofsp state)
                                       'initialize-acl2))
                               state
                             (fms "~%~x0 is now warranted by ~x1, with badge ~
                                   ~x2.~%~%"
                                  (list (cons #\0 ',fn)
                                        (cons #\1 ',(warrant-name fn))
                                        (cons #\2 ',badge))
                                  (standard-co state) state nil))))
                      (with-output
                        :stack :pop
                        (value-triple '(:return-value :warranted)
                                      :on-skip-proofs t))))))))))))

(defun defwarrant-fn (fn)
  (declare (xargs :mode :logic :guard t)) ; for execution speed in safe-mode
  `(defwarrant-fn1 ',fn state))

(defmacro side-effect-event (form)

; Form should return state.

  `(with-output :off summary
     (make-event (pprogn ,form (value '(value-triple :invisible))))))

(defmacro defwarrant (fn)

; We can probably speed up this event, which currently may be particularly slow
; when there are lambda applications because of beta reduction in badger.  One
; solution might be to use some form of memoization.  But a more principled
; solution would be to write a more efficient version of badger that checks an
; alleged badge rather than computing it from scratch, and to use that checker
; in badge-table-guard.  More information is below.

; Inference requires operating with partial information, iteratively extending
; what one knows; inferring ilks inside lambda bodies while having only partial
; information about the ilks of the actuals is tricky; recursive calls (of the
; fn being badged) inside ACL2 lambda bodies are especially tricky.

; After-the-fact checking is easier because one knows everything including ilk
; requirements of the recursive calls.

; It is probably possible to implement a checker that leaves ACL2 lambda
; applications in place, since one knows the ilks of the actuals and can
; transfer them to the ilks of the lambda formals before diving into the body.

; WARNING: Do not extend the functionality of defwarrant by making constrained
; functions warrantable!  That opens a can of worms, namely tracking
; attachments to guard against the calling of lambda$ expressions unbound by
; lambda$-alist during pre-loading of compiled files.  There are probably a
; dozen other reasons not to think about warranted attachable functions!

; Note that the integrity of the badge-table is enforced by badge-table-guard
; and hence does not rely on additional checks made directly by defwarrant,
; specifically, in chk-acceptable-defwarrant1.  See also comments in
; badge-table-guard1.

  `(with-output
     :off ; *valid-output-names* except for error
     (warning warning! observation prove proof-builder event history summary
              proof-tree)
     :stack :push
     :gag-mode nil
     (make-event
      (with-output
        :stack :pop
        ,(defwarrant-fn fn))
      :on-behalf-of :quiet!)))

(defmacro def-warrant (fn)
  (er hard (msg "~x0" `(def-warrant ,fn))
      "Def-warrant has been replaced by defwarrant.  Please use defwarrant ~
       instead."))

(defun defbadge-fn1 (fn state)
  (declare (xargs :mode :program))
  (let ((wrld (w state))
        (ctx `(defbadge . ,fn)))
    (er-progn
     (confirm-apply-books state)
     (mv-let
       (msg flg badge)
       (ok-defbadge fn wrld)
       (cond
        (msg
         (er soft ctx "~@0" msg))
        ((or (apply$-primp fn)
             (assoc-eq fn *apply$-boot-fns-badge-alist*))

; Keep this case in sync with the corresponding case in defwarrant-fn1.

         (pprogn
          (if (global-val 'boot-strap-flg wrld)
              state
            (observation
             (cons 'defbadge fn)
             "The function ~x0 is built-in and already has a badge when ~
              ACL2 starts up.  This event thus has no effect.~|~%"
             fn))
          (value `(with-output
                    :stack :pop
                    (value-triple nil)))))
        (t
         (pprogn
          (cond
           (flg (cond ((f-get-global 'skip-proofs-by-system state)

; Avoid the observation below when we are in include-book or the second pass of
; an encapsulate.

                       state)
                      (t (observation (cons 'defbadge fn)
                                      "The function ~x0 already has a badge ~
                                       because it is built-in, or because ~
                                       defbadge or defwarrant has been ~
                                       previously invoked on it, or because ~
                                       :loop$-recursion t was declared).  ~
                                       This event thus has no effect.~|~%"
                                      fn))))
           (t (prog2$
               (cw "~%~x0 is being given the badge ~x1 but has no warrant.~%~%"
                   fn badge)
               state)))
          (value

; Otherwise, we store the badge for fn in the badge table.  Note that we set
; the warrantp flag of fn to NIL.  We know we're not overriding a previous
; setting of T because if fn had been previously warranted it would have had a
; badge already.

; WARNING: Be sure no event under this (encapsulate () ...) is local!  At one
; time we used (progn ...) instead.  However, we found that defwarrant events
; were never redundant because of the defattach below.

           `(encapsulate ; Read the warning above before changing to progn.
              ()
              (table badge-table
                     :badge-userfn-structure
                     (put-badge-userfn-structure-tuple-in-alist
                      (make-badge-userfn-structure-tuple ',fn NIL ',badge)
                      (cdr (assoc :badge-userfn-structure
                                  (table-alist 'badge-table world)))
                      'defbadge)
                     :put)
              (with-output
                :stack :pop
                (value-triple '(:return-value :badged)
                              :on-skip-proofs t)))))))))))

(defun defbadge-fn (fn)
  (declare (xargs :mode :logic :guard t)) ; for execution speed in safe-mode
  `(defbadge-fn1 ',fn state))

(defmacro defbadge (fn)

; See the comments in defwarrant about speeding up the badger.

; WARNING: Do not extend the functionality of defbadge by badging constrained
; functions!  That opens a can of worms, namely tracking attachments to guard
; against the calling of lambda$ expressions unbound by lambda$-alist during
; pre-loading of compiled files.  There are probably a dozen other reasons not
; to think about badged attachable functions!

  `(with-output
     :off ; *valid-output-names* except for error
     (warning warning! observation prove proof-builder event history summary
              proof-tree)
     :stack :push
     :gag-mode nil
     (make-event
      (with-output
        :stack :pop
        ,(defbadge-fn fn))
      :on-behalf-of :quiet!)))

; -----------------------------------------------------------------
; 9. DEFUN$

(defmacro defun$ (fn formals &rest rest)
  `(progn
     (defun ,fn ,formals ,@rest)
     (defwarrant ,fn)))

(defmacro defun$! (fn formals &rest rest)

; This is like defun$ but it also includes a post-warrant verify-guards.  The
; declarations must NOT have any :verify-guard settings, as this is added
; automatically.  The motivation for this variant of defun$ is that the guards
; on loop$ recursive defuns cannot be expressed until the warrant is available.
; See the comment below on the "ideal design" for defun$.

  `(progn
     (defun ,fn ,formals
       (declare (xargs :verify-guards nil))
       ,@rest)
     (defwarrant ,fn)
     (verify-guards ,fn)))

; The ideal design for defun$ would be for it to determine first whether the
; declarations include :loop$-recursion t and whether the user wants guards
; verified during defun.  If both conditions are true, it could change or add a
; :verify-guards nil setting to the declarations before submitting the defun.
; Then it could lay down a verify-guards command after the defwarrant command.
; Doing this just whenever loop$-recursion is declared would be a mistake since
; the user might not want guards verified.  But determine whether the user
; wants guards verified depends on many things including the default defun mode
; and the default verify-guards-eagerness settings in the world -- which are
; inaccessible in macros.  So to do it "right" we'd have to implement the ideal
; defun$ with a make-event.  Other factors involved in determining whether
; guards are to be verified during defun include information recovered from the
; declarations, including the :mode, :verify-guards, :guard settings and any
; type declarations.  E.g., guard verification is not tried automatically if
; the eagerness value is 1, no :verify-guards value is specified, and no guard
; or type is present.  Recovering the various settings from untranslated
; declarations is messy.

; Since a goal of the ideal design would be to not render an illegal defun
; legal or a legal one illegal when shutting off :verify-guards, the problem is
; even messier than the various combinations of the above factors suggests.
; For example, if the world defaults are :logic mode and
; verify-guards-eagerness 1, and the user has two occurrences of (xargs
; :verify-guards t) among his declares, then changing just one of them to
; (xargs :verify-guards nil) would produce an illegal ambiguous setting from a
; legal defun.  Similarly, if the user had both (xargs :verify-guards t) and
; (xargs :verify-guards nil), then changing the first to (xargs :verify-guards
; nil) would produce a legal defun from an illegal one.

; While all of this could be -- and might someday be -- handled by a suitable
; make-event version of defun or, perhaps better, extending defun to include
; defwarrant when asked to do so by declarations or loop$ recursion, we decided
; at the moment to just cut through the complexity by instructing the user to
; employ defun$! if defun-time guard verification of a loop$-recursive defun is
; wanted!

; -----------------------------------------------------------------
; 10. The LAMB Hack
;     Deprecated as noted above.

; -----------------------------------------------------------------
; 11. The Defattach
;     We attach ``magic'' functions to badge-userfn and apply$-userfn to
;     support top-level evaluation of ground apply$ expressions.  These magic
;     functions are defined in the source file apply-raw.lisp.

; Historical Note: In the foundational work we did two separate attachments.
; But now we have to do a simultaneous attachment to both functions because now
; the constraint on apply$-userfn mentions badge-userfn.

(defattach
  (badge-userfn doppelganger-badge-userfn)
  (apply$-userfn doppelganger-apply$-userfn)
  :hints
  (("Goal" :use (doppelganger-badge-userfn-type
                 doppelganger-apply$-userfn-takes-arity-args))))

; -----------------------------------------------------------------
; 12. Loop$ Scions
;     Define the loop$ scions.  See the Essay on Loop$ in translate.lisp.

; The definitions below are in :program mode.  See community book
; books/system/apply/loop.lisp for termination and guard verification, which
; makes these common-lisp-compliant in the build (see
; *system-verify-guards-alist*).

; See the Essay on Loop$ in the ACL2 source code for a guide to the translation
; of plain and fancy loops.

; -----------------------------------------------------------------
; Tails and Its Tail Recursive Counterpart

; Rather than define accumulator scions, like sum$ and collect$ for both IN
; iteration and ON iteration, we always use IN iteration but lift the target,
; lst, to a list of its successive tails.  Furthermore, we define tails both
; the ``natural'' way and via tail-recursion so that we reason about the
; natural definition but compute in the ACL2 top-level loop via the
; tail-recursive version.  We do this generally for all the functions involved
; in the semantics of LOOP$.  So you'll see the same dance over and over:
; define the tail-recursive version, define the natural version with an mbe but
; with verify-guards nil, prove the lemma equating them, and verify-guards to
; install the fast :exec.

; See apply-prim.lisp for definitions of tails-ac and tails.

; -----------------------------------------------------------------
; Loop$-as and Its Tail Recursive Counterpart

; See apply-prim.lisp for definitions of empty-loop$-as-tuplep,
; car-loop$-as-tuple, cdr-loop$-as-tuple, loop$-as-ac, and loop$-as.

; -----------------------------------------------------------------
; From-to-by and Its Tail Recursive Counterpart

; See apply-prim.lisp for definitions of from-to-by-measure, from-to-by-ac, and
; from-to-by.

; Timing Comparision
; (time$ (length (from-to-by 1 1000000 1))
; Before verify-guards: 0.27 seconds realtime, 0.27 seconds runtime
; After verify-guards:  0.06 seconds realtime, 0.06 seconds runtime

; In the following comments use the constant *m*, defined by (defconst *m*
; (from-to-by 1 1000000 1)), in our standard timing tests to see whether our
; tail-recursive definitions and guard verification help.

;-----------------------------------------------------------------
; Note: See *system-verify-guards-alist* to make scions be in :logic mode.  See
; boot-strap-pass-2-b.lisp for where these functions are warranted during a
; standard build.
; -----------------------------------------------------------------
; Until$, Until$+, and Their Tail Recursive Counterparts

(defun until$-ac (fn lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst)
                       (true-listp ac))
                  :mode :program))
  (cond
   ((endp lst) (revappend ac nil))
   ((apply$ fn (list (car lst))) (revappend ac nil))
   (t (until$-ac fn (cdr lst) (cons (car lst) ac)))))

(defun until$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list (car lst)))
               nil
               (cons (car lst)
                     (until$ fn (cdr lst)))))
       :exec
       (until$-ac fn lst nil)))

; Timing Comparision
; (time$ (length (until$ (lambda$ (x) (equal x 'abc)) *m*)))
; Before verify-guards: 0.56 seconds realtime, 0.56 seconds runtime
; After verify-guards:  0.32 seconds realtime, 0.32 seconds runtime

(defun until$+-ac (fn globals lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst)
                       (true-listp ac))
                  :mode :program))
  (cond
   ((endp lst) (revappend ac nil))
   ((apply$ fn (list globals (car lst))) (revappend ac nil))
   (t (until$+-ac fn globals (cdr lst) (cons (car lst) ac)))))

(defun until$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list globals (car lst)))
               nil
               (cons (car lst)
                     (until$+ fn globals (cdr lst)))))
       :exec
       (until$+-ac fn globals lst nil)))

; -----------------------------------------------------------------
; When$, When$+, and Their Tail Recursive Counterparts

(defun when$-ac (fn lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst)
                       (true-listp ac))
                  :mode :program))
  (if (endp lst)
      (revappend ac nil)
      (when$-ac fn (cdr lst)
                (if (apply$ fn (list (car lst)))
                    (cons (car lst) ac)
                    ac))))

(defun when$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list (car lst)))
               (cons (car lst)
                     (when$ fn (cdr lst)))
               (when$ fn (cdr lst))))
       :exec (when$-ac fn lst nil)))

; Timing Comparision
; (time$ (length (when$ 'integerp *m*)))
; Before verify-guards: 0.52 seconds realtime, 0.52 seconds runtime
; After verify-guards:  0.25 seconds realtime, 0.25 seconds runtime

(defun when$+-ac (fn globals lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst)
                       (true-listp ac))
                  :mode :program))
  (if (endp lst)
      (revappend ac nil)
      (when$+-ac fn globals
                 (cdr lst)
                 (if (apply$ fn (list globals (car lst)))
                     (cons (car lst) ac)
                     ac))))

(defun when$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
           (if (apply$ fn (list globals (car lst)))
               (cons (car lst)
                     (when$+ fn globals (cdr lst)))
               (when$+ fn globals (cdr lst))))
       :exec (when$+-ac fn globals lst nil)))

; -----------------------------------------------------------------
; Sum$, Sum$+, and Their Tail Recursive Counterparts

(defun sum$-ac (fn lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst)
                       (acl2-numberp ac))
                  :mode :program))
  (if (endp lst)
      ac
    (sum$-ac fn
             (cdr lst)
             (+ (ec-call (the-number (apply$ fn (list (car lst)))))
                ac))))

; Note the "fixing" in both sum$-ac and sum$.  Once upon a time we thought
; perhaps we could avoid the fixing in sum$-ac by arranging for sum$-ac to be
; treated as a special loop$ scion, which would have imposed the guard
; conjecture that fn returns a number on every newv in lst.  But that would
; require us to strengthen the :guard below on sum$ accordingly, with the
; condition that (apply$ fn (list x)) is a number for every x in lst.  So the
; fixing in sum$-ac is necessary if we're to avoid that additional
; guard-checking expense for calls of sum$.

(defun sum$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           0
           (+ (ec-call (the-number (apply$ fn (list (car lst)))))
              (sum$ fn (cdr lst))))
       :exec (sum$-ac fn lst 0)))

(defun sum$+-ac (fn globals lst ac)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst)
                       (acl2-numberp ac))
                  :mode :program))
  (if (endp lst)
      ac
    (sum$+-ac fn globals
              (cdr lst)
              (+ (ec-call (the-number (apply$ fn (list globals (car lst)))))
                 ac))))

(defun sum$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           0
           (+ (ec-call (the-number (apply$ fn (list globals (car lst)))))
              (sum$+ fn globals (cdr lst))))
       :exec (sum$+-ac fn globals lst 0)))

; -----------------------------------------------------------------
; Always$ and Always$+

; Note there is no need for the -ac versions since always$ is tail-recursive!
; Thus, there's no use of MBE or delayed guard verification in always$, unlike
; sum$.

(defun always$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :mode :program))
  (if (endp lst)
      t
      (if (apply$ fn (list (car lst)))
          (always$ fn (cdr lst))
          nil)))

(defun always$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :mode :program))
  (if (endp lst)
      t
      (if (apply$ fn (list globals (car lst)))
          (always$+ fn globals (cdr lst))
          nil)))

; -----------------------------------------------------------------
; Thereis$ and Thereis$+

; Note there is no need for the -ac versions since thereis$ is tail-recursive!
; Thus, there's no use of MBE or delayed guard verification in thereis$, unlike
; sum$.

(defun thereis$ (fn lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil))
                       (true-listp lst))
                  :mode :program))
  (if (endp lst)
      nil
      (or (apply$ fn (list (car lst)))
          (thereis$ fn (cdr lst)))))

(defun thereis$+ (fn globals lst)
  (declare (xargs :guard
                  (and (apply$-guard fn '(nil nil))
                       (true-listp globals)
                       (true-list-listp lst))
                  :mode :program))
  (if (endp lst)
      nil
      (or (apply$ fn (list globals (car lst)))
          (thereis$+ fn globals (cdr lst)))))


; -----------------------------------------------------------------
; Collect$, Collect$+, and Their Tail Recursive Counterparts

(defun collect$-ac (fn lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst)
                              (true-listp ac))
                  :mode :program))
  (cond ((endp lst) (revappend ac nil))
        (t (collect$-ac fn (cdr lst)
                        (cons (apply$ fn (list (car lst))) ac)))))

(defun collect$ (fn lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
           (cons (apply$ fn (list (car lst)))
                 (collect$ fn (cdr lst))))
       :exec (collect$-ac fn lst nil)))

(defun collect$+-ac (fn globals lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst)
                              (true-listp ac))
                  :mode :program))
  (cond ((endp lst) (revappend ac nil))
        (t (collect$+-ac fn globals
                         (cdr lst)
                         (cons (apply$ fn (list globals (car lst))) ac)))))

(defun collect$+ (fn globals lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
           (cons (apply$ fn (list globals (car lst)))
                 (collect$+ fn globals (cdr lst))))
       :exec (collect$+-ac fn globals lst nil)))

; -----------------------------------------------------------------
; Append$, Append$+, and Their Tail Recursive Counterparts

; A hard-to-model aspect of the CLTL's LOOP APPEND accumulation is that it
; preserves the final cdr of the last result but, obviously, wipes out the
; final cdrs of the rest of the results.

; ? (loop for x in '((1 2 3 . 7) (4 5 6)) append x)
; (1 2 3 4 5 6)
; ? (loop for x in '((1 2 3 . 7) (4 5 6 . 8)) append x)
; (1 2 3 4 5 6 . 8)

; Rather than try to model this behavior (which would complicate subsequent
; proofs about loop$ append) we just require all results to be true-listps.
; Logically, we'll fix each result with, essentially, fix-true-list.  But the
; special loop$ scion guard conjectures will require it to be proved because
; CLTL doesn't fix the result.

(defun append$-ac (fn lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst)
                              (true-listp ac))
                  :mode :program))
  (cond ((endp lst) (revappend ac nil))
        (t (append$-ac fn
                       (cdr lst)

; We could be more efficient by avoiding ec-call, instead using a version of
; revappend that tests the end with atom instead of endp.  But this way, a
; guard violation will mention the entire offending list, which is particularly
; useful when it's encountered on behalf of (loop$ for ... append ...).  That
; is the common use case, and if someone wants speed they should verify guards
; so that loop$ becomes loop.

                       (ec-call (revappend
                                 (apply$ fn (list (car lst)))
                                 ac))))))

(defun append$ (fn lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil))
                              (true-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
         (append
          (ec-call (the-true-list (apply$ fn (list (car lst)))))
          (append$ fn (cdr lst))))
       :exec (append$-ac fn lst nil)))

(defun append$+-ac (fn globals lst ac)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst)
                              (true-listp ac))
                  :mode :program))
  (cond ((endp lst) (revappend ac nil))
        (t (append$+-ac fn
                        globals
                        (cdr lst)
                        (revappend
                         (ec-call
                          (the-true-list (apply$ fn (list globals (car lst)))))
                         ac)))))

(defun append$+ (fn globals lst)
  (declare (xargs :guard (and (apply$-guard fn '(nil nil))
                              (true-listp globals)
                              (true-list-listp lst))
                  :mode :program))
  (mbe :logic
       (if (endp lst)
           nil
           (append
            (ec-call (the-true-list (apply$ fn (list globals (car lst)))))
            (append$+ fn globals (cdr lst))))
       :exec (append$+-ac fn globals lst nil)))

; lexp, d<, and l< are from books/ordinals/lexicographic-book.lisp.  They are
; needed in the body of do$ below.  Don't change the formals or anything
; else about these defuns since that will break the lexicographic-book.

(defun nfix-list (list)
  (declare (xargs :guard t))
  (if (consp list)
      (cons (nfix (car list))
            (nfix-list (cdr list)))
      nil))

(defun lexp (x)
  (declare (xargs :guard t))
  (or (natp x)
      (and (consp x) (nat-listp x))))

(defun lex-fix (x)
  (declare (xargs :guard t))
  (cond ((atom x) (nfix x))
        (t (nfix-list x))))

(defun d< (x y)
  (declare (xargs :guard (and (nat-listp x) (nat-listp y))))
  (and (consp x)
       (consp y)
       (or (< (car x) (car y))
           (and (= (car x) (car y))
                (d< (cdr x) (cdr y))))))

(defun l< (x y)
  (declare (xargs :guard (and (lexp x) (lexp y))))
  (or (< (len x) (len y))
      (and (= (len x) (len y))
           (if (atom x) (< x y) (d< x y)))))

(defun loop$-default-values1 (values alist)
; See loop$-default-values.
  (declare (xargs :guard t))
  (cond
   ((atom values)
    nil)
   (t (cons (cond
             ((eq (car values) nil) nil)
             ((eq (car values) :df) 0) ; = #d0.0
             (t (cdr (hons-assoc-equal (car values) alist))))
            (loop$-default-values1 (cdr values) alist)))))

(defun loop$-default-values (values alist)

; For the given values, which is really a stobjs-out list, return a list with
; that output signature, in which the values for non-stobjs are nil, the values
; of any :dfs are 0, and the values for any stobjs are obtained from the alist.
; If the values has only one element, we return just the car of the list just
; described.

  (declare (xargs :guard t))
  (cond
   ((and (consp values) (cdr values))
    (loop$-default-values1 values alist))
   (t (car (loop$-default-values1 values alist)))))

; WARNING: Much like the other loop$ scions above, do$ is admitted in :program
; mode and converted to :logic mode during the normal build in
; boot-strap-pass-2-b.lisp, where we convert all the loop$ scions to
; guard-verified :logic mode and warrant them.  However, DO$ is exceptional in
; a couple of ways.  (1) Its measure depends on apply$, and we work around this
; explicitly in chk-acceptable-defwarrant (see the Do$ Wart there).  (2) Its
; well-founded relation is L< with domain LEXP, whose necessary proof of
; well-foundedness seems much more appropriate for a book, where it has existed
; well before the addition of DO$, than in the build.  We get around that issue
; by "cheating" in primordial-world-globals, where we add the combination of L<
; and LEXP to the well-founded-relation-alist; but we verify that "cheat" in
; check-system-events, as noted in comments in the definitions of both of them.

; See the note following the defun of do$ for an illustration of a bug in an
; earlier version of the definition.

(defun do$ (measure-fn alist do-fn finally-fn values dolia)
  (declare (xargs :guard (and (apply$-guard measure-fn '(nil))

; I don't actually need to know that alist is an alist.  If I insert it as
; part of the guard, I have to prove it when I recur on the new-alist.
;                             (alistp alist)

                              (apply$-guard do-fn '(nil))
                              (apply$-guard finally-fn '(nil))
                              (weak-dolia-p dolia))
                  :mode :program
                  :measure (lex-fix (apply$ measure-fn (cons alist 'nil)))
                  :well-founded-relation l<
                  ))

; I don't know that the do-fn or finally-fn actually return well-formed
; triples!  So I coerce their answers to true-lists, which allows me
; to car and cdr them.

  (let* ((triple (true-list-fix (apply$ do-fn (list alist))))
         (exit-token (car triple))
         (val (cadr triple))
         (new-alist (caddr triple)))
    (cond
     ((eq exit-token :return)
      val)
     ((eq exit-token :loop-finish)
; Evaluate the finally body.  If it executes a :return, return the given value;
; else, return nil.
      (let* ((triple (true-list-fix (apply$ finally-fn (list new-alist))))
             (exit-token (car triple))
             (val (cadr triple)))
        (if (eq exit-token :return)
            val
            nil)))
     ((l< (lex-fix (apply$ measure-fn (list new-alist)))
          (lex-fix (apply$ measure-fn (list alist))))
      (do$ measure-fn new-alist do-fn finally-fn values dolia))
     (t (prog2$
         (let ((all-stobj-names (true-list-fix
                                 (access dolia dolia :all-stobj-names)))
               (untrans-measure (access dolia dolia :untrans-measure))
               (untrans-do-loop$ (access dolia dolia :untrans-do-loop$)))
           (er hard? 'do$
               "The measure, ~x0, used in the do loop$ ~
                statement~%~Y12~%failed to decrease!  Recall that do$ tracks ~
                the values of do loop$ variables in an alist.  The measure is ~
                computed using the values in the alist from before and after ~
                execution of the body.  We cannot print the values of double ~
                floats and live stobjs, if any are found in the alist, ~
                because they are raw Lisp objects, not ACL2 objects.  We ~
                print any double float as its corresponding rational and ~
                simply print the name of any live stobj (as a ~
                string).~%~%Before execution of the do body the alist ~
                was~%~Y32.~|After the execution of the do body the alist ~
                was~%~Y42.~|Before the execution of the body the measure ~
                was~%~x5.~|After the execution of the body the measure ~
                was~%~x6.~|~%Logically, in this situation the do$ returns the ~
                value of a term whose output signature is ~x7, where the ~
                value of any component of type :df is #d0.0 and the value of ~
                any stobj component is the last latched value of that stobj."
               untrans-measure
               untrans-do-loop$
               nil
               (eviscerate-do$-alist alist all-stobj-names)
               (eviscerate-do$-alist new-alist all-stobj-names)
               (apply$ measure-fn (list alist))
               (apply$ measure-fn (list new-alist))
               values))
         (loop$-default-values values new-alist))))))
)

; About a bug in DO$ in ACL2 Version_8.5

; In v85, the fifth formal of do$ was named `default', it was initialized by
; translate11-loop$ to be some default value, was passed along unchanged as do$
; iterated, and was returned if and when the measure failed to decrease.
; Actually, before returning the default value, do$ causes a hard error
; explaining the problem.  Logically, of course, the hard error just returns
; nil and the default value is returned.

; However, we realized during the development of v86 that this was a bug.
; Returning a default value computed before the loop$ executes can violate
; single-threadedness if the default value is or includes a stobj.  The problem
; is that as do$ repeatedly executes the body of the do loop$ it may be
; modifying the stobj.  So, logically speaking, if the measure fails to
; decrease, do$ returns the initial value of the stobj, when in fact it has
; modified it.

; This can be demonstrated in v85 as follows:

; (include-book "projects/apply/top" :dir :system)
; (defstobj st fld)
; (defwarrant fld)
; (defwarrant update-fld)

; (defun rev! (lst st)

; ; This function reverses lst and leaves the result in (fld st).  It works by
; ; accumulating successive elements into that field, after setting (fld st) to
; ; nil.  HOWEVER, if the element BANG is encountered the do loop$ below fails
; ; to terminate.  That causes do$ to print a hard error and return the initial
; ; stobj which is allegedly preserved in the `default' argument of do$.

;   (declare (xargs :stobjs (st)
;                   :guard (true-listp lst)
;                   :verify-guards nil))
;   (let ((st (update-fld nil st)))
;     (loop$ with x = lst
;            do
;            :measure (acl2-count x)
;            :guard (and (stp st)
;                        (true-listp x))
;            :values (st)
;            (if (equal x nil)
;                (return st)
;                (progn
;                  (setq st (update-fld (cons (car x) (fld st)) st))
;                  (setq x (if (eq (car x) 'bang)
;                              x
;                              (cdr x))))))))

; Normal behavior:  It really seems to reverse lst into (fld st).
; ACL2 !>(rev! '(1 2 3) st)
; <st>
; ACL2 !>(fld st) ; = (3 2 1)

; The following thm can be proved in v85:

; (thm (implies (warrant fld update-fld)
;               (let ((st (rev! '(BANG 4) st)))
;                 (equal (fld st) nil))))

; That is, when the list (BANG 4) is `reversed' the final value of (fld st) is
; nil.  That is because on the list in question, the measure fails to decrease,
; so the do loop$ causes a hard error and returns the stobj as it was at the
; beginning of the loop$.  But (fld st) in that version of the stobj is nil
; because that is how rev! initializes it.

; However, contrary to the theorem above, if we execute this rev! at the
; top-level of the ACL2 loop a hard error is caused, as expected.  This error
; prevents us from seeing the value.  We know from the defun that the value is
; st, and from the theorem above we expect (fld st) to be nil.  But in fact it
; is not:

; ACL2 !>(rev! '(BANG 4) st)
; HARD ACL2 ERROR in DO$:  The measure, (ACL2-COUNT X), used in the do
; loop$ statement ... failed to decrease! ...

; ACL2 !>(fld st) ; = (BANG)

; Now, in fact, the hard error signalled in the v85 defun of do$ contains a bug
; that provokes a hard raw Lisp error.  So the whole interaction is confusing.

; This confusion can be avoided by redefining hard-error to simply return nil
; (in a way that is not detected as being logically redundant) and turning off
; guard checking, e.g.,

; :redef+
; (defun hard-error (ctx str alist) (declare (ignore ctx str alist)) (car nil))
; :redef-
; (set-guard-checking :none)

; And now we see an actual log that shows behavior contradicting the thm above:

; ACL2 >(rev! '(bang 4) st)
; <st>
; ACL2 >(fld st)
; (BANG)
; ACL2 >

; So in v86 we changed the defun of do$ so that the fifth argument is now the
; output signature (which is specified by the value given to the do loop$
; keyword :values).  In fact, in v86, that argument is named `values'.  If the
; measure fails to decrease a suitable default answer is computed having the
; signature specified by :values.  That default object is composed of default
; constant values except for the stobjs.  The values returned for the stobjs
; are the last latched values from the iteration.

; Thus, in v86 the following theorem is provable

; (thm (implies (warrant fld update-fld)
;               (let ((st (rev! '(BANG 4) st)))
;                 (equal (fld st) '(BANG)))))

; which is consistent with observed behavior.

;-----------------------------------------------------------------
; Note: See *system-verify-guards-alist* to make scions be in :logic mode.  See
; boot-strap-pass-2-b.lisp for where these functions are warranted during a
; standard build.
;-----------------------------------------------------------------


