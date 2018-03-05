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
;    These functions will be used by def-warrant to infer badges which
;    maintains a data structure containing previously inferred badges.

; 5. BADGER and the Badge-Table
;    Define the :PROGRAM mode function BADGER, which infers the badge (if any)
;    of a defined function.  The key routine in BADGER is a :PROGRAM mode
;    interative inference mechanism called GUESS-ILKS-ALIST.

; 6. Essay on CHECK-ILKS
;    For purposes of reassurance only, we locally convert GUESS-ILKS-ALIST to a
;    :LOGIC mode function and prove that when it returns non-erroneously the
;    badge has certain key properties, (b)-(e), which are enumerated when we
;    discuss BADGER.  These properties are not immediately obvious from the
;    defun of GUESS-ILKS-ALIST because it is iterative and is full of error
;    messages.  To state this theorem we will define the :LOGIC mode function
;    CHECK-ILKS.  But this work is not done in the source file.  It is only
;    done during the :acl2-devel certification of the books/system/apply/
;    books.  We leave the essay here to remind us that guess-ilks-alist is
;    really known to imply properties (b)-(e).

; 7. Functional Equivalence
;    Define the functional equivalence relation and prove that it is a
;    congruence relation for APPLY$.  Def-warrant will prove the appropriate
;    congruence rules for each :FN formal of newly badged functions.

; 8. DEF-WARRANT
;    Define DEF-WARRANT.

; 9. DEFUN$
;    Define DEFUN$.

; Historical Note:  Once upon a time we had

;    10. The LAMB Hack
;        Define (LAMB vars body) to be `(LAMBDA ,vars ,body) to provide a
;        rewrite target for functional-equivalence lemmas.  Since ACL2 doesn't
;        rewrite constants, we won't even try to simplify a quoted lambda.  We
;        are not satisfied with the treatment of functional equivalence yet and
;        LAMB is sort of a reminder and placeholder for future work.

; However, we have removed that from the sources because we are not yet
; convinced it is a good way to address the problem of rewriting equivalent
; LAMBDAs.  We plan to experiment with solutions in the user-maintained books.
; As of Version_8.0, our best shot is in
; books/projects/apply/apply-lemmas.lisp, but this may change.

; 11. The Defattach
;     We attach ``magic'' functions to badge-userfn and apply$-userfn to
;     support top-level evaluation of ground apply$ expressions.  These magic
;     functions are defined in the source file apply-raw.lisp.

; Note: This entire file is processed only in pass 2, fundamentally because
; apply$-primp and apply$-prim are only defined in pass 2.

(when-pass-2

; -----------------------------------------------------------------
; 1. Badges

(defun badge (fn)
  (declare (xargs :guard t :mode :logic))
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

#-acl2-devel
(in-theory (disable badge))

; -----------------------------------------------------------------
; 2. Tameness

; These functions are defined for speed, not clarity.  Aside from the obvious
; logical requirements of tameness -- roughly speaking, every function is
; either tame or is a mapping function supplied with quoted tame functions in
; the right places -- we want (tamep x) to imply that x is either a symbol or a
; true-listp and to imply that every function call in x is supplied with the
; right number of arguments (at least with respect to the arities reported by
; badge), and we want tamep guard verified with a guard of t.

(defabbrev tamep-lambdap (fn)

; Fn is allegedly a LAMBDA expression.  We know it's a consp!  We check that it
; has just enough structure to allow guard checking of the tamep clique.  This
; does not actually assure us that the LAMBDA is well formed.  We don't check,
; for example, that the lambda formals are distinct or that the lambda-body is
; a termp with no other free vars.  The weakness of this definition just means
; that apply$ and ev$ assign meaning to some LAMBDA applications that ACL2
; would reject.  That's ok as long as we don't try to evaluate those
; applications directly, e.g., by compiling them.  Finally, we define this as
; an abbreviation because we use it several times in the tamep clique and don't
; want to introduce another function into the mutual recursion.

  (and (eq (car fn) 'LAMBDA)
       (consp (cdr fn))
       (symbol-listp (lambda-formals fn))
       (consp (cddr fn))
       (tamep (lambda-body fn))
       (null (cdddr fn))))

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
  (declare (xargs :guard (true-listp args)
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
; succinct and might actually ruin the doppelganger construction in the
; foundational work of books/projects/apply-model/ (we haven't tried) because
; in that construction there are other symbols besides APPLY$ and EV$ you can't
; apply.  But the reason we keep the full blown tamep-functionp test is more
; aesthetic: it makes the tameness conditions in the ``warrant for apply$''
; (which doesn't actually exist but which is embodied in the lemma
; apply$-APPLY$ proved in books/projects/apply/apply-lemmas.lisp) exactly
; analogous to the tameness conditions for user-defined mapping functions like
; COLLECT.  There is a similar ``warrant for ev$'' embodied in the apply-lemma
; apply$-EV$.

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

  (declare (xargs :guard (and (consp fn) (true-listp args))
                  :guard-hints (("Goal" :do-not-induct t))))
  (ev$ (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
       (ec-call
        (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                  args))))

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
; (true-listp args) and apply$-lambda where we additionally know that fn is a
; cons (LAMBDA-expression).

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
; collect and the tame lambda expression into a tame lambda and apply it
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
; have the function occur in our proofs and so we will always expand it away
; (see apply$-lambda-opener in books/projects/apply/apply-lemmas.lisp).

; About the definition of EV$:

; In books/projects/apply/apply-lemmas.lisp we we prove a simpler version of
; the defun of EV$, conditioned by the hypothesis that x is tamep.  (This
; simpler definition, called ev$-def is LOCAL to that book but is used to prove
; ev$-opener which embodies the definition in an effective way.)  So why do we
; define EV$ as we do above?  In the two clauses dealing with calls of APPLY$
; and EV$ we apply$ the relevant function symbol rather than just calling it,
; e.g., we write (apply$ 'apply$ ...)  instead of (apply$ ...).  We do it this
; way so that we can more easily prove that in all cases, ev$ handles function
; calls by calling apply$ on the ev$-list of the arguments.  But note that we
; don't write it quite that way because we need to prove termination.  That is,
; instead of calling ev$-list we actually write an explicit list of the two
; arguments (list (cadr (cadr x)) (EV$ (caddr x) a)).  Note in particular that
; we do not ev$ the first argument but just take its cadr!  This insures
; termination and is equivalent to (ev$ (cadr x) a) PROVIDED the argument is
; tame!  Note also that we could have called (ev$-list (cdr x) a) had we known
; (cdr x) was suitably tame but that would require admitting this clique as a
; reflexive function: the fact that (ev$ (cadr x) a) is smaller than (cadr x)
; when (cadr x) is tame requires reasoning about ev$ before it is admitted.

#-acl2-devel
(in-theory (disable badge
                    (:executable-counterpart badge)))

; -----------------------------------------------------------------
; 4. Executable Versions of BADGE and TAMEP

; In order to infer badges of new functions as will be done in def-warrant we
; must be able to determine the badges of already-badged functions.  Similarly,
; we must be able to determine that certain quoted expressions are tame.  So we
; define executable versions of badge and tamep that look at data structures
; maintained by def-warrant.

(defun executable-badge (fn wrld)

; Find the badge, if any, for fn in wrld; else return nil.  Aside from
; primitives and the apply$ boot functions, all badges are stored in the
; badge-table entry :badge-userfn-structure.

; Aside: Finding a badge doesn't mean there is a warrant: if the
; :authorization-flg of the badge is nil, there is no warrant, which means
; badge-userfn and thus badge are logically undefined on fn.  But this
; function is used during the analysis of a newly submitted function to
; determine its badge and (possibly) its warrant.

; There's nothing wrong with putting this in logic mode but we don't need it in
; logic mode here.  This function is only used by def-warrant, to analyze and
; determine the badge, if any, of a newly submitted function.  (To be accurate,
; this function is called from several places, but all of them are only
; involved in the def-warrant computation.)  Of course, the badge computed by a
; non-erroneous (def-warrant fn) is then built into the defun of
; APPLY$-WARRANT-fn and thus participates in logical reasoning; so the results
; computed by this function are used in proofs.

  (declare (xargs :mode :program))
  (cond
   ((symbolp fn)
    (let ((temp (hons-get fn *badge-prim-falist*)))
      (cond
       (temp (cdr temp))
       ((eq fn 'BADGE) *generic-tame-badge-1*)
       ((eq fn 'TAMEP) *generic-tame-badge-1*)
       ((eq fn 'TAMEP-FUNCTIONP) *generic-tame-badge-1*)
       ((eq fn 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*)
       ((eq fn 'APPLY$) *apply$-badge*)
       ((eq fn 'EV$) *ev$-badge*)
       (t (get-badge fn wrld)))))
   (t nil)))

; Compare this to the TAMEP clique.

(defabbrev executable-tamep-lambdap (fn wrld)
  (and (eq (car fn) 'LAMBDA)
       (consp (cdr fn))
       (symbol-listp (lambda-formals fn))
       (consp (cddr fn))
       (executable-tamep (lambda-body fn) wrld)
       (null (cdddr fn))))

(mutual-recursion

(defun executable-tamep (x wrld)
  (declare (xargs :mode :program))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((bdg (executable-badge (car x) wrld)))
           (cond
            ((null bdg) nil)
            ((eq (access apply$-badge bdg :ilks)
                 t)
             (executable-suitably-tamep-listp
              (access apply$-badge bdg :arity)
              nil
              (cdr x)
              wrld))
            (t (executable-suitably-tamep-listp
                (access apply$-badge bdg :arity)
                (access apply$-badge bdg :ilks)
                (cdr x)
                wrld)))))
        ((consp (car x))
         (let ((fn (car x)))
           (and (executable-tamep-lambdap fn wrld)
                (executable-suitably-tamep-listp (length (cadr fn))
                                                 nil
                                                 (cdr x)
                                                 wrld))))
        (t nil)))

(defun executable-tamep-functionp (fn wrld)
  (declare (xargs :mode :program))
  (if (symbolp fn)
      (let ((bdg (executable-badge fn wrld)))
        (and bdg
             (eq (access apply$-badge bdg :ilks)
                 t)))
    (and (consp fn)
         (executable-tamep-lambdap fn wrld))))

(defun executable-suitably-tamep-listp (n flags args wrld)
  (declare (xargs :mode :program))
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
                 (executable-tamep-functionp (cadr arg) wrld)))
           (:EXPR
            (and (consp arg)
                 (eq (car arg) 'QUOTE)
                 (consp (cdr arg))
                 (null (cddr arg))
                 (executable-tamep (cadr arg) wrld)))
           (otherwise
            (executable-tamep arg wrld))))
       (executable-suitably-tamep-listp (- n 1) (cdr flags) (cdr args) wrld)))))
)

; -----------------------------------------------------------------
; 5. BADGER and the Badge-Table

; Recall (from constraints.lisp) that three categories of functions have
; badges: the ~800 apply$ primitives, the 6 apply$ boot functions, and all the
; user-defined functions on which def-warrant succeeded.  The last category of
; badges are stored in the badge-table under the key :badge-userfn-structure.
; Given a function fn, (executable-badge fn wrld), defined above in this file,
; returns the badge, or nil.  We are here primarily interested in the
; badge-table, which is maintained by def-warrant.  Recall also that having a
; badge and having a warrant are two different things.  Fn can have a badge but
; no warrant.  If fn's badge has :authorization-flg nil, it has no warrant; if
; the :authorization-flg is t, it has a warrant named APPLY$-WARRANT-fn.
; Def-warrant infers badges (and builds warrants with them) by recursively
; inspecting the body of defun'd functions.  It uses executable-badge to
; acquire badges of subroutines.

; Here are some terms we use below:

; ilk: one of the symbols NIL, :FN, or :EXPR; if a variable or argument
;  position has ilk NIL we sometimes say it is ``vanilla'' or ``ordinary.''  If
;  a variable or argument position has ilk :FN we say it is ``functional'' and
;  if it has ilk :EXPR we say it is ``expressional.''  The badge inference
;  mechanism uses two more pseudo-ilks, :unknown and :unknown*, which never get
;  out of that inference mechanism and should not be confused with ilks.

; ilks: a true list of ilk (or pseudo-ilk) symbols or T denoting a list of as
;  many NILs as we'll need.  The ilks associated with a function symbol fn with
;  formals v1, ..., vn, has length n, and successive formals have the
;  corresponding ilk in ilks.  For example, if ilks is (NIL :FN :EXPR) and the
;  formals are (X Y Z), then X is vanilla, Y is functional and Z is
;  expressional.

; badge: a defrec record structure object associated with a function symbol fn.

;  The badge has name APPLY$-BADGE and three fields:
;  :authorization-flg - indicates whether fn returns a single value
;    or multiple values
;  :arity - the arity of fn
;  :ilks - ilks (of length equal to the arity of fn) corresponding to the
;    formals of fn, or else T denoting a list of nils of the appropriate
;    length.

;   For example, the function COLLECT has badge
;   (APPLY$-BADGE T            ; = :authorization-flg
;                 2            ; = :arity
;                 . (NIL :FN)) ; first formal is ordinary, second formal is
;                              ; treated like a function

;   If a function fn with formals v1, ..., vn, has a badge with
;   :authorization-flg flg, :arity n, and :ilks T or (c1 ... cn) then we know
;   that fn does not traffic in stobjs or state, that fn returns a single value
;   or multiple values according to whether flg is t, the arity of fn is n,
;   and:

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
;      def-warrant and thus:

;      (a) Fn is a defined, singly-recursive (or non-recursive) :logic mode
;          function that (if recursive) is justified with a tame measure, tame
;          domain predicate, and tame well-founded relation, and that (if
;          recursive and at least one formal has ilk :FN or :EXPR) the measure
;          is natural-number valued and the well-founded relation is o<.

;       (b) Every function called in the body of fn has a badge.  (During
;           ilk inference the function being analyzed does not have a badge and
;           but it is being inferred.)

;       (c) Every formal of ilk :FN is only passed into :FN slots and every :FN
;           slot in the body is either occupied by a formal of ilk :FN or by a
;           quoted tame function symbol other than fn itself, or a quoted
;           well-formed (fully translated and closed), tame lambda expression
;           that does not call fn.

;       (d) Every formal of ilk :EXPR is only passed into :EXPR slots and every
;           :EXPR slot in the body is either occupied by a formal of ilk :EXPR
;           or by a quoted, well-formed (fully translated), tame term that does
;           not call fn.

;       (e) If formal vi has ilk :FN or :EXPR then vi is passed unchanged into
;           the ith slot of every recursive call of fn in the body.

; mapping function: a function whose badge includes at least one :FN or :EXPR
;  ilk.

; These conditions are important to the doppelganger construction in the
; foundational work described in the paper ``Limited Second Order Functionality
; in a First Order Setting'' and in books/projects/apply-model/.

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
; the ACL2 lambda applications, not ``LAMBDA apply$'s''.  That is: One must
; distinguish ``ACL2 lambda applications,'' which are just ordinary first-class
; terms, from ``apply$'s of quoted LAMBDA expressions.''  Here we're talking
; just about expanding all of the former, i.e., getting rid of LET's, LET*'s,
; etc!]

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
; keeps track of local variables within lambdas or ilks for each lambda
; expression or something.  In any case, the presence of recursive calls both
; inside the lambdas and outside the lambdas complicates the inductive
; inference.  It is clearly simpler to just get rid of the lambda applications!

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
; (defun fn (x y) (apply$ 'binary-+ (list x y))).

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

; Here is how we beta reduce all ACL2 lambda applications.

(mutual-recursion

(defun expand-all-lambdas (term)
  (declare (xargs :mode :program))
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((flambdap (ffn-symb term))
    (expand-all-lambdas
     (subcor-var (lambda-formals (ffn-symb term))
                 (fargs term)
                 (lambda-body (ffn-symb term)))))
   (t (fcons-term (ffn-symb term)
                  (expand-all-lambdas-list (fargs term))))))

(defun expand-all-lambdas-list (terms)
  (declare (xargs :mode :program))
  (cond
   ((endp terms) nil)
   (t (cons (expand-all-lambdas (car terms))
            (expand-all-lambdas-list (cdr terms))))))
)

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

(defun well-formed-lambdap (x wrld)

; Check that x is (lambda vars body) where vars is a list of distinct legal
; variable names, body is a well-formed term wrt wrld, and the free vars of
; body are a subset of vars.

  (declare (xargs :mode :program))
  (and (consp x)
       (eq (car x) 'LAMBDA)
       (consp (cdr x))
       (arglistp (cadr x))
       (consp (cddr x))
       (termp (caddr x) wrld)
       (null (cdddr x))
       (subsetp-eq (all-vars (caddr x)) (cadr x))))

(mutual-recursion

(defun guess-ilks-alist (fn new-badge term ilk wrld alist)

; Fn is the name of a function being defined.  New-badge is either nil or a
; proposed badge for fn and term is a term (initally the body of fn) occuring
; in a slot of ilk ilk.  Note: term contains no lambda applications!  We try to
; determine the ilks of the free vars in term, extending alist to record what
; we find.  We return (mv msg alist'), where either msg is an error message and
; alist' is nil, or msg is nil and alist' is extension of alist assiging ilks
; to free vars occurring in term.

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
; pre-conditions and two passes of this function.

; A few details:

; All lambda applications in the body of the function being analyzed should be
; expanded away before this function is called.  There may still be QUOTEd
; lambda expressions used as arguments to mapping functions, but no ACL2
; lambda applications.  All free variables encountered in term are formals of
; the function being analyzed!

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
; so we consider quoted LAMBDAs separately from quoted symbols...
      (cond
       ((symbolp (cadr term))
        (cond
         ((eq fn (cadr term))
          (mv (msg "~x0 cannot be warranted because a :FN slot in its ~
                    body is occupied by a quoted reference to ~x0 itself; ~
                    recursion through APPLY$ is not permitted!"
                   fn)
              nil))
         ((executable-tamep-functionp (cadr term) wrld)
          (mv nil alist))
         (t (mv (msg "~x0 cannot be warranted because a :FN slot in its ~
                      body is occupied by a quoted symbol, ~x1, that is not a ~
                      tame function."
                     fn
                     term)
                nil))))
       ((consp (cadr term))
        (cond ((well-formed-lambdap (cadr term) wrld)
               (cond
                ((ffnnamep fn (lambda-body (cadr term)))
                 (mv (msg "~x0 cannot be warranted because a :FN slot ~
                           in its body is occupied by a quoted LAMBDA ~
                           expression, ~x1, that recursively calls ~x0; ~
                           recursion through APPLY$ is not permitted!"
                          fn
                          term)
                     nil))
                ((executable-tamep-lambdap (cadr term) wrld)
                 (mv nil alist))
                (t (mv (msg "~x0 cannot be warranted because a :FN slot ~
                             in its body is occupied by a quoted LAMBDA ~
                             expression, ~x1, whose body is not tame."
                            fn
                            term)
                       nil))))
              (t (mv (msg "~x0 will not be warranted because a :FN slot ~
                           in its body is occupied by a quoted cons object, ~
                           ~x1, that is not a well-formed, fully-translated, ~
                           closed ACL2 lambda expression.  The default ~
                           behavior of APPLY$ on ill-formed input is ~
                           nonsensical, e.g., unquoted numbers are treated ~
                           like variables and macros are treated like ~
                           undefined functions.  It is unwise to exploit this ~
                           default behavior!"
                          fn
                          term)
                     nil))))
       (t (mv (msg "~x0 cannot be warranted because a :FN slot in its ~
                    body is occupied by a quoted constant, ~x1, that does not ~
                    denote a tame function symbol or LAMBDA expression."
                   fn
                   term)
              nil))))
     ((eq ilk :EXPR)
      (cond
       ((termp (cadr term) wrld)
        (cond ((ffnnamep fn (cadr term))
               (mv (msg "~x0 cannot be warranted because an :EXPR slot ~
                         in its body is occupied by a quoted term, ~x1, that ~
                         calls ~x0; recursion through EV$ is not permitted!"
                        fn
                        term)
                   nil))
              ((executable-tamep (cadr term) wrld)
               (mv nil alist))
              (t (mv (msg "~x0 cannot be warranted because an :EXPR ~
                           slot in its body is occupied by a quoted term, ~
                           ~x1, that is not tame."
                          fn
                          term)
                     nil))))
       (t (mv (msg "~x0 will be warranted because an :EXPR slot in its ~
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
    (mv (msg "There are not supposed to be any ACL2 LAMBDA applications in ~
              the term being analyzed by guess-ilks-alist, but we have ~
              encountered ~x0!  This really indicates a coding error in ACL2 ~
              and is not your fault!  Please tell the implementors."
            term)
        nil))
   ((or (eq ilk :FN)
        (eq ilk :EXPR))
    (mv (msg "~x0 cannot be warranted because ~#1~[a :FN~/an :EXPR~] slot in ~
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
                    cannot be warranted, in which case neither can ~x0."
                   fn
                   (ffn-symb term)
                   `(def-warrant ,(ffn-symb term)))
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

(defun ancestrally-dependent-on-apply$p1 (flg x wrld acc)

; This is just all-fnnames1 except it recursively explores the body of each fn
; it encounters and it short circuits if it sees the fnnames APPLY$ or EV$.
; Flg = t means x is a list of terms; else x is a term.  Acc is just the fns
; we've seen so far and is returned, but it is incomplete if its car is APPLY$,
; which is the signal that we found EITHER APPLY$ or EV$!

  (declare (xargs :mode :program))
  (cond
   ((eq (car acc) 'apply$) acc)
   (flg ; x is a list of terms
    (cond ((null x) acc)
          (t (ancestrally-dependent-on-apply$p1
              nil
              (car x)
              wrld
              (ancestrally-dependent-on-apply$p1 t (cdr x) wrld acc)))))
   ((variablep x) acc)
   ((fquotep x) acc)
   ((flambda-applicationp x)
    (ancestrally-dependent-on-apply$p1
     nil
     (lambda-body (ffn-symb x))
     wrld
     (ancestrally-dependent-on-apply$p1 t (fargs x) wrld acc)))
   ((or (eq (ffn-symb x) 'apply$)
        (eq (ffn-symb x) 'ev$))
    (cons 'apply$ acc))
   ((member-eq (ffn-symb x) acc)
    (ancestrally-dependent-on-apply$p1
     t
     (fargs x)
     wrld
     (cons (ffn-symb x) acc)))
   (t
    (ancestrally-dependent-on-apply$p1
     nil
     (body (ffn-symb x) nil wrld)
     wrld
     (ancestrally-dependent-on-apply$p1
      t
      (fargs x)
      wrld
      (cons (ffn-symb x) acc))))))

(defun ancestrally-dependent-on-apply$p (x wrld)
  (declare (xargs :mode :program))
  (let ((ans (ancestrally-dependent-on-apply$p1 nil x wrld nil)))
    (eq (car ans) 'apply$)))

(defun acceptable-warranted-justificationp (fn ens wrld)

; Fn is a function symbol being considered for a warrant.  We check that its
; well-founded-relation is O<, that its domain recognizer is O-P, and that its
; measure is tame, natural-number valued, and not ancestrally dependent on
; APPLY$.  We just use type-set to confirm the type of the measure.

; Our motivation is two-fold.  First, during the foundational construction of
; the model we must admit every G1 function before we admit any G2 function.
; That means all the G1 functions must have measures that are also entirely in
; G1 terms.  Then when we admit the clique of doppelgangers of G2 functions we
; want all the measures to be in G1 so we don't have to think about
; simultaneously admitting the measures.  The check that every measure is tame
; and independent of APPLY$ guarantees that the measure is composed entirely of
; G1 functions.  The check that the measure is a natural guarantees that it
; will fit inside the llist used to justify the G2 doppelgangers.

; We could relax these restrictions, someetimes at the expense of more
; foundational work.

; (1) We need the natp condition only if fn is in G2.  We needn't care if G1
; functions have big measures, but we're lazy.  It requires checking whether fn
; is dependent on APPLY$ and then changing the error messages.  One might be
; tempted to not do any of this check for G1 functions but that would be a
; mistake: we don't want to warrant a G1 function whose measure is a tame G2
; function or else we couldn't admit all the G1 functions ``early.''

; (2) We could allow tame G2 functions in measures (of G1 and G2 functions) if
; we proved that every tame function is ``G1 defineable.''  We believe this but
; haven't written a proof.  The basic construction is: take a tame G2
; expression, like (m lst) where (defun m (lst) (sumlist lst '(lambda (x)
; (binary-+ '1 (nfix x))))).  Copy the definition of the G2 function (e.g.,
; sumlist), deleting the fn args and substituting the quoted tame functions for
; them, beta reducing, and fold.  The result for this m would be (defun m (lst)
; (if (endp lst) 0 (+ (+ 1 (nfix (car lst))) (m (cdr lst))))).  Of course, this
; process has to be done recursively innermost first to reach all the G2
; functions in m.  But if m is tame, we think you can always do this.  If
; someone complains that their G2 function is rejected because its measure
; depends on APPLY$, we could (i) tell them to use this construction themselves
; to fix the problem and not bother us (!), or (ii) just eliminate the
; ancestral check here, if we are really sure: every tame expression is G1
; defineable.

; (3) As for the natural-number restriction, that arises because of our use of
; the original measure for fn in the 4th component of the measure for fn! in
; our admittance of G2 doppelgangers.  We could allow bounded ordinal measures
; on G2 functions, e.g., LLIST measures.  Then the doppelganger measures would
; allot the maximum required amount of space to put all those LLISTs in as the
; ``4th component''.  But we haven't implemented such a check or described in
; the doppelganger proof how to embed the larger but bounded original measures.

  (declare (xargs :mode :program))
  (cond
   ((not (recursivep fn nil wrld)) t)
   (t (let ((just (getpropc fn 'justification nil wrld)))
        (and just
             (eq (access justification just :rel) 'O<)
             (eq (access justification just :mp) 'O-P)
             (executable-tamep
              (access justification just :measure)
              wrld)
             (not (ancestrally-dependent-on-apply$p
                   (access justification just :measure)
                   wrld))
             (mv-let (ts ttree)
               (type-set (access justification just :measure)
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
               (ts-subsetp ts *ts-non-negative-integer*)))))))

; TODO:  We could make badger a little more friendly by:

; (a) detect mutual recursion up front and produce a suitable error msg.  Right
;     now, attempting to badge a member of a mutually recursive clique fails
;     with the explanation that some other member is not badged yet.

; (b) A not-too-difficult improvement would be to include tame
;     mutual recursion.  For example, if my-even and my-odd are the obvious
;     functions, we can't APPLY$ them, even though they are tame.  If we just
;     recognized that if every subroutine used in a clique is tame (except for
;     the clique members being defined, which will have no badges yet), then
;     they're all tame and could be so badged.  This doesn't complicate the
;     model since tame functions are defined in the model just as in the user's
;     chronology and not mutually recursively with the model of APPLY$.

; (c) compute the list of all unbadged functions in a defun and produce a
;     suitable error msg.  Right now, the user is told about them one at a
;     time.

(defun badger (fn ens wrld)

; Badger returns (mv msg badge) where either msg is nil and badge is a badge
; for fn, or else msg is an error message and badge is nil.  When badger
; returns a badge we know the badge satisfies check-ilks as described in Essay
; on Check-Ilks below.

  (declare (xargs :mode :program))
  (cond
   ((and (symbolp fn)
         (arity fn wrld)
         (not (eq (getpropc fn 'symbol-class nil wrld)
                  :PROGRAM))
         (body fn nil wrld))
    (let ((body (expand-all-lambdas (body fn nil wrld)))
          (formals (formals fn wrld)))
      (cond
       ((or (not (all-nils (getpropc fn 'stobjs-in nil wrld)))
            (not (all-nils (getpropc fn 'stobjs-out nil wrld))))

; You might think that checking that if no stobjs are coming in then no stobjs
; are coming out, but you'd be wrong: stobj creators.

        (mv (msg "~x0 cannot be warranted because its signature, ~%~y1 ~
                  ==> ~y2, includes a single-threaded object!"
                 fn
                 (prettyify-stobj-flags
                  (getpropc fn 'stobjs-in nil wrld))
                 (prettyify-stobjs-out
                  (getpropc fn 'stobjs-out nil wrld)))
            nil))
       ((not (acceptable-warranted-justificationp fn ens wrld))

; We insist that every badged function be justified with O< over O-P on a
; measure m that is tame, not ancestrally dependent on APPLY$, and natp.
; See acceptable-warranted-justificationp for some explanation.

        (mv (msg "~x0 cannot be warranted because it its justification is too ~
                  complicated!  Our meta-level proof that there is a model in ~
                  which all warrants are valid requires that warranted ~
                  functions be justified by the well-founded relation O< on ~
                  the domain O-P with a measure that is tame, not ancestrally ~
                  dependent on APPLY$, and natural-number valued as ~
                  determined by type-set.  The relevant fields of ~x0's ~
                  justification are ~%well-founded relation: ~x1~%domain: ~
                  ~x2~%measure: ~x3.~%If the problem is that the measure ~
                  isn't being correctly typed by type-set, you should prove ~
                  the appropriate :type-prescription rule.  Otherwise, you ~
                  should try to admit ~x0 with an acceptable justification.  ~
                  Some of these restrictions could be relaxed at the expense ~
                  of complicating our proof that an acceptable model exists.  ~
                  If you really need ~x0 to be warranted, contact the authors!"
                 fn
                 (access justification
                         (getpropc fn 'justification nil wrld)
                         :rel)
                 (access justification
                         (getpropc fn 'justification nil wrld)
                         :mp)
                 (access justification
                         (getpropc fn 'justification nil wrld)
                         :measure))
            nil))
       (t
; We know fn is a logic mode function symbol.
        (if (quick-check-for-tamenessp fn body wrld)
            (mv nil
                (make apply$-badge
                      :authorization-flg
                      (if (cdr (getpropc fn 'stobjs-out nil wrld))
                          nil
                          t)
                      :arity (arity fn wrld)
                      :ilks t))
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
                                :authorization-flg
                                (if (cdr (getpropc fn 'stobjs-out nil wrld))
                                    nil
                                    t)
                                :arity (arity fn wrld)
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

                          (mv (msg "The second pass of the badger produced a ~
                                    different alist than the first!  The ~
                                    (completed) alist produced by the first ~
                                    pass is ~x0 but the alist produced by the ~
                                    second pass is ~x1.  This must be some ~
                                    kind of coding error in ACL2.  Please ~
                                    report this to the implementors."
                                  alist1 alist2)
                              nil)))))))))))))
   (t (mv (msg "~x0 cannot be warranted because it is not a defined ~
                :logic mode function symbol."
               fn)
          nil))))

(defun badge-table-guard (key val wrld ens)

; See the comment in def-warrant about speeding up this function by using a
; checker version of badger.  (That checker would need to be written.)

  (declare (xargs :mode :program))
  (let* ((new-entry (and (consp val) (car val)))
         (fn (and (consp new-entry) (car new-entry)))
         (specified-badge (and (consp new-entry) (cdr new-entry))))
    (cond
     ((not (eq key :badge-userfn-structure)) ; no need to protect for other keys
      t)
     ((null val) ; initial value
      t)
     ((not (consp val))
      (er hard 'badge-table
          "The value to be saved in badge-table, ~x0, is (surprisingly) not a ~
           cons."
          val))
     ((not (equal (cdr (assoc-eq :badge-userfn-structure
                                 (table-alist 'badge-table wrld)))
                  (cdr val)))
      (er hard 'badge-table
          "The badge-table was to be updated by a record based on the name ~
           ~x0 and badge ~x1, but surprisingly, the table event specified an ~
           extension by that record of~|~%  ~x2~|~%instead of specifying an ~
           extension of the existing list of stored badge structures,~|~%~  ~
           x3."
          fn
          specified-badge
          (cdr val)
          (cdr (assoc-eq :badge-userfn-structure
                         (table-alist 'badge-table wrld)))))
     (t (mv-let
          (msg actual-badge)
          (badger fn ens wrld) ; see comment above about possible checker
          (cond
           (msg (er hard 'badge-table "~@0" msg))
           ((not (equal specified-badge actual-badge))
            (er hard 'badge-table
                "The badge-table update for the name ~x0 specifies a badge of ~
                 ~x1, but the correct badge is ~x2."
                fn specified-badge actual-badge))
           (t t)))))))

(table badge-table nil nil
       :guard
       (badge-table-guard key val world ens))

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

; Fourth, inspection of badger above shows that it signals an error unless fn is
; a defined (not constrained) :logic mode function symbol that does not traffic
; in stobjs or state and that has a natural-number valued measure that
; decreases according to o<.

; Fifth, when badger returns non-erroneously, the badge is constructed with
; make apply$-badge with obviously correct settings for :authorization-flg and
; :arity.  The only question is whether :ilks is set correctly.

; Assurances on Badged Functions (recapitulation)

; If badger assigns new-badge as the badge of fn with (beta-reduced) body,
; body, then we know:

; (a) Fn is a defined, singly-recursive (or non-recursive) :logic mode function
;     that does not traffic in stobjs or state and that (if recursive) is
;     justified with a natural number valued measure decreasing by o<.
;     Furthermore, the badge returned is an apply$-badgep with correct
;     :authorization-flg and :arity and :ilks of either T or a list (in 1:1
;     correspondence with the formals of fn) of NIL, :FN, and/or :EXPR tokens.

; (b) Every function called in body has a badge (including fn if we consider
;     new-badge the badge of fn).

; (c) Every formal of ilk :FN is only passed into :FN slots, and
;     every :FN slot in the body is occupied by
;     * a formal variable of ilk :FN in new-badge, or
;     * a quoted tame function symbol other than fn, or
;     * a quoted, well-formed (fully translated and closed), tame lambda
;       expression that does not call fn.

; (d) Every formal of ilk :EXPR is only passed into :EXPR slots, and
;     every :EXPR slot in the body is occupied by
;     * a formal variable of ilk :EXPR in new-badge, or
;     * a quoted, well-formed (fully translated), tame term that does not call
;       fn.

; (e) If the nth formal, vn, of fn has ilk :FN or :EXPR then vn is passed
;     unchanged into the nth slot of every recursive call of fn.

; To establish this we first inspect badger and see that there are only two
; places where it returns non-erroneously, i.e., (mv nil ...).  In the first
; non-erroneous return, fn has a tame body, and so is tame, and we assign :ilks
; = t, which is obviously correct.  It is the second non-erroneous return that
; is potentially problematic.

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
; the properties of (w state) and the invariants maintained by def-warrant.

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
             :hints
             (("Goal" :in-theory (disable (:executable-counterpart force)))))
          (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn))))
   (t (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn)))))

; -----------------------------------------------------------------
; 8. DEF-WARRANT

; Suppose AP is defined (with defun$) to be a tame function of two arguments.
; Then defun$ will also do something equivalent to the following (modulo
; the note below):

; (defun-sk apply$-warrant-AP nil
;   (forall (args) (and (equal (badge 'AP) '(APPLY$-BADGE T 2 . T))
;                       (equal (apply$ 'AP args)
;                              (ap (car args) (cadr args))))))

; (defthm apply$-AP
;   (implies (force (apply$-warrant-AP))
;            (and (equal (badge 'AP) '(APPLY$-BADGE T 2 . T))
;                 (equal (apply$ 'AP args)
;                        (ap (car args) (cadr args))))))

; (in-theory (disable apply$-warrant-AP))

; which will mean that if we have the hypothesis (apply$-warrant-AP), we will
; rewrite (badge 'AP) to the given badge record and rewrite (apply$ 'AP args)
; to the appropriate call of ap.

; Note: the actual warrant is phrased in terms of badge-userfn and
; apply$-userfn, not badge and apply$, as shown above; but the rewrite rule
; apply$-AP indeed deals with badge and apply$.  We deal with this later.

(defun warrant-fn (names)

; This is a helper function for the macro warrant.  Given (a b c) we return
; ((APPLY$-WARRANT-a) (APPLY$-WARRANT-b) (APPLY$-WARRANT-c))

  (declare (xargs :mode :logic ; :program mode may suffice, but this is nice
                  :guard (symbol-listp names)))
  (cond ((endp names) nil)
        (t (cons (list (warrant-name (car names)))
                 (warrant-fn (cdr names))))))

(defmacro warrant (&rest names)

; This implements the abbreviation (warrant a b c) for:
; (AND (APPLY$-WARRANT-a) (APPLY$-WARRANT-b) (APPLY$-WARRANT-c))

  (declare (xargs :guard (symbol-listp names)))
  `(AND ,@(warrant-fn names)))

; The warrant for AP, illustrated above, is particularly simple because AP is
; tame.  All of its formals are vanilla.  The warrant for a mapping function
; like COLLECT has a tameness condition imposed by the non-vanilla ilks, e.g.,

; (defun-sk apply$-warrant-COLLECT nil
;   (forall (args)
;     (and (equal (badge 'COLLECT) '(APPLY$-BADGE T 2 NIL :FN))
;          (implies (tamep-functionp (cadr args)) ; tameness-conditions
;                   (equal (apply$ 'COLLECT args)
;                          (collect (car args)     ; successive-cadrs
;                                   (cadr args))))))
;   :constrain t)

; (BTW: The actual warrant is a defun-sk phrased in terms of badge-userfn and
; apply$-userfn, not badge and apply$, as shown above; but the rewrite rule
; indeed deals with badge and apply$.  We deal with this later.)

; We originally introduced def-warrant-event here, preceded by supporting
; functions tameness-conditions, successive-cadrs, and necc-name-ARGS-instance.
; However, we call def-warrant-event in the definition of warrantp, which in
; turn is called in the implementation of defattach in file other-events.lisp.
; So those definitions now appear in that file.

(defun def-warrant-fn1 (fn state)
  (declare (xargs :mode :program))
  (let ((ens (ens state))
        (wrld (w state))
        (apply-lemmas-book
         (extend-pathname :system "projects/apply/apply-lemmas.lisp" state)))
    (mv-let (msg bdg)
      (badger fn ens wrld)
      (cond
       (msg
        (er soft 'def-warrant "~@0" msg))
       ((and (not (assoc-equal
                   apply-lemmas-book
                   (global-val 'include-book-alist (w state))))
             (not (equal apply-lemmas-book
                         (active-book-name (w state) state))))

; In order to succeed, def-warrant needs apply-lemmas.lisp to have been
; included.  That is because def-warrant tries to prove congruence rules and at
; the very least needs the lemmas establishing that fn-equal is an equivalence
; and a congruence for apply$.  So we tell the user to load apply-lemmas unless
; it has already been loaded or we're currently including or certifying
; apply-lemmas itself (which, naturally enough, explicitly proves all the
; lemmas it needs to do the def-warrants it tries).

        (er soft 'def-warrant
            "Please execute~%~x0~|before the first defun$ or def-warrant.  ~
             See :DOC def-warrant."
            '(include-book
              "projects/apply/apply-lemmas" :dir :system)))
       ((null (access apply$-badge bdg :authorization-flg))
        (value
         `(progn
            (table badge-table
                   :badge-userfn-structure
                   (cons ',(cons fn bdg)
                         (cdr
                          (assoc :badge-userfn-structure
                                 (table-alist 'badge-table world))))
                   :put)
            ,@(if (eq (access apply$-badge bdg :ilks) t)
                  nil
                (defcong-fn-equal-equal-events
                  (cons fn (formals fn wrld))
                  1
                  (access apply$-badge bdg :ilks)))
            (with-output
              :stack :pop
              (value-triple
               (prog2$
                (cw "~%~x0 cannot be warranted because it returns multiple ~
                     values, but it otherwise satisfies the syntactic ~
                     restrictions on warrants.  So a badge for ~x0 has been ~
                     issued -- allowing you to use ~x0 in other functions ~
                     that may be warranted -- but no warrant for ~x0 can be ~
                     issued.  The badge of ~x0 is ~x1.~%~%"
                    ',fn ',bdg)
                :badged))))))
       (t
        (value
         `(progn
            ,@(def-warrant-event fn (formals fn wrld)
                bdg)
            (table badge-table
                   :badge-userfn-structure
                   (cons ',(cons fn bdg)
                         (cdr (assoc :badge-userfn-structure
                                     (table-alist 'badge-table world))))
                   :put)
            (defattach ,(warrant-name fn) true-apply$-warrant)
            ,@(if (eq (access apply$-badge bdg :ilks) t)
                  nil
                (defcong-fn-equal-equal-events
                  (cons fn (formals fn wrld))
                  1
                  (access apply$-badge bdg :ilks)))
            (with-output
              :stack :pop
              (value-triple
               (prog2$
                (cw "~%~x0 is now warranted, with badge ~x1.~%~%"
                    ',fn ',bdg)
                :warranted))))))))))

(defun def-warrant-fn (fn)
  (declare (xargs :mode :logic :guard t)) ; for execution speed in safe-mode
  `(cond
    ((and (symbolp ',fn)
          (executable-badge ',fn (w state)))

; By returing (value :redundant) in this case, we arrange that (value
; :redundant) is returned by a corresponding defun$, so that :REDUNDANT is
; printed in that case.

     (value '(value-triple :redundant)))
    (t
     (def-warrant-fn1 ',fn state))))

(defmacro def-warrant (fn)

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

  `(with-output
     :off ; *valid-output-names* except for error
     (warning warning! observation prove proof-builder event history summary
              proof-tree)
     :stack :push
     :gag-mode nil
     (make-event
      (with-output
        :stack :pop
        ,(def-warrant-fn fn))
; See note below.
      :check-expansion t)))

; Note on Why We :Check-Expansion T

; Consider the following horrible encapsulate:

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
; DEF-WARRANTs.

; During first pass, stub is tame (more precisely, its witness is tame).  It
; gets the badge (APPLY$-BADGE T 2 . T).  The next event, the defun$ of
; mapstub, analyzes the body and announces that mapstub is a mapping function
; with badge (APPLY$-BADGE T 2 NIL :FN).

; The successful badging of mapstub implicitly depends on stub having a badge.

; But during the second pass, stub is just declared.  The local defun$ is
; skipped.  Stub gets no badge.

; But the expansion of the (def-warrant mapstub) records the pass 1 badge
; of mapstub, so mapstub would get the old -- now inappropriate -- badge if
; we didn't have :CHECK-EXPANSION T!

; Why might it be bad to allow mapstub to be badged while it calls the unbadged
; stub?  The simplest answer is that it violates one of our Assurances on
; Badged Functions, namely ``(b) Every function called in its body has a
; badge.''  But that begs the question.  Why do we care?

; It is worrying because of functional instantiation.  There is no logical
; recording of the badge of stub.  It could be functionally instantiated with a
; function that is not tame, for example.  Perhaps this could be fixed, e.g.,
; by having a constraint on stub that says (badge 'stub) = '(APPLY$-BADGE T 2
; . T) or something.  Even if we solve that problem, there is the problem of
; elaborating the evaluation theory story for mapping functions, especially as
; it concerns the idea of using defattach to make stub executable.  But this
; whole issue -- allowing constrained functions into mapping functions -- we
; just haven't considered a high enough priority to think about!

; Use of :check-expansion t is inefficient, since it re-does the entire
; def-warrant calculation.  It may be possible to change the expansion so that
; it causes an error if stub isn't properly badged during the table event that
; normally stores the badge.  I.e., instead of laying down the quoted badge in:

; (TABLE BADGE-TABLE :BADGE-USERFN-STRUCTURE
;        (CONS '(MAPSTUB APPLY$-BADGE T 2 NIL :FN)
;              (CDR (ASSOC :BADGE-USERFN-STRUCTURE #)))
;        :PUT)

; we could lay down something that checks that that badge is correct (e.g.,
; based on check-ilks-list preceded by the necessary checks on stobjs, etc.) to
; avoid the two-pass guessing in badger?  We'd have to have a way to check the
; measure without access to (ens state), but we could include the old measure
; and just use equal.  And we'd have to have a way to signal an error from the
; middle of a value calculation for a TABLE event, which might have to be a
; hard error...  All this is speculative because efficiency is not a big
; concern right now!  We will wait until users start using APPLY$ and complain
; about performance!

; -----------------------------------------------------------------
; 9. DEFUN$

(defmacro defun$ (fn formals &rest rest)
  `(progn
     (defun ,fn ,formals ,@rest)
     (def-warrant ,fn)))

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
  (badge-userfn concrete-badge-userfn)
  (apply$-userfn concrete-apply$-userfn)
  :hints
  (("Goal" :use (concrete-badge-userfn-type
                 concrete-apply$-userfn-takes-arity-args))))

)

