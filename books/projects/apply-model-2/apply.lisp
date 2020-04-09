; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See the README file on this directory for an important note concerning the
; weak compatibility of this model with ACL2 Version_8.2 definitions. 

(in-package "MODAPP")

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
;    interative inference mechanism called GUESS-ILKS-ALIST.

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

; 8. DEFWARRANT
;    Define DEFWARRANT.

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
;     Define the loop$ scions.  See the Essay on LOOP$ in translate.lisp.
;     (This is not done in the model, just the sources.)

; -----------------------------------------------------------------
; 1. Badges

(defun badge (fn)
  (declare (xargs :guard t))
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

(in-theory (disable apply$-primp badge-prim))

(defthm badge-type
  (or (null (badge fn))
      (apply$-badgep (badge fn)))
  :rule-classes
  ((:forward-chaining
    :corollary (implies (badge fn)
                        (apply$-badgep (badge fn))))))

(in-theory (disable badge))

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

; We do not use lambda-object-shapep (as in the ACL2 Version_8.2 sources)
; because that supports DECLAREs in lambdao objects and we don't do that in the
; model.  However, lambda-formals and lambda-body are just cadr and caddr
; respectively.

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
                   :verify-guards nil
                   ))
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

(verify-guards tamep
  :hints
  (("Goal" :use ((:instance badge-type (fn fn))
                 (:instance badge-type (fn (car x)))))))

; In order to verify the guards of the apply$ clique we need various properties
; implied by tamep.  We prove them here.

(defun suitably-tamep-listp-induction (n flags args)
  (cond
   ((zp n) (list flags args))
   (t (suitably-tamep-listp-induction (- n 1) (cdr flags) (cdr args)))))

(defthm suitably-tamep-listp-implicant-1
  (implies (and (suitably-tamep-listp n flags args)
                (natp n))
           (and (true-listp args)
                (equal (len args) n)))
  :hints (("Goal" :induct (suitably-tamep-listp-induction n flags args)))
  :rule-classes :forward-chaining)

(defthm tamep-implicant-1
  (implies (and (tamep x)
                (consp x))
           (true-listp x))
  :hints (("Goal" :expand (tamep x)
           :use ((:instance badge-type (fn (car x)))))))

; We disable the executable counterparts of tamep because badge-userfn is
; undefined, so running tamep on constants, such as (tamep '(CONS A B)) fails
; and introduces a HIDE.  However, expansion of the definitional axioms allow
; us to use the badge properties of warrants.

(in-theory (disable (:executable-counterpart tamep)
                    (:executable-counterpart tamep-functionp)
                    (:executable-counterpart suitably-tamep-listp)))

; -----------------------------------------------------------------
; 3. Definition of APPLY$ and EV$

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defun ev$-measure (x a)
  (declare (ignore a))
  (llist (acl2-count x) 0))

(defun ev$-list-measure (x a)
  (declare (ignore a))
  (llist (acl2-count x) 0))

(defun apply$-measure (fn args)
  (cond
   ((consp fn)
    (llist (acl2-count fn) 0))
   ((eq fn 'apply$)
    (llist (+ 1 (acl2-count (car args))) 0))
   ((eq fn 'ev$)
    (llist (+ 1 (acl2-count (car args))) 0))
   (t (llist 0 0))))

(defun apply$-lambda-measure (fn args)
  (declare (ignore args))
  (llist (acl2-count (caddr fn)) 1))


(mutual-recursion

 (defun APPLY$ (fn args)
   (declare (xargs :guard (true-listp args)
                   :guard-hints (("Goal" :do-not-induct t))
                   :measure (apply$-measure fn args)
                   :well-founded-relation l<
                   ))
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
   (declare (xargs :guard (and (consp fn) (true-listp args))
                   :guard-hints (("Goal" :do-not-induct t))
                   :measure (apply$-lambda-measure fn args)
                   :well-founded-relation l<
                   ))

; This is essentially apply$-lambda-logical of the sources, except that macro
; uses lambda-object-body and lambda-object-formals (which allow for DECLARE
; forms) and we don't model such lambdas.

   (EV$ (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
        (ec-call
         (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                   args))))

 (defun EV$ (x a)
   (declare (xargs :guard t
                   :measure (ev$-measure x a)
                   :well-founded-relation l<))
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

 (defun EV$-LIST (x a)
   (declare (xargs :guard t
                   :measure (ev$-list-measure x a)
                   :well-founded-relation l<))
   (cond
    ((atom x) nil)
    (t (cons (EV$ (car x) a)
             (EV$-LIST (cdr x) a)))))

)

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

(defthm apply$-lambda-opener
  (equal (apply$-lambda fn args)
         (EV$ (lambda-body fn)
              (pairlis$ (lambda-formals fn)
                        args))))

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

; TODO: We have found that ev$-def-fact below, if stored as a :definition, gets
; in the way of some proofs in applications books (exactly which books has been
; lost in in the mists of time...).  But, oddly, we have been unsuccessful at
; disabling that :definition rule.  (We haven't pursued this possible bug yet.)
; And in earlier versions of report.lisp we needed to force ev$ open more often
; than the :definition rule opened it automatically.  So we prove an opener
; below.  But we need the :definition rule to do it!  And since we can't
; apparently disable the :definition rule, we prove it locally.  And since we
; like to advertise the fact that ev$ has a rather beautiful definition for
; tamep terms, we prove ev$-def-fact as :rule-classes nil.

; Hints at resolving the above mystery: By proving ev$-def after including this
; book and then doing :pr ev$-def we see that
; Clique:       (EV$)
; Controller-alist: ((EV$ T NIL))
; so we speculate the problem mentioned above might have to do with the
; induction heuristic being applied to a disabled rule.  But we haven't
; investigated this possibility yet.

(encapsulate
 nil
 (defthm ev$-def-fact
   (implies (tamep x)
            (equal (ev$ x a)
                   (cond
                    ((variablep x)
                     (cdr (assoc x a)))
                    ((fquotep x)
                     (cadr x))
                    ((eq (car x) 'if)
                     (if (ev$ (cadr x) a)
                         (ev$ (caddr x) a)
                         (ev$ (cadddr x) a)))
                    (t (apply$ (car x) (ev$-list (cdr x) a))))))
   :hints (("Goal" :expand ((EV$ X A))))
   :rule-classes nil)

 (local
  (defthm ev$-def
    (implies (tamep x)
             (equal (ev$ x a)
                    (cond
                     ((variablep x)
                      (cdr (assoc x a)))
                     ((fquotep x)
                      (cadr x))
                     ((eq (car x) 'if)
                      (if (ev$ (cadr x) a)
                          (ev$ (caddr x) a)
                          (ev$ (cadddr x) a)))
                     (t (apply$ (car x) (ev$-list (cdr x) a))))))
    :hints (("Goal" :use ev$-def-fact))
    :rule-classes (:definition)))

 (defthm ev$-opener
   (and (implies (symbolp x)
                 (equal (ev$ x a) (cdr (assoc x a))))
        (equal (ev$ (list 'quote obj) a)
               obj)
        (implies (force (suitably-tamep-listp 3 nil args))
                 (equal (ev$ (cons 'if args) a)
                        (if (ev$ (car args) a)
                            (ev$ (cadr args) a)
                            (ev$ (caddr args) a))))
        (implies (and (not (eq fn 'quote))
                      (not (eq fn 'if))
                      (force (tamep (cons fn args))))
                 (equal (ev$ (cons fn args) a)
                        (apply$ fn (ev$-list args a)))))
   :hints (("Subgoal 1" :expand (ev$ (cons fn args) a)))))

(defthm ev$-list-def
  (equal (ev$-list x a)
         (cond
          ((endp x) nil)
          (t (cons (ev$ (car x) a)
                   (ev$-list (cdr x) a)))))
  :rule-classes
  ((:definition)))

(in-theory (disable ev$ ev$-list))

; We will continue to rely on the defun of apply$ for a while but will
; eventually prove theorems that handle all apply$s that can be handled.  The
; first two rules for apply$ are:

(defthm beta-reduction
  (equal (apply$ (list 'LAMBDA vars body) args)
         (ev$ body (pairlis$ vars args))))

(defthm apply$-primp-badge
  (implies (apply$-primp fn)
           (equal (badge fn)
                  (badge-prim fn)))
  :hints (("Goal" :in-theory (enable badge))))

(defthm badge-BADGE
  (equal (badge 'BADGE) *generic-tame-badge-1*))

(defthm badge-TAMEP
  (equal (badge 'TAMEP) *generic-tame-badge-1*))

(defthm badge-TAMEP-FUNCTIONP
  (equal (badge 'TAMEP-FUNCTIONP) *generic-tame-badge-1*))

(defthm badge-SUITABLY-TAMEP-LISTP
  (equal (badge 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*))

(defthm badge-APPLY$
  (equal (badge 'APPLY$) *apply$-badge*))

(defthm badge-EV$
  (equal (badge 'EV$) *ev$-badge*))

(defthm apply$-primitive
  (implies (apply$-primp fn)
           (equal (apply$ fn args)
                  (apply$-prim fn args))))

(defthm apply$-BADGE
  (equal (apply$ 'BADGE args)
         (badge (car args))))

(defthm apply$-TAMEP
  (equal (apply$ 'TAMEP args)
         (tamep (car args))))

(defthm apply$-TAMEP-FUNCTIONP
  (equal (apply$ 'TAMEP-FUNCTIONP args)
         (tamep-functionp (car args))))

(defthm apply$-SUITABLY-TAMEP-LISTP
  (equal (apply$ 'SUITABLY-TAMEP-LISTP args)
         (suitably-tamep-listp (car args) (cadr args) (caddr args))))

(defthm apply$-APPLY$
  (implies (tamep-functionp (car args))
           (equal (apply$ 'APPLY$ args)
                  (apply$ (car args) (cadr args))))
  :hints (("Goal" :in-theory (enable apply$))))

(defthm apply$-EV$
  (implies (tamep (car args))
           (equal (apply$ 'EV$ args)
                  (ev$ (car args) (cadr args))))
  :hints (("Goal" :in-theory (enable apply$))))

(in-theory (disable badge
                    (:executable-counterpart badge)
                    apply$
                    (:executable-counterpart apply$)))

; -----------------------------------------------------------------
; 4. Executable Versions of BADGE and TAMEP

; In order to infer badges of new functions as will be done in defwarrant we
; must be able to determine the badges of already-badged functions.  Similarly,
; we must be able to determine that certain quoted expressions are tame.  So we
; define executable versions of badge and tamep that look at data structures
; maintained by defwarrant.

(defun executable-badge (fn wrld)

; Find the badge, if any, for fn in wrld; else return nil.  Aside from
; primitives and the apply$ boot functions, all badges are stored in the
; badge-table entry :badge-userfn-structure.

; There's nothing wrong with putting this in logic mode but we don't need it in
; logic mode here.  This function is only used by defwarrant, to analyze and
; determine the badge, if any, of a newly submitted function.  (To be accurate,
; this function is called from several places, but all of them are only
; involved in the defwarrant computation.)  Of course, the badge computed by a
; non-erroneous (defwarrant fn) is then built into the defun of
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
       (t (cdr
           (assoc-eq
            fn
            (cdr
             (assoc-eq :badge-userfn-structure
                       (table-alist 'badge-table wrld)))))))))
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
; user-defined functions on which defwarrant succeeded.  The last category of
; badges are stored in the badge-table under the key :badge-userfn-structure.
; Given a function fn, (executable-badge fn wrld), defined above in this file,
; returns the badge, or nil.  We are here primarily interested in the
; badge-table, which is maintained by defwarrant.  If fn has a badge it has a
; warrant named APPLY$-WARRANT-fn.  Defwarrant infers badges (and builds
; warrants with them) by recursively inspecting the body of defun'd functions.
; It uses executable-badge to acquire badges of subroutines.

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
;   :out-arity k and :ilks T or (c1 ... cn) then we know that fn does not have
;   state or stobjs in its signature, that fn takes n arguments and returns k
;   values, and

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

;      Fn is a defined :logic mode function without state or stobjs in its
;      signature and is either in class (G1) or (G2) as described below:

;      (G1) fn is not ancestrally dependent on apply$ (or on any inapplicative
;           primitive like sys-call).

;      (G2) fn is ancestrally dependent on apply$ and

;        (a) one of these conditions hold:
;            * fn is not recursively defined, or

;            * fn is recursively defined with a natural number measure not
;              ancestrally dependent on apply$, well-founded relation O<, and
;              domain O-P, or

;            * fn is recursively defined with a measure not ancestrally
;              dependent on apply$ and that is the macroexpansion of an LLIST
;              expression, well-founded relation L<, and domain LEXP

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
; to extend the modeling process to accommodate mutually recursive scions into
; the clique with APPLY$ and EV$.

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

; Warning: Well-formed-lambdap is not defined in the ACL2 Version_8.2 sources.
; Its role is played there by well-formed-lambda-objectp, which is more
; complicated to support the lambda cache (via factoring the definition into
; syntactically-plausible-lambda-objectp and more careful checks) and DECLARE
; forms.  The notion defined here is weaker.  We believe that if a lambda
; object satisfies well-formed-lambda-objectp and does not have a DECLARE form
; then it satisfies this function.  This function is functionally equivalent to
; weak-well-formed-lambda-objectp in the Version 8.2 sources if one removes the
; case for a declare form.

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
; in a slot of ilk ilk.  Note: term contains no ACL2 lambda applications!  We
; try to determine the ilks of the free vars in term, extending alist to record
; what we find.  We return (mv msg alist'), where either msg is an error
; message and alist' is nil, or msg is nil and alist' is extension of alist
; assiging ilks to free vars occurring in term.

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
; If fn has a badge upon definition it could only be because of loop$-recursion.
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
                 (mv (msg "~x0 cannot be warranted because a :FN slot in its ~
                           body is occupied by a lambda object, ~x1, that ~
                           recursively calls ~x0; recursion through APPLY$ is ~
                           not permitted!"
                          fn
                          term)
                     nil))
                ((executable-tamep-lambdap (cadr term) wrld)
                 (mv nil alist))
                (t (mv (msg "~x0 cannot be warranted because a :FN slot in ~
                             its body is occupied by a lambda object, ~x1, ~
                             whose body is not tame."
                            fn
                            term)
                       nil))))
              (t (mv (msg "~x0 will not be warranted because a :FN slot in ~
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
       (t (mv (msg "~x0 cannot be warranted because a :FN slot in its ~
                    body is occupied by a quoted constant, ~x1, that does not ~
                    denote a tame function symbol or lambda object."
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
       (t (mv (msg "~x0 will not be warranted because an :EXPR slot in its ~
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
                   `(defwarrant ,(ffn-symb term)))
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
; maningless term (rel m (mp X)).  This term has the property that if g is
; ancestral in it, then g is correspondingly ancestral in
; m, or in the definition of rel, or in the definition of mp.

  (declare (xargs :mode :program))
  (let ((just (getpropc fn 'justification nil wrld)))
    (if just
        (let ((m (access justification just :measure))
              (rel (access justification just :rel))
              (mp (access justification just :mp)))
          (acl2::fcons-term* rel m (acl2::fcons-term* mp 'x)))
        acl2::*t*)))

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
; defined before apply$ (actually, before apply$-userfn).'  Otherwise we return
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

; Note:  This function replaces acceptable-warranted-justificationp

(defun g2-justification (fn ens wrld)

; Fn is a defined function symbol being considered for a warrant and we know
; that fn's measure, if fn is recursive, is not ancestrally dependent on
; apply$-userfn, but that fn's body is ancestrally dependent on apply$-userfn.
; So fn will become a G2 function if we warrant it.  But that means its
; justification has to meet certain criteria.  If it fails to meet the
; criteria, we return (mv msg nil).  If it meets the criteria we return (mv nil
; lst), where lst is the list of components in a LLIST measure justifying fn.

; Every G2 function must satisfy one of the following criteria.

; * fn's justification is NIL, meaning fn is not recursive: answer = (mv nil
;   nil).

; * the type-set of fn's measure is *ts-non-negative-integer*, and the relation
;   and domain are O< and O-P: answer = (mv nil '(m)), where m is fn's measure
;   term.

; * fn's measure is (llist m1 ... mk) with relation and domain ACL2::L< and
;   ACL2::LEXP: answer = (mv nil (m1 ... mk)).

; Note that after suitable checks we treat the simple numeric measure case as
; though it were (llist m).

; The reasons we impose restrictions on G2 measures are:

; (1) We don't care about the measures of G1 functions as long as they're not
; dependent on apply$.  The model construction can order the G1 definitions
; (and any relevant unwarranted definitions) in the user's chronological order
; and admit them all.

; (2) We insist that G2 functions have measures independent of apply$ so we
; don't complicate the admission of the mutually recursive clique involving
; apply$ and all G2 functions.  To weaken this restriction will require a
; meta-level argument that a function in the clique can be used as the measure
; of another one -- a reflexive situation we're not sure we can handle and so
; don't!

; (3) We limit the acceptable measures to either natural numbers or
; lexicographic measures.  The model construction's measure for the
; doppelganger clique is lexicographic and will allocate max slots to
; accommodate all the userfn measures, where max is the length of the longest
; lexicographic measure of any userfn.  Simple numeric measures are treated
; like lexicographic measures of length 1.  We can imagine loosening this
; restriction and allowing an arbitrary ordinal measure (independent of apply$)
; but that requires another meta-level proof based on the structured theory
; paper's universal evaluator to non-constructively define a recursion counter.
; We haven't worked out the details of this proof.

  (declare (xargs :mode :program))
  (cond
   ((not (recursivep fn nil wrld))
    (mv nil nil))
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
                   ((not (eq rel 'O<))
                    (mv (msg "~x0 cannot be warranted because its ~
                              justification's well-founded relation is ~x1 ~
                              instead of O< as required for its ~
                              natural-number measure."
                             fn
                             rel)
                        nil))
                   ((not (eq mp 'O-P))
                    (mv (msg "~x0 cannot be warranted because its ~
                              justification's domain is ~x1 instead of O-P as ~
                              required for its natural-number measure."
                             fn
                             mp)
                        nil))
                   (t (mv nil (list m)))))
                 (t (let ((terms (lex-measure-terms m)))
                      (cond
                       ((null terms)
                        (mv (msg "~x0 cannot be warranted because its ~
                                  measure, ~x1, is not of the right shape.  ~
                                  It must be either a simple natural number ~
                                  measure recognized by primitive type ~
                                  reasoning or a lexicographic measure ~
                                  constructed by LLIST.  Your measure was not ~
                                  constructed by LLIST and its output, V, as ~
                                  deduced by type reasoning is described by ~
                                  ~x2.  If you think your measure does in ~
                                  fact return a natural number, prove it as a ~
                                  :type-prescription lemma."
                                 fn
                                 m
                                 (untranslate
                                  (mv-let (tsterm x)
                                    (acl2::convert-type-set-to-term
                                     'v ts ens wrld nil)
                                    (declare (ignore x))
                                    tsterm)
                                  t
                                  wrld))
                            nil))
                       ((not (eq rel 'L<))
                        (mv (msg "~x0 cannot be warranted because its ~
                                  justification's well-founded relation is ~
                                  ~x1 rather than L< as required for its ~
                                  lexicographic measure."
                                 fn
                                 rel)
                            nil))
                       ((not (eq mp 'ACL2::LEXP))
                        (mv (msg "~x0 cannot be warranted because its ~
                                  justification's domain is domain is ~x1 ~
                                  instead of LEXP as required for its ~
                                  lexicographic measure."
                                 fn
                                 mp)
                            nil))
                       (t (mv nil terms))))))))))))))

; TODO:  We could make badger a little more friendly by:

; (a) compute the list of all unbadged functions in a defun and produce a
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

; Next, we need to find out if the justification of fn, if any, is dependent on
; apply$-userfn.  If so, fn can't be warranted.

       (t (let ((bad-fn
                 (not-pre-apply$-definable
                  nil
                  (nonsensical-justification-term fn wrld)
                  wrld)))
            (cond
             (bad-fn
; A dependence on apply$-userfn was found in the justification of fn.

              (mv (msg "~x0 cannot be warranted because some part of its ~
                        justification (i.e., its measure, well-founded ~
                        relation, or domain predicate) ancestrally calls or ~
                        is justified in terms of ~x1."
                       fn
                       bad-fn)
                  nil))

; At this point we know fn is a candidate for either G1 or G2.  It can be G1 if
; its body doesn't depend on apply$-userfn.  Otherwise, it has to be G2.  But
; in both cases we'll have other constraints to check.

             ((null (bad-ancestor
                     nil ; j-flg (we no longer care about the justification)
                     body
                     *apply$-userfn-callers*
                     wrld))

; Fn will be in G1 if we warrant it.  G1 functions can't be dependent on any
; blacklisted function like sys-call.

              (let ((bad-fn
                     (bad-ancestor nil body *blacklisted-apply$-fns* wrld)))
                (cond
                 (bad-fn
                  (mv (msg "~x0 cannot be warranted because its body is ~
                            ancestrally dependent on ~x1 which is among the ~
                            functions apply$ is not allowed to call."
                           fn
                           bad-fn)
                      nil))
                 (t
; Fn is an acceptable G1 function symbol.
                  (mv nil
                      (make apply$-badge
                            :arity (arity fn wrld)
                            :out-arity (length (getpropc fn 'stobjs-out nil wrld))
                            :ilks t))))))

; Fn will be in G2 if we warrant it.  By the way, we don't explicitly check
; below that fn is independent of blacklisted functions because we check that
; every function called is warranted.  If there's a blacklisted function int
; the body it will be identified as unbadged.

             (t
              (cond
               ((cdr (getpropc fn 'recursivep nil wrld))
                (mv (msg "~x0 cannot be warranted because it is ancestrally ~
                          dependent on apply$-userfn and in a mutually ~
                          recursive clique with ~&1.  Unfortunately, ~
                          defwarrant cannot analyze mutually recursive ~
                          definitions yet."
                         fn
                         (remove1-eq fn (getpropc fn 'recursivep nil wrld)))
                    nil))
               (t (mv-let
                    (msg val)
                    (g2-justification fn ens wrld)
                    (declare (ignore val))

; We can ignore val, the list of lexicographic components in fn's measure,
; because we just need to know whether the justification is acceptable or not.
; The reason we even compute val is so that g2-justification can be used in the
; model constructions of projects/apply-model-2/ex1 and ex2.

                    (cond
                     (msg
                      (mv msg nil))
                     ((quick-check-for-tamenessp fn body wrld)
                      (mv nil
                          (make apply$-badge
                                :arity (arity fn wrld)
                                :out-arity (length (getpropc fn 'stobjs-out nil wrld))
                                :ilks t)))
                     (t
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

                                  (mv (msg "The second pass of the badger ~
                                            produced a different alist than ~
                                            the first!  The (completed) alist ~
                                            produced by the first pass is ~x0 ~
                                            but the alist produced by the ~
                                            second pass is ~x1.  This must be ~
                                            some kind of coding error in ~
                                            ACL2.  Please report this to the ~
                                            implementors."
                                           alist1 alist2)
                                      nil))))))))))))))))))))
   (t (mv (msg "~x0 cannot be warranted because it is not a defined ~
                :logic mode function symbol."
               fn)
          nil))))

; -----------------------------------------------------------------
; 6. Essay on CHECK-ILKS

; The computation above is messy both because we're inferring ilks (using two
; pseudo ``ilks'' :UNKNOWN and :UNKNOWN*) and we're generating ``helpful'' error
; messages, cluttering the code.  We therefore would like to know that when
; badger returns no error msg and a purported badge that the badge is actually
; ``correct,'' where correctness is as succinctly stated as we can manage.  To
; that end we have written a checker (defined below), proved the key property
; mechanically, and can then put together an informal proof of the correctness
; of badger.

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

; Third, we keep track ``occurrence ilks'' as we walk the body.

; Fourth, inspection of badger above shows that it signals an error unless fn
; is a defined (not constrained) :logic mode function symbol that does not have
; stobjs or state in its signature and that has an acceptable justification.
; Here ``acceptable'' means, for G1 and G2 functions, the justification is
; ancestrally independent of apply$-userfn and, additionally for G2 functions,
; the measure is lexicographic (including the trivial numeric case) and the
; well-founded relation and domain are exactly those expected.

; Fifth, when badger returns non-erroneously, the badge is constructed with
; make apply$-badge with obviously correct settings for :arity and :out-arity.
; The only question is whether :ilks is set correctly.

; Sixth, the badger's classification of G1 functions is accurate.  It checks
; that the body is ancestrally independent of apply$-userfn and of all
; blacklisted functions.  The resultant tame badge construction is obviously
; correct.


; Assurances on Badged G2 Functions (recapitulation)

; We focus on the assignment of a new-badge as the badge of a G2 fn with
; (beta-reduced) body, body.

; (a) Fn is a defined, singly-recursive (or non-recursive) :logic mode function
;     that does not traffic in stobjs or state and that (if recursive) is
;     justified with an acceptable measure, well-founded relation, and domain.
;     Furthermore, the badge returned is an apply$-badgep with correct :arity,
;     :out-arity and :ilks of either T or a list (in 1:1 correspondence with
;     the formals of fn) of NIL, :FN, and/or :EXPR tokens.

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
; places where it returns non-erroneously, i.e., (mv nil ...), one for G1
; functions and one for G2 functions.  It is the G2 case where the ilks are
; potentially problematic.

; Briefly reviewing the code in badger leading to the G2 non-erroneous
; return we see that it guesses an alist0 assigning ilks to the vars of body,
; then it produces a proposed new-badge and alist1 from alist0.  Alist1 is just
; alist0 completed on all the formals, by assigning an ilk of NIL to any
; unassigned formal.  New-badge just lists those completed ilks in formals
; order.  We then see that badger tests that (guess-ilks-alist fn new-badge
; body nil wrld alist1) is non-erroneous.  Only if that test succeeds do we
; return new-badge.

; Check-ilks, defined below, checks (b), (c), (d) and (e); as noted, (a) is
; obvious.  We encourage you to read the defun of check-ilks to confirm that if
; it returns t then (b)-(e) hold.

; We could change badger to call check-ilks as with (check-ilks <fn>
; <new-badge> <beta-reduced-body> nil <(w state)>) and cause an error if it
; fails, but there is no need.  We can prove that check-ilks will succeed when
; badger returns from the second non-erroneous exit.  (We enclose the arguments
; to check-ilks above in brackets, e.g., <fn>, ..., <(w state)>, to denote the
; values of those expressions at the second non-erroneous exit above.)

; In particular, consider this theorem below:

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

; Note: We do all this work locally and do not export it.  Our only objective
; is to see check-ilks and know that Pass 2 of guess-ilks-alist implies it.

(local (include-book "tools/flag" :dir :system))

(local
 (encapsulate nil

; To define check-ilks in :logic mode and to reason about guess-ilks-alist, we
; have to verify the termination of some :program mode functions that otherwise
; don't have to be in :logic mode.

   (progn
     (defun count-to-nil (x)
       (if (atom x)
           (if (null x) 0 1)
           (+ 1
              (count-to-nil (car x))
              (count-to-nil (cdr x)))))

     #+acl2-devel ; else not redundant with :? measure
     (verify-termination
       (ffnnamep (declare (xargs :measure (count-to-nil term)
                                 :verify-guards nil)))
       (ffnnamep-lst (declare (xargs :measure (count-to-nil l)
                                     :verify-guards nil))))


     (verify-termination EXECUTABLE-BADGE)

     (verify-termination
       (executable-tamep
        (declare (xargs :measure (acl2-count x))))
       (executable-tamep-functionp
        (declare (xargs :measure (acl2-count fn))))
       (executable-suitably-tamep-listp
        (declare (xargs :measure (acl2-count args)))))

     (verify-termination WELL-FORMED-LAMBDAP)

     (verify-termination CHANGED-FUNCTIONAL-OR-EXPRESSIONAL-FORMALP)


     (verify-termination accumulate-ilk)

     (verify-termination
       (guess-ilks-alist (declare (xargs :measure (acl2-count term))))
       (guess-ilks-alist-list (declare (xargs :measure (acl2-count terms)))))

     )

   (defun find-badge-ilk (var formals ilks)
     (cond
      ((endp formals) nil)
      ((eq var (car formals)) (car ilks))
      (t (find-badge-ilk var (cdr formals) (cdr ilks)))))

   (mutual-recursion

    (defun check-ilks (fn new-formals new-badge term ilk wrld)

; Here we are checking conditions (b), (c), (d) and (e) of our assurances about
; non-erroneous results from badger.

; (b) Every function called in body has a badge (including fn if we consider
;     new-badge the badge of fn).

; (c) Every subterm of body with occurrence ilk :FN is:
;     a formal variable of fn with ilk :FN in new-badge, or
;     a quoted tame function symbol other than fn, or
;     a quoted, well-formed (fully translated and closed), tame lambda
;     expression that does not call fn.

; (d) Every subterm of body with occurrence ilk :EXPR is:
;     a formal variable of fn with ilk :EXPR in new-badge, or
;     a quoted, well-formed (fully translated), tame term that does not call
;     fn.

; (e) If the nth formal, vn, of fn has ilk :FN or :EXPR then vn is passed
;     unchanged into the nth slot of every recursive call of fn.

; Since we rely on our assurances to build the model, and since the assurances
; are phrased as above but checked as below, and since our proof actually
; establishes that the code below returns T when badger succeeds, it behooves
; the reader to inspect this definition and confirm that it implies (b)-(e)!

      (declare (xargs :measure (acl2-count term)))
      (cond
       ((variablep term)
        (eq (find-badge-ilk term new-formals
                            (access apply$-badge new-badge :ilks))
            ilk))
       ((fquotep term)
        (cond
         ((eq ilk :FN)
          (or (and (symbolp (cadr term))
                   (or (not (equal fn (cadr term)))
                       (executable-badge fn wrld))
                   (executable-tamep-functionp (cadr term) wrld))
              (and (consp (cadr term))
                   (and (well-formed-lambdap (cadr term) wrld)
                        (or (not (ffnnamep fn (lambda-body (cadr term))))
                            (executable-badge fn wrld))
                        (executable-tamep-lambdap (cadr term) wrld)))))
         ((eq ilk :EXPR)
          (and (termp (cadr term) wrld)
               (not (ffnnamep fn (cadr term)))
               (executable-tamep (cadr term) wrld)))
         (t t)))
       ((flambdap (ffn-symb term)) nil)
       ((or (eq ilk :FN)
            (eq ilk :EXPR))
        nil)
       ((eq fn (ffn-symb term))
        (and
         (check-ilks-list fn new-formals new-badge
                          (fargs term)
                          (access apply$-badge new-badge :ilks)
                          wrld)
         (or (eq (access apply$-badge new-badge :ilks) t)
             (not (changed-functional-or-expressional-formalp
                   (formals fn wrld)
                   (access apply$-badge new-badge :ilks)
                   (fargs term))))))
       (t (let ((bdg (executable-badge (ffn-symb term) wrld)))
            (and bdg
                 (check-ilks-list fn new-formals new-badge
                                  (fargs term)
                                  (access apply$-badge bdg :ilks)
                                  wrld))))))

    (defun check-ilks-list (fn new-formals new-badge terms ilks wrld)
      (declare (xargs :measure (acl2-count terms)))
      (cond
       ((endp terms) t)
       (t (and
           (check-ilks fn new-formals new-badge
                       (car terms)
                       (cond ((eq ilks T) nil)
                             (t (car ilks)))
                       wrld)
           (check-ilks-list fn new-formals new-badge
                            (cdr terms)
                            (cond ((eq ilks T) T)
                                  (t (cdr ilks)))
                            wrld)))))
    )

   (in-theory (disable executable-badge
                       executable-tamep
                       executable-tamep-functionp
                       well-formed-lambdap
                       changed-functional-or-expressional-formalp))

   (make-flag checker guess-ilks-alist)

   (mutual-recursion
    (defun alist-okp (term formals badge alist wrld)
      (cond
       ((variablep term)
        (and (member term formals)
             (assoc term alist)
             (member (cdr (assoc term alist)) '(nil :fn :expr))
             (equal
              (find-badge-ilk term formals (access apply$-badge badge :ilks))
              (cdr (assoc term alist)))))
       ((fquotep term) t)
       (t (and (symbolp (car term))
               (true-listp (fgetprop (car term) 'formals t wrld))
               (alist-okp-list (fargs term) formals badge alist wrld)))))
    (defun alist-okp-list (terms formals badge alist wrld)
      (cond
       ((endp terms) t)
       (t (and (alist-okp (car terms) formals badge alist wrld)
               (alist-okp-list (cdr terms) formals badge alist wrld))))))

   (defthm-checker
     (defthm guess-ilks-alist-lemma
       (implies (and (alist-okp term formals new-badge alist wrld)
                     (null (mv-nth 0 (guess-ilks-alist fn new-badge term
                                                       ilk wrld alist)))
                     new-badge)
                (equal (mv-nth 1 (guess-ilks-alist fn new-badge term
                                                   ilk wrld alist))
                       alist))
       :flag guess-ilks-alist)
     (defthm guess-ilks-alist-list-lemma
       (implies (and (alist-okp-list terms formals new-badge alist wrld)
                     (null
                      (mv-nth 0 (guess-ilks-alist-list fn new-badge terms
                                                       ilks wrld alist)))
                     new-badge)
                (equal
                 (mv-nth 1 (guess-ilks-alist-list fn new-badge terms
                                                  ilks wrld alist))
                 alist))
       :flag guess-ilks-alist-list)
     :hints (("Goal" :in-theory (enable accumulate-ilk))))

   (defun badge-table-okp (alist)
     (cond
      ((atom alist) (eq alist nil))
      (t (and (consp (car alist))
              (symbolp (caar alist))
              (apply$-badgep (cdar alist))
              (badge-table-okp (cdr alist))))))

   (defthm apply$-badgep-hons-get-lemma
     (implies (and (badge-table-okp alist)
                   (hons-get fn alist))
              (apply$-badgep (cdr (hons-get fn alist))))
     :hints (("Goal" :in-theory (enable hons-assoc-equal))))

   (defthm apply$-badgep-executable-badge-lemma
     (implies (and (badge-table-okp alist)
                   (cdr (assoc-equal fn alist)))
              (apply$-badgep (cdr (assoc-equal fn alist)))))

   (defthm apply$-badgep-executable-badge
     (implies (and (badge-table-okp
                    (cdr (assoc-equal :badge-userfn-structure
                                      (table-alist 'badge-table wrld))))
                   (executable-badge fn wrld))
              (apply$-badgep (executable-badge fn wrld)))
     :hints (("Goal" :in-theory (e/d (executable-badge)
                                     (hons-get apply$-badgep))))
     :rule-classes nil)

   (defthm-checker

     (defthm guess-ilks-alist-correct
       (implies (and (null
                      (mv-nth 0 (guess-ilks-alist fn new-badge term
                                                  ilk wrld alist)))
                     (alist-okp term formals new-badge alist wrld)
                     (badge-table-okp
                      (cdr (assoc-equal :badge-userfn-structure
                                        (table-alist 'badge-table wrld))))
                     (apply$-badgep new-badge)
                     (member ilk '(nil :fn :expr))
                     (termp term wrld))
                (check-ilks fn formals new-badge term ilk wrld))
       :flag guess-ilks-alist)

     (defthm guess-ilks-alist-list-correct
       (implies (and (null
                      (mv-nth 0 (guess-ilks-alist-list fn new-badge terms
                                                       ilks wrld alist)))
                     (alist-okp-list terms formals new-badge alist wrld)
                     (badge-table-okp
                      (cdr (assoc-equal :badge-userfn-structure
                                        (table-alist 'badge-table wrld))))
                     (apply$-badgep new-badge)
                     (or (eq ilks t)
                         (and (true-listp ilks)
                              (subsetp ilks '(nil :fn :expr))))
                     (term-listp terms wrld))
                (check-ilks-list fn formals new-badge terms ilks wrld))
       :flag guess-ilks-alist-list)
     :hints (("Subgoal *1/26" :use ((:instance apply$-badgep-executable-badge
                                               (fn (car term)))))))
   ))

; -----------------------------------------------------------------
; 7. Functional Equivalence

; We now develop the notion of two functions being equivalent.  The basic idea
; is that fn1 is functionally equivalent to fn2 if they are both tame and
; apply$ cannot distinguish them.  We define fn-equal to be this concept, but
; first need the quantified statement that apply$ cannot distinguish the two.

(defun-sk apply$-equivalence (fn1 fn2)
  (forall (args)
    (equal (apply$ fn1 args)
           (apply$ fn2 args))))

(defun fn-equal (fn1 fn2)
  (if (equal fn1 fn2)
      t
      (and (tamep-functionp fn1)
           (tamep-functionp fn2)
           (apply$-equivalence fn1 fn2))))

(local
 (defthm apply$-equivalence-necc-rewriter
   (implies (equal (apply$ fn1 (apply$-equivalence-witness fn1 fn2))
                   (apply$ fn2 (apply$-equivalence-witness fn1 fn2)))
            (equal (apply$ fn1 args)
                   (apply$ fn2 args)))
   :hints (("Goal" :in-theory (disable APPLY$-EQUIVALENCE-NECC)
            :use APPLY$-EQUIVALENCE-NECC))))

(defequiv fn-equal)

(defcong fn-equal equal (apply$ fn args) 1)

(in-theory (disable fn-equal))

; Every time a mapping function is introduced we also prove the fn-equal
; congruence rule.  Here is how we generate it.  For example,

; (generate-fn-equal-congruences '(collect lst fn) 1 '(nil :fn))

; produces the list containing just

; (defcong fn-equal equal (collect lst fn) 2)

(defun defcong-fn-equal-equal-events (term i c1-cn)
  (cond
   ((endp c1-cn) nil)
   ((eq (car c1-cn) :FN)
    (cons `(defcong fn-equal equal ,term ,i
             :hints
             (("Goal" :in-theory (disable (:executable-counterpart force)))))
          (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn))))
   (t (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn)))))

; -----------------------------------------------------------------
; 8. DEFWARRANT

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

(defun warrant-name (fn)

; From fn generate the name APPLY$-WARRANT-fn.

  (declare (xargs :guard (symbolp fn)))
  (intern-in-package-of-symbol
   (coerce
    (append '(#\A #\P #\P #\L #\Y #\$ #\- #\W #\A #\R #\R #\A #\N #\T #\-)
            (coerce (symbol-name fn) 'list))
    'string)
   fn))

(defun warrant-fn (names)

; This is a helper function for the macro warrant.  Given (a b c) we return
; ((APPLY$-WARRANT-a) (APPLY$-WARRANT-b) (APPLY$-WARRANT-c))

  (declare (xargs :guard (symbol-listp names)))
  (cond ((endp names) nil)
        ((assoc-eq (car names)
                   *badge-prim-falist*) ; primitives don't have warrants
         (warrant-fn (cdr names)))
        (t (cons (list (warrant-name (car names)))
                 (warrant-fn (cdr names))))))

(defmacro warrant (&rest names)

; This implements the abbreviation (warrant a b c) for:
; (AND (APPLY$-WARRANT-a) (APPLY$-WARRANT-b) (APPLY$-WARRANT-c))

  (declare (xargs :guard (symbol-listp names)))
  `(AND ,@(warrant-fn names)))

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
;  :constrain t)

; (BTW: The actual warrant is a defun-sk phrased in terms of badge-userfn and
; apply$-userfn, not badge and apply$, as shown above; but the rewrite rule
; indeed deals with badge and apply$.  We deal with this later.)

; Here are the relevant two functions.

(defun tameness-conditions (ilks var)
  (declare (xargs :mode :program))
  (cond ((endp ilks) nil)
        ((eq (car ilks) :FN)
         (cons `(TAMEP-FUNCTIONP (CAR ,var))
               (tameness-conditions (cdr ilks) (list 'CDR var))))
        ((eq (car ilks) :EXPR)
         (cons `(TAMEP (CAR ,var))
               (tameness-conditions (cdr ilks) (list 'CDR var))))
        (t (tameness-conditions (cdr ilks) (list 'CDR var)))))

(defun successive-cadrs (formals var)
  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        (t
         (cons `(CAR ,var)
               (successive-cadrs (cdr formals) (list 'CDR var))))))

; Recall the ``BTW'' notes above.  We need to convert the lemma provided
; by defun-sk into an effective rewrite rule.  To do that we need a hint
; and this function creates that hint.

(defun necc-name-ARGS-instance (ilks)

; This odd little function is used to generate an :instance hint.  Search below
; for :instance to see the application.  But imagine that you wanted a concrete
; list, e.g., '(x y z), of actuals satisfying the given ilks, e.g., (NIL :FN
; :EXPR).  Then, for this example, a suitable list would be '(NIL EQUAL T).
; (Indeed, so would '(NIL ZP NIL), but we just need some suitable list.)  We
; generate it here.  Note that the resulting list will be QUOTEd, so we return
; evgs here.

  (cond ((endp ilks) nil)
        ((eq (car ilks) :fn)
         (cons 'EQUAL (necc-name-ARGS-instance (cdr ilks))))
        ((eq (car ilks) :expr)
         (cons T (necc-name-ARGS-instance (cdr ilks))))
        (t (cons NIL (necc-name-ARGS-instance (cdr ilks))))))

(defun defwarrant-event (fn formals bdg)

; Bdg must be a legal badge for (fn . formals).

; This function returns a list of events that add the appropriate defun-sk
; event for fn and then proves the necessary rewrite rule.

  (declare (xargs :mode :program))
  (let* ((name (warrant-name fn))
         (rule-name (acl2::apply$-rule-name fn))
         (necc-name (intern-in-package-of-symbol
                     (coerce
                      (append (coerce (symbol-name name) 'list)
                              '(#\- #\N #\E #\C #\C))
                      'string)
                     fn)))
    (cond
     ((eq (access apply$-badge bdg :ilks) t)
      `((defun-sk ,name ()
          (forall (args)
            (and
             (equal (badge-userfn ',fn) ',bdg)
             (equal (apply$-userfn ',fn args)
                    ,(if (eql (access apply$-badge bdg :out-arity) 1)
                         `(,fn ,@(successive-cadrs formals 'args))
                         `(mv-list
                           ',(access apply$-badge bdg :out-arity)
                           (,fn ,@(successive-cadrs formals 'args)))))))
          :constrain t)
        (in-theory (disable ,(acl2::definition-rule-name name)))
        (defthm ,rule-name
          (implies
           (force (,(warrant-name fn)))
           (and (equal (badge ',fn) ',bdg)
                (equal (apply$ ',fn args)
                       ,(if (eql (access apply$-badge bdg :out-arity) 1)
                            `(,fn ,@(successive-cadrs formals 'args))
                            `(mv-list
                              ',(access apply$-badge bdg :out-arity)
                              (,fn ,@(successive-cadrs formals 'args)))))))
          :hints (("Goal" :use ,necc-name
                   :expand ((:free (x) (HIDE (badge x))))
                   :in-theory (e/d (badge apply$)
                                   (,necc-name)))))))
     (t
      (let* ((hyp-list (tameness-conditions (access apply$-badge bdg :ilks)
                                            'ARGS))
             (hyp (if (null (cdr hyp-list))
                      (car hyp-list)
                      `(AND ,@hyp-list))))
        `((defun-sk ,name ()
            (forall (args)
              (implies
               ,hyp
               (and
                (equal (badge-userfn ',fn) ',bdg)
                (equal (apply$-userfn ',fn args)
                       ,(if (eql (access apply$-badge bdg :out-arity) 1)
                            `(,fn ,@(successive-cadrs formals 'args))
                            `(mv-list
                              ',(access apply$-badge bdg :out-arity)
                              (,fn ,@(successive-cadrs formals 'args))))))))
            :constrain t)
          (in-theory (disable ,(acl2::definition-rule-name name)))
          (defthm ,rule-name
            (and (implies (force (,(warrant-name fn)))
                          (equal (badge ',fn) ',bdg))
                 (implies
                  (and (force (,(warrant-name fn)))
                       ,hyp)
                  (equal (apply$ ',fn args)
                         ,(if (eql (access apply$-badge bdg :out-arity) 1)
                              `(,fn ,@(successive-cadrs formals 'args))
                              `(mv-list
                                ',(access apply$-badge bdg :out-arity)
                                (,fn ,@(successive-cadrs formals 'args)))))))

; Notice that the necc-name theorem is of the form (forall (args) (and ...))
; but the theorem above is essentially (and ... (forall (args) ...)) because
; the first conjunct is free of ARGS.  We had to write necc-name that way
; because of the requirements of defun-sk.  But now we have to extract the fact
; that we know (APPLY$-WARRANT fn) --> (badge 'fn) = <whatever>, by instantiating
; necc-name with a suitable ARGS that makes the right components suitably tame.

; The first :instance below takes care of the badge conjunct and the second
; takes care of the apply$ conjunct.

            :hints
            (("Goal"
              :use ((:instance ,necc-name
                               (ARGS ',(necc-name-ARGS-instance
                                        (access apply$-badge bdg :ilks))))
                    (:instance ,necc-name))
              :expand ((:free (x) (HIDE (badge x))))
              :in-theory (e/d (badge apply$)
                              (,necc-name)))))))))))

(set-state-ok t)

(defun defwarrant-fn1 (fn state)
  (declare (xargs :mode :program))
  (let ((ens (ens state))
        (wrld (w state))
; In the ACL2 sources we do the following binding but don't need it here.
;       (apply-lemmas-book
;        (acl2::extend-pathname :system "projects/apply/base.lisp" state))
        )
    (mv-let (msg bdg)
      (badger fn ens wrld)
      (cond
       (msg
        (er soft 'defwarrant "~@0" msg))
; In the ACL2 sources we have the following conditional clause which is
; not relevant in the model version of defwarrant:
;        ((and (not (assoc-equal
;                    apply-lemmas-book
;                    (global-val 'acl2::include-book-alist (w state))))
;              (not (equal apply-lemmas-book
;                          (acl2::active-book-name (w state) state)))
;              (not (global-val 'acl2::boot-strap-flg (w state))))

; ; In order to succeed, defwarrant needs base.lisp to have been included.  That
; ; is because defwarrant tries to prove congruence rules and at the very least
; ; needs the lemmas establishing that fn-equal is an equivalence and a
; ; congruence for apply$.  So we tell the user to load top (which includes base)
; ; unless base has already been loaded or we're currently including or
; ; certifying base itself (which, naturally enough, explicitly proves all the
; ; lemmas it needs to do the defwarrants it tries).

; ; We make an exception for the boot-strap, where we take responsibility for the
; ; necessary verification.

;         (er soft 'defwarrant
;             "Please execute~%~x0~|before the first defun$ or defwarrant.  ~
;              See :DOC defwarrant."
;             '(include-book
;               "projects/apply/top" :dir :system)))
       (t
        (value

; WARNING: Be sure no event under this (encapsulate () ...) is local!  At one
; time we used (progn ...) instead.  However, we found that defwarrant events
; were never redundant because of the defattach below.

         `(encapsulate ; Read the warning above before changing to progn.
            ()
            ,@(defwarrant-event fn (formals fn wrld)
                bdg)
            (table badge-table
                   :badge-userfn-structure
                   (cons ',(cons fn bdg)
                         (cdr (assoc :badge-userfn-structure
                                     (table-alist 'badge-table world))))
                   :put)
; In the ACL2 sources we do this but we don't want to do it in the model.
;            ,(if (getpropc fn 'predefined nil wrld)
;                 `(defattach (,(warrant-name fn)
;                              acl2::true-apply$-warrant)
;                    :system-ok t)
;               `(defattach ,(warrant-name fn) acl2::true-apply$-warrant))
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

(defun defwarrant-fn (fn)
  (declare (xargs :mode :logic :guard t)) ; for execution speed in safe-mode
  `(defwarrant-fn1 ',fn state))

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

  `(with-output
     :off ; *valid-output-names* except for error
     (acl2::warning acl2::warning! acl2::observation acl2::prove
                    acl2::proof-builder acl2::event acl2::history
                    acl2::summary acl2::proof-tree)
     :stack :push
     :gag-mode nil
     (make-event
      (with-output
        :stack :pop
        ,(defwarrant-fn fn))
      :on-behalf-of :quiet!
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
; DEFWARRANTs.

; During first pass, stub is tame (more precisely, its witness is tame).  It
; gets the badge (APPLY$-BADGE 2 1 . T).  The next event, the defun$ of
; mapstub, analyzes the body and announces that mapstub is a mapping function
; with badge (APPLY$-BADGE 2 1 NIL :FN).

; The successful badging of mapstub implicitly depends on stub having a badge.

; But during the second pass, stub is just declared.  The local defun$ is
; skipped.  Stub gets no badge.

; But the expansion of the (defwarrant mapstub) records the pass 1 badge
; of mapstub, so mapstub would get the old -- now inappropriate -- badge if
; we didn't have :CHECK-EXPANSION T!

; Why might it be bad to allow mapstub to be badged while it calls the unbadged
; stub?  The simplest answer is that it violates one of our Assurances on
; Badged Functions, namely ``(b) Every function called in its body has a
; badge.''  But that begs the question.  Why do we care?

; It is worrying because of functional instantiation.  There is no logical
; recording of the badge of stub.  It could be functionally instantiated with a
; function that is not tame, for example.  Perhaps this could be fixed, e.g.,
; by having a constraint on stub that says (badge 'stub) = '(APPLY$-BADGE 2 1
; . T) or something.  Even if we solve that problem, there is the problem of
; elaborating the evaluation theory story for mapping functions, especially as
; it concerns the idea of using defattach to make stub executable.  But this
; whole issue -- allowing constrained functions into mapping functions -- we
; just haven't considered a high enough priority to think about!

; Use of :check-expansion t is inefficient, since it re-does the entire
; defwarrant calculation.  It may be possible to change the expansion so that
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
     (defwarrant ,fn)))

; -----------------------------------------------------------------
; 10. The LAMB Hack

; It is helpful to avoid using constants for lambda expressions so that we can
; rewrite them with fn-equal rewrite rules.  ACL2's rewriter returns term as
; soon as it detects (fquotep term).  So a rewrite rule like (fn-equal (list
; 'lambda (list v) v) 'identity) would not fire on '(lambda (v) v) in a
; fn-equal slot because we don't rewrite constants.  Therefore, we will write
; (lamb '(v) 'v) and rewrite lamb expressions.  We want lamb and its executable
; counterpart to be disabled in proofs.  But we want it to execute at the top
; level so we can run things like (sumlist '(1 2 3) (lamb '(x) 'x)).  So we
; merely constrain lamb logically and attach an executable function to it.

(encapsulate
  ((lamb (args body) t))
  (local
   (defun lamb (args body)
     (list 'lambda args body)))
  (defthm consp-lamb
    (and (consp (lamb args body))
         (true-listp (lamb args body)))
    :rule-classes :type-prescription)
  (defthm consp-cdr-lamb
    (consp (cdr (lamb args body))))
  (defthm consp-cddr-lamb
    (consp (cddr (lamb args body))))
  (defthm cdddr-lamb
    (equal (cdddr (lamb args body)) nil))
  (defthm car-lamb
    (equal (car (lamb args body)) 'lambda))

  (defthm lambda-formals-lamb
    (equal (lambda-formals (lamb args body)) args))

  (defthm lambda-body-lamb
    (equal (lambda-body (lamb args body)) body))

  (defthm lamb-reduction
    (equal (apply$ (lamb vars body) args)
           (ev$ body (pairlis$ vars args)))))

(defun xlamb (args body)
  (declare (xargs :guard t))
  (list 'lambda args body))

(defattach lamb xlamb)

; TODO:  How do we prove rules like
; (defun$ my-id (x) x)
; (defthm my-id-is-identity (fn-equal 'my-id 'identity) :rule-classes :rewrite)
; Well, first, it's not a theorem unless 'my-id has been warranted and we have
; the warrant as a hypothesis!
; Second, even if we could prove it, I don't see why we store it because it
; rewrites a constant.  And yet I've seen us store:
; (defthm foo-is-23-backwards (fn-equal 23 (foo)))
; where (defun foo () 23).  So what's going on?

; TODO: Consider this pair of functions followed by the three defwarrants:

; (defun expt-2-and-expt-3 (x)
;  (let ((x2 (* x x)))
;    (mv x2 (* x x2))))

; (defun expt-5 (x)
;   (mv-let (a b)(expt-2-and-expt-3 x)(* a b)))

; (defwarrant expt-5)
; (defwarrant expt-2-and-expt-3)
; (defwarrant expt-5)

; When you do the first (defwarrant expt-5) you get the error:

; ACL2 Error in DEFWARRANT:  EXPT-5 calls the function EXPT-2-AND-EXPT-3
; which does not have a badge.  You may be able to remedy this by executing
; (DEFWARRANT EXPT-2-AND-EXPT-3) but then again it is possible you've
; done that already and EXPT-2-AND-EXPT-3 cannot be warranted, in which
; case neither can EXPT-5.

; This is an accurate but annoying error message because the system can't tell
; us we've never even tried to warrant expt-2-expt-3.  If we warrant it by
; issuing the second defwarrant and then try the first one again, all works.

; Now compare that behavior to

; (defun foo-2-and-foo-3 (x)
;   (let ((x2 (apply$ x (list x))))
;     (mv x2 (* x x2))))

; (defun foo-5 (x)
;   (mv-let (a b) (foo-2-and-foo-3 x) (* a b)))

; (defwarrant foo-5)
; (defwarrant foo-2-and-foo-3)
; (defwarrant foo-5)

; This time the first defwarrant fails with the same error shown above (but
; for FOO-2-AND-FOO-3), the second fails because of the misuse of the :fn
; variable x, and then the third fails with the very same error generated the
; first time we tried it.

; It would be nice if the system knew which functions are ``intrinsically''
; unwarrantable.  That way the (defwarrant expt-5) could report: you haven't
; tried (defwarrant expt-2-and-expt-3) yet, the first (defwarrant foo-5)
; would report the analogous thing, but the last (defwarrant foo-5) would say:
; foo-5 cannot be warranted because foo-2-and-foo-3 cannot be warranted.

; Trying to store this ``intrinsic failure'' information in badges needlessly
; intertwines user-interface/courtesy with logical issues.  But we could keep
; information about past failures elsewhere.  But the notion of ``intrinsic''
; failure also complicates the inference of ilks and badges.  For example, if
; fn takes STATE or misuses a formal then it can't have a badge and we'd have
; to report that in a different way than just failing because we hit an
; unbadged function.  Also, we would have to update the data structure as
; subroutines get badges.  All in all, this just seems uninterestingly
; complicated and we've postponed thinking about it!
