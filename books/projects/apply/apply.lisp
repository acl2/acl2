; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Apply for Tame Functions in ACL2

; This is a WORK IN PROGRESS! -- ALL COMMENTS SUSPECT!

; It is our intention EVENTUALLY to restrict make-applicable so that the
; following is true: any chronology certified with this book has the property
; that, at least theoretically, one could define a suitable apply$, certify the
; chronology, and then prove that the Applicablep hypothesis for every function
; admitted by make-applicable is in fact a theorem.

; Warning: This version of apply.lisp does not have that property!  It is
; possible to use this book in a certified book that may contain theorems that
; are valid because their Applicablep hypotheses are unsatisfiable!

; (ld "apply.lisp" :ld-pre-eval-print t)
; (certify-book "apply")

(in-package "ACL2")

; -----------------------------------------------------------------
; Handling the Primitives

(include-book "apply-prim")

; Reminders and Warnings: The above book defines apply$-primp, badge-prim, and
; apply$-prim in :logic mode.  The first two are guard verified but apply$-prim
; cannot be guard verified because it may well violate guards, e.g.,
; (apply$-prim 'car (list 7)).  To use apply$-prim in a guard verified setting,
; call it inside ec-call!  We also know via badge-prim-type that when
; (apply$-primp fn) is true then (apply$-badgep (badge-prim fn)) and (cdddr
; (badge-prim fn))=t.

; The apply-prim book also defines the constant *badge-prim-falist* which is a
; fast-alist with entries of the form (fn . (APPLY$-BADGE flg arity . T)).  One
; should not hons-acons anything onto this object because that would steal the
; hash table out from under the current value and slow down apply$-primp and
; badge-prim which use hons-get to access this constant.

; -----------------------------------------------------------------
; The Axioms about Badge and Apply$

; Badge-nonprim is constrained to return nil or an apply$-badgep.  The latter
; is a non-cheap record structured with token name APPLY$-BADGE and accessors
; :authorization-flg, :arity, and :ilks.  We abbreviate the :authorization-flg
; value as flg.  Flg indicates whether the associated function, fn, is stobj-
; and state-free and has been analyzed for appropriate use of second-order-like
; arguments.  Flg is nil if fn returns multiple values -- the only thing
; preventing it from being applicable.  In any case, arity is the arity of fn
; and ilks is T or a list of flags NIL, :FN, and/or :EXPR corresponding to the
; formals and indicating how they are used.  If the ilks is a list (c_1
; ... c_arity), we say c_i is the ``ilk'' of the ith argument.  When ilks = T,
; then each arg has ilk NIL, i.e., T is an abbreviation for a list of arity
; NILs.

; The reason we constrain badge-nonprim is so that we can verify guards for
; tamep and apply$ without having to check these facts about badge-nonprim.

(encapsulate
  ((badge-nonprim (fn) t))
  (local (defun badge-nonprim (fn)
           (declare (ignore fn))
           nil))
  (defthm badge-nonprim-type
    (or (null (badge-nonprim fn))
        (apply$-badgep (badge-nonprim fn)))
    :rule-classes
    ((:forward-chaining
      :corollary (implies (badge-nonprim fn)
                          (apply$-badgep (badge-nonprim fn)))))))

; Apply$-nonprim is totally unconstrained.

(defstub apply$-nonprim (fn args) t)

; ----------------------------------------------------------------- 

; To make apply$ executable in the evaluation theory, do the following after
; including this book into a version of ACL2 that supports execution of apply$.
; Note that the instructions below include forms to be executed within the ACL2
; loop and forms to be executed in raw Lisp.

#||
(defattach (badge-nonprim concrete-badge-nonprim)
  :hints
  (("Goal" :use concrete-badge-nonprim-type)))
(defattach apply$-nonprim concrete-apply$-nonprim)
(value :q) ; exit the ACL2 loop into raw Lisp.
(setq *allow-concrete-execution-of-apply-stubs* t)
(defun apply$-lambda (fn args) (concrete-apply$-lambda fn args))
(lp)
||#

; -----------------------------------------------------------------
; These two stubs are used as the ``default values'' of (apply$ fn args) and
; (ev$ x a) when the arguments are not suitably tame.

(defstub untame-apply$ (fn args) t)
(defstub untame-ev$ (x a) t)

; -----------------------------------------------------------------
; The Role of Badge-Table

; The badge-table contains one entry named :badge-nonprim-structure whose value
; is an object that associates APPLY$-BADGEs (see above) with certain function
; symbols.  At the moment that structure is just a simple alist.  We might wish
; to replace it by some sort of tree, property list, fast alist, etc.  Hence
; the rather generic word ``structure'' in its name.

; Note: One reason to adopt a fast representation is that the concrete
; functions that enable the top-level evaluation of tamep and apply$ access
; this structure.  So its speed directly affects the execution speed of mapping
; functions in raw Lisp.  However, a difficulty with structures that exploit
; some kind of hidden backing store, like both user-managed worlds
; (getprop/putprop/extend-world) and fast alists, is that when these structures
; are updated inside encapsulates care must be taken to restore the backing
; store before pass 2.  This is why, for example, we use
; *badge-prim-falist* to get the badge of primitives but
; :badge-nonprim-structure to get the badge of nonprimitives: the
; former can safely be a fast alist because it's constant.  Furthermore, there
; are many more primitives than nonprimitives right now so this makes apply$
; pretty efficient.  However, we don't think of the battle for runtime
; efficiency of apply$ as having been won yet -- it has hardly been fought!
; Rather than fight this battle now we just punt and use a simple alist for
; nonprimitives.  We experimented with a two-level alist, mapping a symbol's
; first char to an alist mapping symbols to pairs, and got performance that was
; sometimes worse than a simple alist (and sometimes better) making efficiency
; hard to assess without some kind of data on the distribution of symbols
; alphabetically.

; Suppose fn has a non-nil badge, with components flg, arity, and ilks.  Then

; (a) Fn is nonprimitive and ``applicable'' in the sense that word is defined
;     below.

; (b) The arity of fn is arity, a natural number.

; (c) If ilks is T, we know that fn is actually tame; otherwise, ilks is a
;     list (c_1 ... c_n), where each c_i is nil, :fn, or :expr.

; (d) When ilks is a list, at least one c_i is not nil because when all the
;     c_i are nil, fn is tame and we store a T instead of a list.

; The badge-table is not used directly by the logic.  It is used in the
; computation of the badge of a newly introduced function.  See
; classify-formals (which is the :program mode workhorse for analyzing
; functions).  It is also used in the support for raw Lisp execution of
; badge-nonprim.  See concrete-badge-nonprim in the ACL2 sources.

; Raw lisp and :program mode functions like classify-formals can't use
; (badge fn) to find the classes of fn's formals because badge is not
; always executable; it calls the defstub badge-nonprim whose value is
; determined by the apply hyp, if any, for fn.  So we need an easy, executable
; way to recover the badge that are known, given the world.  We implement
; that now.

(defconst *generic-tame-badge-1*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 1 :ILKS t))
(defconst *generic-tame-badge-2*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 2 :ILKS t))
(defconst *generic-tame-badge-3*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 3 :ILKS t))
(defconst *apply$-badge*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 2 :ILKS '(:FN NIL)))
(defconst *ev$-badge*
  (MAKE APPLY$-BADGE :AUTHORIZATION-FLG T :ARITY 2 :ILKS '(:EXPR NIL)))

(table badge-table
       :badge-nonprim-structure
       `((tamep . ,*generic-tame-badge-1*)
         (tamep-functionp . ,*generic-tame-badge-1*)
         (suitably-tamep-listp . ,*generic-tame-badge-2*)
         (apply$ . ,*apply$-badge*)
         (ev$ . (2 . ,*ev$-badge*))))

(defun executable-badge (fn wrld)

; There's nothing wrong with putting this in logic mode but we don't need it in
; logic mode here.

  (declare (xargs :mode :program))
  (cond
   ((symbolp fn)
    (let ((temp (hons-get fn *badge-prim-falist*)))
      (cond
       (temp (cdr temp))
       (t (cdr
           (assoc-eq
            fn
            (cdr
             (assoc-eq :badge-nonprim-structure
                       (table-alist 'badge-table wrld)))))))))
   (t nil)))

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
   (t (badge-nonprim fn))))

(in-theory (disable apply$-primp badge-prim))

(defthm badge-type
  (or (null (badge fn))
      (apply$-badgep (badge fn)))
;  :hints (("Goal" :use (badge-prim-type badge-nonprim-type)))
  :rule-classes
  ((:forward-chaining
    :corollary (implies (badge fn)
                        (apply$-badgep (badge fn))))))

(in-theory (disable badge))

; -----------------------------------------------------------------
; Tameness

; These functions are defined for speed, not clarity.  Aside from the obvious
; logical requirements of tameness -- roughly speaking, every function is
; either tame or is a mapping function supplied with quoted tame functions in
; the right places -- we want (tamep x) to imply that x is either a symbol or a
; true-listp, imply that every function call is supplied with the right number
; of arguments (at least with respect to the arities reported by badge),
; and we want it guard verified with a guard of t.

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
            (and (eq (car fn) 'LAMBDA)
                 (consp (cdr fn))
                 (symbol-listp (cadr fn))
                 (consp (cddr fn))
                 (tamep (caddr fn))
                 (null (cdddr fn))
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
            (eq (car fn) 'LAMBDA)
            (consp (cdr fn))
            (symbol-listp (lambda-formals fn))
            (consp (cddr fn))
            (tamep (lambda-body fn)))))

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

; We disable the executable counterparts of tamep because badge-nonprim is
; undefined, so running tamep on constants, such as (tamep '(CONS A B)) fails
; and introduces a HIDE.  However, expansion of the definitional axioms allow
; us to use the badge properties from Applicablep hypotheses.

(in-theory (disable (:executable-counterpart tamep)
                    (:executable-counterpart tamep-functionp)
                    (:executable-counterpart suitably-tamep-listp)))

; -----------------------------------------------------------------
; Definition of APPLY$ and EV$

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
     (ec-call (apply$-prim fn args)))

; See note above about handling the tamep clique as a primitive versus handling
; it here.

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
; succinct and might actually ruin the model (we haven't tried) because in the model
; there are other symbols besides APPLY$ and EV$ you can't apply.  But the
; reason we keep the full blown tamep-functionp test is more aesthetic: it
; makes the apply$ ``applicablep hyp'' exactly analogous to the applicablep hyp
; for user-defined mapping functions like COLLECT.

     (if (tamep-functionp (car args)) ; [termination & model]
         (ec-call (APPLY$ (car args) (cadr args)))
         (untame-apply$ fn args)))
    ((eq fn 'EV$)
     (if (tamep (car args)) ; [model] (not req'd for termination or guards)
         (EV$ (car args) (cadr args))
         (untame-apply$ fn args)))
    (t (apply$-nonprim fn args))))

 (defun apply$-lambda (fn args)
   (declare (xargs :guard (and (consp fn) (true-listp args))
                   :guard-hints (("Goal" :do-not-induct t))
                   :measure (apply$-lambda-measure fn args)
                   :well-founded-relation l<
                   ))
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
     (if (consp (cdr x))
         (apply$ 'APPLY$
                 (list (cadr (cadr x)) (EV$ (caddr x) a)))
         (untame-ev$ x a)))
    ((eq (car x) 'EV$)
     (if (consp (cdr x))
         (apply$ 'EV$ (list (cadr (cadr x)) (EV$ (caddr x) a)))
         (untame-ev$ x a)))
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

; I tried to put ``reasonable'' guards on the apply$ clique and it won't work.
; For example, the reasonable guard on (ev$ x a) is that x is a pseudo-termp
; and a is a symbol-alistp.  But consider the recursive call (ev$ (car args)
; (cadr args)) in apply$.  The governing test (tamep (car args)) might give us
; the former, but there's nothing that can give us the second because, when ev$
; calls itself as it interprets an 'EV$ call, the second actual is the result
; of a recursive evaluation.  So that not only makes the guard proof reflexive
; but puts non-syntactic requirements on the args.

; So I have decided to go with :guard t, except for apply$ where I insist
; (true-listp args) and apply$-lambda where we additionally know that fn is a
; cons (LAMBDA-expression).

; Essay on Applying APPLY$

; Suppose collect and collect* are defined as in chronology.lisp, i.e.,

; (defun$ collect (lst fn)
;   (cond ((endp lst) nil)
;         (t (cons (apply$ fn (list (car lst)))
;                  (collect (cdr lst) fn)))))

; (defun collect* (lst fn)
;   (if (endp lst)
;       nil
;       (cons (apply$ fn (car lst))
;             (collect* (cdr lst) fn))))

; (thm ; [1]
;  (implies (applicablep collect)
;           (equal (apply$ 'collect '((1 2 3) (lambda (x) (binary-+ '3 x))))
;                  '(4 5 6))))

; BTW: The applicablep hyp below is required because otherwise we don't know
; COLLECT is untame.

;  (thm ; [2]
;   (implies (applicablep collect)
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

; Note that [1] and [2] are sort of similar but [1] is more direct than [2].
; One might wish that if we can reduce (apply$ 'collect ...) to a constant we
; could reduce (apply$ 'apply$ '(collect ...)) to the same constant but that is
; not true.  For what it is worth, we can do this:

; (thm ; [3]
;  (implies (applicablep collect)
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

; Perhaps more interestingly, we can do such things as

; (thm ; [4]
;  (implies (applicablep collect)
;           (equal (collect* '(((1 2 3) (lambda (x) (binary-+ '3 x)))
;                              ((10 20 30) (lambda (x) (binary-+ '3 x))))
;                            'collect)
;                  '((4 5 6) (13 23 33))))
;  :hints (("Goal" :in-theory (disable (collect*)))))

; [4] is interesting because we are mapping with a mapping function.  One might
; think that since we can't apply$ a mapping function this wouldn't work.  But
; it's more subtle.  The defun of collect* expands to introduce
; (apply$ 'collect '((1 2 3) (lambda (x) (binary-+ '3 x)))).
; Then the applicablep hyp for collect checks that its functional arg is tame,
; so that expands to (collect '(1 2 3) '(lambda (x) (binary-+ '3 x))).

; Now you might think, ``But why can't we force the expansion of the apply$ on
; the untame collect to get an untame-apply error?''  The reason is that
; there's no such clause in the defun of apply$.  The clause you're thinking
; about only works for (apply$ 'apply$ ...) not (apply$ 'collect ...).  The
; meaning of (apply$ 'collect ...) is, by the defun of apply$, whatever
; apply$-nonprim says it is.

; The Untamed Eval Saga

; I have tried to remove the tamep test at the top of EV$.  It is easy to do if
; one first changes APPLY$ so that it cannot handle fn = 'EV$.  (To be precise,
; I also made it unable to handle fn = 'APPLY$.  I do not think (apply$ 'APPLY$
; '(cons (1 2))) = (cons 1 2) is particularly useful, anyway.)  Then, just kill
; the (not (tamep x)) clause at the top of EV$, eliminate the 'APPLY$ and 'EV$
; cases below that, and change measure of APPLY$, EV$, and EV$-LIST to acl2-count
; of the first arg.  Furthermore, if you do this, it is still possible to certify
; chronology.lisp.

; However, I have not been able to admit the ev! clique in the revised model,
; or, if I did admit it, I could not prove that ev! is ev$.

; To admit the ev! clique, first visit the same changes to apply! and ev! as
; described above, eliminating the 'APPLY$ and 'EV$ cases.  The measures can
; stay the same.  But you must also change the ``look-ahead'' tests, (consp
; (cdr x)), guarding ev!'s handling of 'COLLECT, 'SUMLIST, etc., so that they
; are (and (quotep (cad..dr x)) (tamep-functionp (cadr (cad..dr x)))).  This
; should allow the clique to be admitted.

; The ``look-ahead'' tests are necessary because otherwise ev! passes an
; ev!-list result into apply! and the old apply!-measure no longer works.

; THERE MAY BE A WAY to admit the modified clique with a different
; measure, but I haven't found it.

; But if the look-ahead tests are there in ev!, it makes ev! different from ev$
; because ev! looks for a QUOTE on the functional argument and strips it off
; (so it can terminate) but ev$ calls ev$-list on the arguments.  If there is
; no QUOTE on the functional arg, ev! signals an error but ev$ evaluates.  It
; could be that it evaluates to a tame function name.  If it does, we have to
; prove that the untame-apply$/untame-ev$ signal is the same as calling the
; tame function, which of course it's not.

; So the model has the look ahead tests to insure termination and the actual
; ev$ has the tamep test at the top to guarantee that the look ahead tests are
; all true and to guarantee that the short-circuiting of the ev$-list is equal
; to the ev$-list.

; About the definition of APPLY$-LAMBDA:

; The only reason we define APPLY$-LAMBDA is so that we can attach a concrete
; executable counterpart to it.  We'd prefer not to have the function occur in
; our proofs and so we always expand it away.

(defthm apply$-lambda-opener
  (equal (apply$-lambda fn args)
         (EV$ (lambda-body fn)
              (pairlis$ (lambda-formals fn)
                        args))))

; About the definition of EV$:

; Below we prove a simpler version of the defun of EV$, conditioned by the
; hypothesis that x is tamep.  So why do we define EV$ as we do above?  In the
; two clauses dealing with calls of APPLY$ and EV$ we apply$ the relevant
; function symbol rather than just calling it, e.g., we write (apply$ 'apply$
; ...)  instead of (apply$ ...).  We do it this way so that we can more easily
; prove that in all cases, ev$ handles function calls calling apply$ on the
; ev$-list of the arguments.  But note that we don't write it quite that way
; because we need to prove termination.  That is, instead of calling ev$-list
; we actually write an explicit list of the two arguments (list (cadr (cadr x))
; (EV$ (caddr x) a)).  Note in particular that we do not ev$ the first argument
; but just take its cadr!  This insures termination and is equivalent to (ev$
; (cadr x) a) PROVIDED the argument is tame!  Note also that we could have
; called (ev$-list (cdr x) a) had we known (cdr x) was suitably tame but that
; would require admitting this clique as a reflexive function: the fact that
; (ev$ (cadr x) a) is smaller than (cadr x) when (cadr x) is tame requires
; reasoning about ev$ before it is admitted.

; TODO: We have found that ev$-def-fact, if stored as a :definition, gets in
; the way of some proofs in applications books, like model.lisp.  But, oddly,
; we have been unsuccessful at disabling that :definition rule.  (I haven't
; pursued this possible bug yet.)  And in foldr-exercises.lisp we need to force
; ev$ open more often than the :definition rule does.  So we prove an opener
; below.  But we need the :definition rule to do it!  And since we can't
; apparently disable the :definition rule, we prove it locally.  And since we
; like to advertise the fact that ev$ has a rather beautiful definition for
; tamep terms, we prove ev$-def-fact as :rule-classes nil.

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

(defthm badge-badge
  (equal (badge 'badge) *generic-tame-badge-1*))

(defthm badge-tamep
  (equal (badge 'tamep) *generic-tame-badge-1*))

(defthm badge-tamep-functionp
  (equal (badge 'tamep-functionp) *generic-tame-badge-1*))

(defthm badge-suitably-tamep-listp
  (equal (badge 'suitably-tamep-listp) *generic-tame-badge-3*))

(defthm badge-apply$
  (equal (badge 'apply$) *apply$-badge*))

(defthm badge-ev$
  (equal (badge 'ev$) *ev$-badge*))

(defthm apply$-primitive
  (implies (apply$-primp fn)
           (equal (apply$ fn args)
                  (apply$-prim fn args))))

(defthm apply$-badge
  (equal (apply$ 'BADGE args)
         (badge (car args))))

(defthm apply$-tamep
  (equal (apply$ 'TAMEP args)
         (tamep (car args))))

(defthm apply$-tamep-functionp
  (equal (apply$ 'TAMEP-FUNCTIONP args)
         (tamep-functionp (car args))))

(defthm apply$-suitably-tamep-listp
  (equal (apply$ 'SUITABLY-TAMEP-LISTP args)
         (suitably-tamep-listp (car args) (cadr args) (caddr args))))

(in-theory (disable badge
                    (:executable-counterpart badge)
                    apply$
                    (:executable-counterpart apply$)))

; -----------------------------------------------------------------
; The Applicability Hypotheses

; Suppose AP is defined (with the new defun$) to be a tame function of two
; arguments.  Then the new defun$ will also do:

; (defun-sk applicablep-AP nil
;   (forall (args) (and (equal (badge 'AP) t)
;                       (equal (apply$ 'AP args)
;                              (ap (car args) (cadr args))))))

; (defthm apply$-AP
;   (implies (force (applicablep-AP))
;            (and (equal (badge 'AP) t)
;                 (equal (apply$ 'AP args)
;                        (ap (car args) (cadr args))))))

; (in-theory (disable applicablep-AP))

; which will mean that if we have the hypothesis (applicablep-AP), we will rewrite
; (badge 'AP) to T and rewrite (apply$ 'AP args) to the appropriate call of
; ap.  [Actually, instead of badge and apply$ above the defun-sk is about
; badge-nonprim and apply$-nonprim.  But the snippet above is spiritually
; correct.]

; ----------------------------------------------------------------- 
; Sugarcoating Applicability Hypotheses

; We don't want to write or read things like:

; (implies (and (applicablep-AP)                                  ; [1]
;               (applicablep-REV)
;               (applicablep-COLLECT)
;               ... other hyps...)
;          concl)

; We prefer to write and read:

; (implies (and (Applicablep AP REV COLLECT)                      ; [2]
;                ... other hyps...)
;           concl)

; In this section we arrange for this abbreviation.  Note that (applicablep ap
; rev collect) does not expand into a conjunction!  That would put individual
; applicablep-fn hypotheses into the hypotheses and they would not be collected
; together again by prettyprinting.  Instead, we keep them together in a list.
; Furthermore, each hypotheses is marked by a special function and we have
; rules that tell us how to find these hypotheses in the list.

; First, we adopt the convention that every applicablep hypothesis, h, is
; marked by being embedded in a call of the identity function
; applicablep-marker.  The reason for this marking will become clearer in a
; moment.

; Then we define applicablep as a macro that expands, in the case of [2] above,
; to

; (applicablep-listp (list (applicablep-marker (applicablep-ap))  ; [3]
;                          (applicablep-marker (applicablep-rev))
;                          (applicablep-marker (applicablep-collect))))

; Then we prove two theorems that enable us to relieve marked applicablep-fn
; hyps by inspecting calls of applicablep-listp.

; Finally, we arrange to prettyprint [3] as [2].

(defun applicablep-marker (x) x)

(defun make-applicablep-name (fn)
  (declare (xargs :guard (symbolp fn)))
  (intern-in-package-of-symbol
   (coerce
    (append '(#\A #\P #\P #\L #\I #\C #\A #\B #\L #\E #\P #\-)
            (coerce (symbol-name fn) 'list))
    'string)
   fn))

(encapsulate
 nil
 (local
  (defthm character-listp-cdr
    (implies (character-listp x)
             (character-listp (cdr x)))))

 (defun unmake-applicablep-name (hyp-name)
   (declare (xargs :guard (symbolp hyp-name)))
   (intern-in-package-of-symbol
    (coerce (cddddr (cddddr (cddddr (coerce (symbol-name hyp-name) 'list))))
            'string)
    hyp-name)))

(defun make-list-applicablep (names)
  (declare (xargs :guard (symbol-listp names)))
  (cond ((endp names) nil)
        (t (cons (list 'applicablep-marker
                       (list (make-applicablep-name (car names))))
                 (make-list-applicablep (cdr names))))))


(defmacro Applicablep (&rest names)
  (declare (xargs :guard (symbol-listp names)))
  `(applicablep-listp (list ,@(make-list-applicablep names))))

(defun applicablep-listp (lst)

; This is just the conjunction over lst, but has the unusual name so we can
; expect it only to be used with conjunctions of apply hyps.

  (if (endp lst)
      t
      (and (car lst)
           (applicablep-listp (cdr lst)))))

(defthm applicablep-lemma1
  (implies (and (applicablep-listp lst)
                (member (applicablep-marker a) lst))
           (applicablep-marker a)))

(defthm applicablep-lemma2
  (implies (and (applicablep-listp lst1)
                (subsetp lst2 lst1))
           (applicablep-listp lst2)))

(in-theory (disable applicablep-marker applicablep-listp
                    (:executable-counterpart applicablep-marker)
                    (:executable-counterpart applicablep-listp)))

(defun applicablep-untranslate-preprocess1 (term)
  (cond
   ((variablep term)
    :unrecognized)
   ((fquotep term)
    (cond
     ((equal term *nil*)
      nil)
     (t :unrecognized)))
   ((eq (ffn-symb term) 'cons)
    (let ((rest (applicablep-untranslate-preprocess1 (fargn term 2))))
      (cond
       ((eq rest :unrecognized)
        :unrecognized)
       (t
        (let ((hyp (fargn term 1)))
          (case-match hyp
            (('applicablep-marker (applicablep-name))
             (cond
              ((symbolp applicablep-name)
               (let ((fn-name (unmake-applicablep-name applicablep-name)))
                 (cond
                  ((eq applicablep-name (make-applicablep-name fn-name))
                   (cons fn-name rest))
                  (t :unrecognized))))
              (t :unrecognized)))
            (& :unrecognized)))))))
   (t :unrecognized)))

(defun applicablep-untranslate-preprocess (term w)

; When this function returns nil it means that we do not do anything special to
; term, i.e., it is untranslated and prettyprinted by ACL2's standard
; mechanism.  If we return non-nil, the returned ``term'' is prettyprinted in
; its place.

  (declare (ignore w))
  (case-match term
    (('applicablep-listp term)
     (let ((temp (applicablep-untranslate-preprocess1 term)))
       (cond
        ((eq temp :unrecognized)
         nil)
        (t `(Applicablep ,@temp)))))
    (& nil)))

(table user-defined-functions-table
       'untranslate-preprocess
       'applicablep-untranslate-preprocess)

; -----------------------------------------------------------------
; The Badge Table:

; The badge of a function fn is either nil (meaning fn is not analyzable or has
; not been analyzed) or is an APPLY$-BADGE record as noted above.

; In order to compute the badge of a new defun, we must be able to look up
; the badge of all the already-defined functions.  We will have applicablep
; hypotheses telling us the relevant badge, but we need an easier way to
; find a badge than inspecting the defun-sk for the function's applicablep
; hypothesis.  So we maintain a table for that purpose.  Every time a new
; function is analyzed, we extend the table.

; But first, we have to be able to compute the ilks, ci, of each formal vi in a
; term from the badges in the table.  Here is how we do that.

; Every formal of every function with an assigned badge has one of these ilks:
; nil (meaning :vanilla)
; :fn
; :expr
; We enforce the convention that if the ilks of a badge is T then all formals
; have ilk nil.

; We imagine a fourth ilk: :unknown, which we use in the code below.  If we
; determine that a formal has ilk :unknown, then the entire function is
; unanalyzable and no badge is generated or stored for it.  So no badge records
; an :unknown ilk, but it is useful to think of every formal of every function
; without a badge as having :unknown ilk.

; If a function has an :unknown formal, the function just isn't in the table at
; all and any function that calls it will inherit an :unknown classification.

; Recall also the :authorization-flg of the apply$-badge record.  If that flag
; is T, the function is known to APPLY$; if it is NIL, it means the function is
; analyzable and the formals have the ilks indicated, but the function returns
; multiple values and so cannot be known to APPLY$, which is single-valued.

; TODO: Maybe we should change from the automatic inference of ilks to the
; declaration of ilks by the user?  We implemented such a thing in v27x
; sources.

; TODO: We don't deal with mutual recursion yet!

; TODO: We handle lambda applications in function bodies by beta reducing them.
; This can be pretty inefficient.

; TODO: I think the above conflicts with the treatment of lambdas in tamep,
; which treats all lambda formals as :vanilla.  I think I may be misclassifying
; some formals.  Provoke an oddity!

; Let's assume these ``pre-check conditions'' for fn:

; (a) body does not use STATE or any stobj,

; (b) every function called in body (except fn itself) has a badge (possibly
; with :authorization-flg = nil), and

; (c) every :FN slot and :EXPR slot of every function called in body is
;     occupied by either a quoted constant naming an analyzed function or a
;     formal variable, and

; Then to check that the ith formal, var, has class :FN we can proceed as
; follows:

;   let n1 be the number of times var occurs as the actual in a :FN slot.
;   Let n2 be the number of times var occurs as the actual in the ith slot of a
;   recursive call.
;   Let n3 be the number of recursive calls.
;   Let k be the number of times var occurs in the body.

;   Then if n1 > 0, n2=n3, and n1+n2 = k then we know that var occurs at least
;   once in a :FN slot, it is always passed identically in recursion,
;   and it occurs nowhere else.

; The analogous check works for formals of class :EXPR.

; To check that a formal is of class :VANILLA (nil), we check that every
; occurrence is in a :vanilla slot.

; If any formal is not of one of the classes, it is :unknown.

; Note that this works only if the pre-check conditions hold.  For example, x
; in (apply$ (cons x x) y) would be classed as :vanilla were it not for
; pre-check condition (c).

; Note about Lambda Applications

; We beta reduce all lambda applications when classifying the formals of
; defuns.  This is pretty inefficient for large defuns.  We might want to
; re-implement it.  But there is a subtlety here.

; Consider ((lambda (x y) (cons (apply$ x y) (apply$ x y))) fn args).  To count
; the number of times fn occurs in a :fn slot, we beta reduce this application
; to (cons (apply$ fn args) (apply$ fn args)) and then report that fn is used 2
; times.  Since we are comparing this sense of ``how many'' with count-occur,
; we must do beta reduction in count-occur.  That's odd because if asked how
; many times fn occurs in the lambda application above the answer is surely 1.
; But to be comparable to the way we count :fn occurrences we have to say 2.
; So if we optimize the way we count special (and other occurrences) to
; eliminate the beta reductions, be sure to keep all the counts comparable.

(mutual-recursion
 (defun all-special-slots-okp (fn ilk term wrld)
   (declare (xargs :mode :program))
   (cond
    ((variablep term)
     t)
    ((fquotep term)
     (cond
      ((eq ilk :fn)
       (let ((xfn (cadr term)))
         (cond ((symbolp xfn)
                (and (executable-badge xfn wrld)
                     t))
               (t
                (and (consp xfn)
                     (eq (car xfn) 'lambda)
                     (consp (cdr xfn))
                     (symbol-listp (cadr xfn))
                     (consp (cddr xfn))
                     (null (cdddr xfn))
                     (termp (caddr xfn) wrld)
                     (all-special-slots-okp fn nil (caddr xfn) wrld))))))
      ((eq ilk :expr)
       (let ((xexpr (cadr term)))
         (and (termp xexpr wrld)
              (all-special-slots-okp fn nil xexpr wrld))))
      (t t)))
    ((or (eq ilk :fn)
         (eq ilk :expr))
     nil)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (all-special-slots-okp
      fn ilk
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))
      wrld))
    ((eq fn (ffn-symb term))
     (all-special-slots-okp-list fn nil (fargs term) wrld))
    (t (let ((bdg (executable-badge (ffn-symb term) wrld)))
         (cond
          ((null bdg) nil)
          ((eq (access apply$-badge bdg :ilks) t)
           (all-special-slots-okp-list fn nil (fargs term) wrld))
          (t (all-special-slots-okp-list fn
                                         (access apply$-badge bdg :ilks)
                                         (fargs term)
                                         wrld)))))))

 (defun all-special-slots-okp-list (fn ilks terms wrld)
   (cond
    ((endp terms) t)
    (t (and (all-special-slots-okp fn
                                   (car ilks)
                                   (car terms)
                                   wrld)
            (all-special-slots-okp-list fn
                                        (cdr ilks)
                                        (cdr terms)
                                        wrld))))))

(defun pre-check-body-for-classify-formals (fn body wrld)
  (declare (xargs :mode :program))

; You might think that checking that no stobjs are coming in then no stobjs are
; coming out, but you'd be wrong: stobj creators.

  (and (all-nils (getprop fn 'stobjs-in nil 'current-acl2-world wrld))
       (all-nils (getprop fn 'stobjs-out nil 'current-acl2-world wrld))
       (all-special-slots-okp fn :vanilla body wrld)))

(mutual-recursion
 (defun count-special-occurrences (fn var spec-ilk ilk term wrld)
   (declare (xargs :mode :program))
   (cond
    ((variablep term)
     (cond ((and (eq var term)
                 (eq spec-ilk ilk))
            1)
           (t 0)))
    ((fquotep term)
     0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-special-occurrences
      fn var spec-ilk ilk
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))
      wrld))
    ((eq fn (ffn-symb term))
     (count-special-occurrences-list fn var spec-ilk nil
                                     (fargs term)
                                     wrld))
    (t (let ((bdg (executable-badge (ffn-symb term) wrld)))
         (cond
          ((null bdg) 0)
          ((eq (access apply$-badge bdg :ilks) t)
           (count-special-occurrences-list fn var spec-ilk nil
                                           (fargs term)
                                           wrld))
          (t (count-special-occurrences-list fn var spec-ilk
                                             (access apply$-badge bdg :ilks)
                                             (fargs term)
                                             wrld)))))))  

 (defun count-special-occurrences-list (fn var spec-ilk ilks terms wrld)
   (cond
    ((endp terms) 0)
    (t (+ (count-special-occurrences fn var spec-ilk (car ilks) (car terms) wrld)
          (count-special-occurrences-list fn var spec-ilk (cdr ilks) (cdr terms) wrld))))))

(mutual-recursion
 (defun count-unchanged-formal (fn var i term)
   (declare (xargs :mode :program))
   (cond
    ((variablep term) 0)
    ((fquotep term) 0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-unchanged-formal
      fn var i
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))))
    (t
     (+ (if (and (eq fn (ffn-symb term))
                 (eq var (nth i term)))
            1
            0)
        (count-unchanged-formal-list fn var i (fargs term))))))
 (defun count-unchanged-formal-list (fn var i terms)
   (cond
    ((endp terms) 0)
    (t (+ (count-unchanged-formal fn var i (car terms))
          (count-unchanged-formal-list fn var i (cdr terms)))))))

(mutual-recursion
 (defun count-calls (fn term)
   (declare (xargs :mode :program))
   (cond
    ((variablep term) 0)
    ((fquotep term) 0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-calls
      fn
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))))
    (t (+ (if (eq fn (ffn-symb term)) 1 0)
          (count-calls-list fn (fargs term))))))
 (defun count-calls-list (fn terms)
   (cond
    ((endp terms) 0)
    (t (+ (count-calls fn (car terms))
          (count-calls-list fn (cdr terms)))))))

(mutual-recursion
 (defun count-occur (var term)
   (declare (xargs :mode :program))
   (cond
    ((variablep term)
     (if (eq var term) 1 0))
    ((quotep term) 0)
    ((flambdap (ffn-symb term)) ; See `Note about Lambda Applications' above
     (count-occur
      var
      (subcor-var (lambda-formals (ffn-symb term))
                  (fargs term)
                  (lambda-body (ffn-symb term)))))
    (t (count-occur-list var (fargs term)))))
 (defun count-occur-list (var terms)
   (cond
    ((endp terms) 0)
    (t (+ (count-occur var (car terms))
          (count-occur-list var (cdr terms)))))))

(defun functional-formalp (fn var i term wrld)
  (declare (xargs :mode :program))
  (let ((n1 (count-special-occurrences fn var :fn nil term wrld))
        (n2 (count-unchanged-formal fn var i term))
        (n3 (count-calls fn term))
        (k (count-occur var term)))
    (and (> n1 0)
         (= n2 n3)
         (= (+ n1 n2) k))))

(defun expressional-formalp (fn var i term wrld)
  (declare (xargs :mode :program))
  (let ((n1 (count-special-occurrences fn var :expr nil term wrld))
        (n2 (count-unchanged-formal fn var i term))
        (n3 (count-calls fn term))
        (k (count-occur var term)))
    (and (> n1 0)
         (= n2 n3)
         (= (+ n1 n2) k))))

(defun vanilla-formalp (fn var term wrld)
  (declare (xargs :mode :program))
  (let ((n1 (count-special-occurrences fn var nil nil term wrld))
        (k (count-occur var term)))
    (= n1 k)))

(defun classify-formal (fn var i term wrld)
  (declare (xargs :mode :program))
  (cond
   ((functional-formalp fn var i term wrld) :fn)
   ((expressional-formalp fn var i term wrld) :expr)
   ((vanilla-formalp fn var term wrld) nil)
   (t :unknown)))

(defun classify-formals1 (fn vars i term wrld)
  (declare (xargs :mode :program))
  (cond
   ((endp vars) nil)
   (t (cons (classify-formal fn (car vars) i term wrld)
            (classify-formals1 fn (cdr vars)
                               (+ 1 i)
                               term wrld)))))

(defun classify-formals (fn wrld)
  (declare (xargs :mode :program))
  (let ((body (body fn nil wrld))
        (formals (formals fn wrld)))
    (cond
     ((pre-check-body-for-classify-formals fn body wrld)
      (let ((ilks (classify-formals1 fn formals 1 body wrld)))
        (cond
         ((member-eq :unknown ilks) :unknown)
         ((all-nils ilks) t)
         (t ilks))))
     (t :unknown))))

; -----------------------------------------------------------------
; Functional Equivalence

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

; The following rewrite rule is needed to prove that fn-equal is an equivalence
; and to prove that fn-equal is an equality preserving congruence for mapping
; functions.  But it might be too expensive in general.  It's possibly saving
; grace is the presence of fn2 as a free var.  We'll start this development by
; making it non-local and enabled but that might change.

(defthm fn-equal-apply$-rewriter
    (implies (and (fn-equal fn1 fn2)
                  (syntaxp (and (not (equal fn1 fn2))
                                (term-order fn1 fn2))))
             (equal (apply$ fn1 args)
                    (apply$ fn2 args))))

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
    (cons `(defcong fn-equal equal ,term ,i)
          (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn))))
   (t (defcong-fn-equal-equal-events term (+ 1 i) (cdr c1-cn)))))

; -----------------------------------------------------------------
; Creating the Applicablep Hypothesis for Fn

; Given a fn whose badge are known (and not :unknown!), we can create the
; Applicablep Hypothesis for fn with make-applicablep-event.  The three
; functions defined immediately below are just helpers for that function.

(defun applicablep-tamep-hyps (ilks var)
  (declare (xargs :mode :program))
  (cond ((endp ilks) nil)
        ((eq (car ilks) :FN)
         (cons `(TAMEP-FUNCTIONP (CAR ,var))
               (applicablep-tamep-hyps (cdr ilks) (list 'CDR var))))
        ((eq (car ilks) :EXPR)
         (cons `(TAMEP (CAR ,var))
               (applicablep-tamep-hyps (cdr ilks) (list 'CDR var))))
        (t (applicablep-tamep-hyps (cdr ilks) (list 'CDR var)))))

(defun applicablep-actuals (formals var)
  (declare (xargs :mode :program))
  (cond ((endp formals) nil)
        (t
         (cons `(CAR ,var)
               (applicablep-actuals (cdr formals) (list 'CDR var))))))

(defun applicablep-ARGS-instance (ilks)

; This odd little function is used to generate an :instance hint.  Search below
; for :instance to see the application.  But imagine that you wanted a concrete
; list, e.g., '(x y z), of actuals satisfying the given ilks, e.g., (NIL :FN
; :EXPR).  Then, for this example, a suitable list would be '(NIL EQUAL T).
; (Indeed, so would '(NIL ZP NIL), but we just need some suitable list.)  We
; generate it here.  Note that the resulting list will be QUOTEd, so we return
; evgs here.

  (cond ((endp ilks) nil)
        ((eq (car ilks) :fn)
         (cons 'EQUAL (applicablep-ARGS-instance (cdr ilks))))
        ((eq (car ilks) :expr)
         (cons T (applicablep-ARGS-instance (cdr ilks))))
        (t (cons NIL (applicablep-ARGS-instance (cdr ilks))))))

(defun make-applicablep-event (fn formals bdg)

; This function should not be called (access apply$-badge bdg
; :authorization-flg) is nil!

; This function returns a list of events that add the appropriate defun-sk
; event for fn and then proves the necessary rewrite rule.

  (declare (xargs :mode :program))
  (let* ((name (make-applicablep-name fn))
         (rule-name (intern-in-package-of-symbol
                     (coerce (append '(#\A #\P #\P #\L #\Y #\$ #\-)
                                     (coerce (symbol-name fn) 'list))
                             'string)
                     fn))
         (necc-name (intern-in-package-of-symbol
                     (coerce
                      (append (coerce (symbol-name name) 'list)
                              '(#\- #\N #\E #\C #\C))
                      'string)
                     fn)))
    (cond
     ((null (access apply$-badge bdg :authorization-flg))
      (er hard 'make-applicablep-event
          "We attempted to introduce an APPLICABLEP-fn event for a function, ~
           ~x0, whose badge has :authorization-flg = NIL!  This is an ~
           implementation error."
          fn))
     ((eq (access apply$-badge bdg :ilks) t)
      `((defun-sk ,name ()
          (forall (args)
            (and (equal (badge-nonprim ',fn) ',bdg)
                 (equal (apply$-nonprim ',fn args)
                        (,fn ,@(applicablep-actuals formals 'args))))))
        (in-theory (disable ,name))
        (defthm ,rule-name
          (implies (force (Applicablep ,fn))
                   (and (equal (badge ',fn) ',bdg)
                        (equal (apply$ ',fn args)
                               (,fn ,@(applicablep-actuals formals 'args)))))
          :hints (("Goal" :use ,necc-name
                   :expand ((:free (x) (HIDE (badge x))))
                   :in-theory (e/d (badge apply$
                                    (:executable-counterpart applicablep-marker)
                                    (:executable-counterpart applicablep-listp))
                                   (,necc-name)))))))
     (t
      (let* ((hyp-list (applicablep-tamep-hyps (access apply$-badge bdg :ilks)
                                               'ARGS))
             (hyp (if (null (cdr hyp-list))
                      (car hyp-list)
                      `(AND ,@hyp-list))))
        `((defun-sk ,name ()
            (forall (args)
              (implies ,hyp
                       (and (equal (badge-nonprim ',fn) ',bdg)
                            (equal (apply$-nonprim ',fn args)
                                   (,fn ,@(applicablep-actuals formals 'args)))))))
          (in-theory (disable ,name))
          (defthm ,rule-name
            (and (implies (force (Applicablep ,fn))
                          (equal (badge ',fn) ',bdg))
                 (implies (and (force (Applicablep ,fn))
                               ,hyp)
                          (equal (apply$ ',fn args)
                                 (,fn ,@(applicablep-actuals formals 'args)))))

; Notice that the necc-name theorem is of the form (forall (args) (and ...))
; but the theorem above is essentially (and ... (forall (args) ...)) because
; the first conjunct is free of ARGS.  We had to write necc-name that way
; because of the requirements of defun-sk.  But now we have to extract the fact
; that we know (Applicablep fn) --> (badge 'fn) = <whatever>, by instantiating
; necc-name with a suitable ARGS that makes the right components suitably tame.

; The first :instance below takes care of the badge conjunct and the second
; takes care of the apply$ conjunct.

            :hints
            (("Goal"
              :use ((:instance ,necc-name
                               (ARGS ',(applicablep-ARGS-instance
                                        (access apply$-badge bdg :ilks))))
                    (:instance ,necc-name))
              :expand ((:free (x) (HIDE (badge x))))
              :in-theory (e/d (badge apply$
                                         (:executable-counterpart applicablep-marker)
                                         (:executable-counterpart applicablep-listp))
                              (,necc-name)))))))))))

(defun ancestral-all-fnnames1 (flg x wrld ans)
  (declare (xargs :mode :program))
  (cond
   (flg ; x is a list of fnnames
    (cond ((null x) ans)
          (t (ancestral-all-fnnames1
              t (cdr x) wrld
              (ancestral-all-fnnames1 nil (car x) wrld ans)))))
   ((or (member-eq x ans)
        (member-eq x '(apply$ ev$ ev$-list)))
    ans)
   (t (ancestral-all-fnnames1
       t (all-fnnames (body x nil wrld)) wrld
       (cons x ans)))))

(defun remove-fns-with-known-badge (lst wrld)
  (declare (xargs :mode :program))
  (cond
   ((null lst) nil)
   ((executable-badge (car lst) wrld)
    (remove-fns-with-known-badge (cdr lst) wrld))
   (t (cons (car lst)
            (remove-fns-with-known-badge (cdr lst) wrld)))))

(defmacro make-applicable (fn)
  `(with-output
     :off :all
     :stack :push
     :gag-mode nil
     (make-event
      (with-output
        :stack :pop
        (let ((fn ',fn)
              (wrld (w state)))
          (cond
           ((and (symbolp fn)
                 (arity fn wrld)
                 (not (eq (getprop fn 'symbol-class nil 'current-acl2-world wrld)
                          :PROGRAM))
                 (body fn nil wrld))
            (cond
             ((executable-badge fn wrld)
              (prog2$
               (cw "~%~x0 is already applicable, with badge ~x1.~%"
                   fn
                   (executable-badge fn wrld))
               (value '(value-triple :invisible))))
             (t
; We know fn is a logic mode function symbol.
              (let ((ilks (classify-formals fn wrld)))
                (cond
                 ((eq ilks :UNKNOWN)
                  (let ((ancestral-fns
                         (remove-fns-with-known-badge
                          (ancestral-all-fnnames1 nil fn wrld nil)
                          wrld)))
                    (cond
                     ((null (cdr ancestral-fns))
                      (er soft 'make-applicable
                          "~x0 cannot be made applicable because of one of ~
                           the following: (a) it returns multiple values, (b) ~
                           it uses STATE or some other stobj (or the ~
                           primordial state-like formal STATE-STATE), (c) it ~
                           does not respect the syntactic conventions on the ~
                           use of functional and/or expressional argument ~
                           positions in its body (e.g., it uses a quoted ~
                           LAMBDA expression whose body is not fully ~
                           translated or it uses one of its formals in both a ~
                           functional slot and a vanilla slot)."
                          fn))
                     (t
                      (er soft 'make-applicable
                          "~x0 cannot be made applicable at this time because ~
                           it (somehow) calls one or more functions that are ~
                           not yet applicable.  You should try to make these ~
                           other functions applicable first.  Of course, they ~
                           may not satisfy our restrictions on applicability ~
                           and so it may be impossible.  We recommend that ~
                           you try to make each of the following functions ~
                           applicable in the order they are listed: ~x1."
                          fn ancestral-fns)))))
                 (t (let ((bdg (make apply$-badge
                                     :authorization-flg
                                     (equal (length (getprop fn 'stobjs-out nil 'current-acl2-world wrld))
                                            1)
                                     :arity (arity fn wrld)
                                     :ilks ilks)))
                      (cond
                       ((null (access apply$-badge bdg :authorization-flg))
                        (value
                         `(encapsulate
                            nil
                            (table badge-table
                                   :badge-nonprim-structure
                                   (cons ',(cons fn bdg)
                                         (cdr
                                          (assoc :badge-nonprim-structure
                                                 (table-alist 'badge-table
                                                              world))))
                                   :put)
                            ,@(if (eq ilks t)
                                  nil
                                  (defcong-fn-equal-equal-events
                                    (cons fn (formals fn wrld)) 1 ilks))
                            (with-output
                              :stack :pop
                              (value-triple (cw "~%~x0 cannot be made ~
                                                 applicable because it ~
                                                 returns multiple values, but ~
                                                 it otherwise satisfies the ~
                                                 rules for applicable ~
                                                 functions and so can be ~
                                                 called in the body of a ~
                                                 single-valued function that ~
                                                 could be made applicable.  ~
                                                 The badge of ~x0 is ~x1.~%~%"
                                                ',fn ',bdg))))))
                       (t
                        (value
                         `(encapsulate
                            nil
                            ,@(make-applicablep-event fn (formals fn wrld)
                                                      bdg)
                            (table badge-table
                                   :badge-nonprim-structure
                                   (cons ',(cons fn bdg)
                                         (cdr
                                          (assoc :badge-nonprim-structure
                                                 (table-alist 'badge-table
                                                              world))))
                                   :put)
                            ,@(if (eq ilks t)
                                  nil
                                  (defcong-fn-equal-equal-events
                                    (cons fn (formals fn wrld)) 1 ilks))
                            (with-output
                              :stack :pop
                              (value-triple (cw "~%~x0 is now applicable, ~
                                                 with badge ~x1.~%~%"
                                                ',fn ',bdg))))))))))))))
           ((and (symbolp fn)
                 (arity fn wrld)
                 (null (body fn nil wrld)))
            (er soft 'make-applicable
                "~x0 is a declared function and cannot be made ~
              applicable.  Sorry!"
                fn))
           (t (er soft 'make-applicable
                  "Make-applicable should only be called on a defined logical ~
                 function symbol.  It is not permitted to call it on a ~
                 non-symbol, a symbol that is not a function symbol, or a ~
                 function symbol in :PROGRAM mode.  ~x0 is an inappropriate ~
                 argument."
                  fn))))))))

(defmacro defun$ (fn formals &rest rest)
  (let ( ;(body (car (last rest)))
;(dcls (all-but-last rest))
        )
    `(progn
      (defun ,fn ,formals ,@rest)
      (make-applicable ,fn))))

; -----------------------------------------------------------------
; The Lamb Hack

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
