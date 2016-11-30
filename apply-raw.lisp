; ACL2 Version 7.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2016, Regents of the University of Texas

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

; Support for experiments with apply$: raw Lisp code.  See other-events.lisp
; for logic code support (search for "Support for experiments with apply$").

; In this file we include essays and code in support of an experiment in how we
; might allow the evaluation of forms ancestrally dependent on apply$ (as
; defined in the community book /projects/apply/apply.lisp) at the top-level of
; the ACL2 loop.  This support is not enabled in ACL2, but can be activated (at
; the cost of invalidating our soundness assurances) as described below.
; This file is to be loaded in raw Lisp; for related code that can be loaded in
; the ACL2 loop, see the end of other-events.lisp.

; This section implements raw Lisp code for apply$-lambda as well as the
; ``dopplegangers'' for apply$-userfn and badge-userfn.  For relevant
; background not provided here, we refer you to the files in community books
; directory books/projects/apply/ and especially:

; * files that introduce apply$:
;   - apply-prim.lisp
;   - constraints.lisp
;   - apply.lisp

; * a wide variety of functions using apply$:
;   - user-book.lisp

; * files that illustrate how to define the ``doppelgangers'' of badge-userfn
;   and apply$-userfn, suitable for attaching to those two constrained
;   functions, enabling evaluation in the evaluation theory and making all of
;   the warrants issued in the above user-book.lisp valid in the evaluation
;   theory:

;   - doppelgangers.lisp
;   - defattach-demo.lisp
;   - all-warrants-valid.lisp

; A Little Background

; APPLY$ involves two critical constrained functions, BADGE-USERFN and
; APPLY$-USERFN.  (It also involves two others, used to deliver ``undefined''
; results, but these can remain undefined for our purposes.)  These two
; critical constrained functions are used to provide the meaning of BADGE and
; APPLY$ for those functions that the user introduces with defun$ (or
; def-warrant).

; In the following we assume that sq and collect have been defined as follows:
; (defun sq (x) (* x x))
; (defun collect (lst fn)
;   (if (endp lst)
;       nil
;       (cons (apply$ fn (list (car lst)))
;             (collect (cdr lst) fn))))

; Sq is an example of a ``tame function'' in the sense that we can arrange for
; (apply$ 'sq (list x)) to be (sq x), unconditionally.  Collect is an ``almost
; tame'' function, henceforth known as a ``mapping function,'' in the sense
; that its definition (ancestrally) depends on apply$ but, additionally, the
; results delivered when its second argument, fn, is a tame function could be
; computed by a function not involving apply$, e.g.,

; (defun collect-sq (lst)
;   (if (endp lst)
;       nil
;       (cons (sq (car lst))
;             (collect-sq (cdr lst))))).

; The ``badge,'' if any, of a symbol tells us whether it is tame or a mapping
; function and which formals are ``functional.''

; Naively, the functions BADGE and APPLY$ ``grow'' as new tame functions and
; new mapping functions are introduced.  This ``growth'' is actually handled by
; defining BADGE and APPLY$ to be equal to the constrained functions
; badge-userfn and apply$-userfn on symbols that are not built into their
; definitions, and then providing hypotheses that stipulate the properties of
; those constrained functions on the user-defined symbols in question.
; These hypotheses are called ``warrants.''

; Warrant (Merriam-Webster);
; [noun] commission or document giving authority to do something

; In our case, a warrant for function symbol fn is a 0-ary predicate named
; APPLY$-WARRANT-fn that specifies values returned by badge-userfn and
; apply$-userfn when they're given the symbol 'fn.  For example, the
; warrant for collect, named APPLY$-WARRANT-COLLECT, tells us:

;  (badge-userfn 'COLLECT) = '(apply$-badge t 2 NIL :FN)

;  and

;  (implies (tamep (cadr args))
;           (equal (apply$-userfn 'COLLECT args)
;                  (collect (car args) (cadr args))))

; The hypothesis in the second conjunct above is called the ``tameness
; condition'' for COLLECT.

; Proofs about the behavior of APPLY$, when APPLY$ is supplied with symbols
; that are not built in, require the relevant warrants as hypotheses.  This
; solves the LOCAL problem, since the warrant for fn ancestrally depends on the
; function fn.

; The user can cause functions to acquire warrants by executing the def-warrant
; event defined in apply.lisp.  E.g., a warrant for collect can be issued by
; (def-warrant collect), after defining it as above.  The defun$ event of
; apply.lisp is just an abbreviation for a defun followed by a def-warrant.

; Since APPLY$ involves the two critical constrained functions, it simply can't
; be executed on most terms containing functions that are not built into it.

; But we would like to be able to execute it in contexts allowing attachments.
; We would like be able to type (APPLY$ 'SQ '(3)) at the top-level of the ACL2
; loop and and get 9.  We would like to be able to type (COLLECT '(1 2 3) 'SQ)
; and get (1 4 9).  These answers are justified by the theorem:

; (thm (implies (apply$-warrant-SQ)
;               (and (equal (apply$ 'SQ '(3)) 9)
;                    (equal (collect '(1 2 3) 'SQ) '(1 4 9)))))

; But true evaluation is impossible in any current version of ACL2 because
; BADGE-USERFN and APPLY$-USERFN are undefined.

; Of course, this theorem may be meaningless because there may be no way to
; make (apply$-warrant-SQ) true.  However, in the files doppelgangers.lisp,
; defattach-demo.lisp and all-warrants-valid.lisp we show that for all the
; warranted functions defined in user-book.lisp we can define two functions,
; badge-userfn! and apply$-userfn! (note the exclamation point distinguishing
; the symbols from the previously mentioned constrained functions), in such a
; way that (a) we can do:

; (defattach badge-userfn badge-userfn!)
; (defattach apply$-userfn apply$-userfn!)

; so that the expected evaluations are possible in the evaluation theory, and
; (b) all the warrants issued in user-book.lisp are provably valid in the
; evaluation theory.

; Of course, these attachments only work for that fixed set of functions
; defined in user-book.lisp.  If the user defines a new tame or mapping
; function, we would have to compute a new pair of attachment functions.

; So the strategy we take in the experimental code below (to support evaluation
; of apply$ in the evaluation theory) is to define raw Lisp versions of the
; attachment functions that secretly inspect the logical world to see whether
; the symbol being considered has a warrant and if so then behave as the
; doppelganger of badge-userfn or apply$-userfn would behave.  These raw Lisp
; versions of the doppelgangers are named concrete-badge-userfn and
; concrete-apply$-userfn.

; But we have not yet established that the resulting evaluation theory
; satisfies the consistency requirements of the Essay on Defattach.  Therefore,
; we do not make this experimental support available in ACL2.

; This support is only activated if the user executes certain commands, among
; which is one that voids the soundness guarantees we offer.  This activation
; is accomplished by carrying out The Rubric discussed below.

; Executing The Rubric immediately after starting up the ACL2 image built from
; these sources converts ACL2 into what we will temporarily call ``ACL2(a)''
; which allegedly supports the execution of apply$ as defined in apply.lisp.
; Eventually, either we'll abandon ACL2(a) or make trusted versions of these
; features a permanent part of ACL2.  But it may us take several release cycles
; to decide!

; To tell whether we're in ACL2 or ACL2(a) we test the raw Lisp special
; variable *allow-concrete-execution-of-apply-stubs*.  That variable is t iff
; we're in ACL2(a) and we assume the only assignment to it is via The Rubric.

; The Rubric

; If you want to convert ACL2 into ACL2(a) evaluate each of the forms below
; immediately after starting your ACL2 session.

;   (include-book "projects/apply/apply" :dir :system)
;   (defattach (badge-userfn concrete-badge-userfn)
;     :hints
;     (("Goal" :use concrete-badge-userfn-type)))
;   (defattach apply$-userfn concrete-apply$-userfn)
;   (value :q)
;   (defun apply$-lambda (fn args) (concrete-apply$-lambda fn args))
;   (setq *allow-concrete-execution-of-apply-stubs* t)
;   (lp)
;   (quote (end of rubric))

; Because The Rubric requires you execute a form in raw Lisp, The Rubric
; eliminates the soundness guarantees provided by the ACL2 implementors!

; Some of the code below affects the behavior of ACL2.  Other parts of the code
; is only active in ACL2(a).  We identify the latter with comments that start
; with ``; ACL2(a) only''.

; -----------------------------------------------------------------

(defvar *allow-concrete-execution-of-apply-stubs* nil)

; ACL2(a) only -- the definition below is only relevant in ACL2(a)
(defun query-badge-userfn-structure (msgp fn wrld)

; This function is only called in contexts in which
; *allow-concrete-execution-of-apply-stubs* is true.  This function takes a
; purported function symbol, fn, and determines if it has been assigned a badge
; by def-warrant.  We return one of three answers:

; - (mv nil badge): fn was found in the badge-table and the badge is badge.
;      Note that fn may or may not have a warrant!  It does have a warrant if
;      (access apply$-badge badge :authorization-flg) = (cadr badge) = t, and
;      it doesn't have a warrant otherwise.  Because we haven't included the
;      defrec for apply$-badge we have to use the cadr form rather than the
;      access form.  If fn has a warrant, it is named APPLY$-WARRANT-fn.

; - (mv msg nil): there is no entry for fn in the badge-table, so no
;      def-warrant has been successful on fn; msg is a tilde-@ msg possibly
;      explaining in a little more detail why fn doesn't have a badge.

; - (mv t nil): same as above but we don't bother to explain why.

; Note that if the first result is non-nil it means we failed to find a badge.
; But that first result could either be an error msg or just T.  It is a msg if
; the input argument msgp is t and it is not a message if msgp is nil.  That
; is, msgp = t means generate an explanatory message; msgp=nil means signal
; failure with first result T.

; It is important that if this function returns (mv nil badge) for a world
; then it returns that same answer for all extensions of the world!

; We assume that the user does not mess with the badge-table!  This is a
; ``bulletproofing issue.''

  (cond
   ((not (symbolp fn))
    (mv (or (not msgp)
            (msg "~x0 is not a symbol" fn))
        nil))
   ((not (function-symbolp fn wrld))
    (mv (or (not msgp)
            (msg "~x0 is not a known function symbol" fn))
        nil))
   ((eq (symbol-class fn wrld) :program)
    (mv (or (not msgp)
            (msg "~x0 is a :PROGRAM mode function symbol" fn))
        nil))
   (t
    (let ((bdg ; the badge of nonprim fn, if any
           (cdr
            (assoc-eq
             fn
             (cdr
              (assoc-eq :badge-userfn-structure
                        (table-alist 'badge-table
                                     wrld)))))))
      (cond
       ((null bdg) ; fn is a function sybmol with no badge assigned
        (cond ((null msgp) (mv t nil))
              (t (mv (msg "~x0 has not been warranted" fn)
                     nil))))
       (t (mv nil bdg)))))))

; The Rubric will:
; (defattach (badge-userfn concrete-badge-userfn) ...)
; (defattach (apply$-userfn concrete-apply$-userfn) ...)

; We define the two concrete- functions below.

; Because we want to implement their bodies in raw Lisp, we would like to
; introduce them with defun-overrides commands like

; (defun-overrides concrete-badge-userfn (fn) ...)
; (defun-overrides concrete-apply$-userfn (fn args) ...)

; But the defun-overrides macro requires that STATE be among the formals of the
; function introduced and it is not.  So we can't use defun-overrides per se.
; Instead, we use the code that defun-overrides would have introduced, but
; delete the parts about state!  We believe this is sound because (a) the
; concrete implementations cause the same kind of error that calling an
; undefined function causes if applied to arguments for which the answer is
; unspecified, and (b) once the answer is specified in a world, the answer is
; the same for all future extensions of the world.  Important to observation
; (b) is that we cannot apply$ functions to stobjs or state.

; TODO: If we believe that defun-overrides is ok if the definition has the
; kind of behavior described above, it might be good to add a comment to that
; effect in defun-overrides or provide a disciplined version of
; ``defun-overrides-for-fns-that-implicitly-use-the-world-consistenty''.

; Here is the STATE-free expansion of
; (defun-overrides concrete-badge-userfn (fn) ...)
; ==>
;  (assert (member 'state formals :test 'eq))
(progn (push 'concrete-badge-userfn *defun-overrides*) ; see add-trip

; The next two items are pushed to the left margin so they get picked up by
; etags.  But they're really part of the progn!

; The following defun has two notes in it which are given afterwards.

; (Note: for now we leave comments of the form ``Error {[x]}'', to support our
; own testing that provokes these messages.)

(defun concrete-badge-userfn (fn)
;  (declare (ftype (function (t) (values t))  ; See next comment.
;                  apply$-primp))
  (cond
   ((or (not *allow-concrete-execution-of-apply-stubs*)
        (not *aokp*))    ; See Note 1.
    (throw-raw-ev-fncall ; See Note 2.
     (list* 'ev-fncall-null-body-er
            nil
; Error {[1]}
            'concrete-badge-userfn
            (print-list-without-stobj-arrays
             (list fn)))))

; ACL2(a) only - the rest of this cond is only relevant in ACL2(a)

; If the constraint on badge-userfn includes the requirement that (badge-userfn
; fn) = nil when fn is a primitive or a boot function, as discussed in the Note
; on Strengthening the Constraint in badge-userfn-type found in
; constraints.lisp, then we need a clause like that below together with the
; declare ftype above.  But there is a problem: when we add
; concrete-badge-userfn as a trusted clause processor, further below, we need
; to specify a constraint for it that includes the requirement just stated, and
; we do not have apply$-primp in the logic during the ACL2 build.  If someday
; we make apply$ a primitive, we can include this constraint, but not yet.

;   ((or (apply$-primp fn)
;        (eq fn 'badge)
;        (eq fn 'tamep)
;        (eq fn 'tamep-functionp)
;        (eq fn 'suitably-tamep-listp)
;        (eq fn 'apply$)
;        (eq fn 'ev$))
;    nil)

   (t (mv-let (failure-msg bdg)
        (query-badge-userfn-structure t fn (w *the-live-state*))
        (cond
         ((and (null failure-msg)
               (cadr bdg)) ; = (access apply$-badge bdg :authorization-flg)
          bdg)
         (t (let* ((failure-msg
                    (if failure-msg
                        failure-msg
; Error {[4.5]}
                        (msg "~x0 returns multiple values, so it has a badge ~
                              but no warrant"
                             fn)))
                   (msg
                    (cond
                     ((eq *aokp* 'badge-userfn)
; Error {[2]}
                      (msg "The value of BADGE-USERFN is not specified on ~
                            ~x0 because ~@1."
                           fn failure-msg))
                     ((eq *aokp* t)
; Error {[3]}
                      (msg "The value of CONCRETE-BADGE-USERFN is not ~
                            specified on ~x0 because ~@1."
                           fn failure-msg))
                     (t
; Error {[4]}
                      (msg "The value of ~x0 is not specified.  ~x0 is a ~
                            constrained function with ~x1 as its attachment ~
                            and in this instance that attachment calls ~
                            CONCRETE-BADGE-USERFN on ~x2 and is not ~
                            specified because ~@3."
                           *aokp*
                           (symbol-value
                            (attachment-symbol *aokp*))
                           fn
                           failure-msg)))))
              (throw-raw-ev-fncall ; See Note 3.
               (list* 'ev-fncall-null-body-er
                      nil
                      msg
                      (print-list-without-stobj-arrays
                       (list fn)))))))))))

; Notes on CONCRETE-BADGE-USERFN

; Note 1. on the test of *aokp*: We once thought that it was unnecessary to
; test *aokp* in concrete-badge-userfn.  The (faulty) reasoning was that
; concrete-badge-userfn is the attachment for badge-userfn.  We wouldn't be
; running concrete-badge-userfn if attachments weren't ok.  The flaw in that
; reasoning is that concrete-badge-userfn is itself a :logic mode function and
; might be called directly by the user at the top level of the ACL2 loop, or
; used in some other function used in proofs or hints.  So we might find
; ourselves executing concrete-badge-userfn even though *aokp* is nil.  We need
; for it to act undefined when *aokp* is nil.

; Note 2.  on throw-raw-ev-fncall: Throughout this function we cause errors
; when the answer is not determined by the known warrants.  The various errors
; are all equivalent to ``ACL2 cannot evaluate a call to the undefined
; function....''  Once upon a time we signalled the errors by calling
; (throw-without-attach nil fn formals) which expands in raw Lisp to

; `(throw-raw-ev-fncall
;    (list* 'ev-fncall-null-body-er
;            nil
;           ',fn
;           (print-list-without-stobj-arrays (list ,@formals))))

; When fn is a symbol, throw-raw-ev-fncall uses the standard undefined function
; error msg, reporting fn as the culprit.  If fn is a consp,
; throw-raw-ev-fncall uses fn as the message.  But as shown above,
; throw-without-attach puts a quote on fn when it expands.  So using
; throw-without-attach prevents us from creating our own messages with msg, as
; we do above.  So instead of throw-without-attach we use its expansion,
; without the quote on the ``fn'' arg.

; End of Notes on CONCRETE-BADGE-USERFN

(defun-*1* concrete-badge-userfn (fn)
  (concrete-badge-userfn fn))

; End of progn from ``defun-overrides''
)

; Essay on a Misguided Desire for Erroneous APPLY$s to Print Exactly the
; Same Error Messages whether Evaluation of APPLY$ Stubs is Supported or Not

; One possible objection to our handling of errors in concrete-badge-userfn
; arises with the question: If we attempt an evaluation of apply$ that is bound
; to fail, do we get exactly the same error message regardless of whether
; evaluation of the critical apply$ constrained functions is supported or not?
; The answer is "No."  In fact, the answer is "No, there's no reason to expect
; that!"

; Here is an example.

; In ACL2, even versions not supporting evaluation of apply$, we can include
; the distributed apply.lisp book and introduce these two functions:

; (defun$ sq (x) (* x x))
; (defun$ foo (fn1 fn2 x)
;   (cons (apply$ fn1 (list x))
;         (apply$ fn2 (list x))))

; Then trying to evaluate (foo 'sq 'cube 3) causes the error:

; ACL2 Error in TOP-LEVEL: ACL2 cannot ev the call of undefined function
; APPLY$-USERFN on argument list: (SQ (5))

; because we can't apply$ 'SQ.

; But if we execute The Rubric in an ACL2 that supports the evaluation of
; apply$ and try that same form, we get a different error:

; ACL2 Error in TOP-LEVEL: The value of APPLY$-USERFN is not specified on CUBE
; because CUBE is not a known function symbol.

; We got past the (apply$ 'SQ ...) but now failed on (apply$ 'CUBE ...).

; So we can't expect unchanged erroneous behavior because the compuation paths
; are just different in the two scenarios.

; End of Essay on A Misguided Desire...

; ACL2(a) only -- the next defun is only relevant in ACL2(a)
(defun concrete-check-apply$-hyp-tamep-hyp (ilks args wrld)

; Compare to tameness-conditions in apply.lisp.

  (declare (ftype (function (t t) (values t))
                  executable-tamep
                  executable-tamep-functionp))

  (cond ((endp ilks) t)
        ((eq (car ilks) :fn)
         (and (executable-tamep-functionp (car args) wrld)
              (concrete-check-apply$-hyp-tamep-hyp (cdr ilks) (cdr args) wrld)))
        ((eq (car ilks) :expr)
         (and (executable-tamep (car args) wrld)
              (concrete-check-apply$-hyp-tamep-hyp (cdr ilks) (cdr args) wrld)))
        (t (concrete-check-apply$-hyp-tamep-hyp (cdr ilks) (cdr args) wrld))))

; Here is the STATE-free expansion of
; (defun-overrides concrete-apply$-userfn (fn args) ...)
; ==>
;  (assert (member 'state formals :test 'eq))
(progn (push 'concrete-apply$-userfn *defun-overrides*) ; see add-trip

; The next two items are pushed to the left margin so they get picked up by
; etags.  But they're really part of the progn!

(defun concrete-apply$-userfn (fn args)
;           (progn (chk-live-state-p ',name state)
  (cond
   ((or (not *allow-concrete-execution-of-apply-stubs*)
        (not *aokp*))
    (throw-raw-ev-fncall
     (list* 'ev-fncall-null-body-er
            nil
; Error {[5]}
            'concrete-apply$-userfn
            (print-list-without-stobj-arrays
             (list fn args)))))
; ACL2(a) only -- rest of this cond is only relevant in ACL2(a)
   (t (mv-let (failure-msg bdg)
        (query-badge-userfn-structure t fn (w *the-live-state*))
        (cond
         ((or failure-msg        ; there is no badge for fn
              (null (cadr bdg))) ; fn is not warranted
          (let* ((failure-msg
                  (if failure-msg
                      failure-msg
; Error {[8.5]}
                      (msg "~x0 returns multiple values, it has a badge but ~
                            no warrant"
                           fn)))
                 (msg (cond
                       ((eq *aokp* 'apply$-userfn)
; Error {[6]}
                        (msg "The value of APPLY$-USERFN is not specified on ~
                              ~x0 because ~@1."
                             fn failure-msg))
                       ((eq *aokp* t)
; Error {[7]}
                        (msg "The value of CONCRETE-APPLY$-USERFN is not ~
                              specified on ~x0 because ~@1."
                             fn failure-msg))
                       (t
; Error {[8]}
                        (msg "The value of ~x0 is not specified.  ~x0 is a ~
                              constrained function with ~x1 as its attachment ~
                              and in this instance that attachment calls ~
                              CONCRETE-APPLY$-USERFN on ~x2 and is not ~
                              specified because ~@3."
                             *aokp*
                             (symbol-value
                              (attachment-symbol *aokp*))
                             fn
                             failure-msg)))))
            (throw-raw-ev-fncall
             (list* 'ev-fncall-null-body-er
                    nil
                    msg
                    (print-list-without-stobj-arrays
                     (list fn args))))))
          ((eq (cdddr bdg) t) ; = (access apply$-badge bdg :ilks)
           (apply (*1*-symbol fn)
                  (if (= (caddr bdg) ; = (access apply$-badge bdg :arity)
                         (length args))
                      args
                      (take (caddr bdg) ; = (access apply$-badge bdg :arity)
                            args))))
          ((concrete-check-apply$-hyp-tamep-hyp
            (cdddr bdg) ; = (access apply$-badge bdg :ilks)
            args
            (w *the-live-state*))
           (apply (*1*-symbol fn)
                  (if (= (caddr bdg) ; = (access apply$-badge bdg :arity)
                         (length args))
                      args
                      (take (caddr bdg) ; = (access apply$-badge bdg :arity)
                            args))))
          (t
           (let ((msg
                  (cond
                   ((eq *aokp* 'apply$-userfn)
; Error {[9]}
                    (msg "The value of APPLY$-USERFN is not specified~ ~
                          when the first argument, fn, is ~x0, and the ~
                          second argument, args, is ~x1.  Fn has badge ~x2 ~
                          and args is not known to satisfy the tameness ~
                          requirement of that badge."
                         fn args bdg))
                   ((eq *aokp* t)
; Error {[10]}
                    (msg "The value of CONCRETE-APPLY$-USERFN is not ~
                          specified when the first argument, fn, is ~x0, and ~
                          the second argument, args, is ~x1.  Fn has badge ~
                          ~x2 and args is not known to satisfy the tameness ~
                          requirement of that badge."
                         fn args bdg))
                   (t
; Error {[11]}
                    (msg "The value of ~x0 is not specified. ~x0 is a ~
                          constrained function with ~x1 as its attachment and ~
                          in this instance that attachment calls ~
                          CONCRETE-APPLY$-USERFN with first argument, fn, ~
                          being ~x2 and second argument, args, being ~x3.  ~
                          But fn has badge ~x4 and args is not known to ~
                          satisfy the tameness requirement of fn's badge."
                         *aokp*
                         (symbol-value
                          (attachment-symbol *aokp*))
                         fn
                         args
                         bdg)))))
              (throw-raw-ev-fncall
               (list* 'ev-fncall-null-body-er
                      nil
                      msg
                      (print-list-without-stobj-arrays
                       (list fn args)))))))))))

(defun-*1* concrete-apply$-userfn (fn args)
  (concrete-apply$-userfn fn args))

; End of progn from ``defun-overrides''
)

; ACL2(a) only -- everything else in this file is only relevant in ACL2(a)

; What we've described so far is adequate to run APPLY$ and EV$ forms in the
; evaluation theory after attaching the doppelgangers of badge-userfn and
; apply$-userfn for the current world to those critical functions.

; Now we turn to the optimization of APPLY$-LAMBDA.  In apply.lisp,
; we have the theorem:
; (equal (apply$-lambda fn args)
;        (ev$ (lambda-body fn)
;             (pairlis$ (lambda-formals fn)
;                       args)))

; But we wish to apply certain lambdas more efficiently in the evaluation
; theory.

; A rough sketch of what we do is: The Rubric redefines APPLY$-LAMBDA in raw
; Lisp to check that the LAMBDA has a variety of important properties,
; including that the lambda is a well-formed, fully translated, closed, ACL2
; lambda expression whose body is guard verified as though the input guard on
; the lambda were :guard T.  If it has these properties we compile it and apply
; that compiled function object with CLTL's apply instead of interpreting its
; body with *1* EV$.

; TODO: Something to think about: Do attachments affect this?  I'm not sure
; they do.  Attachments already, supposedly, are correct in the case of our
; running compiled guard verified code.  And I believe that's really all that
; is happening here.

; The problem we face below is that LAMBDA objects are just quoted constants.
; Their bodies are not inspected at translate time nor affected by
; macroexpansion.  Indeed, we don't even know if a lambda-looking constant will
; be treated as a lambda expression until it reaches APPLY$-LAMBDA.  Before a
; lambda object can be compiled we have to know it is a well-formed ACL2 lambda
; expression, i.e., (LAMBDA formals body), where formals is a list of distinct
; variable symbols, body is an ACL2 term in logic mode, that there are no free
; variables in the body other than the formals, and that the body is tame.

; From apply.lisp we have the theorem above saying that (apply$-lambda fn args)
; is unconditionally equal to the ev$ of the body under an alist created from
; the formals and args.  So if the lambda object in question does not satisfy the
; rules above, we can still ev$ it as per the theorem.

; Even if all those conditions are met, the compiled code can't be executed
; unless the LAMBDA is Common Lisp compliant -- a notion that is not currently
; implemented for LAMBDA expressions in ACL2.  Finally, even Common Lisp
; compliant LAMBDAs can't be executed in raw Lisp unless their guards are
; satisfied by the actuals, but LAMBDAs don't carry guards in ACL2.  And we
; envision LAMBDAs being applied iteratively over large domains.  We don't want
; to check their guards on every element of the domain.

; To finesse these guard issues we insist that the LAMBDA be Common Lisp
; compliant when the input guard is T, making the determination of compliance
; completely independent of the particular actuals to which the LAMBDA will be
; applied, i.e., LAMBDAs passing our tests can be compiled and applied in raw
; Lisp to any ACL2 objects.

; The last condition above is like saying that the LAMBDA is ``guard verified
; and has an input guard of T.''  We call these LAMBDAs ``unrestricted.''

; Note that '(LAMBDA (X) (SQ X)) is NOT unrestricted if SQ is defined as
; in the obvious way:

; (defun$ sq (x) (* x x))

; In particular, for that defun of sq, '(LAMBDA (X) (SQ X)) has the non-trivial
; guard obligation (acl2-numberp x).  However, if we defined sq this way

; (defun$ sq (x) (declare (xargs :guard t)) (* (fix x) (fix x)))

; then '(LAMBDA (X) (SQ X)) would satisfy our properties, we say it's
; unrestricted, and we could apply it to any inputs without hard errors.

; The following LAMBDA expressions are unrestricted even with the original
; defun of sq:

; '(LAMBDA (X) (SQ (FIX X)))
; '(LAMBDA (X) (BINARY-* (FIX X) (FIX X)))

; They too can be applied to anything.

; When the ``variety of important properties'' noted above are met, we will
; arrange for APPLY$-LAMBDA to compile the LAMBDA and use CLTL's apply function
; to apply the resulting CLTL function object.  Our code has only been tested
; for CCL.

; Our decision to optimize only the application of unrestricted LAMBDAs, while
; somewhat dissatisfying, probably allows the user to efficiently use most
; mapping functions (by ensuring that the LAMBDA expression is unrestricted).
; This generally means typing LAMBDA expressions with ``fixers'' around each
; use of a formal in the body.

; We will cache this check for well-formed, translated, tame, compliant,
; unrestricted LAMBDAs, with their compiled versions, so that if we encounter
; this same LAMBDA again -- in the same logical world -- we get the compiled
; function object without having to re-check the properties or call the
; compiler.  The cache is called the ``compiled-LAMBDA cache'' or cl-cache.

; We implemented our own cache.  We considered four alternatives:

; (a) Do Nothing: Let ACL2(a) behave normally by running the *1* code for
; APPLY$-LAMBDA, which just interprets the lambda-body with EV$.

; (b) Compile but Don't Cache: recognize and compile unrestricted lambdas every
; time they're applied but do not cache the test or compilation results.
; Clearly, the hope behind this approach was that the increased speed of
; executing compiled code overcomes the cost of recognition and compilation.

; (c) Fast-Alist Cache: recognize and compile unrestricted lambdas, caching
; recognized lambdas with their compiled code via a fast-alist.  Finding a
; lambda in the cache means it satisfies the ``variety of important
; properties'' and gives us its compiled version.  Lambdas without those
; properties are cached separately to avoid having to recognize them again.

; (d) Home-Grown Cache: Like (c) except we rolled our own cache.

; Experiments with all four scenarios are detailed in a long comment below
; under the name Essay on the Performance of APPLY$.  An executive summary of
; those experiments is: Our Fast-Alist cache performs about 50% slower than our
; Home-Grown cache.  The Do Nothing and the Compile but Don't Cache approaches
; are much worse.  But many things affect performance.  Choosing the best
; implementation depends on the expected size of the LAMBDAs, whether
; unrestricted LAMBDAs occur frequently enough to matter, frequency of
; application of a given LAMBDA, etc., how often the world changes
; (invalidating or at least complicating the cache), etc.

; Our tests were with one relatively small LAMBDA,

; (LAMBDA (X) (BINARY-+ '3 (BINARY-* '2 X))) ; ``bad variant''

; and its ``good variant'' with a FIX around the use of X.  The bad variant
; fails to satisfy the properties required for compilation (it has a
; non-trivial guard obligation); the good variant is unrestricted.  We then
; tested (sum *million* <lambda>), where *million* is a list of the first 1
; million naturals.  We focused mainly on the good variant because we are
; interested in the cost of recognizing, compiling, and caching suitable
; lambdas.  But note that both Scenario (c) and (d) pay the price of
; recognizing and compiling the good lambda just once in the (sum *million*
; <lambda>) test and then find that same (in fact, EQ) <lambda> in the cache
; 999,999 times while the world remains unchanged.

; Our experiments indicate that if we are going to apply a lambda fewer than
; about 50 times, recognizing and compiling good ones is not worth it: we could
; just interpret the lambda body with EV$ in the same amount of time.

; Our current implementation choice (Home-Grown Cache) is thus skewed toward
; the fast execution of mapping functions, like sum, over large domains.  This
; is motivated by the original problem that inspired work on apply$: how to
; provide robust and convenient iterative primitives for interactive use to the
; ACL2(a) user.

; Two severe disadvantages of the current Home-Grown Cache are that it
; maintains only 3 cache lines (i.e., is capable of remembering only three
; compiled lambdas) and is cleared every time the world changes.  The choice of
; a small, fixed number of cache lines makes the implementation faster because
; each line is a separate raw Lisp variable, but at the expense of more
; voluminous code as we check and fill or empty each line with code that looks
; much like the code for the line before it.  But the small, fixed number of
; lines was considered adequate for executing ``typical'' mapping expressions,
; like (sum (collect ... '(lambda (x) ...))  '(lambda (y) ...)).  Both lambdas
; would be compiled and cached for the duration of the evaluation.  We don't
; anticipate many interactively submitted ground mapping expressions to involve
; more than 3 lambdas.  An advantage of the Fast-Alist Cache is that it
; maintains an arbitrary number of cache lines.  We are content at the moment
; to recompile such expressions every time the world changes.

; See the Essay on the Performance of APPLY$ for details of our experiments and
; implementation of a quick-and-dirty Fast-Alist Cache.

; A Collection of TODOs related to Compilation and Caching

; TODO: The current implementation clears the cache whenever the world has
; changed since the last execution.  Perhaps we could carry the cache forward
; as the world is merely extended.  That is, if the current world is not EQ to
; the one associated with the current cache, we check whether the current world
; is an extension of it.  If so, we just set the associated cache world to the
; new current world and proceed.  Note that we can actually encounter LAMBDA
; objects containing ``function symbols'' that do not exist or that have been
; guard verified.  So if we cache lambdas that FAIL our tests, we can't carry
; them forward!

; TODO: Because of the uncertainty regarding how mapping functions will
; actually be used, it might be worthwhile to implement a user-settable flag
; that specifies whether and how APPLY$-LAMBDA is cached.  Scenarios (a), (c),
; and (d) immediately come to mind as optimal depending on usage.
; whether we (a) do nothing and just interpret LAMBDA
; applications, (c) use fast-alists (but possibly take advantage of their
; flexibility and simplicity to support multiple worlds or extensions of a
; cached world, which we don't do in the experiments described below), and (d)
; the limited but fast home-grown cache here, which is best for standing in one
; world and executing mapping expressions over massive ranges.

; TODO: It should also be noted that if our goal is fast execution of iterative
; primitives, further work might be done along the lines of macro expanding
; (SUM lst '(LAMBDA (X) good-body)) under the hood in raw Lisp to (LOOP FOR X
; IN lst SUM good-body).  For what it is worth the time required to execute the
; LOOP version of our (sum *million* lambda) test is 10 times faster than
; Scenario (d).

; TODO: If a LAMBDA could carry an explicit (declare (xargs :guard ...)) we
; could think about extending guard verification to specially handle mapping
; functions.  For example, if in a DEFUN guarded by (p lst) we encountered:

; (sum lst
;      '(lambda (x)
;         (declare (xargs :guard (integerp x)))
;         (sq x)))

; governed by (q lst), could generate the proof obligation

; (implies (and (p lst) (q lst) (member x lst)) (integerp x))
;                               ^^^^^^^^^^^^^^
; or

; (implies (and (p lst) (q lst)) (all lst '(lambda (x) (integerp x))))
;                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

; To generate the first, ACL2 would have to know how to apply a
; ``pick-a-point'' strategy to given user-defined mapping function, i.e., to
; associate ``member'' with the user-defined mapping function ``sum'' as in the
; first formula shown above, or to associate ``all'' with ``sum'' as in the
; second.  And we'd need some way to validate these associations to guarantee
; that the proof obligation really does imply that the lambda is always applied
; to legal input.  Remember, ``mapping functions'' don't necessarily map over
; lists, e.g., one might define (map-from-to i j step fn) that iterates i
; upwards by step until it exceeds j and applies fn to each i generated...  So
; the issue really is how do we compute or characterize the set of objects to
; which a mapping function might apply its functional argument?

; Recognizing Tame, Compliant, Unrestricted Lambdas

; Because we don't compile every lambda, it's important that we warn the
; user when we encounter an uncompilable lambda.

(defun slow-apply$-warning (fn reason state)

; This function interprets the reasons (given by
; tame-compliant-unrestricted-lambdap, below) that fn is not suitable.  See the
; next function.  This message is controlled by a user-settable switch.

  (declare (xargs :mode :program))
  (let ((action (f-get-global 'slow-apply$-action state)))
    (if action
        (let* ((unknown-reason "it failed some test whose internal code is ~
                                ~x0.  Please report this code to the ~
                                implementors.")
               (msg (cond
                     ((symbolp reason)
                      (case reason
                        (:non-compliant-symbol
                         (msg "its guards have not been verified."))
                        (:ill-formed-lambda
                         (msg "it is an ill-formed LAMBDA expression.  A ~
                               well-formed LAMBDA must look like this (LAMBDA ~
                               (v1 ... vn) body) where the vi are distinct ~
                               variable symbols and body is a fully ~
                               translated term containing no free variables ~
                               other than the vi."))
                        (:non-term-lambda-body
                         (msg "its body is not fully translated."))
                        (:non-tamep-lambda-body
                         (msg "its body is not tame."))
                        (:free-vars-in-lambda-body
                         (msg "its body contains free variables other than ~
                               the LAMBDA formals."))
                        (:still-bad-lambda
                         (msg "it was previously rejected as bad."))
                        (otherwise
                         (msg unknown-reason reason))))
                     ((consp reason)
                      (cond
                       ((eq (car reason) :restricted-compliant-symbol)
                        (msg "it has a guard of ~X01 but only functions with ~
                              :guard T can be given fast handling."
                             (untranslate (cdr reason) t (w state))
                             nil))
                       ((eq (car reason) :non-compliant-lambda-subrs)
                        (msg "it calls ~&0 whose guards have not been verified."
                             (cdr reason)))
                       ((eq (car reason) :unproved-lambda-body-guard-conjectures)
                        (msg "we cannot trivially verify the guards of the ~
                              body.  The unproved guard obligation is ~X01.  ~
                              The ACL2 theorem prover may be able to prove ~
                              this formula, but we do not try very hard to ~
                              prove guards during the application of apply$.  ~
                              The most direct way to get fast execution would ~
                              be to introduce a new function symbol with ~
                              :guard T whose body is the body of this LAMBDA ~
                              and then use that new symbol instead of the ~
                              LAMBDA expression.  Sorry."
                             (prettyify-clause-set (cdr reason)
                                                   nil
                                                   (w state))
                             nil))
                       (t (msg unknown-reason reason))))
                     (t (msg unknown-reason reason)))))
          (pprogn
           (fms "~%~%**********************************************************~%~
                 Slow Apply$ of ~x0 because ~@1  To inhibit this warning ~x2.~%~
                 **********************************************************~%~%"
                     (list (cons #\0 fn)
                           (cons #\1 msg)
                           (cons #\2 '(assign slow-apply$-action nil)))
                     (f-get-global 'proofs-co state)
                     state
                     nil)
           (value nil)))
        (value nil))))

(defun tame-compliant-unrestricted-lambdap (fn bad-lambdas ens wrld state)

; Fn is expected to be a lambda expression (but we check in any case).  We
; check that fn is definitely tame, guard verified and that the guard is T.
; Bad-lambdas is the list of LAMBDAs previously rejected in this same
; wrld.

; To check that a lambda body is compliant and unrestricted we
; first confirm that all the funtions used in it are compliant and
; then we generate the guard obligations of the body and throw out
; the ones provable by the Tau System.  The resulting set must be empty
; for us to consider the LAMBDA compliant and unrestricted.

  (declare (ftype (function (t t) (values t))
                  executable-tamep))
  (cond
   ((member-equal fn bad-lambdas)

; See The CL-Cache Implementation Details for a discussion of the uses of
; equal (member-equal) and eq (member-eq) here.

    (er-progn (if (member-eq fn bad-lambdas)
                  (value nil)
                  (slow-apply$-warning fn :still-bad-lambda state))
              (value nil)))
   ((not (and (consp fn)
              (eq (car fn) 'LAMBDA)
              (consp (cdr fn))
              (consp (cddr fn))
              (null (cdddr fn))
              (arglistp (lambda-formals fn))))
    (er-progn (slow-apply$-warning fn :ill-formed-lambda state)
              (value nil)))
   ((not (termp (lambda-body fn) wrld))
    (er-progn (slow-apply$-warning fn :non-term-lambda-body state)
              (value nil)))
   ((not (executable-tamep (lambda-body fn) wrld))
    (er-progn (slow-apply$-warning fn :non-tamep-lambda-body state)
              (value nil)))
   ((not (subsetp-eq (all-vars (lambda-body fn)) (lambda-formals fn)))
    (er-progn (slow-apply$-warning fn :free-vars-in-lambda-body state)
              (value nil)))
   (t
    (let ((non-compliant-fns (collect-non-common-lisp-compliants
                              (all-fnnames-exec (lambda-body fn))
                              wrld)))
      (cond
       (non-compliant-fns
        (er-progn
         (slow-apply$-warning fn
                              (cons :non-compliant-lambda-subrs
                                    non-compliant-fns)
                              state)
         (value nil)))
       (t (mv-let (cl-set ttree)
            (guard-obligation-clauses (cons :term (lambda-body fn))
                                      nil ens wrld state)
            (mv-let (cl-set1 ttree calist)
              (tau-clausep-lst cl-set ens wrld nil ttree state nil)
              (declare (ignore ttree calist))
              (cond
               (cl-set1
                (er-progn
                 (slow-apply$-warning
                  fn
                  (cons :unproved-lambda-body-guard-conjectures
                        cl-set)
                  state)
                 (value nil)))
               (t (value t)))))))))))

; With this check in hand, we can now implement the cl-cache.

; The CL-Cache Implementation Details

; The cl-cache stores the 3 most recent LAMBDA-expressions applied in the
; current ACL2 world.  When the world changes the cache is effectively cleared
; because we no longer know that the compiled definitions are current.  The
; cache also stores -- in a separate list -- any LAMBDA-expression encountered
; in the current world for which we have already detected non-compliance.  When
; one of those is encountered we just silently EV$.

; Each of the 3 cache lines is a nil or cons consisting of an input and an
; output, where input is a lambda expression and output is the corresponding
; compiled code object wrt the current world.  The input of a non-nil cache
; line is always a tame compliant unrestricted ACL2 LAMBDA-expression and the
; output is its compiled-function counterpart.  When we look for a
; LAMBDA-expression in the cache, we compare with EQUAL.  We actually use EQ
; occasionally for elimination of redundancy in error messages.

; We expect the common situation is that a mapping function repeatedly applies
; the very same (EQ) function over and over.  But if the user types (or yanks
; back down) a LAMBDA-expression, it will not be EQ, just EQUAL.  So we choose
; EQUAL to catch those re-typed LAMBDAs.  (Of course, EQUALs that are EQ are
; quickly checked.)  If a LAMBDA-expression is EQUAL to a cache line, we know
; it's legal in the current world and we already have its compiled code.  If it
; is EQUAL in the bad LAMBDAs list we know we don't have to check again that it
; is tame, compliant, guard verified, etc., because we know it fails.  If it is
; EQ to a bad LAMBDA we additionally know that it has already been reported
; verbosely and we can just report that it is slow (still) and not explain why.

; Lines are kept in access order, most recent first, and stored in the special
; variables *cl-cache-1*, *cl-cache-2*, and *cl-cache-3*.  The first line in
; the sequence that is nil indicates that subsequent lines are irrelevant.

; The non-compliant LAMBDAs are stored in the list *cl-cache-bad-lambdas*.

; The cache is protected by *cl-cache-world* which holds the world that was
; current when the compiler was called.  Every time the world changes, the
; cache is effectively cleared.

; We handle the possibility of interrupts rendering the cache inconsistent.
; Here is how: Before we inspect or modify the cache we enter a
; without-cache-interrupts environment.  This is actually a misnomer.
; Interrupts can happen but they won't leave us exposed.  Instead, the
; environment just renders the cache :invalid by setting the *cl-cache-world*
; to :invalid.  We detect that condition the next time we access the cache and
; wipe it out.

; Specifically, imagine that a cache manipulation is interrupted and aborted by
; ctrl-c or an error.  The cache is left invalid by means of the
; *cl-cache-world* being :invalid.  The next time we attempt to manipulate the
; cache we will first enter the without-cache-interrupts environment.  Upon
; finding it already :invalid, we clear the lines and save the then-current
; world into the temporary location used to restore the *cl-cache-world* upon
; exit.  So if the coming cache manipulation is interrupted, none of its
; results will be available.  If we exit the without-cache-interrupts normally,
; the *cl-cache-world* is restored from that temporary location.

; Note that this implementation does not allow nested without-cache-interrupts.
; The second entry will set the saved world to :invalid and then we're hosed.
; So this is fragile code and is meant to to protect the user against
; interrupts but not protect the system implementors against fuzzy thinking!

(defvar *cl-cache-world* nil)
(defvar *cl-cache-saved-world* nil)
(defvar *cl-cache-1* nil)
(defvar *cl-cache-2* nil)
(defvar *cl-cache-3* nil)
(defvar *cl-cache-bad-lambdas* nil)

(defmacro without-cache-interrupts (&rest args)

; (without-cache-interrupts form1 form2 ... formk) evaluates all the forms and
; returns the value of formk.  But it first resets the *cl-cache-world* to
; :invalid and restores it before exiting.

  `(prog2
       (cond
        ((eq *cl-cache-world* :invalid)
         (setq *cl-cache-1* nil)
         (setq *cl-cache-2* nil)
         (setq *cl-cache-3* nil)
         (setq *cl-cache-bad-lambdas* nil)
         (setq *cl-cache-saved-world* (w *the-live-state*)))
        (t (setq *cl-cache-saved-world* *cl-cache-world*)
           (setq *cl-cache-world* :invalid)))
       (progn ,@args)
       (setq *cl-cache-world* *cl-cache-saved-world*)))

(defun compile-tame-compliant-unrestricted-lambda (fn)
  (without-cache-interrupts

; Because we're in a without-cache-interrupts, we know the cache world is
; literally :invalid right now.  But the saved cache world holds the world for
; which the cache is valid.

   (cond
    ((eq *cl-cache-saved-world* (w *the-live-state*)) ; Cache is valid
     (cond
      ((null *cl-cache-1*)
       (cond
        ((null *cl-cache-bad-lambdas*)
         (er hard 'compile-tame-compliant-unrestricted-lambda
             "The cl-cache is in an inconsistent state:  the *cl-cache-world* ~
              was the current world (before we saved it in ~
              *cl-cache-saved-world* and invalidated *cl-cache-world* to ~
              handle interruptions).  So the cache is supposedly valid, which ~
              is supposed to imply that there is at least one *cl-cache-i* ~
              entry or *cl-cache-bad-lambda* entry, but the first cache line ~
              is empty and so is the bad lambdas list.  Please report this to ~
              the implementors and if you can reproduce it with a simple ~
              script we'd really appreciate it -- though we expect it's due ~
              to some unfortunately timed interrupt."))
        ((mv-let (erp val state)
           (tame-compliant-unrestricted-lambdap
            fn
            *cl-cache-bad-lambdas*
            (ens *the-live-state*)
            (w *the-live-state*)
            *the-live-state*)
           (declare (ignore erp state))
           val)
         (setq *cl-cache-2* nil)

; Note: According to the CLTL HyperSpec, (compile nil fn) returns the
; compiled-function corresponding to the function fn, which may be either a
; function or a lambda expression.  We know fn is a well-formed LAMBDA when we
; get here.  The nil in the call of compile below indicates that compile should
; return the compiled object; (a non-nil first argument would indicate that
; compile is to set that symbol's function cell to the compiled object and
; return the symbol.)

         (setq *cl-cache-1* (cons fn (compile nil fn)))
         (cdr *cl-cache-1*))
        (t (setq *cl-cache-bad-lambdas* (add-to-set-eq fn *cl-cache-bad-lambdas*))
           nil)))
      ((equal (car *cl-cache-1*) fn)
       (cdr *cl-cache-1*))
      ((null *cl-cache-2*)
       (cond
        ((mv-let (erp val state)
           (tame-compliant-unrestricted-lambdap
            fn
            *cl-cache-bad-lambdas*
            (ens *the-live-state*)
            (w *the-live-state*)
            *the-live-state*)
           (declare (ignore erp state))
           val)
         (setq *cl-cache-3* nil)
         (setq *cl-cache-2* *cl-cache-1*)
         (setq *cl-cache-1* (cons fn (compile nil fn)))
         (cdr *cl-cache-1*))
        (t (setq *cl-cache-bad-lambdas* (add-to-set-eq fn *cl-cache-bad-lambdas*))
           nil)))
      ((equal (car *cl-cache-2*) fn)

; Swap lines 1 and 2 because 2 is more recent.  Leave line 3 untouched.  It
; doesn't matter if line 3 is filled or not.

       (let ((temp *cl-cache-2*))
         (setq *cl-cache-2* *cl-cache-1*)
         (setq *cl-cache-1* temp))
       (cdr *cl-cache-1*))
      ((and *cl-cache-3*
            (equal (car *cl-cache-3*) fn))
       (let ((temp *cl-cache-3*))
         (setq *cl-cache-3* *cl-cache-2*)
         (setq *cl-cache-2* *cl-cache-1*)
         (setq *cl-cache-1* temp))
       (cdr *cl-cache-1*))

; The cache is full and fn is not in it.  If fn is suitably compliant, we put
; it in at line 1, moving the other two down, and pushing line 3 out.  Note
; that line 3 may be nil here, but that doesn't matter.

      ((mv-let (erp val state)
         (tame-compliant-unrestricted-lambdap
          fn
          *cl-cache-bad-lambdas*
          (ens *the-live-state*)
          (w *the-live-state*)
          *the-live-state*)
         (declare (ignore erp state))
         val)
       (setq *cl-cache-3* *cl-cache-2*)
       (setq *cl-cache-2* *cl-cache-1*)
       (setq *cl-cache-1*
             (cons fn (compile nil fn)))
       (cdr *cl-cache-1*))
      (t (setq *cl-cache-bad-lambdas* (add-to-set-eq fn *cl-cache-bad-lambdas*))
         nil)))
    (t

; Since the cache is invalid for the current world, we ignore its contents.  We
; fill line 1 if fn is suitably compliant.  We set line 2 to nil just to
; ensure the invariant.  We reset the bad lambdas list because in this new
; world they may be ok.  We reset the saved world to the current world so that
; when we pop out of the without-cache-interrupts the cache world is the
; current one.

     (cond
      ((mv-let (erp val state)
         (tame-compliant-unrestricted-lambdap
          fn
          nil ; known bad lambdas in this new wrld
          (ens *the-live-state*)
          (w *the-live-state*)
          *the-live-state*)
         (declare (ignore erp state))
         val)
       (setq *cl-cache-saved-world* (w *the-live-state*))
       (setq *cl-cache-bad-lambdas* nil)
       (setq *cl-cache-2* nil)
       (setq *cl-cache-1*
             (cons fn (compile nil fn)))
       (cdr *cl-cache-1*))
      (t

; Since this is a new world, we ignore the old value of *cl-cache-bad-lambdas*
; and restart it with just this fn in it.

         (setq *cl-cache-saved-world* (w *the-live-state*))
         (setq *cl-cache-bad-lambdas* (add-to-set-eq fn nil))
         nil))))))

; We define concrete-apply$-lambda with the intention that it will be used
; (under the hood) as the raw Lisp definition of apply$-lambda.  Apply$-lambda
; will be a guard-verified :logic mode function and so when supplied with
; constant arguments satisfying its guard, it will be invoked directly.  If the
; apply.lisp book were part of the sources we could provide a #-acl2-loop-only
; clause in the logical definition to do the work below.  We cannot provide an
; MBE solution: the raw Lisp involves a call to the compiler, which produces a
; non-ACL2 compiled code object.  But as long as the apply book is ``user
; written'' and not part of the sources, the only solution we can think of is
; to load the apply book and then go under the hood and redefine apply$-lambda
; to be concrete-apply$-lambda.

; We originally tried to do this with the ``defun-overrides'' approach used
; above for badge-userfn and apply$-userfn.  In that approach, we would
; defattach concrete-apply$-lambda to apply$-lambda after loading the apply
; book.  But that's impossible because apply$-lambda is a defun'd, not
; constrained, function.

(defun concrete-apply$-lambda (fn args)

; This function must be equal to APPLY$-LAMBDA when the fn is a consp and args
; is a true-list.  But it must also implement the feature that it allows
; top-level evaluation.  So, if we are in an environment where attachments are
; allowed and we're in ACL2(a), we get the compiled code for the LAMBDA (if
; it's equivalent to the slower way) and just apply that code.  Otherwise, we
; just do what apply$-lambda itself would do: call ev$ on the body.  Since this
; function is only called when the raw Lisp version of apply$-lambda is called,
; we know that the guard of apply$-lambda is satisfied, i.e., (consp fn) and
; (true-listp args).  But we don't know anything else and so have to use the
; same ec-calls we see in the comparable branch of apply$-lambda.

  (declare (ftype (function (t t) (values t))
                  ev$))
  (if (and *aokp*
           *allow-concrete-execution-of-apply-stubs*)
      (let ((compiled-version ; see the Essay on the Compiled-LAMBDA Cache
             (compile-tame-compliant-unrestricted-lambda fn)))
        (cond
         ((null compiled-version)
          (EV$ (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
               (ec-call
                (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                          args))))
         (t

; We know that fn is a well-formed, tame, compliant, unrestricted (:guard t)
; LAMBDA expression and compiled-version is its compiled code.  We can run it!

          (let ((arity (length (cadr fn))))
            (apply compiled-version
                   (if (= arity
                          (length args))
                       args
                       (take arity args)))))))
      (EV$ (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
           (ec-call
            (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                      args)))))

; The Rubric for Setting Up the Execution of APPLY$ includes the redefinition
; of the raw Lisp version of apply$-lambda:

; (defun apply$-lambda (fn args)
;   (concrete-apply$-lambda fn args))

; overriding the strictly logical defun of that function.

; Essay on the Performance of APPLY$

; In this experiment we will time runs of variations of

; (sum *million* '(lambda (x) (binary-+ '3 (binary-* '2 (fix x)))))

; where the LAMBDA expression is sometimes replaced by an ideal function symbol
; and sometimes by a Common Lisp compliant (with guard T) function symbol.

; Fire up this version of ACL2 and run The Rubric EXCEPT the redefinition of
; apply$-lambda!

;   (include-book "projects/apply/apply" :dir :system)
;   (defattach (badge-userfn concrete-badge-userfn)
;     :hints
;     (("Goal" :use concrete-badge-userfn-type)))
;   (defattach apply$-userfn concrete-apply$-userfn)
;   (value :q)
;   ; (defun apply$-lambda (fn args) (concrete-apply$-lambda fn args))
;   (setq *allow-concrete-execution-of-apply-stubs* t)
;   (lp)
;   (quote (end of rubric except apply$-lambda))

; Note as of this point in the experiment, we are able to run
; BADGE-USERFN and APPLY$-USERFN, but because we have not redefined
; APPLY$-LAMBDA we will be using *1* EV$ to interpret LAMBDA applications.

;   (progn
;
;   ; This is the ``old style'' way to do this computation. ;
;     (defun$ sum-3+2x (lst)
;       (declare (xargs :guard t))
;       (cond ((atom lst) 0)
;             (t (+ (+ 3 (* 2 (fix (car lst))))
;                   (sum-3+2x (cdr lst))))))
;
;   ; Here is the mapping function approach. ;
;     (defun$ sum (lst fn)
;       (cond ((endp lst) 0)
;             (t (+ (apply$ fn (list (car lst)))
;                   (sum (cdr lst) fn)))))
;
;     (defun$ test-fn-0 (x)        ; an ideal function ;
;       (+ 3 (* 2 (fix x))))
;
;     (defun$ test-fn-1 (x)        ; a Common Lisp compliant (guard t) function ;
;       (declare (xargs :guard t))
;       (+ 3 (* 2 (fix x))))
;
;     (defconst *test-bad-lambda*      ; a LAMBDA with a non-trivial guard ;
;       '(lambda (x)
;          (binary-+ '3 (binary-* '2 x))))
;
;     (defconst *test-good-lambda*      ; the unrestricted LAMBDA expression ;
;       '(lambda (x)
;          (binary-+ '3 (binary-* '2 (fix x)))))
;
;     (defun nats (n)
;       (if (zp n) nil (cons n (nats (- n 1)))))
;
;     (defconst *million* (nats 1000000))
;     )

; Unless otherwise indicated, each of the time$ forms below is executed three
; times in succession.  We record all three time measurements but only one byte
; count because the byte counts are always the same.

; Test 1. old-fashioned way:

;   (time$ (sum-3+2x *million*))

; 0.02 seconds realtime, 0.02 seconds runtime
; 0.01 seconds realtime, 0.01 seconds runtime
; 0.02 seconds realtime, 0.02 seconds runtime
; (16 bytes allocated).

; Test 2. ideal function symbol (not guard verified):

;   (time$ (sum *million* 'test-fn-0))

; 0.47 seconds realtime, 0.47 seconds runtime
; 0.49 seconds realtime, 0.49 seconds runtime
; 0.47 seconds realtime, 0.47 seconds runtime
; (16,000,032 bytes allocated).

; Test 3.  compliant function symbol (guard verified, guard T):

;   (time$ (sum *million* 'test-fn-1))

; 0.40 seconds realtime, 0.40 seconds runtime
; 0.40 seconds realtime, 0.40 seconds runtime
; 0.40 seconds realtime, 0.40 seconds runtime
; (16,000,032 bytes allocated).

; Test 4. Interpreted ``Bad'' LAMBDA (non-trivial guard obligation):
; This case will be handled specially by our APPLY$-LAMBDA support, once we
; install it!

;   (time$ (sum *million* *test-bad-lambda*))

; 1.49 seconds realtime, 1.49 seconds runtime
; 1.49 seconds realtime, 1.49 seconds runtime
; 1.49 seconds realtime, 1.49 seconds runtime
; (128,000,032 bytes allocated).

; Test 5. Interpreted Good LAMBDA (with FIX):
; This case will be handled specially by our APPLY$-LAMBDA support, once we
; install it!

;   (time$ (sum *million* *test-good-lambda*))

; 6.54 seconds realtime, 6.54 seconds runtime
; 6.51 seconds realtime, 6.51 seconds runtime
; 6.53 seconds realtime, 6.53 seconds runtime
; (144,000,032 bytes allocated).

; It may be counterintuitive that Test 4 is faster than Test 5.  But while
; the lambda in Test 4 has a non-trivial guard, it is always true.  Meanwhile,
; the lambda in Test 5 has a trivial guard but one extra FIX in it.  And after
; we evaluate that FIX, we still have to check all the guards that we checked in
; Test 4.  So of course Test 5 is more expensive:  the lambda is bigger and we
; interpret both of them.

; What is genuinely surprising is suprising how MUCH longer it takes!  But note
; that Test 5 cost 16 million more bytes than Test 4.  That's 16 bytes per call
; of apply$, all because of that extra FIX.

; Test 6.  Let's add another level of FIX:
; The point of this experiment is to see if it takes still longer.

;   (time$ (sum *million* '(lambda (x) (binary-+ '3 (binary-* '2 (fix (fix x)))))))

; 11.12 seconds realtime, 11.12 seconds runtime
; (160,000,032 bytes allocated).

; Note that we spent about 16 million more bytes because of that second FIX.
; So things are consistent and interpretation is pretty expensive.

; Now we install our apply$-lambda optimization.

;   (value :q)
;   (defun apply$-lambda (fn args) (concrete-apply$-lambda fn args))
;   (lp)

; Test 7. ``Bad'' LAMBDA with caching compiler:

;   (time$ (sum *million* *test-bad-lambda*))



; **********************************************************
; Slow Apply$ of (LAMBDA (X) (BINARY-+ '3 (BINARY-* '2 X))) because we
; cannot trivially verify the guards of the body.  The unproved guard
; obligation is (ACL2-NUMBERP X).  The ACL2 theorem prover may be able
; to prove this formula, but we do not try very hard to prove guards
; during the application of apply$.  The most direct way to get fast
; execution would be to introduce a new function symbol with :guard T
; whose body is the body of this LAMBDA and then use that new symbol
; instead of the LAMBDA expression.  Sorry.  To inhibit this warning
; (ASSIGN SLOW-APPLY$-ACTION NIL).
; **********************************************************

; 1.62 seconds realtime, 1.62 seconds runtime
; (128,109,008 bytes allocated).

; If we repeat that same test again, the lambda will be found on the bad
; lambdas list and we avoid our check...

; Test 8. Repeat of ``Bad'' LAMBDA with caching compiler:

;   (time$ (sum *million* *test-bad-lambda*))

; 1.62 seconds realtime, 1.62 seconds runtime
; (128,000,032 bytes allocated).

; Note that it's only a tiny bit faster even though the answer (``yes, the
; lambda is bad'') is already cached.  But it was cached after the first
; apply$-lambda call in Test 7 above!  So the last 999,999 calls in Test 7 were
; actually handled at the same speed as all one million calls here in Test 8.

; Test 9. ``Good'' LAMBDA with caching compiler:
; The first of the one million apply$-lambdas will run the test to confirm that
; the lambda is tame, compliant, and unrestricted, then it will compile the
; lambda and cache the result.  The next 999,999 apply$-lambdas will just find
; the compiled code in the cache and avoid both the test and the compiler.

;   (time$ (sum *million* *test-good-lambda*))

; 0.12 seconds realtime, 0.12 seconds runtime
; (16,021,408 bytes allocated).

; Test 10. Repeat of ``Good'' LAMBDA with caching compiler:
; If we run the same thing again, all 1,000,000 apply-lambdas will avoid the
; test and find the compiled code in the cache.


;   (time$ (sum *million* *test-good-lambda*))

; 0.12 seconds realtime, 0.12 seconds runtime
; (16,000,032 bytes allocated).

; Note that the time is the same but it cost about 21K fewer conses.

; We considered whether a fast-alist would be comparable to our special-purpose
; 3-line cache.  We can implement that as follows:

; This is a quick and dirty test of fast-alists.  If fast-alists seem
; attractive after this we would have to slow down this implementation a little
; by avoiding cache inconsistency caused by interrupts.  But fast-alists offer
; more flexibility and we could add features such as: having an unlimited
; number of cache lines (instead of just three) and maybe supporting multiple
; worlds or at least extensions of previously cached worlds.

; But this is all speculation until we find out if the fastest fast-alist
; implementation comes close to the current implementation.

; Note: The following screws up the 3-line cache invariants and implementation.
; So don't proceed unless you're finished experimenting with that
; implementation!

;   (value :q)
;   (setq *cl-cache-world* nil)
;   (setq *cl-cache-bad-lambdas* nil)
;   (defvar *cl-cache-fast-alist* nil)
;
;   (defun compile-tame-compliant-unrestricted-lambda (fn)
;
;   ; *cl-cache-fast-alist* is a fast alist mapping some lambda expressions to
;   ; their compiled counterparts.  It is accessed only if (w *the-live-state*)
;   ; is eq to *cl-cache-world*.  We add a new <fn, compiled-code> pair to the
;   ; fast alist whenever fn is a tame, compliant, unrestricted lambda.
;   ; Otherwise we add fn to the bad lambdas list.  If the world is not the one
;   ; the fast-alist is expecting, we set the alist to nil and start over.  No
;   ; provision is taken here for interrupts or extensions of the world.
;
;   ; In this quick and dirty trial, the bad-lambdas are kept in an ordinary
;   ; list as before.  But that won't matter because the list will be nil in
;   ; all our tests; all our lambdas will be good.
;
;     (cond
;      ((eq *cl-cache-world* (w *the-live-state*))
;       (let* ((hfn (hons-copy fn))
;              (cfn (hons-get hfn *cl-cache-fast-alist*)))
;         (cond
;          (cfn (cdr cfn))
;          ((mv-let (erp val state)
;             (tame-compliant-unrestricted-lambdap
;              hfn
;              *cl-cache-bad-lambdas*
;              (ens *the-live-state*)
;              (w *the-live-state*)
;              *the-live-state*)
;             (declare (ignore erp state))
;             val)
;           (let ((ans (compile nil fn)))
;             (setq *cl-cache-fast-alist*
;                   (hons-acons hfn ans
;                               *cl-cache-fast-alist*))
;             ans))
;          (t (setq *cl-cache-bad-lambdas* (cons hfn *cl-cache-bad-lambdas*))
;             nil))))
;      (t (setq *cl-cache-fast-alist* nil)
;         (setq *cl-cache-bad-lambdas* nil)
;         (setq *cl-cache-world* (w *the-live-state*))
;         (compile-tame-compliant-unrestricted-lambda fn))))
;
;   (lp)

; Test 11. ``Good'' LAMBDA with quick and dirty fast-alist cache:

;   (time$ (sum *million* *test-good-lambda*))

; 0.19 seconds realtime, 0.18 seconds runtime
; 0.18 seconds realtime, 0.18 seconds runtime
; 0.18 seconds realtime, 0.18 seconds runtime
; (16,025,392 bytes allocated). ; first time
; (16,000,032 bytes allocated). ; subsequent

; Recall that Test 10 (the 3-line cache) took 0.12 seconds.  (/ 0.18 0.12) =
; 1.50.  So the quick and dirty fast-alist in Test 11 takes 50% longer than our
; 3-line cache in Test 10.

; Test 12.  No caching, but compiling when possible:

; One might wonder if the cache is doing us any good since the test and
; compilation are pretty fast.  If you redefine the function below and run the
; test you get the answer:

;   (value :q)
;   (defun compile-tame-compliant-unrestricted-lambda (fn)
;     (cond
;      ((mv-let (erp val state)
;         (tame-compliant-unrestricted-lambdap
;          fn
;          *cl-cache-bad-lambdas*
;          (ens *the-live-state*)
;          (w *the-live-state*)
;          *the-live-state*)
;         (declare (ignore erp state))
;         val)
;       (compile nil fn))
;      (t nil)))
;   (lp)

;   (time$ (sum *million* *test-good-lambda*))

; 318.78 seconds realtime, 318.59 seconds runtime
; (21,409,930,800 bytes allocated).

; So it's obvious that the check and cost of compiling is not worth it unless
; you cache the result.  If you're not caching the result, you might as well
; just interpret the lambda body, as was done in Test 5, where we did this same
; computation via interpretation in about 6.5 seconds.

; Test 13.  Raw LISP LOOPs are 10 times faster:

;   (value :q)

; Raw Lisp loop with FIXing:

;   (time$ (loop for x in *million* sum (+ 3 (* 2 (fix x)))))

; 0.01 seconds realtime, 0.00 seconds runtime
; 0.01 seconds realtime, 0.01 seconds runtime

; Raw Lisp LOOP without FIXing:

;   (time$ (loop for x in *million* sum (+ 3 (* 2 x))))

; 0.00 seconds realtime, 0.00 seconds runtime
; 0.01 seconds realtime, 0.01 seconds runtime

; We now return to the Executive Summary of our performance results above,
; the four scenarios we described had the following total times:

; (a) Do Nothing                 6.53   [see Test 5]
; (b) Compile but Don't Cache  318.78   [see Test 12]
; (c) Fast-Alist Cache           0.18   [see Test 11]
; (d) Home-Grown Cache           0.12   [see Test 9]

; Note that our (sum *million* *test-good-lambda*) test applies the same (EQ)
; LAMBDA a million times without there being any change in the world.  These
; tests focused on the ``good'' lambda variant.

; Thus, method (a) interprets the good body a million times, method (b)
; recognizes and compiles the good body a million times, methods (c) and (d)
; recognize and compile the good variant once and then find it in the cache
; 999,999 times.

; Both scenarios (c) and (d) pay the price of recognizing this particular good
; lambda and compiling it.  We can compute the price of that from
; Scenario (b), where it the good lambda is recognized and compiled a million
; times.  (/ 318.78 (expt 10.0 6)) = 0.00032 (approx).  (This ignores the
; cost of doing the ``real work'' of cdring down the list, applying the
; compiled lambda, and summing up the answer.  That is estimated below but is
; trivial compared to 321.93.)

; We can estimate the time it takes to do the real work by doing the following
; in raw Lisp:

;   (defvar *compiled-good-lambda* (compile nil *test-good-lambda*))
;   (defun lisp-sum (x)
;     (if (endp x)
;         0
;         (+ (apply *compiled-good-lambda* (list (car x))) (lisp-sum (cdr x)))))
;   (time (lisp-sum *million*))

; The result is 0.026175 seconds.  Scenarios (c) and (d) both pay this price.

; So the overhead that both Scenarios (c) and (d) pay is
; recognizing and compiling once:  0.00032
; real work:                       0.02258

; total overhead:                  0.0229

; If we subtract the total overhead from the times measured for Scenarios (c)
; and (d) we are left with the time to do all the cache lookups in each
; scenario.

; (c) Fast-Alist Cache: (- 0.18 0.0229) = 0.1571 seconds
; (d) Home-Grown Cahce: (- 0.12 0.0229) = 0.097 seconds

; So (/ 0.1571 0.097) = 1.61

; Thus, the Fast-Alist Cache is about 60% slower than the Home-Grown Cache in
; this test.

; It also interesting to note that just interpreting the good LAMBDA (the Do
; Nothing scenario (a)), which completely ignores issues of recognizing and
; compiling good ones, can be done a million times in 6.27 seconds, ignoring
; the trivial overhead.  That means this good lambda is interpreted by EV$ in
; about 0.00000627 seconds.  But the cost of recognizing it and compiling it is
; about 0.00032 seconds, about 51 times longer.  So we have to see the same
; good LAMBDA expression at least 51 times in the same world before either
; Scenario (c) or (d) pays off.

; Thus, this whole idea of compiling and caching is ``best'' only in the
; context of applications where the user is mapping over ``long'' (> 50) lists.
; In a simple map over a few dozen things the compiler and caching aren't going
; to pay off.

; This suggests that if we come to a trusted evaluation story we probably ought
; to invest in some kind of user-settable switch that determines how
; apply$-lambda is handled so the user can optimize the sort of computations
; being done.
