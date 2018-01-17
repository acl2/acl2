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
; This file supports top-level execution of apply$ by implementing the crucial
; executable functions attached to badge-userfn and apply$-userfn.  We proceed
; in four main steps:

; * define concrete-badge-userfn, which will be attached to badge-userfn

; * define concrete-apply$-userfn, which will be attached to apply$-userfn

; * optimize apply$-lambda with compilation and caching

; * Essay on Admitting a Model for Apply$ and the Functions that Use It, the
;   full version of the proof sketched in the paper ``Limited Second Order
;   Functionality in a First Order Setting''

; The two concrete- functions mentioned above are actually partially
; constrained in other-events.lisp; the definitions here are their raw Lisp
; implementations.  The model described in the paper (and justified in the
; essay here) is relevant because, in addition to making the warrants valid, it
; is executable and thus literally serves as our guide for implementing the
; attachments to badge-userfn and apply$-userfn.

; Historical Note: Prior to Version_8.0, apply$ was introduced in a user book
; and had no built-in support.  Therefore, it was impossible to execute it in
; general.  However, to facilitate experimentation, we ``secretly'' supported
; it and allowed the user to activate that support -- and render moot any
; soundness guarantees of ACL2! -- by executing ``The Rubric''.  That code
; changed ``ACL2'' into the possibly unsound ``ACL2(a)''.  Here is the (now
; obsolete) comment introducing The Rubric:

;  The Rubric

;  If you want to convert ACL2 into ACL2(a) evaluate each of the forms below
;  immediately after starting your ACL2 session.

;    (include-book "projects/apply/apply" :dir :system)
;    (defattach
;      (badge-userfn concrete-badge-userfn)
;      (apply$-userfn concrete-apply$-userfn)
;      :hints
;      (("Goal" :use (concrete-badge-userfn-type
;                     concrete-apply$-userfn-takes-arity-args))))
;    (value :q)
;    (defun apply$-lambda (fn args) (concrete-apply$-lambda fn args))
;    (setq *allow-concrete-execution-of-apply-stubs* t)
;    (lp)
;    (quote (end of rubric))

;  Because The Rubric requires you execute a form in raw Lisp, The Rubric
;  eliminates the soundness guarantees provided by the ACL2 implementors!

; End of Historical Note

; -----------------------------------------------------------------

; In the days when The Rubric was necessary, the raw lisp variable
; *allow-concrete-execution-of-apply-stubs* told us whether it had been
; executed.  We now just set that variable to t.  We could have eliminated it
; entirely, but left references to that variable in our code to mark places
; where we're providing explicit support for execution of apply$.

(defvar *allow-concrete-execution-of-apply-stubs*
  t)

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

; It is important that if this function returns (mv nil badge) for a world then
; it returns that same answer for all extensions of the world!  The guard on
; the badge table, badge-table-guard, guarantees this invariant.

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
           (get-badge fn wrld)))
      (cond
       ((null bdg) ; fn is a function symbol with no badge assigned
        (cond ((null msgp) (mv t nil))
              (t (mv (msg "~x0 has not been warranted" fn)
                     nil))))
       (t (mv nil bdg)))))))

; The (extensible) attachments for badge-userfn and apply$-userfn are
; concrete-badge-userfn and concrete-apply$-userfn.  They will be attached to
; badge-userfn and apply$-userfn to extend the evaluation theory appropriately.
; See the defattach event at the end of apply.lisp.  We define the two
; concrete- functions below.

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

; Recall the Note on Strengthening the Constraint in badge-userfn-type found in
; apply-constraints.lisp.  There we discussed a bootstrapping problem arising
; from adding the additional constraint that badge-userfn returns nil on
; primitives and boot functions.  That strengthened constraint would have to be
; implemented here too, perhaps with code like the following.

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
; function....''  Once upon a time we signaled the errors by calling
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

; In ACL2, prior to the integration of apply$, we could include the distributed
; apply.lisp book and introduce these two functions:

; (defun$ sq (x) (* x x))
; (defun$ foo (fn1 fn2 x)
;   (cons (apply$ fn1 (list x))
;         (apply$ fn2 (list x))))

; Then trying to evaluate (foo 'sq 'cube 3) would cause the error:

; ACL2 Error in TOP-LEVEL: ACL2 cannot ev the call of undefined function
; APPLY$-USERFN on argument list: (SQ (5))

; because we can't apply$ 'SQ.

; But if we repeat that experiment today, we get a different error:

; ACL2 Error in TOP-LEVEL: The value of APPLY$-USERFN is not specified on CUBE
; because CUBE is not a known function symbol.

; We got past the (apply$ 'SQ ...) but now failed on (apply$ 'CUBE ...).

; So we can't expect unchanged erroneous behavior because the computation paths
; are just different in the two scenarios.

; End of Essay on A Misguided Desire...

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
   (t (mv-let (failure-msg bdg)
        (query-badge-userfn-structure t fn (w *the-live-state*))
        (cond
         ((or failure-msg        ; there is no badge for fn
              (null (cadr bdg))) ; fn is not warranted
          (let* ((failure-msg
                  (if failure-msg
                      failure-msg
; Error {[8.5]}
                      (msg "~x0 returns multiple values, so it has a badge ~
                            but no warrant"
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

; What we've described so far is adequate to run APPLY$ and EV$ forms in the
; evaluation theory after attaching the concrete- ``doppelgangers'' of
; badge-userfn and apply$-userfn for the current world to those critical
; functions.

; Now we turn to the optimization of APPLY$-LAMBDA.  The following is provable:

; (equal (apply$-lambda fn args)
;        (ev$ (lambda-body fn)
;             (pairlis$ (lambda-formals fn)
;                       args)))

; Indeed, it is apply$-lambda-opener in books/projects/apply/apply-lemmas.lisp.

; But we wish to apply certain lambdas more efficiently in the evaluation
; theory.

; You can skip all this and just read how apply$-lambda works by looking at the
; definition of apply$-lambda in this file.  There you will notice code that
; sometimes short-cuts the logic code below it (and in the definition of
; apply$-lambda in apply.lisp) by invoking raw lisp code produced by
; compile-tame-compliant-unrestricted-lambda.  That function is explained and
; then defined below.

; A rough sketch of what we do is provide raw lisp code in APPLY$-LAMBDA to
; check that the LAMBDA has a variety of important properties, including that
; the lambda is a well-formed, fully translated, closed, ACL2 lambda expression
; whose body is guard verified as though the input guard on the lambda were
; :guard T.  If it has these properties we compile it and apply that compiled
; function object with CLTL's apply instead of interpreting its body with *1*
; EV$.

; The problem we face below is that LAMBDA objects are just quoted constants.
; Their bodies are not inspected at translate time nor affected by
; macroexpansion.  Indeed, we don't even know if a lambda-looking constant will
; be treated as a lambda expression until it reaches APPLY$-LAMBDA.  Before a
; lambda object can be compiled we have to know it is a well-formed ACL2 lambda
; expression, i.e., (LAMBDA formals body), where formals is a list of distinct
; variable symbols, body is an ACL2 term in logic mode, that there are no free
; variables in the body other than the formals, and that the body is tame.

; From apply-lemmas.lisp we have the theorem above saying that (apply$-lambda
; fn args) is unconditionally equal to the ev$ of the body under an alist
; created from the formals and args.  So if the lambda object in question does
; not satisfy the rules above, we can still ev$ it as per the theorem.

; Even if all those conditions are met, the compiled code can't be executed
; unless the LAMBDA is Common Lisp compliant -- a notion that is not currently
; implemented for LAMBDA expressions in ACL2, which does not support the
; specification of guards on lambda expressions.  Finally, even Common Lisp
; compliant LAMBDAs can't be executed in raw Lisp unless their guards are
; satisfied by the actuals, so we'd have to check guards on LAMBDAs on every
; apply$-lambda done by a mapping function.  We envision LAMBDAs being applied
; iteratively over large domains.  We don't want to check their guards on every
; element of the domain.

; To finesse these guard issues we insist that the LAMBDA be Common Lisp
; compliant when the input guard is T, making the determination of compliance
; of an application completely independent of the particular actuals to which
; the LAMBDA is applied, i.e., LAMBDAs passing our tests can be compiled and
; applied in raw Lisp to any ACL2 objects.

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
; to apply the resulting CLTL function object.  Our Version_8.0 code has only
; been benchmarked in CCL, prior to December 2017.

; Our decision to optimize only the application of unrestricted LAMBDAs, while
; somewhat dissatisfying, probably allows the user to efficiently use most
; mapping functions (if the user ensures that the LAMBDA expression is
; unrestricted).  This generally means typing LAMBDA expressions with
; ``fixers'' around each use of a formal in the body.

; We will cache this check for well-formed, translated, tame, compliant,
; unrestricted LAMBDAs, with their compiled versions, so that if we encounter
; this same LAMBDA again -- in the same logical world -- we get the compiled
; function object without having to re-check the properties or call the
; compiler.  The cache is called the ``compiled-LAMBDA cache'' or cl-cache.

; We implemented our own cache.  We considered four alternatives:

; (a) Do Nothing: Let ACL2 behave normally by running the *1* code for
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
; those experiments is: Our Fast-Alist cache has performed about 50% slower
; than our Home-Grown cache.  The Do Nothing and the Compile but Don't Cache
; approaches are much worse.  But many things affect performance.  Choosing the
; best implementation depends on the expected size of the LAMBDAs, whether
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
; ACL2 user.

; Two severe disadvantages of our original Home-Grown Cache are that it
; maintained only 3 cache lines (i.e., was capable of remembering only three
; compiled lambdas) and was cleared every time the world changes.
; The following historical note explained our thinking at the time.

;   The choice of a small, fixed number of cache lines makes the implementation
;   faster because each line is a separate raw Lisp variable, but at the
;   expense of more voluminous code as we check and fill or empty each line
;   with code that looks much like the code for the line before it.  But the
;   small, fixed number of lines was considered adequate for executing
;   ``typical'' mapping expressions, like (sum (collect ... '(lambda (x) ...))
;   '(lambda (y) ...)).  Both lambdas would be compiled and cached for the
;   duration of the evaluation.  We don't anticipate many interactively
;   submitted ground mapping expressions to involve more than 3 lambdas.  An
;   advantage of the Fast-Alist Cache is that it maintains an arbitrary number
;   of cache lines.  We are content at the moment to recompile such expressions
;   every time the world changes.

; Now, we use a structure that contains 1000 cache lines by default, but can be
; adjusted by the user to contain any number of cache lines that is at least 3.

; See the Essay on the Performance of APPLY$ for details of our original
; experiments and implementation of a quick-and-dirty Fast-Alist Cache.

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
; and (d) immediately come to mind as optimal depending on usage.  whether we
; (a) do nothing and just interpret LAMBDA applications, (c) use fast-alists
; (but possibly take advantage of their flexibility and simplicity to support
; multiple worlds or extensions of a cached world, which we don't do in the
; experiments described below), and (d) fast home-grown cache here, which is
; best for standing in one world and executing mapping expressions over massive
; ranges.

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

; Warning: We rely on the assumption that this function always returns nil.

; This function interprets the reasons (given by
; tame-compliant-unrestricted-lambdap, below) that fn is not suitable.  See the
; next function.  This message is controlled by a user-settable switch.

  (declare (xargs :mode :program))
  (if (f-get-global 'slow-apply$-action state)
      (let* ((unknown-reason "it failed some test whose internal code is ~x0. ~
                              ~ Please report this code to the implementors.")
             (msg (cond
                   ((symbolp reason)
                    (case reason
                      (:non-compliant-symbol
                       (msg "its guards have not been verified."))
                      (:ill-formed-lambda
                       (msg "it is an ill-formed LAMBDA expression.  A ~
                             well-formed LAMBDA must look like this (LAMBDA ~
                             (v1 ... vn) body) where the vi are distinct ~
                             variable symbols and body is a fully translated ~
                             term containing no free variables other than the ~
                             vi."))
                      (:non-term-lambda-body
                       (msg "its body is not fully translated."))
                      (:non-tamep-lambda-body
                       (msg "its body is not tame."))
                      (:free-vars-in-lambda-body
                       (msg "its body contains free variables other than the ~
                             LAMBDA formals."))
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
                            The ACL2 theorem prover may be able to prove this ~
                            formula, but we do not try very hard to prove ~
                            guards during the application of apply$.  The ~
                            most direct way to get fast execution would be to ~
                            introduce a new function symbol with :guard T ~
                            whose body is the body of this LAMBDA and then ~
                            use that new symbol instead of the LAMBDA ~
                            expression.  Sorry."
                           (prettyify-clause-set (cdr reason)
                                                 nil
                                                 (w state))
                           nil))
                     (t (msg unknown-reason reason))))
                   (t (msg unknown-reason reason)))))
        (cw "~%~%~
             **********************************************************~%~
             Slow Apply$ of ~x0 because ~@1  To inhibit this warning ~x2.~%~
             **********************************************************~%~%"
            fn
            msg
            '(assign slow-apply$-action nil)))
    nil))

(defun tame-compliant-unrestricted-lambdap (fn bad-lambdas
                                               &aux
                                               (ens (ens *the-live-state*))
                                               (wrld (w *the-live-state*))
                                               (state *the-live-state*))

; Fn is expected to be a lambda expression (but we check in any case).  We
; check that fn is definitely tame, guard verified and that the guard is T.
; Bad-lambdas is the list of LAMBDAs previously rejected in this same
; wrld.

; To check that a lambda body is compliant and unrestricted we
; first confirm that all the functions used in it are compliant and
; then we generate the guard obligations of the body and throw out
; the ones provable by the Tau System.  The resulting set must be empty
; for us to consider the LAMBDA compliant and unrestricted.

  (declare (ftype (function (t t) (values t))
                  executable-tamep))
  (cond
   ((member-equal fn bad-lambdas)

; See The CL-Cache Implementation Details for a discussion of the uses of
; equal (member-equal) and eq (member-eq) here.

    (if (member-eq fn bad-lambdas)
        nil
      (slow-apply$-warning fn :still-bad-lambda state)))
   ((not (and (consp fn)
              (eq (car fn) 'LAMBDA)
              (consp (cdr fn))
              (consp (cddr fn))
              (null (cdddr fn))
              (arglistp (lambda-formals fn))))
    (slow-apply$-warning fn :ill-formed-lambda state))
   ((not (termp (lambda-body fn) wrld))
    (slow-apply$-warning fn :non-term-lambda-body state))
   ((not (executable-tamep (lambda-body fn) wrld))
    (slow-apply$-warning fn :non-tamep-lambda-body state))
   ((not (subsetp-eq (all-vars (lambda-body fn)) (lambda-formals fn)))
    (slow-apply$-warning fn :free-vars-in-lambda-body state))
   (t
    (let ((non-compliant-fns (collect-non-common-lisp-compliants
                              (all-fnnames-exec (lambda-body fn))
                              wrld)))
      (cond
       (non-compliant-fns
        (slow-apply$-warning fn
                             (cons :non-compliant-lambda-subrs
                                   non-compliant-fns)
                             state))
       (t (mv-let (cl-set ttree)
            (guard-obligation-clauses (cons :term (lambda-body fn))
                                      nil ens wrld state)
            (mv-let (cl-set1 ttree calist)
              (tau-clausep-lst cl-set ens wrld nil ttree state nil)
              (declare (ignore ttree calist))
              (cond
               (cl-set1 (slow-apply$-warning
                         fn
                         (cons :unproved-lambda-body-guard-conjectures
                               cl-set)
                         state))
               (t t))))))))))

; With this check in hand, we can now implement the cl-cache.

; The CL-Cache Implementation Details

; The cl-cache stores (by default) the 1000 most recent LAMBDA-expressions
; applied in the current ACL2 world.  When the world changes the cache is
; effectively cleared because we no longer know that the compiled definitions
; are current.  The cache also stores -- in a separate list -- any
; LAMBDA-expression encountered in the current world for which we have already
; detected non-compliance.  When one of those is encountered we just silently
; EV$.

; Each of the cache lines is a nil or cons consisting of an input and an
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

; Lines are kept in access order, most recent first.  The first line in the
; sequence that is nil indicates that subsequent lines are irrelevant.  We
; actually arrange that all subsequent lines are also nil, but that is probably
; not important.

; The non-compliant LAMBDAs are stored in a list.  The cache is protected by a
; world holding the world that was current when the compiler was called.  Every
; time the world changes, the cache is effectively cleared.

; We handle the possibility of interrupts rendering the cache inconsistent.
; Here is how: Before we modify the cache we render the global cache invalid,
; restoring the global cache only when modification is complete.  See the use
; of prog1 in compile-tame-compliant-unrestricted-lambda.

; Specifically, imagine that a cache manipulation is interrupted and aborted by
; ctrl-c or an error.  The cache is left invalid.  The next time we attempt to
; manipulate the cache we will find it :invalid, in which case we build a new
; cache.

; For efficiency, we often destructively modify the cache.

; Here is our cache structure.  The value of our global cache variable
; (*cl-cache*, introduced further below) is either such a structure or else is
; an integer, at least 3, representing the intended size of such a structure.

(defrec cl-cache

; Warning: Keep this in sync with functions update-cl-cache-xxx, which (as of
; this writing) immediately follow this definition.

; Invariants on the fields include:

; - :World is an ACL2 logical world (indeed, it is the current ACL2 world after
;   this structure is read or written).

; - :Size is a positive integer.

; - :Alist is a circular list that repeats after :size elements; each of its
;   elements is a cons or nil; and for 0 <= i < j < size, if (nth i alist) =
;   nil then (nth j alist) = nil.

; - :Last is (nthcdr (1- size) alist).

; - :Bad-lambdas is a true-list.

; Note that :size and :last are constant fields for a given cl-cache.  However,
; the cdr of :last can change.

  ((world . alist) (size . last) . bad-lambdas)
  t)

(defun update-cl-cache-alist (cl-cache x)
  (setf (cdar cl-cache) x))

(defun update-cl-cache-last (cl-cache x)
  (setf (cdadr cl-cache) x))

(defun update-cl-cache-bad-lambdas (cl-cache x)
  (setf (cddr cl-cache) x))

(defparameter *cl-cache-size-default*

; We want to make this default large enough so that most users will never need
; to think about it.  However, we also want to make it small enough so that
; updates aren't slowed down too much when lookups need to walk linearly
; through a full cache and fail.  That probably won't happen often, so it seems
; like a minor consideration; hence we make the cache reasonably large by
; default.

; An experiment shows essentially the same timing results for
; books/system/tests/apply-timings.lisp when this value is 5 as when it is
; 1000.

  1000)

(defvar *cl-cache*

; Normally *cl-cache* is a cl-cache record.  However, it can be the intended
; :size of such a record, which indicates that *cl-cache* is uninitialized.

  *cl-cache-size-default*)

(defun cl-cache-init (size)

; We insist on a size that is at least 3.  Sizes of 1 and 2 might work, but we
; haven't carefully considered those cases.

; We considered making this function available to the user.  However, it seemed
; a bad idea to allow this to be run inside a book (via make-event) and thus
; affect the rest of the session.  Of course, if one knows about this function
; one can use a trust tag to invoke it in raw Lisp.

  (declare (type (integer 3 *) size))
  (progn$ (or 

; The following check is important since the type declaration won't necessarily
; be checked in safety 0.

           (and (integerp size)
                (<= 3 size))
           (er hard! 'set-cl-cache
               "Illegal argument (should be nil or integer not less than 3), ~
                ~x0, for cl-cache-init."
               size))
          (setq *cl-cache* size)
          t))

(defun make-circular-list (n)

; Return (mv L Last), L is a list, Last is (nthcdr (1- n) L), and (cdr Last) is
; L.  Thus, L can be viewed as a list containing n slots, such that
; conceptually, its last cons is L.

  (let* ((lst (make-list n))
         (last (last lst)))
    (setf (cdr last) lst)
    (mv lst last)))

(defun make-cl-cache (size)
  (mv-let (alist last)
    (make-circular-list size)
    (make cl-cache
          :world (w *the-live-state*)
          :alist alist
          :size size
          :last last
          :bad-lambdas nil)))

(defun cl-cache-size (cl-cache)

; Cl-cache can be a cl-cache record or the most recent size of a *cl-cache*
; record.

  (cond
   ((consp cl-cache)
    (access cl-cache cl-cache :size))
   (t (assert (natp cl-cache))
      cl-cache)))

(defun cl-cache-print ()

; This is just a debugging utility.

  (let ((cl-cache *cl-cache*))
    (cond ((consp cl-cache)
           (loop for i from 1 to (access cl-cache cl-cache :size)
                 as pair in (access cl-cache cl-cache :alist)
                 do (format t "~3d. ~s~&" i pair)))
          (t (format t
                     "Cl-cache is uninitialized with size ~s.~%"
                     *cl-cache*))))
  t)

(defun cl-cache-add-entry (cl-cache pair tail previous-tail)

; We assume that the :alist of cl-cache, truncated to its first :size elements
; (to account for its being a circular list), is as follows, where note that
; tail has at least two elements.

;            ((f1 . c1) (f2 . c2) ... (fk . ck) xxx yyy ...).
;                                     | previous-tail >>
;                                               | tail >>

; We want to add a new element (fn . c) to the front of the :alist and discard
; xxx.

;   ((fn . c) (f1 . c1) (f2 . c2) ... (fk . ck) yyy ...).

; This function does exactly that.  It is evaluated purely for that destructive
; update to cl-cache.

; A naive version of this algorithm creates a new cons, pushing (fn . c) to the
; front of the alist.  However, we reuse tail, which after all is a cons pair
; that would otherwise be garbage; that pair thus serves as the new alist.

  (let ((alist (access cl-cache cl-cache :alist)))
    (setf (cdr previous-tail) (cdr tail))
    (setf (car tail) pair)
    (setf (cdr tail) alist)
    (let ((new-alist tail)
          (last (access cl-cache cl-cache :last)))
      (update-cl-cache-alist cl-cache tail)
      (setf (cdr last) new-alist))
    t))

(defun compile-tame-compliant-unrestricted-lambda (fn)

; This function is used directly in the raw Lisp code for apply$-lambda.

  (let* ((cl-cache *cl-cache*)
         (state *the-live-state*)
         (wrld (w state)))
    (cond
     ((and (consp cl-cache)
           (eq (access cl-cache cl-cache :world)
               wrld)) ; Cache is valid
      (prog1
          (let* ((cl-alist (access cl-cache cl-cache :alist))
                 (bad-lambdas (access cl-cache cl-cache :bad-lambdas)))

; We make *cl-cache* invalid here, to be restored if we don't interrupt.

            (setq *cl-cache* (access cl-cache cl-cache :size))
            (assert (car cl-alist)) ; valid cl-cache has at least one entry
            (cond
             ((equal (caar cl-alist) fn)

; The cl-cache is valid and its first entry is also valid.  Simply return the
; compiled function.

              (cdar cl-alist))
             (t

; We search the cl-cache starting with the second element.  The variable, tail,
; is the tail of the :alist that starts with the ith element as we loop,
; beginning with i=2 and stopping one short of the size.  If we find an entry
; that is either nil or a hit, then we delete that entry destructively, and we
; push a suitable pair onto the front of the cache, using cl-cache-add-entry.
; If we don't get a hit, then with the "finally" clause we do something a bit
; special.

              (loop for i from 1 to (- (access cl-cache cl-cache :size) 2)
                    as tail on (cdr cl-alist)
                    as previous-tail on cl-alist

; The following code doesn't seem (after limited testing) to speed things up in
; general, so there doesn't seem to be much reason to add it.

;              when
;              (cond ((= i 1)
;                     (and (car tail) (equal (caar tail) fn)))
;                    ((= i 2)
;                     (and (cadr tail) (equal (cadar tail) fn))))
; ; optimization: just swap
;              do
;              (let ((pair1 (car cl-alist))
;                    (pair2 (nth i cl-alist)))
;                (setf (car cl-alist) pair2
;                      (nth i cl-alist) pair1)
;                (return (cdr pair2)))

                    when (or (null (car tail)) ; fn not found
                             (equal (caar tail) fn))
                    do (let ((pair (if (null (car tail))
                                       (and (tame-compliant-unrestricted-lambdap
                                             fn bad-lambdas)
                                            (cons fn (compile nil fn)))
                                     (car tail))))
                         (cond (pair (cl-cache-add-entry cl-cache
                                                         pair
                                                         tail
                                                         previous-tail)
                                     (return (cdr pair)))
                               (t (update-cl-cache-bad-lambdas
                                   cl-cache
                                   (add-to-set-eq fn bad-lambdas))
                                  (return nil))))
                    finally
                    (progn

; First advance to the last tail.

                      (setq tail (cdr tail)
                            previous-tail (cdr previous-tail))
                      (assert (eq tail (access cl-cache cl-cache :last)))
                      (let* ((found (equal (caar tail) fn))
                             (pair (cond (found (car tail))
                                         ((tame-compliant-unrestricted-lambdap
                                           fn bad-lambdas)
                                          (cons fn (compile nil fn))))))
                        (cond (pair
                               (when (not found)
                                 (setf (car tail) pair))
                               (update-cl-cache-alist cl-cache tail)
                               (update-cl-cache-last cl-cache previous-tail)
                               (return (cdr pair)))
                              (t (update-cl-cache-bad-lambdas
                                  cl-cache
                                  (add-to-set-eq fn bad-lambdas))
                                 (return nil)))))))))
        (setq *cl-cache* cl-cache)))
     (t (let* ((size (cl-cache-size cl-cache))
               (cl-cache *cl-cache*))

; Next we make *cl-cache* invalid, to be restored if we don't interrupt.

          (setq *cl-cache* size)
          (setq cl-cache
                (cond ((consp cl-cache)

; We reuse the structure of cl-cache, updating its fields appropriately with
; minimal consing.

                       (loop for i from 1 to size
                             as tail on (access cl-cache cl-cache :alist)
                             do
                             (setf (car tail) nil))
                       (change cl-cache cl-cache
                               :world wrld
                               :bad-lambdas nil))
                      (t (make-cl-cache size))))
          (prog1
              (cond
               ((tame-compliant-unrestricted-lambdap fn nil)
                (let ((c (compile nil fn))
                      (cl-alist (access cl-cache cl-cache :alist)))
                  (setf (car cl-alist)
                        (cons fn c))
                  c))
               (t (update-cl-cache-bad-lambdas
                   cl-cache
                   (list fn))
                  nil))
            (setq *cl-cache* cl-cache)))))))

; Historical Essay on the Performance of APPLY$

; Preamble to Essay

; This essay describes an experiment performed before apply$ was integrated
; into the sources.  It can no longer be performed as described!  We might do a
; similar experiment with the integrated handling of apply$ as we test other
; approaches to caching compiled lambdas.  But for the moment, we'll leave this
; comment in place merely as a historical note to justify the initial support
; for speeding up apply$-lambda.

; For this experiment we used a slightly different fast home-grown cache, which
; was limited to three cache lines.  Our current cache is a bit faster.
; Consider the following three tests defined in community book
; books/system/tests/apply-timings.lisp, each running 10 million iterations
; where in each iteration: the first applies a single lambda, the second
; applies two lambdas, and the third applies three lambdas.

;   (cw-apply-test *10M* 1)
;   (cw-apply-test *10M* 2)
;   (cw-apply-test *10M* 3)

; The respective results using our 3-line cache (the one used below, and using
; CCL) were measured at:

; 0.91 seconds realtime, 0.91 seconds runtime
; 2.99 seconds realtime, 3.00 seconds runtime
; 5.73 seconds realtime, 5.73 seconds runtime

; The respective results using our current cache (as of mid-January, 2018,
; using CCL) were measured at:

; 0.69 seconds realtime, 0.69 seconds runtime
; 2.58 seconds realtime, 2.59 seconds runtime
; 4.48 seconds realtime, 4.48 seconds runtime

; The timings suggest that it was worthwhile moving to the variable-lines cache
; from the three-line cache, but also that the historical results reported
; below would not be dramatically different using the variable-lines cache in
; place of the three-line cache that was used.

; Note by the way that if we reduce 1000 cache lines to 5 cache lines, the
; times are essentially unchanged.

; The Essay Proper

; In this experiment we will time runs of variations of

; (sum *million* '(lambda (x) (binary-+ '3 (binary-* '2 (fix x)))))

; where the LAMBDA expression is sometimes replaced by an ideal function symbol
; and sometimes by a Common Lisp compliant (with guard T) function symbol.

; Fire up this version of ACL2 and run The Rubric EXCEPT the redefinition of
; apply$-lambda!  [Remember:  these instructions cannot be followed any more!
; For example, we don't redefine apply$-lambda anymore, so you can't not
; redefine it!  But you can sort of guess what we mean just knowing that
; (concrete-apply$-lambda fn args) is raw Lisp for what you now see in the raw
; Lisp code of the defun apply$-lambda.]

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

; What is genuinely surprising is surprising how MUCH longer it takes!  But note
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
; implementation!  [Notes added January 2018: again, we no longer use a 3-line
; cache; and tame-compliant-unrestricted-lambdap now takes only two arguments.]

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
; (d) Home-Grown Cache: (- 0.12 0.0229) = 0.097 seconds

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

; End of  Historical Essay on the Performance of APPLY$
; =================================================================

; [The following essay is meant as supplementary material to the proof sketch
; in the paper ``Limited Second Order Functionality in a First Order Setting''.
; It does not necessarily describe the implemented version of apply$,
; def-warrant, badger, etc., in ACL2 Version_8.0 or later.  However, as always,
; we base our belief that ACL2 is sound on careful coding with attention to
; proofs like this.  When new features are added, we work out extensions of
; these proofs to explain those features, but we do not always re-write the
; entire proof.]

; Essay on Admitting a Model for Apply$ and the Functions that Use It

; Throughout the essay below we occasionally refer to books, e.g., apply.lisp.
; All such books are in community books directory books/projects/apply-model/.

; Goal:

; Our goal is to show that there is an evaluation theory that makes all
; warrants valid.  That evaluation theory is created by

; (DEFATTACH BADGE-USERFN BADGE-USERFN!)
; (DEFATTACH APPLY$-USERFN APPLY$-USERFN!)

; We call BADGE-USERFN! and APPLY$-USERFN! the ``doppelgangers'' of
; BADGE-USERFN and APPLY$-USERFN, respectively.  To carry out the attachments
; we must show that the two doppelgangers are guard verified, that the guards
; of BADGE-USERFN and APPLY$-USERFN imply those of their doppelgangers, and
; that the constraints on BADGE-USERFN and APPLY$-USERFN are satisfied by their
; doppelgangers.

; To define APPLY$-USERFN! we will define a doppelganger for every function
; with a badge except for the user-defined functions that are not ancestrally
; dependent on APPLY$.

; =================================================================
; Review:

; The signatures, guards, and constraints on badge-userfn and apply$-userfn
; are as follows:

; Function:        BADGE-USERFN
; Formals:         (FN)
; Signature:       (BADGE-USERFN *) => *
; Guard:           T
; Guards Verified: T
; Constraint:      (IMPLIES (BADGE-USERFN FN)
;                           (APPLY$-BADGEP (BADGE-USERFN FN)))
; Function:        APPLY$-USERFN
; Formals:         (FN ARGS)
; Signature:       (APPLY$-USERFN * *) => *
; Guard:           (TRUE-LISTP ARGS)
; Guards Verified: T
; Constraint:      T (none)

; We distinguish ``ACL2 lambda application'' from a ``LAMBDA application.''  An
; example of the former is ((lambda (x) (+ 1 (square x))) a) and an example of
; the latter is (apply$ '(LAMBDA (X) (BINARY-+ '1 (SQUARE X))) (list a)).  The
; apply$ above might also be an apply$!, as will be made clear in context.

; We generally use lower case names, like f and m, as meta-variables and
; uppercase when we are exhibiting concrete symbols and terms.  Mixed case
; ``terms'' are generally schemas.  For example, if f is understood to be TIMES
; then (F f) is (F TIMES).  Occasionally we exhibit concrete events in
; lowercase and use uppercase within it to highlight certain symbols, but we
; always alert the reader to this breach of our normal convention.

; Caveat: It's almost impossible to follow any meta-variable convention
; perfectly.  We apologize for sometimes unexplained choices of case that we
; thought had obvious importance and also for the unconscious clear violations
; of our own conventions.

; A function that returns multiple values can have a badge but will not have a
; warrant.

; Functions with badges are partitioned into primitives (e.g., CAR and
; BINARY-APPEND), boot functions (e.g., TAMEP and APPLY$), and user-defined
; (e.g., SQUARE and COLLECT).

; Non-primitive badged functions are partitioned into:
; G1 -- ancestrally independent of APPLY$, and
; G2 -- ancestrally dependent on APPLY$.
; Thus ``all non-primitive badged functions'' is the same set as ``all G1 and
; G2 functions.''

; G1 includes boot functions like TAMEP and user-defined functions like SQUARE
; that don't require APPLY$ in the chronology.

; G2 includes boot functions APPLY$, EV$, and EV$-LIST and user-defined
; functions like COLLECT that do require APPLY$ in the chronology.

; We often limit our attention to user-defined G1 and G2 functions as opposed
; to all G1 and G2 functions, thus removing from consideration the boot
; functions like TAMEP, APPLY$, and EV$.

; Every function in G1 is tame.  Some functions in G2 may be tame.  For
; example, (defun collect-squares (lst) (collect lst 'SQUARE)) is a tame G2
; function.

; We believe every tame expression is G1 definable in the sense that an
; equivalent expression could be written in terms of (possibly newly
; introduced) G1 functions.  See the discussion in
; acceptable-warranted-justificationp in apply.lisp.  However, we do not
; exploit that belief (or prove it) here.

; If a formal has ilk :FN or has ilk :EXPR we call it a :FN/:EXPR formal or say
; it has ilk :FN/:EXPR.  That's technically a misnomer: there is no :FN/:EXPR
; formal because there is no ``:FN/:EXPR'' ilk.  The ilks are NIL, :FN, and
; :EXPR.

; Some important facts about any user-defined badged function, f, with formals
; (x1 ... xn), and body, b, include the following.  Note that the first three
; bullet points apply to both G1 and G2 functions but the final ones are
; relevant only to G2 functions (because no G1 function can call a function
; with :FN/:EXPR ilks or else it would be dependent on APPLY$):

; - f's measure term is entirely in G1 functions.  In our model, this is
;   insured by the acceptable-warranted-justificationp called from badger in
;   apply.lisp: the measure is tame (all badged) and ancestrally independent of
;   APPLY$, i.e., G1.

; - f's measure is natural number valued and its well-founded relation is O<
;   over O-P.  We assume without loss of generality that the measure takes all
;   of the formals.

; - f is singly recursive, not in a mutually recursive clique.

; - in every recursive call of f in b, the actuals in :FN/:EXPR positions are
;   passed identically, i.e., if the ith formal, v_i, is of ilk :FN/:EXPR then
;   the ith actual of every recursive call is v_i.

; - in every call of a G2 function other than f in b, the actuals in :FN slots
;   are either formals of ilk :FN or else quoted tame functions and the
;   actuals in :EXPR slots are either formals of ilk :EXPR or else quoted
;   tame expressions.  Clarification for emphasis: The same :FN/:EXPR formal
;   may be used multiple times in different slots of the appropriate ilk.  If
;   the called G2 function, g, has two :FN slots and v_1 is a :FN formal of f,
;   then v_1 may be passed into both :FN slots of the call of g in f.  This is
;   not allowed in calls of f in f, where each formal must occupy its original
;   position.

; - every function symbol mentioned in every quoted tame object in a :FN/:EXPR
;   slot of b was warranted before f was warranted in the user's chronology.
;   Corollary: f is not used as a function symbol in any quoted tame object in
;   a :FN/:EXPR slot of its body.  Clarification 1: A function g may be defun'd
;   and not immediately assigned a warrant: no warrant is generated until
;   (def-warrant g) occurs.  But if g appears in, say, a quoted LAMBDA
;   expression in a :FN slot in the definition of f after g has been defun'd
;   but before g has been warranted, that LAMBDA expression would not be tame
;   and hence the function f would not have a badge.  Clarification 2: the
;   notion of the functions mentioned in a quoted object is the obvious
;   extension of the more familiar notion of function symbols in pseudoterms.
;   By virtue of the fact that f has a badge, we know these quoted objects are
;   appropriately tame and the tameness computation identifies which of the
;   symbols in the quoted object represent ``functions'' and checks that they
;   have the appropriate badges and thus that they have been defined.


; All of these facts (and others) are checked by (def-warrant f) which fails if
; any of the checks fail.

; We could loosen some of the restrictions.  The insistence that the measure be
; a natp is only relevant for G2 functions and even then could be loosened to
; bounded ordinal.  We'd have to change the proof here.  We could eliminate the
; restriction that measures be independent of APPLY$ if we were sure of the
; claim that every tame expression is G1 definable.  See the discussion in
; acceptable-warranted-justificationp.  We could allow mutual recursion if we
; generalized the badger to handle it; we'd have to allow it in our G2
; doppelganger construction.

; In the evaluation theory, all G1 functions will be defined exactly as in the
; user's history, except that we omit any mention of guards.

; All G2 functions will have doppelgangers.

; The name of the doppelganger for a G2 function f is written f!.

; =================================================================
; The Standard Doppelganger Construction:

; In constructing the model we will define every G1 function exactly as the
; user did, except that we will omit any :guards because we don't need guards
; in this application.  We know that every G1 function is justified in terms of
; G1 functions (every justification of a badged function has well-founded
; relation O< on domain O-P with a tame measure that is ancestrally independent
; of APPLY$ (and, coincidentally, natp valued, though while always enforced
; that observation needn't be for G1 functions)).  That means that if we just
; copy the user's unguarded G1 definitions down in the same order they will be
; admissible for the same reasons as before.  None of them rely on G2 functions
; for admission.

; So now we describe how to define the doppelgangers for G2 functions.

; Suppose f is a user-defined G2 function with formals (v1 ... vn), and body b.
; Let (m v1 ... vn) be the measure used to admit f.  Note that the measure is
; entirely in G1 and so can be written after the G1 functions are defined.
; The measure is also a natp, which will be discussed when we discuss the
; measure for the G2 doppelgangers.   Then the definition of the
; doppelganger of f, namely f!, is (DEFUN f! (v1 ... vn) b''), where b'' is
; obtained in two steps as follows.  First, let b' be the result of
; renaming in b every G2 function called, replacing the called function
; by its doppelganger name.  (Here we truly mean only ACL2 function calls, not
; ``calls'' within quoted LAMBDAs and terms.)  Next, consider a call of f! in b'
; ``marked'' if the measure conjecture for that call,

; (IMPLIES (AND t1 ... tn) (O< (m a1 ... an) (m v1 ... vn)))

; mentions a G2 function.  Create b'' by visiting every marked call, c, in b'
; and replacing c by

; (IF (O< (m a1 ... an)
;         (m v1 ... vn))
;     c
;     NIL).

; We call the O< term above the ``O< condition'' for the marked call.  The O<
; condition will be sufficient to justify call c during the admission of the
; clique.  These conditions cannot be proved until all the G2 functions are
; defined.  However, once all the G2 functions are defined, each O< condition
; is implied by the tests governing it.  Logically this follows from the proof
; that the doppelgangers are equivalent to their counterparts in the evaluation
; theory.  But, practically speaking, to prove that equivalence may require
; recapitulating for the doppelgangers the lemma development the user used
; during the admission of f.

; Example of the Standard Doppelganger Construction:

; Let (PROW LST FN) be a G2 function and define the G2 function

; (DEFUN$ PROW* (LST FN)
;   (DECLARE (XARGS :MEASURE (LEN LST)))
;   (COND ((OR (ENDP LST)
;              (ENDP (CDR LST)))
;          (APPLY$ FN (LIST LST LST)))
;         (T (PROW* (PROW LST FN) FN))))

; To create the doppelganger definition we carry out the steps described.
; First, rename the G2 functions to their doppelgangers.  Note that the G2
; functions mentioned in PROW* are APPLY$, PROW, and PROW*.  So the renaming
; produces:

; (DEFUN$ PROW*! (LST FN)
;   (DECLARE (XARGS :MEASURE (LEN LST)))
;   (COND ((OR (ENDP LST)
;              (ENDP (CDR LST)))
;          (APPLY$! FN (LIST LST LST)))
;         (T (PROW*! (PROW! LST FN) FN))))

; The call (PROW*! (PROW! LST FN) FN) is marked because the
; measure conjecture for that call is:

; (IMPLIES (AND (NOT (ENDP LST))
;               (NOT (ENDP (CDR LST))))
;          (O< (LEN (PROW! LST FN)) (LEN LST)))

; and involves the doppelganger of a G2 function, namely PROW.  So in the next
; step we replace the marked call by the IF expression described above and get
; the final definition of the doppelganger for prow*:

; (DEFUN$ PROW*! (LST FN)
;   (DECLARE (XARGS :MEASURE (LEN LST)))
;   (COND ((OR (ENDP LST)
;              (ENDP (CDR LST)))
;          (APPLY$! FN (LIST LST LST)))
;         (T (IF (O< (LEN (PROW! LST FN)) (LEN LST))
;                (PROW*! (PROW! LST FN) FN)
;                NIL))))

; We claim that the O< condition inserted is implied by the governing tests --
; or will be once all the G2 functions are defined.  Intuitively, the proof is
; ``the same'' as that of the measure conjecture proved for that case in the
; user's chronology:

; (IMPLIES (AND (NOT (ENDP LST))
;               (NOT (ENDP (CDR LST))))
;          (O< (LEN (PROW LST FN)) (LEN LST)))

; If the user had to prove lemmas to handle the admission of PROW*, then the
; analogous lemmas, with the analogous proofs, will be provable in the
; evaluation theory because in the evaluation theory each doppelganger is
; provably equivalent to its correspondent in the user's chronology.

; =================================================================
; On the Practicality of the Standard Construction:

; Note that the doppelganger construction would be simplest to carry out on a
; fully translated, beta-reduced body b.  The result wouldn't necessarily be
; executable and so all the doppelgangers ought to be introduced with defun-nx.
; Producing an executable version of the body from the translated,
; beta-reduced, renamed, and properly annotated marked calls is harder and
; would require some creativity.  For the purposes of showing that all warrants
; are valid, having executable doppelgangers is unnecessary.

; But from time to time we are tempted to implement a ``Doppelganger Button''
; that would actually carry out the method described here to produce an
; executable theory containing the doppelgangers of all the currently badged
; functions.  That is a good project for a student, perhaps.

; In that spirit, here is a suggestion for how one might do it:

;   Given a translated term u, let's write [u] for the result of applying
;   ec-call to every function call.  Let f be a G2 function with formals (v1
;   ... vn) and body b and measure (old-m v1 ... vn).  Let xb be the
;   translation of b.  Let xb'' be the transformation of xb as described in the
;   Standard Doppelganger Construction.

;   Define f! as:

;   (DEFUN f! (v1 ... vn)
;     (declare (xargs :guard t
;                     :measure (f!-measure v1 ... vn) ;   see f!-measure below
;                     :well-founded-relation l<))
;     (MBE :LOGIC xb''
;          :EXEC [xb]))

;   Then guard verification should be trivial because of the ec-call wrappers,
;   and execution would work out because we have left the mv-let forms (etc.)
;   in place in the :EXEC.

;   Of course, *1* functions (via ec-call) run a bit slower than their raw Lisp
;   counterparts.  But this shouldn't be important if we provide fast
;   execution, so the more direct execution capability via this MBE is just for
;   use during development, or maybe later for debugging.

; But let's remind ourselves that we don't really need executable
; doppelgangers.  During evaluation, each step needs to be justified by the
; evaluation theory.  (apply$ 'f (list x y ...)) = (f x y ...) is provable
; in the evaluation theory (when the tameness of the :FN/:EXPR arguments among
; (list x y ...) is established).  However, we cannot assume that the call of
; f on the right-hand side satisfies the guards of f.  So we implement the call
; with (*1*f x y ...).

; =================================================================
; Doppelganger Chronology

; (1) Define badge-userfn! as shown in the following schema, where {f_1, ...,
; f_k} is the set of all user-defined G1 and G2 function names and where
; badge_{f_i} means the badge of f_i.

; (DEFUN BADGE-USERFN! (FN)
;   (DECLARE (XARGS :GUARD T))
;   (CASE FN
;     (f_1 'badge_{f_1})
;     ...
;     (f_k 'badge_{f_k})
;     (OTHERWISE NIL)))

; For each user-defined G1 or G2 function name, badge-userfn! returns its badge
; constant.  It is trivial to show that it satisfies the requirements for its
; attachment to badge-userfn, i.e., that is guard verified, that its guards are
; implied by those of badge-userfn, and that it returns nil or a well-formed
; badge.

; (2) Use the standard doppelganger construction to get the definitions of
; BADGE!, TAMEP!, TAMEP-FUNCTIONP!, and SUITABLY-TAMEP-LISTP!

; (3) Introduce each G1 function with the user's definition except with any
; :guard declaration removed.  The order of the G1 functions should be as in
; the user's chronology.

; (4) Define APPLY$!, APPLY$-USERFN1!, EV$!, EV$-LIST! and the doppelgangers of
; all G2 functions in a mutual-recursion event.  We give schematic definitions
; of APPLY$!, APPLY$-USERFN1!, EV$!, and EV$-LIST! below; the G2 functions are
; handled via the standard construction.  We describe the measure used to admit
; this clique in this essay.  Clarification:  Note that in this step we define
; a function named APPLY$-USERFN1!, not APPLY$-USERFN!.

; (5) Define
;  (DEFUN APPLY$-USERFN! (FN ARGS)
;    (DECLARE (XARGS :GUARD T))
;    (EC-CALL (APPLY$-USERFN1! FN ARGS)))

; The doppelganger chronology is admissible.  The only questionable part is
; the proof of the measure conjectures for the clique introduced in step (4).
; That proof is given below.

; Once all 5 steps have been carried out it is possible to prove that
; every doppelganger is equal to its user counterpart in the evaluation theory
; produced by

; (DEFATTACH BADGE-USERFN BADGE-USERFN!)
; (DEFATTACH APPLY$-USERFN APPLY$-USERFN!)

; The proofs are by straightforward recursion induction.  For the G2 functions
; the recursion induction is with respect to the recursion exhibited in the
; doppelganger mutual-recursion.  For the G2 functions all of the equivalences
; must be proved simultaneously along with the proofs that the inserted O<
; conditions on marked calls are implied by their governors.  The latter can be
; proved because the induction hypotheses equating doppelgangers and their
; counterparts allow us to rewrite the O< conditions (which are stated in
; doppelganger terms) into their counterparts, and the resulting conjecture is
; known to be a theorem by the measure conjectures proved during the admission
; of the user's functions.

; =================================================================
; Schematic Definitions of APPLY$!, EV$!, EV$!-LIST

; Below we exhibit schematic definitions of the G2 boot functions.  They are
; all defined in a mutually recursive clique with the doppelgangers of all
; user-defined G2 functions.  The definitions below are schematic because they
; have to handle the (here unknown) user-defined functions.

; We will argue below that there is a measure that justifies this clique.  We
; exhibit measures later.  But the proof that our measures decrease requires a
; complete analysis of inter-clique calls.  We list all inter-clique calls in
; the section named Table of Inter-Clique Calls below.  Some of those calls are
; schematic and so we annotate some calls below with bracketed numbers
; indicating that the annotated call is addressed by the indicated row of the
; table.  The inter-clique call by APPLY$! to APPLY$-USERFN1!
; is annotated with a mysterious ``[  ].''  We explain later!

; None of the following defuns have explicit :guards: their guards are
; implicitly T but they are not guard verified.

; (DEFUN APPLY$! (FN ARGS)
;   (COND
;    ((CONSP FN)
;     (EV$! (LAMBDA-BODY FN)                                          ; [ 1]
;           (PAIRLIS$ (LAMBDA-FORMALS FN) ARGS)))
;    ((APPLY$-PRIMP FN)
;     (APPLY$-PRIM FN ARGS))
;    ((EQ FN 'BADGE)
;     (BADGE! (CAR ARGS)))
;    ((EQ FN 'TAMEP)
;     (TAMEP! (CAR ARGS)))
;    ((EQ FN 'TAMEP-FUNCTIONP)
;     (TAMEP-FUNCTIONP! (CAR ARGS)))
;    ((EQ FN 'SUITABLY-TAMEP-LISTP)
;     (SUITABLY-TAMEP-LISTP! (CAR ARGS) (CADR ARGS) (CADDR ARGS)))
;    ((EQ FN 'APPLY$)
;     (IF (TAMEP-FUNCTIONP! (CAR ARGS))
;         (APPLY$! (CAR ARGS) (CADR ARGS))                           ; [ 2]
;         (UNTAME-APPLY$ FN ARGS)))
;    ((EQ FN 'EV$)
;     (IF (TAMEP! (CAR ARGS))
;         (EV$! (CAR ARGS) (CADR ARGS))                              ; [ 3]
;         (UNTAME-APPLY$ FN ARGS)))
;    (T (APPLY$-USERFN1! FN ARGS))))                                 ; [  ]

; The definition of APPLY$-USERFN1!, which is used in the defun above of
; APPLY$-USERFN!, is shown below.  But we need some notation.

; In the definition of APPLY$-USERFN1! let {g_1, ..., g_j} be the user-defined
; G1 function names and let {f_1, ..., f_k} be the user-defined G2 function
; names.

; We introduce some rather unconventional notation to describe APPLY$-USERFN1!
; schematically.

; If g is some user-defined G1 function of arity n, then (g (CAR ARGS) (CADR
; ARGS) ...) denotes a call of g on the first n elements of ARGS, extending
; with NILs as necessary.

; Let f be some user-defined G2 function of arity n.  Then in the pattern:

; (IF (AND (tame! (CAR ARGS)) (tame! (CADR ARGS)) ...)
;     (f! (CAR ARGS) (CADR ARGS) ...)
;     (UNTAME-APPLY$ FN ARGS))

; (tame! x), where x is the car/cdr expression for the ith (0-based) element of
; ARGS, means T, (TAMEP-FUNCTIONP! x), or (TAMEP! x) depending on whether the
; ilk of the ith formal is NIL, :FN, or :EXPR.  The call of f! is to the first
; n elements of ARGS, extending with NILs as necessary.

; For example, if TWOFER has ilks (NIL :FN :EXPR NIL), then

; (IF (AND (tame! (CAR ARGS)) (tame! (CADR ARGS)) ...)
;     (TWOFER! (CAR ARGS) (CADR ARGS) ...)
;     (UNTAME-APPLY$ FN ARGS))

; means

; (IF (AND T
;          (TAMEP-FUNCTIONP! (CADR ARGS))
;          (TAMEP! (CADDR ARGS))
;          T)
;     (TWOFER! (CAR ARGS) (CADR ARGS) (CADDR ARGS) (CADDDR ARGS))
;     (UNTAME-APPLY$ FN ARGS))

; which is logically equivalent to

; (IF (AND (TAMEP-FUNCTIONP! (CADR ARGS))
;          (TAMEP! (CADDR ARGS)))
;     (TWOFER! (CAR ARGS) (CADR ARGS) (CADDR ARGS) (CADDDR ARGS))
;     (UNTAME-APPLY$ FN ARGS))

; If f has no :FN/:EXPR formals, then the IF test reduces to T and the IF can
; be eliminated.

; We use this rather cumbersome notation to remind the reader, later during our
; measure proof, that we have tameness hypotheses about every :FN/:EXPR element
; of ARGS and that they are phrased in terms of the doppelgangers of
; tamep-functionp and tamep.

; (DEFUN APPLY$-USERFN1! (FN ARGS)
;   (CASE FN
;     (g_1 (g_1 (CAR ARGS) (CADR ARGS) ...))
;     ...
;     (g_j (g_j (CAR ARGS) (CADR ARGS) ...))
;     (f_1 (IF (AND (tame! (CAR ARGS)) (tame! (CADR ARGS)) ...)
;              (f_1! (CAR ARGS) (CADR ARGS) ...)
;              (UNTAME-APPLY$ FN ARGS)))
;     ...                                                              ; [ 4]
;     (f_k (IF (AND (tame! (CAR ARGS)) (tame! (CADR ARGS)) ...)
;              (f_k! (CAR ARGS) (CADR ARGS) ...)
;              (UNTAME-APPLY$ FN ARGS)))
;     (OTHERWISE
;      (UNTAME-APPLY$ FN ARGS))))

; Note: APPLY$-USERFN1! calls every G1 function, but calls the doppelganger of
; every G2 function (after appropriate tameness tests).

; To define EV$ we need some notation.

; Let f be some G2 function of arity n.  The expression

; (APPLY$! 'f list-ev$!-or-cadr-exprs)

; means

; (APPLY$! 'f (LIST z1 ... zn)),

; where zi is (EV$! (NTH i X) A), if the ilk of the ith (1-based) formal of f
; is NIL, and is (CADR (NTH i X)) otherwise.  The NTHs are actually expanded to
; car/cdr expressions since i is fixed.

; For example, if TWOFER has ilks (NIL :FN :EXPR NIL), then

; (APPLY$! 'TWOFER list-ev!-or-cadr-exprs)

; means

; (APPLY$! 'TWOFER
;          (LIST (EV$! (NTH 1 X) A)
;                (CADR (NTH 2 X))
;                (CADR (NTH 3 X))
;                (EV$! (NTH 4 X) A)))

; which is logically equivalent to:

; (APPLY$! 'TWOFER
;          (LIST (EV$! (CADR X) A)
;                (CADR (CADDR X))
;                (CADR (CADDDR X))
;                (EV$! (CAR (CDDDDR X)) A)))

; The odd treatment of the :FN/:EXPR argument positions simplifies the
; termination argument.  We explain later.

; In the following, {f_1, ..., f_k} is the set of user-defined functions of G2
; that have one or more :FN/:EXPR arguments.  All user-defined G1 functions and
; those user-defined G2 functions with no :FN/:EXPR arguments are handled by
; the last COND clause.

; (DEFUN EV$! (X A)
;   (COND
;    ((NOT (TAMEP! X))
;     (UNTAME-EV$ X A))
;    ((VARIABLEP X)
;     (CDR (ASSOC-EQUAL X A)))
;    ((FQUOTEP X)
;     (CADR X))
;    ((EQ (CAR X) 'IF)
;     (IF (EV$! (CADR X) A)                                       ; [ 5]
;         (EV$! (CADDR X) A)                                      ; [ 6]
;         (EV$! (CADDDR X) A)))                                   ; [ 7]
;    ((EQ (CAR X) 'APPLY$)
;     (APPLY$! 'APPLY$                                            ; [ 8]
;              (LIST (CADR (CADR X))
;                    (EV$! (CADDR X) A))))                        ; [12]
;    ((EQ (CAR X) 'EV$)
;     (APPLY$! 'EV$ (LIST (CADR (CADR X)) (EV$! (CADDR X) A))))   ; [ 9]
;    ((EQ (CAR X) 'f_1)
;     (APPLY$! 'f_1 list-ev$!-or-cadr-exprs))
;    ...                                                          ; [10]
;    ((EQ (CAR X) 'f_k)
;     (APPLY$! 'f_k list-ev$!-or-cadr-exprs))
;    (T
;     (APPLY$! (CAR X)                                            ; [11]
;              (EV$!-LIST (CDR X) A)))))                          ; [13]

; (DEFUN EV$!-LIST (X A)
;   (COND
;    ((ATOM X) NIL)
;    (T (CONS (EV$! (CAR X) A)                                    ; [14]
;             (EV$!-LIST (CDR X) A)))))                           ; [15]

; Note: Inspection of the four definitions in this section reveals that
; APPLY$-USERFN1! is only called by APPLY$!.  It cannot be called by any user
; defined function because it does not have a badge.  Thus, it could be
; eliminated from the clique and inlined in APPLY$!.  However, we want a
; function name for the big-switch that is APPLY$-USERFN1! so we can use it
; (under an EC-CALL) in our definition of APPLY$-USERFN!.

; =================================================================
; The Measure for the APPLY$! Clique

; We start by describing the measure for the doppelgangers of user-defined G2
; functions and only afterwards do we present the measures for APPLY$!, EV$!,
; and EV$-LIST!.

; Let f be a user-defined G2 function with doppelganger f!.

; The measure for f! is a lexicographic 5-tuple where the first four components
; are computed by the macro expressions given below.  The fifth component is
; always 1.

; (tameness-bit f): 0 if all of the :FN/:EXPR formals of f are tame, 1
;    otherwise.  Here by ``tame'' we mean accepted by tamep-functionp! or
;    tamep!, respectively according to the ilk of the formal.

; (max-internal-weight f): maximal weight of the internals: see below

; (chronological-position f): the position of (def-warrant f) in the user's
;    chronology.  The position of APPLY$ and APPLY$-USERFN is 0, the positions
;    of EV$ and EV$-LIST are 1, the position of the first badged user-defined
;    function is 2, the next such function 3, etc.

; (original-measure f): measure term used to admit f in the user's chronology
;    (which we have required to exist rather than being local; indeed to be
;    definable in terms of G1 functions).

; Implementation Note: Each component above requires knowledge of how f was
; defined and so requires looking at the world created by the user's
; chronology.  So in fact, the four macros mentioned above look at the constants
; described below:

; *USER-FNS*                      list of user-defined badged functions in
;                                  chronological order of their def-warrant
;                                  events

; *G2-FNS*                        list of all G2 functions, including APPLY$
;                                  and EV$, which are the first two elements,
;                                  listed in chronological order of their
;                                  def-warrants

; *G1-FNS*                        list of all G1 functions in chronological
;                                  order of their def-warrants

; *TAMENESS-CONDITIONS*           alist pairing each user-defined G2 function
;                                  symbol to the list of tameness expressions
;                                  determining tameness bit

; *WEIGHT-ALIST*                  alist pairing each user-defined G2 function
;                                  symbol with its weight

; *MAX-INTERNAL-WEIGHT-ALIST*     alist pairing each user-defined G2 function
;                                  symbol with the term expressing the
;                                  maximal weight of its internals

; *ORIGINAL-MEASURES-ALIST*       alist pairing each user-defined G2 function
;                                  symbol with the original measure
;                                  term used in its admission

; The values of these constants are computed from the world by make-event forms
; in doppelgangers.lisp, run after locally including "user-defs".  We list the
; constants in this note because they may help you understand the definitions.
; For example, if you (include-book "doppelgangers") and then print the value of
; *MAX-INTERNAL-WEIGHT-ALIST* you will see each user-defined G2 function in
; "user-defs" together with the expression to be used as the second component
; of the measure of its doppelganger.

; End of Implementation Note

; Our notion of ``maximal internal weight'' requires explanation!

; The ``internals'' of the definition of f are

; i.   the :FN/:EXPR formals,

; ii.  the quotations of every user-defined G2 function name (other than f
;      itself) whose doppelganger is called in the body of f!, and

; iii. the quoted :FN/:EXPR actuals (i.e., quoted LAMBDA expressions to apply
;      and terms to evaluate) occurring in the body of f!.

; For example, consider the G2 function COLLECT-A, which maps over its ordinary
; argument, lst, applying its :FN argument, FN, and also calls the G2 function
; SUMLIST on a quoted LAMBDA in a :FN position.  Note also that the quoted
; LAMBDA mentions the G2 function FOLDR.  [Note: the terms in this example are
; not schemas despite their mixed case.  These are concrete terms from
; user-defs.lisp.  We have uppercased the ``internals''.]

; (defun$ collect-a (lst FN)
;   (cond ((endp lst) nil)
;         (t (cons (apply$ fn (list
;                              (SUMLIST (nats (car lst))
;                                       '(LAMBDA (I)
;                                          (FOLDR (NATS I)
;                                                 '(LAMBDA (J K)
;                                                    (BINARY-* (SQUARE J) K))
;                                                 '1)))))
;                  (collect-a (cdr lst) fn)))))

; The internals are thus
; i.   FN
; ii. 'SUMLIST
; iii. the quoted LAMBDA expression, '(LAMBDA (I) (FOLDR ...)).

; The ``maximal internal weight'' for collect-a, written (max-internal-weight
; collect-a), expands to the maximum of the ``weights'' of the internals above:

; (max (weight FN)
;      (max (weight 'SUMLIST)
;           (weight '(LAMBDA (I)
;                            (FOLDR (NATS I)
;                                   '(LAMBDA (J K)
;                                      (BINARY-* (SQUARE J) K))
;                                   '1)))))

; Note: Weight is defined below but the weights of items ii and iii in the
; expression above can simply be computed.  It will turn out that the
; expression above is equivalent to (max (weight fn) (max 26 50)) = (max
; (weight fn) 50), but this is less informative.

; End of example.

; The weight of an object is computed in a way similar to the acl2-count: sum
; the recursively obtained weights of the components.  However, while
; ACL2-COUNT assigns every symbol a size of 0, WEIGHT assigns G2 function
; symbols a non-0 size determined by the weight of the function's beta-reduced
; body as of the point in the chronology at which the function is introduced.
; Still undefined symbols have weight 0 but acquire non-0 weight upon their
; definition as G2 functions.  We will give formal definition in a moment.

; For example, consider the G2 function (again, this is not a schema):

; (defun$ sumlist (lst fn)
;   (cond ((endp lst) 0)
;         (t (+ (apply$ fn (list (car lst)))
;               (sumlist (cdr lst) fn))))).

; Its weight (at the position in the chronology when the function is defined)
; is 26, which happens to also be the acl2-count of its beta-reduced body.  The
; weight of the symbol SUMLIST in its body is 0 when SUMLIST is being defined.
; But occurrences of SUMLIST in subsequent G2 functions will have weight 26.
; The weight of FOLDR is 25, which is also the acl2-count of its beta-reduced
; body.

; However, the weight of the LAMBDA expression quoted in the collect-a example
; above, which necessarily occurred after FOLDR was defined, is 50 even though
; its acl2-count is just 25.  The reason its weight is larger than its
; acl2-count is that the symbol FOLDR in the LAMBDA expression contributes an
; additional 25 (whereas it contributes nothing to the acl2-count of the
; LAMBDA).

; End of example.

; An important observation is that if a G2 function mentions a quoted LAMBDA
; expression in a :FN position, then every function symbol occurring in the
; LAMBDA's body will have already been defined.  If a function g mentions a
; quoted LAMBDA in a :FN position and the LAMBDA uses an undefined (or even an
; un-badged) symbol, then g would be un-badged and not be a G2 function.

; The weight of an object is determined with respect to an alist that maps G2
; functions to their weights.  This concept is named WEIGHT1:

; (DEFUN WEIGHT1 (X WEIGHT-ALIST)
;   (IF (CONSP X)
;       (+ 1
;          (WEIGHT1 (CAR X) WEIGHT-ALIST)
;          (WEIGHT1 (CDR X) WEIGHT-ALIST))
;       (IF (SYMBOLP X)
;           (LET ((TEMP (ASSOC-EQ X WEIGHT-ALIST)))
;             (COND
;              ((NULL TEMP) 0)
;              (T (CDR TEMP))))
;           (ACL2-COUNT X))))

; and is just ACL2-COUNT except for the symbols bound in the alist.

; To determine the weights of the G2 symbols we process the G2 functions
; (except for APPLY$ and EV$) in chronological order of their def-warrants,
; binding each symbol to the weight of its beta-reduced body as computed with
; respect to the weights of the preceding function symbols.

; (DEFUN GENERATE-WEIGHT-ALIST (FNS WEIGHT-ALIST WRLD)
;   (DECLARE (XARGS :MODE :PROGRAM))
;   (COND
;    ((ENDP FNS) WEIGHT-ALIST)
;    (T (GENERATE-WEIGHT-ALIST
;        (CDR FNS)
;        (CONS (CONS (CAR FNS)
;                    (WEIGHT1 (EXPAND-ALL-LAMBDAS (BODY (CAR FNS) NIL WRLD))
;                             WEIGHT-ALIST))
;              WEIGHT-ALIST)
;        WRLD))))

; We define the constant *WEIGHT-ALIST* to be the resultant alist:

; (MAKE-EVENT
;  `(DEFCONST *WEIGHT-ALIST*
;     ',(GENERATE-WEIGHT-ALIST (CDDR *G2-FNS*) NIL (W STATE))))

; and then we define the function weight to use this fixed alist:

; (DEFUN WEIGHT (X) (WEIGHT1 X *WEIGHT-ALIST*))

; We now make some observations about weights and measures.

; Reminder: An easily made mistake is to think of the weight of f as the
; second component of f's measure.  That is wrong!  The second component of
; f's measure is the maximal internal weight of f.

; Weight Observation 1:  (weight x) is a natural number.

; Weight Observation 2: If x is a cons, its weight is strictly greater than the
; weights of its car and cdr.  This will allow EV$! to recur into the car and
; cdr of expressions.

; Weight Observation 3: The weight assigned to any recursive G2 function symbol
; f is strictly greater than the weight of any proper subexpression in the
; beta-reduced body of f.  The weight is calculated as of the chronological
; position of the function's introduction and sums the ``then-current'' weight
; of every symbol occurrence in the beta-reduced body plus increments for
; the conses in the body.  Furthermore, because the function is in G2, it calls
; at least one function (i.e., its body is not a simple variable) so there is
; at least one cons in the body.  A corollary of this observation is that the
; weight assigned to any recursive G2 function symbol is strictly greater than
; the weight of internals ii and iii.

; Note: The whole notion of weight (actually, of WEIGHT1) is odd as a concept
; to be applied to terms because it does not treat its argument x as a term but
; as a binary tree.  In particular, it is completely insensitive to which
; symbols are used as variables, which are inside quotes, and which are used as
; functions.  It is exactly like acl2-count in this regard and yet acl2-count
; is a very useful general-purpose measure for functions that recur into terms.
; So is weight.  But it bears noting that a function whose defining event uses
; previously defined symbols inside quoted constants or as variable symbols
; will have an ``artificially'' high weight.

; It remains to discuss the measures for APPLY$!, APPLY$-USERFN1!, EV$!, and
; EV$-LIST!.

; (DEFUN APPLY$!-MEASURE (FN ARGS)
;   (LLIST 0
;          (MAX (WEIGHT FN)
;               (IF (FN/EXPR-ARGS FN ARGS)
;                   (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS FN ARGS)))
;                   0))
;          (CHRONOLOGICAL-POSITION APPLY$)
;          0
;          1))

; The function FN/EXPR-ARGS returns the elements of its second argument that
; are in positions with the :FN/:EXPR ilks of its first argument.  For example,
; if TWOFER has ilks (NIL :FN :EXPR NIL) then (FN/EXPR-ARGS 'TWOFER '(A SQUARE
; (REV X) D)) is '(SQUARE (REV X)).  The function MAXIMAL-WEIGHT returns the
; maximal weight of the elements of its arguments.

; (DEFUN APPLY$-USERFN1!-MEASURE (FN ARGS)
;   (LLIST 0
;          (MAX (WEIGHT FN)
;               (IF (FN/EXPR-ARGS FN ARGS)
;                   (+ 1 (MAX-WEIGHT (FN/EXPR-ARGS FN ARGS)))
;                   0))
;          (CHRONOLOGICAL-POSITION APPLY$-USERFN)
;          0
;          0))

; The measures of EV$! and EV$-LIST! are:

; (DEFUN EV$!-MEASURE (X A)
;   (LLIST 0 (WEIGHT X) (CHRONOLOGICAL-POSITION EV$) 0 1))

; (DEFUN EV$!-LIST-MEASURE (X A)
;   (LLIST 0 (WEIGHT X)  (CHRONOLOGICAL-POSITION EV$-LIST) 0 1))

; As already explained, the measure of each user-defined doppelganger, f!, is

; (DEFUN f!-MEASURE (...)
;   (LLIST (TAMENESS-BIT f)
;          (MAX-INTERNAL-WEIGHT f)
;          (CHRONOLOGICAL-POSITION f)
;          (ORIGINAL-MEASURE f)
;          1))

; As mentioned earlier, APPLY$-USERFN1! is only called by APPLY$! and is could
; have been inlined.  The measures given above employ a standard construction
; for justifying the call of such a function.  All measures in the clique
; except that for APPLY$-USERFN1! have a fifth component of 1.  The measure of
; APPLY$-USERFN1! uses the same first four components as its only caller,
; APPLY$!, but uses 0 as its fifth component.  Thus APPLY$! can call
; APPLY$-USERFN1! (preserving the first four components of APPLY$!'s measure)
; and APPLY$-USERFN1! can then call any function whose measure is dominated by
; APPLY$!'s.  Intuitively, it's just as though we've inlined the call of
; APPLY$-USERFN1!.

; The proof below that the measures decrease is actually for the version of the
; clique in which we have inlined the call of APPLY$-USERFN1! in APPLY$!.  Only
; the first four components of the measures are relevant.  This explains why
; we annotated the call by APPLY$! to APPLY\$-USERFN1! with [  ].

; =================================================================
; Table of Inter-Clique Calls

; The proof that our measures decrease must inspect the definitions of APPLY$!,
; EV$!, EV$-LIST!, and any user-defined function, f!, and consider every call
; from any of those functions to any other, including (in the case of calls
; from the generic f!) calls to other user-defined G2 functions.

; If f! is the doppelganger of a user-defined G2 function then the only allowed
; calls from f! into the clique may be classified as follows.  The bracketed
; numbers are those used in our table of inter-clique calls below.

; [16] (APPLY$! v ...)  -- where v is a :FN formal of f!.  Of note is the
;                          fact that we know nothing about the term occupying
;                          the second argument of APPLY$! here.  E.g.,
;                          f could be defined:
;                          (DEFUN f (V U) (APPLY$ V U)).

; [17] (APPLY$! 'x ...) -- where x is a tame function (symbol or LAMBDA)

; [18] (EV$! v ...)     -- where v is an :EXPR formal of f!

; [19] (EV$! 'x ...)    -- where x is a tame expression

; [20] (g! ...)         -- g! is the doppelganger of a user-defined G2 function
;                          other than f and every :FN slot of the call of g! is
;                          occupied by either a :FN formal of f! or a quoted
;                          tame function symbol or LAMBDA expression, and every
;                          :EXPR argument of the call of g! is occupied by
;                          either an :EXPR formal of f! or a quoted tame
;                          expression.

; [21] (f! ...)         -- where every :FN/:EXPR slot of the call is occupied
;                          by the corresponding formal of f!.

; Note that f! may not call EV$-LIST! because that function does not have a
; badge.  In calls [17], [19], and [20] we know that the quoted objects in
; :FN/:EXPR positions are tame! because if they were not, f would not have a
; badge and would not be in G2.

; Below is a complete listing of all inter-clique calls.  Each line raises a
; measure proof obligation.  For example, line [ 1] means that (APPLY$! FN
; ARGS) calls (EV$! (CADDR FN) ...)  when (CONSP FN), i.e., when FN is treated
; as a LAMBDA expression.  We elide irrelevant arguments.  This line means we
; have to show that

; (IMPLIES (CONSP FN)
;          (L< (EV$!-MEASURE (CADDR FN) ...)
;              (APPLY$!-MEASURE FN ARGS))).

; The reader's immediate obligation is to confirm that these 21 cases cover all
; of the possible inter-clique calls.  Our earlier definitions of APPLY$!,
; APPLY$-USERFN1!, EV$!, and EV$-LIST! are annotated with these same bracketed
; numbers to point out the calls in question.  The possible inter-clique calls
; made by the doppelganger of the arbitrary user-defined G2 function, f!, are
; listed above.

; Some calls in the table are syntactically different, e.g., (CADDR x) vs
; (LAMBDA-BODY x) vs (NTH 2 x), but logically equivalent.  Our proof deals with
; some calls collectively because the same logical argument justifies them,
; e.g., for (EV$! (CADR X) A) and (EV$! (CADDR X) A).  But we list all classes
; of calls.

; Table of Inter-Clique Calls

; [A] (APPLY$! FN ARGS)
;  [ 1]  (EV$! (CADDR FN) ...)           ; (CONSP FN)
;  [ 2]  (APPLY$! (CAR ARGS) (CADR ARGS)); FN='APPLY$ and (CAR ARGS) tame!
;  [ 3]  (EV$! (CAR ARGS) (CADR ARGS))   ; FN='EV$ and (CAR ARGS) tame!
;  [ 4]  (f! (CAR ARGS) ...)             ; FN='f and the :FN/:EXPR ARGS tame!

; [B] (EV$! X A)                         ; in all calls below, (CONSP X) and
;                                        ;   X is tame!
;  [ 5]  (EV$! (CADR X) A)               ; (CAR X)='IF
;  [ 6]  (EV$! (CADDR X) A)              ; (CAR X)='IF
;  [ 7]  (EV$! (CADDDR X) A)             ; (CAR X)='IF
;  [ 8]  (APPLY$! 'APPLY$ args')         ; (CAR X)='APPLY$; see note below
;  [ 9]  (APPLY$! 'EV$ args')            ; (CAR X)='EV$; see note below
;  [10]  (APPLY$! 'f args')              ; (CAR X)='f and f has :FN/:EXPR
;                                        ;   formals; see note below
;  [11]  (APPLY$! (CAR X) ...)           ; (CAR X) has no :FN/:EXPR formals
;  [12]  (EV$! (NTH i X) ...)            ; (CAR X)='f and ith ilk of f is NIL;
;                                        ;   see note below
;  [13]  (EV$!-LIST (CDR X) ...)         ; (CAR X) has no :FN/:EXPR formals

; [C] (EV$-LIST! X A)
;  [14]  (EV$! (CAR X) ...)              ; (CONSP X)
;  [15]  (EV$!-LIST (CDR X) ...)         ; (CONSP X)

; [D] (f! v_1 ... v_n)
;  [16]  (APPLY$! v ...)                 ; v is a formal of f! of ilk :FN
;  [17]  (APPLY$! 'x ...)                ; x is a tame! function
;  [18]  (EV$ v ...)                     ; v is a formal of f! of ilk :EXPR
;  [19]  (EV$ 'x ...)                    ; x is a tame! expression
;  [20]  (g! ...)                        ; each :FN/:EXPR actual is a formal
;                                        ;   of f! or a quoted tame! object
;  [21]  (f! ...)                        ; each :FN/:EXPR actual is the
;                                        ;   corresponding formal of f!

; Note: Lines [8], [9], [10] mean that (EV$! X A) calls APPLY$! on 'APPLY$,
; 'EV$, and 'f with argument list args', where args' is (LIST e_1 e_2 ... e_n),
; where n is the arity of (CAR X) and where e_i is (CADR (NTH i X)) if the ith
; formal of (CAR X) is of ilk :FN/:EXPR and is (EV$! (NTH i X) A) otherwise.

; For example, if f is a function whose ilks are (NIL :FN NIL :EXPR NIL), then
; line 10 would read:

; [10] (APPLY$! 'f (LIST (EV$! (NTH 1 X) A) ; ilk NIL
;                        (CADR (NTH 2 X))   ; ilk :FN
;                        (EV$! (NTH 3 X) A) ; ilk NIL
;                        (CADR (NTH 4 X))   ; ilk :EXPR
;                        (EV$! (NTH 5 X) A) ; ilk NIL
;                        ))

; Intuitively, each e_i is (EV$! (NTH i X) A).  But if X is tame!, we know the
; elements of X in :FN/:EXPR slots are actually QUOTEd, so the intuitive (EV$!
; (NTH i X) A) will in fact evaluate to (CADR (NTH i X)).  It makes our
; termination argument simpler if we go ahead and define EV$! this way.  By
; the way, line [10] is only applicable if f has at least one :FN/:EXPR formal.
; If f is a G2 function with no :FN or :EXPR formals, then it is handled by
; line [11].

; =================================================================
; Proofs of the Measure Obligations

; -----------------------------------------------------------------
; [A] (APPLY$! FN ARGS)
;  [ 1]  (EV$! (CADDR FN) ...)           ; (CONSP FN)

; Proof Obligation:
; (IMPLIES (CONSP FN)
;          (L< (EV$!-MEASURE (CADDR FN) ...)
;              (APPLY$!-MEASURE FN ARGS)))

; The crux of this argument is that both measures have first component 0 and
; their second components settle the question.  The second component of
; (EV$!-MEASURE (CADDR FN) ...) is (WEIGHT (CADDR FN)).  The second component
; of (APPLY$!-MEASURE FN ARGS) is

; (MAX (WEIGHT FN)
;      (IF (FN/EXPR-ARGS FN ARGS)
;          (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS FN ARGS)))
;          0))

; But (WEIGHT (CADDR FN)) < (WEIGHT FN), when FN is a CONSP, no matter what
; legal value *weight-alist* has.  In particular, the following is a theorem

; (IMPLIES (AND (CONSP X)
;               (NOT (ASSOC-EQUAL NIL WA))
;               (SYMBOLP-TO-NATP-ALISTP WA))
;          (< (WEIGHT1 (CADDR X) WA)
;             (WEIGHT1 X WA)))

; and all legal values of *WEIGHT-ALIST* are SYMBOLP-TO-NATP-ALISTPS and NIL is
; never bound on that alist because it is not an ACL2 function symbol.  We do
; not go into this level of detail in our proofs below and only do so here to
; remind the reader that we're dealing with meta-theorems about the ACL2 world.
; That is, one might think that this particular Proof Obligation above could be
; dispatched by loading doppelgangers.lisp and doing

; (thm (IMPLIES (CONSP FN)
;               (L< (EV$!-MEASURE (CADDR FN) A)
;                   (APPLY$!-MEASURE FN ARGS))))

; because no user functions are involved in this conjecture.  But that is wrong
; because WEIGHT is a function of *WEIGHT-ALIST* which is a function of the
; user's chronology.

; -----------------------------------------------------------------
; [A] (APPLY$! FN ARGS)
;  [ 2]  (APPLY$! (CAR ARGS) (CADR ARGS)); FN='APPLY$ and (CAR ARGS) tame!

; Proof Obligation:
; (IMPLIES (AND (EQ FN 'APPLY$)
;               (TAMEP-FUNCTIONP! (CAR ARGS)))
;          (L< (APPLY$!-MEASURE (CAR ARGS) (CADR ARGS))
;              (APPLY$!-MEASURE FN ARGS)))

; The first components are both 0 and this lexicographic inequality is settled
; by the second components.  The inequality of the second components is

; (< (MAX (WEIGHT (CAR ARGS))
;         (IF
;          (FN/EXPR-ARGS (CAR ARGS) (CADR ARGS))
;          (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS (CAR ARGS) (CADR ARGS))))
;          0))
;    (MAX (WEIGHT 'APPLY$)
;         (IF
;          (FN/EXPR-ARGS 'APPLY$ ARGS)
;          (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS 'APPLY$ ARGS)))
;          0)))

; The weight of 'APPLY$ is 0.  Consider the FN/EXPR-ARGS term on the left-hand
; side.  If (CAR ARGS) is a tame function, there are no functional/expressional
; arguments, so the left-hand side reduces to (WEIGHT (CAR ARGS)).

; On the right-hand side, (FN/EXPR-ARGS 'APPLY$ ARGS) is (LIST (CAR ARGS))
; because the ilks of 'APPLY$ is (:FN NIL).  The MAXIMAL-WEIGHT of that list is
; (WEIGHT (CAR ARGS)).  So the right-hand side is (+ 1 (WEIGHT (CAR ARGS))).

; So the inequality above is

; (< (WEIGHT (CAR ARGS)) (+ 1 (WEIGHT (CAR ARGS))))

; This explains why there is a +1 in the second component of the APPLY$!
; measure: so APPLY$ can apply itself (and, as it will turn out in case [3]
; below, 'EV$) when the first element of ARGS is tame.

; -----------------------------------------------------------------
; [A] (APPLY$! FN ARGS)
;  [ 3]  (EV$! (CAR ARGS) (CADR ARGS))   ; FN='EV$ and (CAR ARGS) tame!

; Proof Obligation:
; (IMPLIES (AND (EQ FN 'EV$)
;               (TAMEP! (CAR ARGS)))
;          (L< (EV$!-MEASURE (CAR ARGS) (CADR ARGS))
;              (APPLY$!-MEASURE FN ARGS)))

; Both measures have first component 0 and the question is settled by the
; second components.  The inequality in question is:

; (< (WEIGHT (CAR ARGS))
;    (IF (FN/EXPR-ARGS 'EV$ ARGS)
;        (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS 'EV$ ARGS)))
;        0))

; after simplifying (WEIGHT 'EV$) in the second component of (APPLY$!-MEASURE
; 'EV$ ARGS) to 0.  Similar to case [2], the FN/EXPR-ARGS term simplifies to
; (LIST (CAR ARGS)) and so the inequality becomes

; (< (WEIGHT (CAR ARGS)) (+ 1 (WEIGHT (CAR ARGS))))

; -----------------------------------------------------------------
; [A] (APPLY$! FN ARGS)
;  [ 4]  (f! (CAR ARGS) ...)             ; FN='f and the :FN/:EXPR ARGS tame!

; Proof Obligation:

; We are considering (APPLY$ 'f ARGS), where f is a user-defined G2 function
; and all of the elements of ARGS in :FN/:EXPR positions correspond,
; appropriately, to tame functions or expressions.

; We wish to show the conclusion:

; (L< (f!-MEASURE (CAR ARGS) ... (CAD...DR ARGS))
;     (APPLY$!-MEASURE 'f ARGS))

; Since we know all the :FN/:EXPR arguments of ARGS are tame, the tameness-bit
; of the left-hand side is 0, as is the tameness-bit of the right-hand side.
; The inequality of second components reduces to:

; (< (MAX weights-i
;         (MAX weights-ii
;              weights-iii))
;    (MAX (WEIGHT 'f)
;         (IF
;          (FN/EXPR-ARGS 'f ARGS)
;          (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS 'f ARGS)))
;          0)))

; where weights-i is the maximal weight of any :FN/:EXPR element of ARGS,
; weights-ii is the maximal weight of any other user-defined G2 function called
; in the body of f, and weights-iii is the maximal weight of any quoted tame
; function or expression used in :FN/:EXPR slots in the body of f.

; Note that (WEIGHT 'f) is strictly larger than weights-ii and weights-iii
; because the weight of a function is the sum of the weights of all objects in
; its body.  Furthermore, (FN/EXPR-ARGS 'f ARGS) is the list of all the ARGS
; measured in weights-i, so (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS 'f ARGS))) is
; strictly bigger than weights-i.  Thus, the inequality above holds.

; -----------------------------------------------------------------
; [B] (EV$! X A)                         ; in all calls below, (CONSP X) and
;                                        ;   X is tame!
;  [ 5]  (EV$! (CADR X) A)               ; (CAR X)='IF
;  [ 6]  (EV$! (CADDR X) A)              ; (CAR X)='IF
;  [ 7]  (EV$! (CADDDR X) A)             ; (CAR X)='IF
;  [12]  (EV$! (NTH i X) ...)            ; (CAR X)='f and ith ilk of f is NIL
;  [13]  (EV$!-LIST (CDR X) ...)         ; (CAR X) has no :FN/:EXPR formals
; [C] (EV$-LIST! X A)
;  [14]  (EV$! (CAR X) ...)              ; (CONSP X)
;  [15]  (EV$!-LIST (CDR X) ...)         ; (CONSP X)

; Proof Obligation: We can consider these inter-calls of EV$! and EV$-LIST!
; together because it is always the second components of the measures that
; decide the questions and the first two components of (EV$!-MEASURE X A) and
; of (EV$-LIST! X A) are identical, namely (LLIST 0 (WEIGHT X) ...).

; So taking [12], say, as typical, the proof obligation is

; (IMPLIES (AND (CONSP X)
;               (TAMEP! X))
;          (L< (EV$!-MEASURE (CAD...DR X) ...)
;              (EV$!-MEASURE X A)))

; But the WEIGHT of any proper subtree of X is smaller than that of X.  The
; same argument works for all these cases.

; -----------------------------------------------------------------
; [B] (EV$! X A)                         ; in all calls below, (CONSP X) and
;                                        ;   X is tame!
;  [ 8]  (APPLY$! 'APPLY$ args')         ; (CAR X)='APPLY$; see note below
;  [ 9]  (APPLY$! 'EV$ args')            ; (CAR X)='EV$; see note below

; Proof Obligation: When X is a tame term and (CAR X)='APPLY$,
; (EV$! X A)
; calls
; (APPLY$! 'APPLY$ (LIST (CADR (CADR X)) (EV$! (CADDR X) A)))

; Case [ 9] is exactly the same except EV$ calls APPLY$ with first argument
; 'EV$ instead of 'APPLY$.

; The proofs of [ 8] and [ 9] are otherwise identical so we focus on [ 8].

; The second element of the list-expression above is irrelevant and we will
; generalize it to Z below.

; The proof obligation is thus:

; (IMPLIES (AND (CONSP X)
;               (TAMEP! X)
;               (EQ (CAR X) 'APPLY$))
;          (L< (APPLY$!-MEASURE 'APPLY$ (LIST (CADR (CADR X)) Z))
;              (EV$!-MEASURE X A)))

; The first components of both sides are 0 and the comparison of the second
; components becomes:

; (< (MAX (WEIGHT 'APPLY$)
;         (IF (FN/EXPR-ARGS 'APPLY$
;                           (LIST (CADR (CADR X)) Z))
;             (+ 1 (MAXIMAL-WEIGHT
;                   (FN/EXPR-ARGS 'APPLY$
;                                 (LIST (CADR (CADR X)) Z))))
;             0))
;    (WEIGHT X))

; which in turn becomes

; (< (+ 1 (WEIGHT (CADR (CADR X))))
;    (WEIGHT X))

; But if X is tamep! and its CAR is APPLY$ (or EV$) then the length of X is 3
; and the inequality holds.  This can be confirmed in general by

; (THM
;  (IMPLIES (AND (CONSP X)
;                (OR (EQ (CAR X) 'APPLY$)
;                    (EQ (CAR X) 'EV$))
;                (TAMEP X)          ; Note the general TAMEP, not the model TAME!
;                (SYMBOLP-TO-NATP-ALISTP WA))
;           (< (+ 1 (WEIGHT1 (CADR (CADR X)) WA))
;              (WEIGHT1 X WA))))

; -----------------------------------------------------------------
; [B] (EV$! X A)                         ; in all calls below, (CONSP X) and
;                                        ;   X is tame!
;  [10]  (APPLY$! 'f args')              ; (CAR X)='f and f has :FN/:EXPR
;                                        ;   formals; see note below

; As explained in the note referenced above, args' is (LIST e_1 e_2
; ... e_n), where n is the arity of f and where e_i is (CADR (NTH i X)) if the
; ith formal of (CAR X) is of ilk :FN/:EXPR and is (EV$! (NTH i X) A)
; otherwise.

; Proof Obligation: We know X is a tame expression, its CAR is 'f, and that f
; has at least one :FN/:EXPR formal.  From tameness we know X is a true-list of
; length 1+n, where n is the arity of f.  We could thus write X as '(f x_1
; ... x_n), where x_i is (NTH i X).  Let m be an i such that x_i is in a
; :FN/:EXPR slot of f and has maximal weight among all :FN/:EXPR x_i.  That is,
; x_m is in a :FN/:EXPR slot and (WEIGHT x_m) is maximal among the :FN/:EXPR
; x_i.  We know x_m exists because f has at least one :FN/:EXPR formal.  From
; tameness we also know that each :FN/:EXPR x_i is of the form (QUOTE ...).
; Thus (WEIGHT (CADR x_m)) is maximal among the weights of (CADR x_i) for
; :FN/:EXPR x_i.

; We must prove

; (L< (APPLY$!-MEASURE 'f args')
;     (EV$!-MEASURE X A))

; The first components are both 0.  The comparisons of the second components is

; (< (MAX (WEIGHT 'f)
;         (IF (FN/EXPR-ARGS 'f args')
;             (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS 'f args')))
;             0))
;    (WEIGHT X))

; But since f has at least one :FN/:EXPR formal, (FN/EXPR-ARGS 'f args') is
; non-nil and (MAXIMAL-WEIGHT (FN/EXPR-ARGS 'f args')) is (WEIGHT (CADR x_m)).
; Thus, the inequality reduces to:

; (< (MAX (WEIGHT 'f)
;         (+ 1 (WEIGHT (CADR x_m))))
;    (WEIGHT X))

; But both f and x_m are proper subtrees of X (and indeed there is at least 1
; cons in X holding f and x_m together!), so (WEIGHT X) dominates the WEIGHTs
; of both (even when we add 1 to that of (CADR x_m)).

; -----------------------------------------------------------------
; [B] (EV$! X A)                         ; in all calls below, (CONSP X) and
;                                        ;   X is tame!
;  [11]  (APPLY$! (CAR X) ...)           ; (CAR X) has no :FN/:EXPR formals

; Proof Obligation: We know x is tame, its car is 'f and thus x is of the form
; (f x_1 ... x_n), where n is the arity of f.  No formal of f has ilk :FN or
; :EXPR.  In this case, (EV$! X A) calls (APPLY$ 'f (EV$-LIST! (CDR X) A)).  We
; must prove

; (L< (APPLY$!-MEASURE 'f (EV$-LIST! (CDR X) A))
;     (EV$!-MEASURE X A))

; As usual, the first components of the measures are 0 and the question is
; decided by the second components with the question:

; (< (MAX (WEIGHT 'f)
;         (IF (FN/EXPR-ARGS 'f (EV$-LIST! (CDR X) A))
;             (+ 1 (MAXIMAL-WEIGHT
;                   (FN/EXPR-ARGS 'f (EV$-LIST! (CDR X) A))))
;             0))
;    (WEIGHT '(f x_1 ... x_j)))

; However, since there are no :FN/:EXPR arguments for f, the FN/EXPR-ARGS
; expression is NIL and the inequality simplifies to

; (< (WEIGHT f)
;    (WEIGHT '(f x_1 ... x_j)))

; which is obviously true.

; -----------------------------------------------------------------
; [D] (f! v_1 ... v_n)
;  [16]  (APPLY$! v ...)                 ; v is a formal of f! of ilk :FN

; Proof Obligation.  In this case, the definition of f! calls APPLY$! on one of
; the {v_1, ..., v_n}, namely v, and v is of ilk :FN.  We know nothing about
; the second argument of that APPLY$!, denoted by the ellipsis in [16].  For
; clarity we replace that ellipsis by a variable z and must prove:

; (L< (APPLY$!-MEASURE v z)
;     (f!-MEASURE v_1 ... v_n)

; If any of the :FN/:EXPR arguments among v_i is not tame, the tameness bit of
; the f!-MEASURE is 1.  But the tameness bit of APPLY$!-MEASURE is 0 and so the
; inequality holds.  Thus, we may assume all :FN/:EXPR v_i are tame!.  Thus, v
; is a tame! function.

; Consider the comparison of the second components.

; (< (MAX (WEIGHT v)
;         (IF (FN/EXPR-ARGS v z)
;             (+ 1 (MAXIMAL-WEIGHT (FN/EXPR-ARGS v z)))
;             0))
;    (max weight-i
;         (max weight-ii
;              weight-iii)))

; Weight-i is the maximum of the WEIGHTs of the :FN/:EXPR elements of {v_1,
; ..., v_n}.  Note that v is in that set and thus (WEIGHT v) <= weight-i.  The
; right hand side above is thus no smaller than (WEIGHT v).

; But since v is tame, (FN/EXPR-ARGS v z) is NIL and the inequality becomes:

; (< (weight v)
;    (max weight-i
;         (max weight-ii
;              weight-iii)))

; which is either true or else the equality holds between the left- and
; right-hand sides.

; In the case of the equality, L< compares the third components, the
; chronological-position of APPLY$ to that of f.  But f's position is always
; strictly larger.

; So the L< holds.

; -----------------------------------------------------------------
; [D] (f! v_1 ... v_n)
;  [17]  (APPLY$! 'x ...)                ; x is a tame! function

; Proof Obligation: We have the preconditions described for case [16] except
; here f is calling APPLY$! on a quoted tame! function, x.

; (L< (APPLY$!-MEASURE 'x z)
;     (f!-MEASURE v_1 ... v_n))

; Because x is tame the situation is much like that above.  The first
; components are both 0, the (FN/EXPR-ARGS 'x z) introduced by expanding
; APPLY$!-MEASURE is NIL, and the comparison of the second components becomes:

; (< (weight 'x)
;    (max weight-i
;         (max weight-ii
;              weight-iii)))

; Here, weight-iii is the maximum of the weights of every quoted object
; occurring in a :FN/:EXPR slot of the body of f and x is one of those objects.
; So again, either the inequality holds or an equality holds and we consider
; the third components.

; But the chronological-position of APPLY$ is smaller than that of f.

; -----------------------------------------------------------------
; [D] (f! v_1 ... v_n)
;  [18]  (EV$ v ...)                     ; v is a formal of f! of ilk :EXPR
;  [19]  (EV$ 'x ...)                    ; x is a tame! expression

; Proof Obligation: These two cases are analogous to [16] and [17] because the
; second component of EV$!-MEASURE is just the weight of the object being
; evaluated, which, here, is either v or 'x.  That is, [18] is like [16] after
; [16] has simplified away the FN/EXPR-ARGS expression, and [19] is analogously
; like [17].

; For example, the comparison of the second components for [18] becomes:

; (< (weight v)
;    (max weight-i
;         (max weight-ii
;              weight-iii)))

; which was proved in [16], and that for [19] becomes

; (< (weight 'x)
;    (max (max weight-i
;         (max weight-ii
;              weight-iii)))
; which was proved in [17].

; -----------------------------------------------------------------
; [D] (f! v_1 ... v_n)
;  [20]  (g! ...)                        ; each :FN/:EXPR actual is a formal
;                                        ;   of f! or a quoted tame! object

; Proof Obligation: This is the case where f! is calling some other G2
; function.  Let g! be of arity m and denote the actuals in the (g! ...) term
; as a_1, ..., a_m.  Every actual in a :FN position of g! is either a :FN
; formal of f! or is a quoted tame function symbol or LAMBDA.  Similarly,
; every actual in an :EXPR position of g! is either an :EXPR formal of f! or a
; quoted tame expression.

; The conclusion of the proof obligation is

; (l< (g!-MEASURE a_1 ... a_m)
;     (f!-MEASURE v_1 ... v_n))

; Consider the first components of the two measures, call them g-bit and f-bit.
; Each depends on the tameness of their respective arguments.  If g-bit < f-bit
; we are done.  If g-bit = f-bit we must consider the other components.  The
; remaining case, g-bit > f-bit, means g-bit = 1 and f-bit = 0, which means
; some :FN/:EXPR actual, a_i, is untame while every :FN/:EXPR v_j is tame.  But
; a_i is either one of {v_1, ..., v_n} or is tame.  So g-bit > f-bit is
; impossible.

; Thus, at worst we must consider the second components of the two measures.

; (< (MAX-INTERNAL-WEIGHT g)
;    (MAX-INTERNAL-WEIGHT f))

; which is

; (< (MAX g-weight-i
;         (MAX g-weight-ii
;              g-weight-iii))
;    (MAX f-weight-i
;         (MAX f-weight-ii
;              f-weight-iii)))

; The meaning of the meta-variables above is as follows:

; g-weight-i: maximal WEIGHT of the :FN/:EXPR actuals among {a_1, ..., a_m}.

; g-weight-ii: maximal WEIGHT of G2 functions other than g called in the body
;              of g

; g-weight-iii: maximal WEIGHT of the quoted tame functions and expressions
;               occurring in :FN/:EXPR slots in the body of g

; We analogously define the ``f-weights.''

; We will show that the left-hand side is weakly dominated by the right-hand
; side.

; Consider g-weight-i.  Note that every object measured in g-weight-i is
; measured either in f-weight-i or f-weight-iii.  In particular, consider an
; object measured in g-weight-i.  That object is in a :FN/:EXPR argument of the
; call of g! and is either a :FN/:EXPR formal of f! or is a quoted tame object.
; If it is a :FN/:EXPR formal of f! it is measured in f-weight-i.  If it is a
; quoted tame object in a :FN/:EXPR position of the call of g! it is measured
; in f-weight-iii because the call of g! occurs in the body of f!.  Thus,
; g-weight-i can be no bigger than the right-hand side above.

; As for g-weight-ii and g-weight-iii, both are strictly smaller than (WEIGHT
; 'g) because they just measure components of the body of g.  But since g! is
; called in f!, (WEIGHT 'g) is among the things measured in f-weight-ii.  Thus,
; g-weight-ii and g-weight-iii can be no bigger than the right-hand side above.

; Thus, the comparison of the second components is, at worst, an equality, and
; we must consider the third components.  But (chronological-position g) is
; strictly less than (chronological-position f).

; -----------------------------------------------------------------
; [D] (f! v_1 ... v_n)
;  [21]  (f! ...)                        ; each :FN/:EXPR actual is the
;                                        ;   corresponding formal of f!

; Proof Obligation: Here f! is calling itself recursively.  Let the actuals of
; the call of f! above be a_1, ..., a_n.  We know that if the v_i has ilk
; :FN/:EXPR then a_i is v_i.  This recursive call is governed by some tests
; whose conjunction we will denote by tst.  The proof obligation for this call
; of f! is

; (IMPLIES tst
;          (L< (f!-MEASURE a_1 ... a_n)
;              (f!-MEASURE v_1 ... v_n)))

; Because the :FN/:EXPR a_i are equal to the corresponding v_i the first three
; components of the two measures are equal and the comparison above can be
; decided by the comparison of the fourth components.  Let the original measure
; function used to admit f be m.  Thus, the conjecture above reduces to

; (IMPLIES tst
;          (O< (m a_1 ... a_n)
;              (m v_1 ... v_n)))

; If this formula involves any G2 function then the call of recursive f! was
; considered marked by the standard doppelganger construction and thus the
; concluding O< comparison is one of the tests governing the recursive call.
; Hence, the formula trivially holds.

; Otherwise, up to the renaming of G1 functions to their doppelgangers, the
; formula is identical to the measure conjecture proved for the corresponding
; call of f when f was admitted.  But the doppelganger of each G1 function is
; defined identically to its counterpart except for renaming, so the formula is
; a theorem here too.

; -----------------------------------------------------------------
; Q.E.D.
; -----------------------------------------------------------------
;

(defun apply$-lambda (fn args)

; Keep this in sync with the logical definition (as noted below), which is in
; apply.lisp.  The present definition is the one that will be installed in
; ACL2, because of the inclusion of apply$-lambda in
; *boot-strap-pass-2-acl2-loop-only-fns*.

  (declare (ftype (function (t t) (values t))
                  ev$))
  (let ((compiled-version ; see the Essay on the Compiled-LAMBDA Cache
         (and *aokp*
              *allow-concrete-execution-of-apply-stubs*
              (compile-tame-compliant-unrestricted-lambda fn))))
    (when compiled-version
      (return-from apply$-lambda
                   (let ((arity (length (cadr fn))))
                     (apply compiled-version
                            (if (= arity
                                   (length args))
                                args
                              (take arity args)))))))

; Warning: Keep the code below in sync with the logical definition of
; apply$-lambda.

  (ev$ (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
       (ec-call
        (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                  args))))

