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

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

; See the Essay on the APPLY$ Integration in apply-prim.lisp for an overview.
; This file supports top-level execution of apply$ by implementing the crucial
; executable functions attached to badge-userfn and apply$-userfn.  We proceed
; in four main steps:

; * define doppelganger-badge-userfn, which will be attached to badge-userfn

; * define doppelganger-apply$-userfn, which will be attached to apply$-userfn

; * optimize apply$-lambda with compilation and caching

; * Essay on Admitting a Model for Apply$ and the Functions that Use It, the
;   full version of the proof sketched in the paper ``Limited Second Order
;   Functionality in a First Order Setting''

; The two doppelganger- functions mentioned above are actually partially
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
;      (badge-userfn doppelganger-badge-userfn)
;      (apply$-userfn doppelganger-apply$-userfn)
;      :hints
;      (("Goal" :use (doppelganger-badge-userfn-type
;                     doppelganger-apply$-userfn-takes-arity-args))))
;    (value :q)
;    (defun apply$-lambda (fn args) (concrete-apply$-lambda fn args))
;    (setq *allow-doppelganger-execution-of-apply-stubs* t)
;    (lp)
;    (quote (end of rubric))

;  Because The Rubric requires you execute a form in raw Lisp, The Rubric
;  eliminates the soundness guarantees provided by the ACL2 implementors!

; End of Historical Note

; -----------------------------------------------------------------

; In the days when The Rubric was necessary, the raw lisp variable
; *allow-concrete-execution-of-apply-stubs* (which we would now call
; *allow-doppelganger-execution-of-apply-stubs*) told us whether it had been
; executed.  Later, we just set that variable to t.  Since then (after
; Version_8.0) we have eliminated that variable.

(defun query-badge-userfn-structure (fn wrld)

; We determine whether fn is badged and whether it is warranted.  We return (mv
; bad-fn-msg badge warrantp) where bad-fn-msg is either nil or a message that
; explains that fn is not a known function or else has not been badged.  If
; bad-fn-msg is nil, then badge is the badge and warrantp indicates whether fn
; has a warrant.

; This function is a gatekeeper for the execution of badge-userfn and
; apply$-userfn (q.v.).

; It is important that if this function returns a non-nil badge a world then it
; returns that same answer for all extensions of the world!  The guard on the
; badge table, badge-table-guard, guarantees this invariant.

; Programming Note: This function assumes fn is being used as a ``userfn,''
; i.e., by badge-userfn or apply$-userfn.  It fails to answer correctly if, for
; example, fn is CONS or APPLY$.  Use executable-badge if you want to answer
; the question ``does fn have a badge?''  This function differs from the more
; primitive get-badge, get-warrant, and get-warrant-and-badge by virtue of
; checking that fn is a known function symbol.

  (cond
   ((not (symbolp fn))
    (mv (msg "~x0 is not a symbol" fn)
        nil nil))
   ((not (function-symbolp fn wrld))
    (mv (msg "~x0 is not a known function symbol" fn)
        nil nil))
   (t
    (mv-let (badge warrantp)
      (get-badge-and-warrantp fn wrld)
      (cond
       ((null badge) ; fn is a function symbol with no badge assigned
        (mv (msg "~x0 has not been badged" fn)
            nil nil))
       (t (mv nil badge warrantp)))))))

; The (extensible) attachments for badge-userfn and apply$-userfn are
; doppelganger-badge-userfn and doppelganger-apply$-userfn.  They will be
; attached to badge-userfn and apply$-userfn to extend the evaluation theory
; appropriately.  See the defattach event at the end of apply.lisp.  We define
; the two doppelganger- functions below.

; Because we want to implement their bodies in raw Lisp, we would like to
; introduce them with defun-overrides commands like

; (defun-overrides doppelganger-badge-userfn (fn) ...)
; (defun-overrides doppelganger-apply$-userfn (fn args) ...)

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
; (defun-overrides doppelganger-badge-userfn (fn) ...)
; ==>
;  (assert (member 'state formals :test 'eq))
(progn (push 'doppelganger-badge-userfn *defun-overrides*) ; see add-trip

; The next two items are pushed to the left margin so they get picked up by
; etags.  But they're really part of the progn!

; The following defun has two notes in it which are given afterwards.

(defun doppelganger-badge-userfn (fn)

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.

  (cond
   ((and (null *aokp*) ; See Note 1.
         (null *warrant-reqs*))
    (throw-raw-ev-fncall ; See Note 2.
     (list* 'ev-fncall-null-body-er
            nil
            'doppelganger-badge-userfn
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

   (t

; We know either *aokp* = t (meaning we are in the evaluation theory) or else
; *aokp*=nil and *warrant-reqs* is non-nil (meaning we're in the prover and
; warrants are required).

      (mv-let (bad-fn-msg badge warrantp)
        (query-badge-userfn-structure fn (w *the-live-state*))

; Note:  If bad-fn-msg is nil then we know fn has a badge and badge is it.

        (cond
         ((and (null bad-fn-msg)    ; there is a badge and either we're in the
               (or *aokp* warrantp)); evaluation theory or fn has a warrant
          (or (not warrantp)
              (maybe-extend-warrant-reqs fn nil 'badge-userfn))
          badge)
         (t (throw-raw-ev-fncall
             (list* 'ev-fncall-null-body-er
                    nil

; See the comment under the second throw-raw-ev-fncall in
; doppelganger-apply$-userfn, for why we assume here that this call has come
; from badge-userfn.

                    (msg "The value of ~x0 is not specified on ~x1 because ~
                          ~@2."
                         'BADGE-USERFN
                         fn
                         (cond (bad-fn-msg bad-fn-msg)
                               (t (msg "~x0 has not been warranted"
                                       fn))))
                    (print-list-without-stobj-arrays
                     (list fn))))))))))

; Notes on DOPPELGANGER-BADGE-USERFN

; Note 1. on the test of *aokp*: We once thought that it was unnecessary to
; test *aokp* in doppelganger-badge-userfn.  The (faulty) reasoning was that
; doppelganger-badge-userfn is the attachment for badge-userfn.  We wouldn't be
; running doppelganger-badge-userfn if attachments weren't ok.  The flaw in
; that reasoning is that doppelganger-badge-userfn is itself a :logic mode
; function and might be called directly by the user at the top level of the
; ACL2 loop, or used in some other function used in proofs or hints.  So we
; might find ourselves executing doppelganger-badge-userfn even though *aokp*
; is nil.  We need for it to act undefined when *aokp* is nil.  This same
; reasoning applies to doppelganger-apply$-userfn.  More recently, however, we
; have made doppelganger-badge-userfn untouchable; thus, we could now remove
; the *aokp* test.  (The issue for the *warrant-reqs* test is similar.)  But
; for now, at least, we'll leave this *aokp* test, mainly to protect against
; inappropriate execution if untouchability is removed, but with the bonus that
; this test provides extra protection in case our thinking here is flawed!

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

; End of Notes on DOPPELGANGER-BADGE-USERFN

(defun-*1* doppelganger-badge-userfn (fn)
  (doppelganger-badge-userfn fn))

; End of progn from ``defun-overrides''
)

; Essay on a Misguided Desire for Erroneous APPLY$s to Print Exactly the
; Same Error Messages whether Evaluation of APPLY$ Stubs is Supported or Not

; One possible objection to our handling of errors in doppelganger-badge-userfn
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

(defun maybe-extend-warrant-reqs (fn args caller)

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.

; This function is evaluated only for side effect, to update *warrant-reqs* as
; appropriate to reflect the need for a true warrant on fn when applying fn to
; args.  Caller is used only in an error message (which quite possibly nobody
; will see), to reflect that caller, which is apply$-userfn or badge-userfn as
; of this writing.

; See *warrant-reqs* for a description of the values of that variable, which
; should serve to explain the code below.

  (let ((warrant-reqs *warrant-reqs*)) ; bind the special, for efficiency
    (cond ((null warrant-reqs) nil)
          ((eq t warrant-reqs)
           (setq *warrant-reqs* (list fn)))
          ((eq :nil! warrant-reqs)
           (setq *warrant-reqs* fn) ; the function responsible for the abort
           (throw-raw-ev-fncall
            (list* 'ev-fncall-null-body-er
                   nil
                   (msg "The value of ~x0 is not specified on ~x1 because the ~
                         use of warrants is not permitted in this context."
                        caller fn)
                   (print-list-without-stobj-arrays
                    (list fn args)))))
          ((symbolp warrant-reqs) ; invalid value for *warrant-reqs*
           (er hard! 'maybe-extend-warrant-reqs
               "Implementation error: *warrant-reqs* has an input value of ~
                ~x0."
               warrant-reqs))
          ((member fn warrant-reqs :test #'eq) nil)
          (t (push fn *warrant-reqs*)))))

; Here is the STATE-free expansion of
; (defun-overrides doppelganger-apply$-userfn (fn args) ...)
; ==>
;  (assert (member 'state formals :test 'eq))
(progn (push 'doppelganger-apply$-userfn *defun-overrides*) ; see add-trip

; The next two items are pushed to the left margin so they get picked up by
; etags.  But they're really part of the progn!

(defun raw-apply-for-badged-fn (fn arity args)
  (cond
   ((and (eq (symbol-class fn (w *the-live-state*)) :program)
         (not (f-get-global 'safe-mode *the-live-state*)))
    (state-free-global-let*
     ((safe-mode t))
     (apply (*1*-symbol fn)
            (if (= arity (length args))
                args
                (take arity args)))))
   (t (apply (*1*-symbol fn)
             (if (= arity (length args))
                 args
                 (take arity args))))))

(defun doppelganger-apply$-userfn (fn args)

; See the Essay on Evaluation of Apply$ and Loop$ Calls During Proofs.

  (cond
   ((and (null *aokp*) ; See Note 1.
         (null *warrant-reqs*))
    (throw-raw-ev-fncall ; See Note 2.
     (list* 'ev-fncall-null-body-er
            nil
            'doppelganger-apply$-userfn
            (print-list-without-stobj-arrays
             (list fn args)))))
   (t (mv-let (bad-fn-msg badge warrantp)
        (query-badge-userfn-structure fn (w *the-live-state*))
        (cond
         ((or bad-fn-msg ; no badge for fn, or there is a badge but we're in
              (and (null *aokp*) ; prover (so warrants are required) but fn
                   (not warrantp))) ; has no warrant
          (throw-raw-ev-fncall
           (list* 'ev-fncall-null-body-er
                  nil

; The following message assumes that we got here by way of a call to
; apply$-userfn.  Since doppelganger-apply$-userfn is untouchable, that must be
; the case unless the user has changed that, in which case the error message
; below might be confusing -- but surely nobody should remove untouchability of
; doppelganger-apply$-userfn!  See the Essay on Memoization with Attachments.

                  (msg "The value of ~x0 is not specified on ~x1 because ~@2."
                       'APPLY$-USERFN fn
                       (cond (bad-fn-msg bad-fn-msg)
                             (t (msg "~x0 has not been warranted"
                                     fn))))
                  (print-list-without-stobj-arrays
                   (list fn args)))))

; If we get here we know that fn has a badge and that either *aokp* is true (so
; no warrants are necessary) or fn has a warrant.

         ((eq (access apply$-badge badge :ilks) t)
          (or (not warrantp)
              (maybe-extend-warrant-reqs fn args 'apply$-userfn))
          (if (int= (access apply$-badge badge :out-arity) 1)
              (raw-apply-for-badged-fn fn
                                       (access apply$-badge badge :arity)
                                       args)
            (multiple-value-list
             (raw-apply-for-badged-fn fn
                                      (access apply$-badge badge :arity)
                                      args))))
         ((concrete-check-apply$-hyp-tamep-hyp
           (access apply$-badge badge :ilks)
           args
           (w *the-live-state*))
          (or (not warrantp)
              (maybe-extend-warrant-reqs fn args 'apply$-userfn))
          (if (int= (access apply$-badge badge :out-arity) 1)
              (raw-apply-for-badged-fn fn
                                       (access apply$-badge badge :arity)
                                       args)
            (multiple-value-list
             (raw-apply-for-badged-fn fn
                                      (access apply$-badge badge :arity)
                                      args))))
         (t
          (throw-raw-ev-fncall
           (list* 'ev-fncall-null-body-er
                  nil

; See a comment above about a corresponding msg in the previous
; throw-raw-ev-fncall.

                  (msg "The value of ~x0 is not specified when the first ~
                        argument, fn, is ~x1, and the second argument, args, ~
                        is ~x2.  Fn has badge ~x3 and args is not known to ~
                        satisfy the tameness requirement of that badge."
                       'APPLY$-USERFN fn args badge)
                  (print-list-without-stobj-arrays
                   (list fn args))))))))))

(defun-*1* doppelganger-apply$-userfn (fn args)
  (doppelganger-apply$-userfn fn args))

; End of progn from ``defun-overrides''
)

; What we've described so far is adequate to run APPLY$ and EV$ forms in the
; evaluation theory after attaching the ``doppelgangers'' of badge-userfn and
; apply$-userfn for the current world to those critical functions.

; Now we turn to the optimization of APPLY$-LAMBDA.  The following is provable:

; (equal (apply$-lambda fn args)
;        (ev$ (lambda-object-body fn)
;             (pairlis$ (lambda-object-formals fn)
;                       args)))

; Indeed, it is apply$-lambda-opener in books/projects/apply/base.lisp.
; The *1* version of apply$-lambda is what we call apply$-lambda-logical,
; essentially defined as the right-hand side of the equation above: interpret
; the body with ev$ under the alist binding the formals to the actuals.

; But we wish to apply certain lambdas more efficiently in the evaluation
; theory by executing compiled code after checking guards.  As noted in the
; Essay on Lambda Objects and Lambda$, we have an elaborate cache that stores
; lambda objects seen (or perhaps likely to be seen) by apply$-lambda and
; associates critical information with them like whether they are well-formed
; and Common Lisp compliant (``guard verified'') and the compiled versions of
; them and their guards.  Below is the Essay on the CL-Cache Implementation
; Details that is more precise than the earlier essay cited above.


; Essay on the CL-Cache Implementation Details

; The cl-cache (compliant lambda cache) is a raw Lisp, not ACL2, structure that
; stores (by default) the 1000 most recent LAMBDA-expressions applied in this
; session.  Technically, *cl-cache* is a defrec triple consisting of a size, a
; circular alist, and a pointer to the ``last'' cell in the alist before it
; closes the loop.  But intuitively it is just an alist whose maximum size is
; as given but whose virtual size is the number of entries from the beginning
; to the first nil.  The circularity gives us an extremely efficient way to add
; new entries at the front without consing.  This abstract view of the
; *cl-cache* is violated in a very important way: the *cl-cache* is intially a
; natural number greater than 2 that is the size of the circular alist.  The
; first time we need to add a lambda to the cache we allocate the full
; structure.

; To clear the *cl-cache* just set it to the desired size with (setq *cl-cache*
; k).  Initially, k=1000.  [It might be better to implement a function for
; initializing the cache to a new size.  Better yet, we could make that
; function available to the user in the loop; see the TODO on this, below.]

; The alist basically associates information with lambda objects.  Whenever we
; search the alist for a given lambda and exhaust the virtual alist (i.e., hit
; a nil) we can re-use that link in the alist to create a new first cell for
; the lambda we looked for.

; We now confine our discussion to the structure and use of each line.

; Each cl-cache line consists of a defrec with the following fields.  WARNING:
; The fields in this raw Lisp defrec are destructively updated!

; - :lambda-object is a lambda object (not necessarily well-formed)

; - :status is a keyword token that explains how to interpret the line;
;    the status is one of :GOOD, :BAD, :UGLY, or :UNKNOWN.

;    :GOOD means the lambda-object is well-formed and Common Lisp compliant in
;     the current world

;    :BAD means the lambda-object is not well-formed or not Common Lisp
;     compliant in the current world, but that (with high probability) there is
;     a world in which it is well-formed and compliant

;    :UGLY means the lambda-object is so ill-formed it can never be :GOOD

;    :UNKNOWN means that we do not know the status of this object in the
;     current world and leave it to apply$-lambda to determine.

; - :absolute-event-number is the max-absolute-event-number of the world in
;    which the guards were proved and thus the world in which the line became
;    :GOOD.  If the line's status is not :GOOD, the :absolute-event-number is
;    nil.

; - :extracts is a list of splo-extracts-tuples that allows us to re-check
;    well-formedness and guard verification without re-parsing the lambda
;    expression

; - :problem is an object that indicates why the :status isn't :GOOD

; - :hits is the number of times we have fetched this line

; - :guard-code is the compiled code for (LAMBDA formals guard) or nil

; - :lambda-code is the compiled code of lambda-object or nil

; Generally speaking, apply$-lambda does the work to correctly set the status
; of a cache line when the line's lambda-object is applied.  The resultant
; status set by apply$-lambda is always :GOOD, :BAD, or :UGLY.  We give more
; details below.  But whenever a lambda object is guard verified, either by
; apply$-lambda (where proofs are limited to Tau), the guard verification of a
; defun containing the object, or because verify-guards was called explicitly
; on the object, a :GOOD cache line is set up.  However, every time the world
; is extended, the status of every :BAD line is set to :UNKNOWN because, who
; knows, perhaps the formerly :BAD object is :GOOD in this new world.  Every
; time the world is retracted, the status of every :GOOD line is set to
; :UNKNOWN if its :absolute-event-number is greater than the max such number in
; the retracted world, for symmetric reasons.

; We now describe how apply$-lambda handles the lambda object it is given.
; Some objects reaching apply$-lambda carry a special mark, *lambda$-marker*,
; as described in the Essay on Lambda Objects and Lambda$.  These objects are
; not actually lambda objects but marked untranslated lambda$ expressions.
; Using the lambda$-alist, apply$-lambda converts these objects to lambda
; objects.  Next, apply$-lambda fetches (or creates and adds) the cache line
; for the object.  Thereafter, its actions depend on the status of the line.

; In the discussion below:

; - w is understood to be the current world for the apply$-lambda

; - ``Run *1*'' means use *1*apply$-lambda to apply the :lambda-object to the
;    actuals

; - ``Run code'' means use raw Lisp's apply to run the compiled :guard-code on
;   the actuals to the apply$-lambda.  If the guard-code succeeds, use raw
;   Lisp's apply to run the :lambda-code on the actuals.  If the :guard-code
;   fails, run *1*.

; :GOOD - the :lambda-object is well-formed and guard verified in w: run code.

; :BAD - the :lambda-object was (probably) once known to be well-formed and
;        Common Lisp compliant in some world but not in w; (the ``probably''
;        comes from the possibility that guard obligations are unprovable,
;        i.e., contradictory, in which case it would have been better to assign
;        status :UGLY but we don't try to do that!): run *1*

; :UGLY - the :lambda-object is hopelessly ill-formed: run *1*.

; :UNKNOWN - work to establish a proper status (:GOOD or :BAD) in w for this
;         object and then apply the object as appropriate for that new status.

; The ``work to establish'' :GOOD or :BAD status is as follows.  A quick check
; is to see whether the :lambda-object is on common-lisp-compliant-lambdas of
; w.  If so, its status is :GOOD and we're done.  If not, we first check
; whether the object is well-formed in w.  This can be done more efficiently
; than might at first appear since we know the object had status :GOOD or :BAD
; in some other world and hence is basically the right shape.  The :extracts of
; the cache line give us the relevant TYPE expressions, guards, and bodies
; without having to re-parse the object.  (:Extracts is a list of
; splo-extracts-tuples extracted from the lambda object and from every lambda
; object within it.)  We basically make termp checks on these components,
; additionally checking Common Lisp compliant symbol-classes for the functions
; involved in the guard and body, and tameness of the body.  Provided these
; checks succeed we generate the guard obligations of the :lambda-object and we
; attempt to prove them with the Tau System.  If this succeeds the object is
; :GOOD, otherwise it is :BAD.

; The algorithm sketched above is implemented by fetch-cl-cache-line.

; Through Version-8.1, the cache management generated warnings about whether we
; were running *1* apply$-lambda, i.e., Slow APPLY$ Warning.  There was a
; rather subtle use of eq versus equal that allowed us to keep these warnings
; to a minimum when the very same lambda was repeatedly applied as by a mapping
; function.  This version does not issue warnings.  We decided instead to
; provide the raw Lisp function print-cl-cache (with a :logic mode interface)
; to print out the cache.  If the user experiences poor performance he or she
; can inspect the cache for :BAD or :UGLY lambdas with high hit counts and look
; at the :problem field of the relevant lines to see what's wrong with each
; expensive lambda.

; Lines are kept in access order, most recent first.  The first line in the
; sequence that is nil indicates that subsequent lines are irrelevant.  We
; actually arrange that all subsequent lines are also nil, but that is probably
; not important.

; We handle the possibility of interrupts rendering the cache inconsistent.
; Here is how: Before we modify the cache we render the global cache invalid
; (by setqing it to its size) and restore the global cache only when
; modification is complete.

; Specifically, imagine that a cache manipulation is interrupted and aborted by
; ctrl-c or an error.  The cache is left invalid.  The next time we attempt to
; manipulate the cache we will re-initialize it.  All old caching is lost.

; For efficiency, we often destructively modify the cache.

; History of the cl-cache

; When we first started working on optimizing apply$-lambda in late 2017 for
; release with Version_8.0 in December, we considered four alternatives:

; (a) Do Nothing: Let ACL2 behave normally by running the *1* code for
; APPLY$-LAMBDA, which just interprets the lambda-body with EV$.

; (b) Compile but Don't Cache: recognize and compile unrestricted lambdas every
; time they're applied but do not cache the test or compilation results.  Note:
; Version_8.0 did not support declarations in lambda objects and hence all
; lambda objects were considered to have a guard of T, hence the term
; ``unrestricted lambda.''  Clearly, the hope behind this approach was that the
; increased speed of executing compiled code overcomes the cost of recognition
; and compilation.

; (c) Fast-Alist Cache: recognize and compile unrestricted lambdas, caching
; recognized lambdas with their compiled code via a fast-alist.  Finding a
; lambda in the cache means it satisfies the ``variety of important
; properties'' and gives us its compiled version.  Lambdas without those
; properties are cached separately to avoid having to recognize them again.

; (d) Home-Grown Cache: Like (c) except we rolled our own cache.

; Experiments with all four scenarios are detailed in a long comment below
; under the name Historical Essay on the Performance of APPLY$.  An executive
; summary of those experiments is: Our Fast-Alist cache has performed about 50%
; slower than our Home-Grown cache.  The Do Nothing and the Compile but Don't
; Cache approaches are much worse.  But many things affect performance.
; Choosing the best implementation depends on the expected size of the LAMBDAs,
; whether unrestricted LAMBDAs occur frequently enough to matter, frequency of
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

; See the Historical Essay on the Performance of APPLY$ for details of our
; original experiments with designs (a)-(d).

; Two severe disadvantages of our original Home-Grown Cache were that it
; maintained only 3 cache lines (i.e., was capable of remembering only three
; compiled lambdas) and was cleared every time the world changed.
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

; After considering design options (a)-(d) mentioned above we moved to a
; structure that contains 1000 cache lines (by default, but any size of at
; least 3 is acceptable) arranged as a ring.  The clever thing about the
; ring-based cache is a destructively modified ring of lines.  This allowed the
; most recently added/hit entry to always be at the ``front'' and the rest of
; the entries ordered the same as before.  But the content of a ``line'' has
; evolved considerably as we added declarations to lambda objects.

; In the earliest implementations, a line was just a pair consisting of an
; unrestricted (implicit :guard of t) lambda object and its compiled
; counterpart.  With the introduction of declare into lambda objects it was
; advantageous for the cache to contain parts of the lambda object -- e.g., one
; example TYPE expression, (p X), for each (TYPE (SATISFIES p) ...); the guard
; term; and the body term -- to make it faster to check well-formedness.  In
; the first such elaboration, each line contained a status (:GOOD, :BAD, or
; :UGLY) and a logical world, w, with the meaning that the status was known to
; be accurate in that logical world.  When apply$-lambda accessed the cache
; line for a lambda object it would check whether the current world was an
; extension of w and, if so, a :GOOD status meant the object was well-formed
; and compliant in the current world.  However, if the current world was not an
; extension of w, the status had to be recomputed.  The status of :BAD objects
; had to be recomputed every time a world different from w was seen.  :GOOD
; objects whose guard was true on the actuals were applied by running compiled
; code; :BAD objects were run by interpreting the body using *1* apply$-lambda
; (i.e., apply$-lambda-logical).  :UGLY lambdas were so ill-formed they could
; never be good.

; The main motivation for the :GOOD/:BAD idea was in an example like (map
; '<obj> '(x1 x2 ...)), where <obj> was :GOOD in the line's world, w, but w was
; not an extension of the world in which the apply$-lambda was called.  In this
; case, the attempt to apply$-lambda <obj> to x1 would reset the :status to
; :BAD (if indeed, <obj> was not well-formed and compliant in the current
; world) ans set the line's world to the current world; then when <obj> was
; applied to x2, no additional checks were made: <obj> is :BAD in the world of
; the line and *1* apply$-lambda was used.

; But we didn't like this structure because it forced us to save up to 1000
; worlds, possibly hanging on to much garbage; in addition, it required testing
; whether one world is an extension of another every time we applied a lambda
; object.  (In truth, we never tested this design extensively.  In fact, most
; worlds stored in the cache are almost certainly just tails of the current
; world and the test for extension was pretty fast because we reset the stored
; world to the current world whenever the test succeeded so that subsequent
; extension tests succeeded immediately.  But we just thought the design
; inelegant.)

; Thus, we adopted a different scheme in use as of this writing (Fall, 2018).
; There are no worlds stored in lines and the status flag, :GOOD, :BAD, :UGLY,
; and :UNKNOWN, is always accurate with respect to the current world.  This
; forces us to manipulate the cache a little bit on every world extension
; (e.g., defthm) or retraction (e.g., :ubt).  On extensions, we change every
; :BAD to :UNKNOWN; on retractions we turn some :GOOD lines to :UNKNOWN.
; Whenever apply$-lambda sees an object of :UNKNOWN status is updates the
; status to the current world.

; As of this writing we have not benchmarked our ring-based cache since we
; moved to support declarations in lambda objects and we elaborated cache lines
; from pairs to defrecs.  The reason is pretty compelling: we had no choice but
; to move to a more elaborate cache line to support non-trivial guards and
; their apply-time guard verification and guard checking.  As the design has
; evolved it got harder to compare it to old designs because, for example,
; we'll see a slowdown on every world extension and retraction whether apply$
; is involved or not.  The cache size and the complexity of the guards and
; guard verification proofs also affects timing.  So our current thinking is
; simply: build the best cache we can imagine, get LOOP working (it's not part
; of the system as of Fall, 2018) solve the ``LOOP guard verification'' problem
; (see below), and then test to see if the cache is adequate.

; [end of history]

; A Collection of TODOs related to Compilation and Caching

; TODO: Because of the uncertainty regarding how mapping functions will
; actually be used, it might be worthwhile to implement a user-settable flag
; that specifies whether and how APPLY$-LAMBDA is cached.  Scenarios (a), (c),
; and (d) above immediately come to mind as optimal depending on usage.

; TODO: Perhaps we should implement a better way to reset or clear the cache.
; Right now, we just tell the user to drop into raw Lisp and set *cl-cache* to
; a number (at least 3) that is the new size.  This clears the cache and allows
; it to be reallocated (upon the first fetch from it) to the given size.  But
; perhaps it would be better to provide a function for extending or retracting
; the cache size while preserving the contents or clearing it.  Such a function
; is akin to cl-cache-init and we left a comment there: ``We considered making
; this function available to the user.  However, it seemed a bad idea to allow
; this to be run inside a book (via make-event) and thus affect the rest of the
; session.''  So think about this before giving the user a more sophisticated
; way to grow the cache.

; TODO: As noted in the Essay on Lambda Objects and Lambda$, it is possible for
; a good looking lambda object to have unprovable guard conjectures and thus be
; classed as :BAD, causing us to try to prove the conjectures every time the
; lambda is applied after an extension.  It would be cheaper to classify the
; object as :UGLY but that requires solving the decidability problem.  However,
; we could change the meaning of :UGLY from ``:GOOD in no possible world'' to
; ``we've given up trying to prove it :GOOD.''  We could then switch :BAD to
; :UGLY on, say, the 10th unsuccessful try to prove the guards.  We could set
; the :problem to something informative like, :GIVEN-UP-TRYING-TO-
; VERIFY-GUARDS.  This just dooms the object to be applied with *1*
; apply$-lambda.  If the user noticed the problem and knew how to prove the
; guards he or she could use verify-guards to set the :status to :GOOD.

; TODO: Solve the LOOP guard verification problem!  Under some conditions (SUM
; 'fn lst) could be replaced, under the hood in raw Lisp, by (LOOP FOR X IN lst
; SUM (fn X)).  Note that execution of the LOOP version of our (sum lambda
; *million*) test is 10 times faster than Scenario (d).

; But this requires knowing that every element of lst satisfies the guard of fn
; and that under those conditions fn always returns a number.  Those two
; statements about fn and lst constitute what might be called the ``proper
; guard for SUM.''  Otherwise, fn has to check its guard on every element of
; lst, and SUM has to check that the output of fn is a number before summing it
; into the answer.

; So perhaps the proper guard for (SUM fn lst) is something like:

; (and (tame-fn-of-n-args fn 1)                           ; [1]
;      (all (guard-of-fn fn) lst)                         ; [2]
;      (implies (apply$ (guard-of-fn fn) (list x))        ; [3]
;               (acl2-numberp (apply$ fn (list x)))))

; where [1] says fn is a tame function of 1 argument, [2] says that every
; element of lst satisfies the guard of fn, and [3] says when the guard of fn
; holds on its input, fn returns a number.  Of course, the shocking thing about
; this guard is that it presumes we have a function, here named guard-of-fn,
; that can take a function or lambda object and return its guard as a lambda
; object.  This is akin to the kind of information about functions only
; accessible via warrants and so suggests an extension of badges to contain
; guard objects.  Furthermore, we somehow have to know these guard objects are
; guard verified and themselves have a guard of T.

; But if some instance of (sum fn lst) were known to satisfy the proper guard,
; we could replace (sum fn lst) by the obvious loop statement in raw Lisp.

; Other problems that come up in trying to solve the LOOP guard verification
; problem are

; (a) How do you check a guard like that shown above?  [1] is easy, [2] might
; require running the guard on every element of lst, which might not be any
; faster than what we do now, and [3] contains a free variable, x, and is
; probably ``checked'' by proof rather than evaluation.

; (b) We'd need strategies for proving and using these quantified hypotheses.
; The obvious strategy is something like pick-a-point.  If you want to prove
; (all p lst), then prove (implies (member e lst) (p e)).

; (c) Not every mapping function visits every element of the domain over which
; it is mapping.  There is a sense in which the function named all above is a
; McCarthyesque ``derived function'' from sum.  But perhaps if the goal is only
; to replace certain mapping functions by certain LOOP statements we just build
; in the proper guard for each built-in optimized mapping function and forget
; about how to figure out the proper guard in general!

; TODO: Consider adding a cache for apply$ on symbols.  What has to happen for
; (apply$ 'sym args) to run in the evaluation theory?

; - We need apply$ to reduce to apply$-userfn.
; - We need to look up the attachment of apply$-userfn, to get
;   doppelganger-apply$-userfn, which amounts to evaluating special
;   variable (attachment-symbol apply$-userfn) =
;   ACL2_*1*_ACL2::APPLY$-USERFN (see throw-or-attach).
; - Apply$-userfn calls doppelganger-apply$-userfn.
; ... then, looking at the defun of doppelganger-apply$-userfn:
; - We need to look up the value of special variable *aokp*.
; - We need to compute query-badge-userfn-structure.
; - We need to call apply.
;
; Maybe we can install a cache on apply$-userfn (or its concrete counterpart?)
; to short-circuit a lot of this?

; [end of todos]

; Here is our cache structure.  The value of our global cache variable
; (*cl-cache*, introduced further below) is either such a structure or else is
; an integer, greater than 2, representing the intended size of such a
; structure.

(defrec cl-cache

; Warning: Keep this in sync with access-cl-cache.

; Invariants on the fields include:

; - :Size is a positive integer.

; - :Alist is a circular list that repeats after :size elements; each of its
;   elements is a cl-cache-line record (see below) or nil; and for 0 <= i < j <
;   size, if (nth i alist) = nil then (nth j alist) = nil.

; - :Last is (nthcdr (1- size) alist).

; Note that :size and :last are constant fields for a given cl-cache.  However,
; the cdr of :last can change.

;  car   cadr   cddr
  (alist size . last)
  t)

(defmacro access-cl-cache (c field)

; Keep this in sync with the defrec for cl-cache.

; We are going to destructively update the fields in the cl-cache.  This macro
; allows us to write

; (setf (access-cl-cache c :alist) val)

; It would have been nice to use ACL2's access macro

; (setf (access cl-cache c :alist) val)

; but that expands to a LET with the car/cdr nest inside and setf cannot handle
; it.

  (case field
    (:alist `(car ,c))
    (:size `(cadr ,c))
    (:last `(cddr ,c))
    (otherwise (er hard 'access-cl-cache "Illegal field name, ~x0." field))))

(defrec cl-cache-line

; Warning: Keep this in sync with access-cl-cache-line!

; Invariants on the fields include
; - :lambda-object is a lambda object (not necessarily well-formed)
; - :status is a keyword token that explains (below) how to interpret the line
; - :absolute-event-number is nil or a number.  This entry is a number iff the
;    status is :GOOD and the number is the greatest absolute-event-number of
;    the world at the time the line was detected as :GOOD.
; - :extracts is a list of splo-extracts-tuples that allows us to re-check
;    well-formedness and guard verification without re-parsing the lambda
;    expression
; - :problem is an object that indicates why the :status is :BAD
; - :hits is the number of times we have fetched this line
; - :guard-code is the compiled code for (LAMBDA formals guard)
; - :lambda-code is the compiled code of the :lambda-object

;     caaar         cdaar      cadar                    cddar
  (((lambda-object . status) . (absolute-event-number . extracts))
   .
   ((problem . hits) . (guard-code . lambda-code)))
 ;   caadr    cdadr     caddr      .  cdddr

  t)

(defmacro access-cl-cache-line (line field)

; Warning:  Keep this macro in sync with the record declaration cl-cache-line!

; We are going to destructively set the fields in cl-cache-line records.

  (case field
    (:lambda-object `(caaar ,line))
    (:status `(cdaar ,line))
    (:absolute-event-number `(cadar ,line))
    (:extracts `(cddar ,line))
    (:problem `(caadr ,line))
    (:hits `(cdadr ,line))
    (:guard-code `(caddr ,line))
    (:lambda-code `(cdddr ,line))
    (otherwise
     (er hard 'access-cl-cache-line "Illegal field name, ~x0." field))))

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
          :alist alist
          :size size
          :last last)))

(defun cl-cache-size (cl-cache)

; Cl-cache can be a cl-cache record or the most recent size of a *cl-cache*
; record.

  (cond
   ((consp cl-cache)
    (access cl-cache cl-cache :size))
   (t (assert (natp cl-cache))
      cl-cache)))

(defun prettyify-splo-extracts-tuples (extracts)
  (cond
   ((endp extracts) nil)
   (t (cons `(splo-extracts-tuple
              :gflg ,(access splo-extracts-tuple (car extracts) :gflg)
              :satisfies-exprs
              ,(access splo-extracts-tuple (car extracts) :satisfies-exprs)
              :guard ,(access splo-extracts-tuple (car extracts) :guard)
              :body ,(access splo-extracts-tuple (car extracts) :body))
            (prettyify-splo-extracts-tuples (cdr extracts))))))

(defun print-cl-cache-line (i line)

; Line is assumed to be the (non-nil) cl-cache-line record at position i in the
; alist.

  (let ((lambda-object (access cl-cache-line line :lambda-object))
        (status (access cl-cache-line line :status))
        (absolute-event-number
         (access cl-cache-line line :absolute-event-number))
        (extracts (access cl-cache-line line :extracts))
        (problem (access cl-cache-line line :problem))
        (hits (access cl-cache-line line :hits))
        (guard-code (access cl-cache-line line :guard-code))
        (lambda-code (access cl-cache-line line :lambda-code)))
    (cw "(~c0. :lambda-object ~y1
          ~t2:status         ~x3
          ~t2:abs-event-no   ~x4
          ~t2:extracts       ~y5
          ~t2:problem        ~y6
          ~t2:hits           ~x7~%~
          ~t2:guard-code     ~s8~%~
          ~t2:lambda-code    ~s9)~%"
         (cons i 4)
         lambda-object
         7
         status
         absolute-event-number
         (prettyify-splo-extracts-tuples extracts)
         problem
         hits
         (if guard-code "<code>" "NIL")
         (if lambda-code "<code>" "NIL"))))

(defun print-cl-cache-fn (i j)

; This is just a debugging utility.  It returns nil but prints to the comment
; window.  It is the raw Lisp workhorse for the :logic mode constant nil
; ``function'' named print-cl-cache (which is really a macro so the arguments
; can be optional).  The user can call (print-cl-cache ...) in the ACL2 loop and
; see the cache.

; I and j, when supplied, must be natural numbers corresponding to cache lines,
; 0 <= i <= j < size.

; We print all the cache lines between lines i and j (inclusive) or until we
; see a nil line.  I defaults to 0.  J defaults to i if i was supplied and
; otherwise to size-1.  If i and/or j are non-nil but not legal cache lines, i
; defaults to 0 and j to size-1.


  (let ((cl-cache *cl-cache*))
    (cond ((consp cl-cache)
           (cw "See the defun of print-cl-cache for a comment containing ~
                reminders about the cache!~%~%")
           (let* ((min
                   (cond ((and (natp i)
                               (< i (access cl-cache cl-cache :size)))
                          i)
                         (t 0)))
                  (max
                   (cond ((and (natp j)
                               (<= min j)
                               (< j (access cl-cache cl-cache :size)))
                          j)
                         ((and i (null j)) i)
                         (t (- (access cl-cache cl-cache :size) 1)))))
; This is a really dumb way to print from min to max but stops at the first
; nil!
             (loop for i from 0 to (- (access cl-cache cl-cache :size) 1)
                   as line in (access cl-cache cl-cache :alist)
                   until (null line)
                   when (and (<= min i) (<= i max))
                   do (print-cl-cache-line i line)))
           nil)
          (t (cw "Cl-cache is uninitialized with size ~x0.~%"
                 *cl-cache*)
             nil))))

(defun cl-cache-add-entry (cl-cache line tail previous-tail)

; We assume that the :alist of cl-cache, truncated to its first :size elements
; (to account for its being a circular list), is as follows, where note that
; tail has at least two elements.

;            ((f1 ...) (f2 ...) ... (fk ...) xxx yyy ...).
;                                           | tail
;                                  | previous-tail

; That is, tail is the cdr of the alist whose car is xxx above and
; previous-tail is the cdr whose car is (fk ...) above and whose cdr is tail.

; We want to add a new element (fn ...) to the front of the :alist and discard
; xxx.

;   ((fn ...) (f1 ...) (f2 ...) ... (fk ...) yyy ...).

; This function does exactly that.  It is evaluated purely for that destructive
; update to cl-cache.  However, it returns line, the cl-cache-line that
; contains the lambda expression we went to the cache to find.

; A naive version of this algorithm creates a new cons, pushing (fn . c) to the
; front of the alist.  However, we reuse tail, which after all is a cons pair
; that would otherwise be garbage; that pair thus serves as the new alist.

  (let ((alist (access cl-cache cl-cache :alist)))
    (setf (cdr previous-tail) (cdr tail))
    (setf (car tail) line)
    (setf (cdr tail) alist)
    (let ((new-alist tail)
          (last (access cl-cache cl-cache :last)))
      (setf (access-cl-cache cl-cache :alist) tail)
      (setf (cdr last) new-alist))
    line))

(defun invalidate-some-cl-cache-lines (flg wrld)

; Flg is either EXTENSION or RETRACTION.  Wrld is the about-to-be-installed
; world. We scan down the lines in the *cl-cache* and destructively modify the
; :status fields of certain lines.  In particular, when flg is EXTENSION, we
; visit every :BAD line and set it to :UNKNOWN.  When flg is RETRACTION, we
; visit every :GOOD line and set it to :UNKNOWN unless the line's
; :absolute-event-number is less than or equal to the greatest
; absolute-event-number in the new current world.  We return nil.

  (and (consp *cl-cache*)
       (let ((cl-cache *cl-cache*)
             (lines (access cl-cache *cl-cache* :alist))
             (evno (if (eq flg 'RETRACTION)
                       (max-absolute-event-number wrld)
                       nil)))

; We temporarily clear the cache in case we're interrupted.

         (setq *cl-cache* (access cl-cache *cl-cache* :size))
         (cond
          ((eq flg 'EXTENSION)
           (loop for line in lines
                 until (null line)
                 when (eq (access cl-cache-line line :status) :BAD)
                 do
                 (setf (access-cl-cache-line line :status) :UNKNOWN)))
          (t ; RETRACTION
           (loop for line in lines
                 until (null line)
                 when
                 (and (eq (access cl-cache-line line :status) :GOOD)
                      (< evno
                         (access cl-cache-line line :absolute-event-number)))
                 do
                 (setf (access-cl-cache-line line :absolute-event-number) nil)
                 (setf (access-cl-cache-line line :status) :UNKNOWN))))
; Restore the cache.
         (setq *cl-cache* cl-cache)
         nil)))

(defun collect-from-extracts (key extracts acc)

; Key should be one of :satisfies-exprs, :guard, or :body.  Extracts is a list
; of splo-extracts-tuples.  We map over extracts and collect a duplicate-free
; list of all the terms in the key slot and union them into acc.  The order of
; the terms is reversed from their appearance-order in extracts.  Note that
; :gflg is not among the keys recognized.  It makes no sense to collect all the
; :gflgs as their meanings apply only to the tuple they're in.

  (cond
   ((endp extracts) acc)
   (t (collect-from-extracts
       key
       (cdr extracts)
       (case key
         (:satisfies-exprs
; We use the -removing-duplicates version here to reverse the satisfies-exprs
; as they're added to the accumulator.
          (union-equal-removing-duplicates
           (access splo-extracts-tuple (car extracts) :satisfies-exprs)
           acc))
         (:guard
          (add-to-set-equal
           (access splo-extracts-tuple (car extracts) :guard)
           acc))
         (:body
          (add-to-set-equal
           (access splo-extracts-tuple (car extracts) :body)
           acc))
         (otherwise (er hard 'collect-from-extracts
                        "We cannot collect values of key ~x0."
                        key)))))))

(defun maybe-re-validate-cl-cache-line (line w state)

; We know line once had :status :GOOD or :BAD but it now has :status :UNKNOWN.
; In this function we determine the proper status for the lambda object in w.
; We call this re-validating the line in the sense of accurately resolving the
; status to :GOOD or :BAD in the current world, w.  If the status is set to
; :GOOD we also record the absolute-event-number of w in the line.

; To re-validate the line we only have to inspect the :extracts of the line,
; including testing termp and tamep for various extracts and re-generating and
; trying to prove the guard clauses in the new w.  If we succeed, we
; destructively modify line to restore its :status to :GOOD and recompile the
; lambda.  If we fail, we update its :status to :BAD.  We return line in any
; case, BUT NOTE THAT LINE WILL HAVE BEEN MODIFIED!

; On the need to recompile: At first blush it may appear unnecessary to
; recompile the :lambda-object.  The :code in the line was compiled in a world
; in which the lambda was :GOOD.  It is :GOOD again in this world.  Won't the
; compiled code be the same?  After all, the body is composed entirely of
; functions and variables and constants, not macros, and while the functions
; may be defined differently in this world they'd be called in the same way
; because they have the same signatures.  But that assumes the compiler is very
; generic.  Consider what an optimizing compiler might do.  Suppose the lambda
; in question is (lambda (x) (foo x)), and that in the world when the lambda
; was first compiled foo was defined to be T, but in the current world foo is
; defined to be NIL.  It is conceivable the compiler could optimize away the
; foo and just compile (lambda (x) T), which would be wrong in the current
; world.  We don't want to assume anything about the compiler except that valid
; compiled code remains valid as the world is extended (a pretty basic
; assumption throughout ACL2).

; Another slightly nagging question related to re-compilation is whether ilks
; matter?  That is, even though foo might again be defined with same arity,
; making the lambda expression that called foo be tame, etc., again, perhaps
; foo's ilks have changed.  Perhaps the ilks of the first defun of foo was (:FN
; NIL) but the ilks of the new (current) defun is (NIL NIL).  Does it make any
; difference to the compiled code (ignoring the already discussed possibility
; of an optimizing compiler)?  No, because the compiler is unaware of ilks.
; Now one might think that we could trick the compiler into seeing something
; troubling because ilks control where lambda$s can occur and we've already
; seen that misplaced lambda$s can cause unsound evaluation.  But if we could,
; we could trick it without use of lambda$ by consing up lambdas (to avoid the
; translate-time conveniences).

; But we don't want to assume the compiler doesn't optimize and so we always
; recompile anyway.

  (let* ((ens (ens state))
         (extracts (access cl-cache-line line :extracts)))
    (assert (eq (access-cl-cache-line line :status) :UNKNOWN))
    (setf (access-cl-cache-line line :problem) 're-validation-interrupted)
    (cond
     ((well-formed-lambda-objectp1 extracts w)
      (let* ((non-compliant-fns1
              (collect-non-common-lisp-compliants
               (all-fnnames1-exec
                t
                (collect-from-extracts :guard extracts nil)
                nil)
               w))
             (non-compliant-fns2
              (or non-compliant-fns1
                  (collect-non-common-lisp-compliants
                   (all-fnnames1-exec
                    t
                    (collect-from-extracts :body extracts nil)
                    nil)
                   w))))
        (cond
         ((null non-compliant-fns2)
          (mv-let (cl-set ttree)

; In general, we now generate guard clauses and try to prove them with tau.
; But if this lambda expression has been guard verified in w, we don't bother.
; Instead we just act like no guard clauses are generated.  One might wonder
; how it is that a lambda expression that was successfully processed by
; verify-guards (and thus is found on common-lisp-compliant-lambdas) is not
; already :GOOD in the cache since verify-guards adds :GOOD lines for each
; lambda it successfully processes and since when we retract we do not switch
; :GOOD objects to :UNKNOWN if the retracted world still contains the event
; that made it good.  (The second observation means that as long as the current
; cache was just produced by a retraction, we won't find a still Common Lisp
; compliant lambda in it with status :UNKNOWN.)  One answer is that the lambda
; might have been pushed out of the cache by more recent lambdas.  Another
; answer is that the cache updating might have been interrupted and left us
; with an uninitialized cache but a still-accurate list of
; common-lisp-compliant-lambdas in the world.  This feature lets us inherit all
; the known :GOOD lambdas from the world, but we only inherit them as needed by
; apply$.  It is not clear that searching common-lisp-compliant-lambdas is
; faster than generating and applying tau to guard clauses (probably it is) but
; in any case there will probably be verified lambdas in the world that can't
; be verified by tau because they were verified by verify-guards which allows
; hints and user interaction.

            (if (member-equal (access cl-cache-line line :lambda-object)
                              (global-val 'common-lisp-compliant-lambdas w))
                (mv nil nil)
                (guard-clauses-for-fn
                 (access cl-cache-line line :lambda-object)
                 nil ; debug-p
                 ens w
                 nil nil nil))       ; safe-mode gc-off ttree
            (declare (ignore ttree)) ; assumption-free ttree
            (mv-let (cl-set1 ttree calist)
              (tau-clausep-lst cl-set ens w nil nil state nil)
              (declare (ignore ttree calist)) ; assumption-free ttree
              (cond
               ((null cl-set1)

; This line is actually :GOOD in w!  We clear the :problem, recompile, set the
; line's :absolute-event-number to the most recent such number in w, and set
; :status to :GOOD.

                (mv-let (guard-lambda body-lambda)
                  (make-compileable-guard-and-body-lambdas
                   (access cl-cache-line line :lambda-object)
                   state)
                  (setf (access-cl-cache-line line :guard-code)
                        (compile nil guard-lambda))
                  (setf (access-cl-cache-line line :lambda-code)
                        (compile nil body-lambda))
                  (setf (access-cl-cache-line line :problem) nil)
                  (setf (access-cl-cache-line line :absolute-event-number)
                        (max-absolute-event-number w))
                  (setf (access-cl-cache-line line :status) :GOOD)
                  line))

; All other exits set the status to :BAD but we attribute that to different
; problems.

               (t
                (setf (access-cl-cache-line line :problem)
                      (cons 'unproved-guard-clauses cl-set1))
                (setf (access-cl-cache-line line :status) :BAD)
                line)))))
         (t
          (setf (access-cl-cache-line line :problem)
                (cond
                 (non-compliant-fns1
                  (cons 'guard-uses-non-compliant-fns non-compliant-fns1))
                 (t
                  (cons 'body-uses-non-compliant-fns non-compliant-fns2))))
          (setf (access-cl-cache-line line :status) :BAD)
          line))))
     (t

; The problem could be that some type predicate symbol is not a unary function,
; that the guard or body is not a term, that there are program mode functions
; around, or that the body is not tame.  We don't say!

      (setf (access-cl-cache-line line :problem)
            'not-well-formed)
      (setf (access-cl-cache-line line :status) :BAD)
      line))))

(defun valid-cl-cache-line (line w state)

; Apply$ has been asked to apply the :lambda-object found in cl-cache-line
; line.  We re-validate line if necessary and possible.  This destructively
; modifies line.  In any case, we return line.  It is up to the caller to then
; interpret the :status of the line.

  (let ((status (access cl-cache-line line :status)))
    (setf (access-cl-cache-line line :hits)
          (1+ (access cl-cache-line line :hits)))
    (cond
     ((eq status :UNKNOWN)
      (maybe-re-validate-cl-cache-line line w state))
     (t line))))

; Historical Note: Earlier in the development of the cl-cache we classed as
; :UGLY any lambda whose guard or body was not a pseudo-termp.  Otherwise the
; lambda was at least :BAD, which meant we kept trying to check its
; well-formedness every time it was applied.  But there are lambdas that pass
; the pseudo-termp test but which will never be well-formed, e.g., (cadr x),
; (equal x y z), or (bar (foo x) (foo x y)).  So we decided to implement the
; notion of a ``potential term'' and class as :UGLY lambdas that either fail
; the syntactic plausibility test, e.g., not the right shape or not having a
; pseudo-termp body, or that fail the potential-termp test.  The reason we keep
; the pseudo-termp test at all is that it doesn't involve the world and we
; think it's pretty fast.  It is also worth remembering that because of
; translate-time enforcement of the well-formedness of explicitly quoted lambda
; objects and lambda$s, the only way these :UGLY lambdas can enter the system
; is if the user sneaks one past translate, e.g., `(lambda (x) (cadr x)).  So
; basically this ``costly'' extra check is probably almost never done.  One
; could thus conclude that it's not worth implementing.  But it just offended
; us to see lambdas in the cache classified as :BAD (which means they're
; candidates for upgrading to :GOOD) when in fact they're never going to be
; :GOOD!  Of course, that can still happen because of guard conditions, e.g.,
; (lambda$ (x) (declare (type integer x)) (cdr x)) produces a well-formed
; lambda that can never be guard verified and yet we'll say it's merely :BAD
; and keep trying.

(defun potential-function-namep (x w)

; We say a name is a ``potential function name'' if there is a world in which
; the name could be introduced as a function symbol by the user.  Clearly the
; name must be a symbol.  It must pass all the other checks on function names,
; e.g., not be a keyword or in the main Lisp package.  Finally, it must not be
; a predefined name, e.g., binary-append.

  (and (symbolp x)
       (not (getpropc x 'predefined nil w))
       (mv-let (erp msg)
         (chk-all-but-new-name-cmp x 'potential-function-namep 'function w)
         (declare (ignore msg))
         (null erp))))

(mutual-recursion

(defun potential-termp (x arity-alist w)
  (declare (xargs :guard (plist-worldp-with-formals w)))

; If there is a world in which x is a term, we return the required arity-alist.
; Else we return :illegal.  The expected idiom for asking whether x is a
; potential term is (not (eq (potential-termp x nil w) :illegal)).

; We only maintain and return arity-alist so we can check that nonprimitive
; symbols are used with the same arity in every occurrence, e.g., (cons (foo x)
; (foo x y)) is :illegal.  Note that a non-term, like (foo x y) in a world
; where foo has arity 1, can still be a potential term.  However, (car x y) is
; :illegal, as is (list x y).

  (cond ((atom x)
         (if (legal-variablep x)
             arity-alist
             :illegal))
        ((eq (car x) 'quote)
         (if (and (consp (cdr x))
                  (null (cddr x)))
             arity-alist
             :illegal))
        ((symbolp (car x))
         (let ((arity-alist (potential-term-listp (cdr x) arity-alist w)))
           (cond
            ((eq arity-alist :illegal) :illegal)
            ((and (getpropc (car x) 'predefined nil w)
                  (arity (car x) w))

; If a symbol is predefined as a function symbol, then it MUST be used
; correctly.  Also note that no predefined function ever gets on the
; arity-alist so we needn't check for arity conflicts with other occurrences.

             (if (eql (length (cdr x)) (arity (car x) w))
                 arity-alist
                 :illegal))
            ((potential-function-namep (car x) w)
             (let* ((temp (assoc-eq (car x) arity-alist))
                    (n (length (cdr x)))
                    (arity (if temp (cdr temp) n))
                    (arity-alist (if temp
                                     arity-alist
                                     (cons (cons (car x) n) arity-alist))))
               (if (eql n arity)
                   arity-alist
                   :illegal)))
            (t :illegal))))
        ((and (consp (car x))
              (true-listp (car x))
              (eq (car (car x)) 'lambda)
              (eql 3 (length (car x)))
              (arglistp (cadr (car x))))
         (let* ((arity-alist1
                 (potential-termp (caddr (car x)) arity-alist w))
                (arity-alist
                 (if (eq arity-alist1 :illegal)
                     :illegal
                     (potential-term-listp (cdr x) arity-alist1 w))))
           (if (and (not (eq arity-alist :illegal))
                    (null (set-difference-eq
                           (all-vars (caddr (car x)))
                           (cadr (car x))))
                    (eql (length (cadr (car x)))
                         (length (cdr x))))
               arity-alist
               :illegal)))
        (t :illegal)))

(defun potential-term-listp (x arity-alist w)
  (declare (xargs :guard (plist-worldp-with-formals w)))
  (cond ((atom x)
         (if (eq x nil)
             arity-alist
             :illegal))
        (t (let ((arity-alist (potential-termp (car x) arity-alist w)))
             (cond
              ((eq arity-alist :illegal) :illegal)
              (t (potential-term-listp (cdr x) arity-alist w)))))))

)

; Here are some tests of potential-termp.  It doesn't matter if foo and/or bar
; are defined or what their arities are.

; (consp (potential-termp '(foo x) nil (w state)))
; (consp (potential-termp '(bar (foo x)) nil (w state)))
; (consp (potential-termp '(bar (foo x) (foo y)) nil (w state)))
; (eq (potential-termp '(bar (foo x) (foo x y)) nil (w state)) :illegal)
; (eq (potential-termp '(car x y) nil (w state)) :illegal)
; (eq (potential-termp '(list x y) nil (w state)) :illegal)
; (eq (potential-termp '(let (foo x)) nil (w state)) :illegal)
; (eq (potential-termp '(foo 1) nil (w state)) :illegal)
; (eq (potential-termp '*foo* nil (w state)) :illegal)

(defun make-new-cl-cache-line (fn status w state)

; We create a new cl-cache-line record for fn.  Status is :GOOD, :BAD, :UGLY,
; or :UNKNOWN.  If :UNKNOWN, we determine the status, otherwise we assume the
; caller knows what it's doing and set up the cache line without checking
; further than necessary to compute the extracts.

; On What the Caller Must Guarantee: To call this function with status :GOOD
; you must know that fn is a well-formed-lambda-objectp, that in the current
; world all functions used in the guard and body of fn are guard verified, and
; that the guard conjectures for fn can be proved in w and that the world after
; executing the event proving the guards will have max-absolute-event-number
; one greater than that of w.  To call it with status :BAD you must know that
; fn is at least syntactically plausible.  In a sense, :BAD means ``it's not
; compilable or compliant in world w but as the world changes it's worth
; checking again!''  Normally one would expect that a :BAD line had been :GOOD
; in some world that got undone and now either some symbol in guard or body is
; undefined or not guard verified or has unprovable guards in w.  You can call
; this function with status :UGLY and force the lambda always to be run with
; *1*apply$.  Calling it with status :UNKNOWN will determine the correct status
; for w.

; Warning: We do not install the new cache line in *cl-cache*!  We just create
; and return a new cl-cache-line record!

  (cond
   ((eq status :UGLY)
    (make cl-cache-line
          :lambda-object fn
          :status :UGLY
          :absolute-event-number nil
          :extracts nil
          :problem nil
          :hits 1
          :guard-code nil
          :lambda-code nil))
   (t

; No matter what the caller says about the status, we have to recover the
; splo-extracts-tuples.  We could optimize this computation for known :GOOD and
; :BAD lambdas but for the moment we just do the full syntactic plausibility
; check.

    (let ((extracts (syntactically-plausible-lambda-objectp nil fn)))
      (cond
       ((null extracts)
        (cond ((or (eq status :GOOD) (eq status :BAD))
               (er hard 'make-new-cl-cache-line
                   "The caller of make-new-cl-cache-line said the status of ~
                    ~x0 is ~x1 but we have determined that it is actually ~
                    :UGLY.  Please contact the ACL2 developers."
                   fn status))
              (t
; Note that the :extracts field below is nil, upon which
; well-formed-lambda-objectp1 would return t if it were called on it, when in
; fact fn is syntactically ill-formed.  Because fn's :status is :UGLY,
; well-formed-lambda-objectp1 should never be called on these extracts.

               (make cl-cache-line
                     :lambda-object fn
                     :status :UGLY
                     :absolute-event-number nil
                     :extracts nil
                     :problem nil
                     :hits 1
                     :guard-code nil
                     :lambda-code nil))))
       ((eq status :GOOD)

; For status = :GOOD, the fn should be well-formed in w and w must be able to
; prove the guard conjectures, and for status = :BAD, there should (probably)
; exist a world in which fn is well-formed and guard-verifiable but it is not
; in this w.  We don't check these things because we assume the caller knows
; what it's doing.

        (mv-let (guard-lambda body-lambda)
          (make-compileable-guard-and-body-lambdas fn state)
          (make cl-cache-line
                :lambda-object fn
                :status status
                :absolute-event-number (+ 1 (max-absolute-event-number w))
                :extracts extracts
                :problem nil
                :hits 1
                :guard-code (compile nil guard-lambda)
                :lambda-code (compile nil body-lambda))))
       ((eq status :BAD)
; See note above about status :GOOD and :BAD.
        (make cl-cache-line
              :lambda-object fn
              :status :BAD
              :absolute-event-number nil
              :extracts extracts
              :problem nil
              :hits 1
              :guard-code nil
              :lambda-code nil))

; Otherwise, the caller says the status is :UNKNOWN.

       ((well-formed-lambda-objectp1 extracts w)

; We create a cache line with status :UNKNOWN and then re-validate it, which
; leaves its status :GOOD or :BAD.  Re-validation also compiles the guard and
; body of :GOOD lines.

        (maybe-re-validate-cl-cache-line
         (make cl-cache-line
               :lambda-object fn
               :status :UNKNOWN
               :absolute-event-number nil
               :extracts extracts
               :problem nil
               :hits 1
               :guard-code nil
               :lambda-code nil)
         w state))
       ((eq (potential-term-listp
             (collect-from-extracts
              :satisfies-exprs
              extracts
              (collect-from-extracts
               :guard
               extracts
               (collect-from-extracts
                :body
                extracts
                nil)))
             nil
             w)
            :illegal)
        (make cl-cache-line
              :lambda-object fn
              :status :UGLY
              :absolute-event-number nil
              :extracts nil
              :problem nil
              :hits 1
              :guard-code nil
              :lambda-code nil))
       (t

; There is no point in trying to re-validate since we know something is wrong
; -- the lambda object is not well-formed in w -- but it might eventually be.

        (make cl-cache-line
              :lambda-object fn
              :status :BAD
              :absolute-event-number nil
              :extracts extracts
              :problem 'not-well-formed
              :hits 1
              :guard-code nil
              :lambda-code nil)))))))

(defun fetch-cl-cache-line (fn vline)

; This function takes a lambda object, fn, and returns a valid cache line for
; fn in the current world of state.  It destructively updates the cache.  Vline
; is either nil or a valid cache line for fn.  If vline is non-nil line is
; added to the front of the cache (replacing any old line for fn) and returned.
; BTW: The :hits field of the old line, if any, is transferred to vline.

; WARNING: Don't think ``valid'' means ``:GOOD''!  Valid just means the status
; is correct for the current world.  The status of the returned line may be
; :GOOD, :BAD, or :UGLY.

; Motivation: This function performs a double duty.  When called with vline =
; nil it is the way we query the cache for a line containing a given lambda
; expression.  It adds a suitable line if none if found.  When called with
; vline non-nil, this is the way we add a pre-computed line to the cache, as we
; do when we've verified the guards of a defun and wish to pre-load the cache
; with all the well-formed lambda objects which are now known to be guard
; verified.

  (let* ((cl-cache *cl-cache*)
         (state *the-live-state*)
         (w (w state))
         (valid-p (consp cl-cache))
; See the first setq below for why valid-p may be nil.
         (valid-cl-alist (and valid-p
                              (access cl-cache cl-cache :alist))))
    (cond
     ((car valid-cl-alist) ; hence validp
      (prog1
          (progn

; We make *cl-cache* invalid here, to be restored in the second part of this
; prog1 if we're not interrupted.

            (setq *cl-cache* (access cl-cache cl-cache :size))
            (cond

; To see why we use hons-equal-lite when comparing lambda objects below instead
; of EQUAL, see the comment about hons-copy in translate11-lambda-object.

             ((hons-equal-lite (access cl-cache-line
                                       (car valid-cl-alist)
                                       :lambda-object)
                               fn)

; The call to valid-cl-cache-line below destructively changes the line.
; Furthermore, this line is still the top (first) line in cl-cache :alist, so
; we don't have to move it the top as we do in general.  The (if vline ...)  is
; testing whether vline is a new, presumably valid, cache line built by our
; caller, or a line found in the cache.  When new, we always preserve the old
; :hit count by transfering it into the new line.

              (if vline
                  (progn
                    (setf (access-cl-cache-line vline :hits)
                          (access cl-cache-line (car valid-cl-alist) :hits))
                    (setf (car valid-cl-alist) vline))
                  (valid-cl-cache-line (car valid-cl-alist) w state)))
             (t

; We search the cl-cache starting with the second element.  The variable, tail,
; is the tail of the :alist that starts with the ith element as we loop,
; beginning with i=2 and stopping one short of the size.  If we find an entry
; that is either nil (i.e., a free slot in the cache) or a hit on fn, then we
; delete that entry destructively, and we push a suitable line onto the front
; of the cache, using cl-cache-add-entry.  If we don't get a hit, the alist is
; full and we have to do something a bit special to drop the last line and add
; a new one.  That is done in the "finally" clause.

              (loop for i from 1 to (- (access cl-cache cl-cache :size) 2)
                    as tail on (cdr valid-cl-alist)
                    as previous-tail on valid-cl-alist

; We tried swapping the zeroth and ith lines in the special case that we find
; fn in the ith line.  But with a bit of testing we didn't see a noticeable
; effect of that optimization, so we don't bother with it here.

                    when (or (null (car tail)) ; fn not found
                             (hons-equal-lite (access cl-cache-line
                                                      (car tail)
                                                      :lambda-object)
                                              fn))
                    do

; We have either found fn's line in the cache or have searched all lines
; without finding fn but have found an empty slot into which we can store a new
; line for fn.

                    (let ((line
                           (if (null (car tail))
                               (or vline
                                   (make-new-cl-cache-line
                                    fn :UNKNOWN w state))
                               (if vline
                                   (progn
                                     (setf
                                      (access-cl-cache-line vline :hits)
                                      (access cl-cache-line (car tail) :hits))
                                     vline)
                                   (valid-cl-cache-line (car tail) w state)))))
                      (return
                       (cl-cache-add-entry cl-cache
                                           line
                                           tail
                                           previous-tail)))
                    finally

; The cache's alist is full and does not contain a line for fn unless it is the
; very last line (which we haven't inspected yet).  Unless that last line is
; fn's, we make a new line for fn toss out the last line.

                    (progn

; First advance to the last tail.

                      (setq tail (cdr tail)
                            previous-tail (cdr previous-tail))
                      (assert (eq tail (access cl-cache cl-cache :last)))
                      (let* ((found
                              (hons-equal-lite
                               (access cl-cache-line (car tail) :lambda-object)
                               fn))
                             (line
                              (if vline
                                  (if found
                                      (progn
                                        (setf (access-cl-cache-line vline
                                                                    :hits)
                                              (access cl-cache-line
                                                      (car tail)
                                                      :hits))
                                        vline)
                                    vline)
                                (cond
                                 (found
                                  (valid-cl-cache-line (car tail) w state))
                                 (t
                                  (make-new-cl-cache-line fn :UNKNOWN
                                                          w state))))))
                        (when (or vline (not found))
                          (setf (car tail) line))
                        (setf (access-cl-cache cl-cache :alist) tail)
                        (setf (access-cl-cache cl-cache :last) previous-tail)
                        (return line)))))))

; The value of the form above is the value of fetch-cl-cache-line, which is
; always a valid cl-cache-line for fn.  Its status will be :good, :bad, or
; :ugly and the caller of this routine should inspect the status to decide
; whether to run *1*apply or the :guard-code and :lambda-code.  The following
; just restores *cl-cache* which had been set to its :size in case of
; interrupts.

        (setq *cl-cache* cl-cache)))

; We get here if the cache has not been initialized.

     (t (let ((size (cl-cache-size cl-cache)))
          (when (not valid-p) ; else leave cl-cache unchanged

; First we make *cl-cache* invalid, to be restored if we don't interrupt.

            (setq *cl-cache* size)
            (setq cl-cache
                  (cond ((consp cl-cache)

; We reuse the structure of cl-cache, updating its fields appropriately with
; minimal consing.

                         (loop for i from 1 to size
                               as tail on (access cl-cache cl-cache :alist)
                               do
                               (setf (car tail) nil)))
                        (t (make-cl-cache size)))))
          (prog1
              (let ((cl-alist (access cl-cache cl-cache :alist))
                    (line (or vline ; No need to move :hits from existing line
                                    ; because the cache is empty.
                              (make-new-cl-cache-line fn :UNKNOWN w state))))
                (setf (car cl-alist) line))
            (setq *cl-cache* cl-cache)))))))

(defun add-good-lambda-objects-to-cl-cache (lambda-objects wrld state)

; Lambda-objects is a list of well-formed lambda objects.  We assume our caller
; has, in wrld, verified the guards of every element in lambda-objects.  We add
; a :GOOD cache line for every object.

  (if (not (global-val 'boot-strap-flg wrld))
      (loop for obj in lambda-objects
            do

; This fetch-cl-cache-line is done for side-effects on the cache: with
; the non-nil vline argument it just adds the new line to the cache.

            (fetch-cl-cache-line obj
                                 (make-new-cl-cache-line
                                  obj
                                  :GOOD
                                  wrld state)))
      nil))

; The following functions are useful in debugging.

(defun ping-cl-cache-line (i)

; This function fetches the :lambda-object of the ith line in the cache and
; returns its now valid :status in the current world.  Note that this also has
; the effects of updating the :hit count of the line and of moving the line to
; the front of the cache.

  (access cl-cache-line
          (fetch-cl-cache-line
           (access cl-cache-line
                   (nth i (access cl-cache *cl-cache* :alist))
                   :lambda-object)
           nil)
          :status))

(defun prettyify-cl-cache-line (line)

; This function takes a cl-cache-line and returns a simple ACL2 object
; (printable in ACL2) that sort of summarizes the line.  It is mainly used to
; enable tracing.  See the comment below.

  (list (access cl-cache-line line :lambda-object)
        (access cl-cache-line line :status)
        (prettyify-splo-extracts-tuples
         (access cl-cache-line line :extracts))
        (access cl-cache-line line :problem)
        (and (access cl-cache-line line :guard-code)
             '<guard-code>)
        (and (access cl-cache-line line :lambda-code)
             '<lambda-code>)))

; The following is a raw Lisp trace command that helps follow the activity in
; the cache.  It might be out-of-date if the signatures of these functions has
; changed, but it indicates the idea!

; (trace
;  (syntactically-plausible-lambda-objectp)
;  (well-formed-lambda-objectp1)
;  (maybe-re-validate-cl-cache-line
;   :entry (list (prettyify-cl-cache-line (nth 0 arglist))
;                (nth 1 arglist)
;                (nth 2 arglist))
;   :exit (list (prettyify-cl-cache-line (car values))))
;  (valid-cl-cache-line
;   :entry (list (prettyify-cl-cache-line (nth 0 arglist))
;                (nth 1 arglist)
;                (nth 2 arglist))
;   :exit (list  (prettyify-cl-cache-line (car values))))
;  (make-new-cl-cache-line :exit (list (prettyify-cl-cache-line (car values))))
;  (fetch-cl-cache-line :exit (list (prettyify-cl-cache-line (car values)))))

; Historical Essay on the Performance of APPLY$

; Preamble to Essay

; This essay describes an experiment performed before apply$ was integrated
; into the sources.  Furthermore, it only worked on ``unrestricted'' lambda
; objects, those having no declarations (i.e., with an implicit :guard of T).
; It can no longer be performed as described!  Indeed some of the
; infrastructure code mentioned below has since been deleted from the sources.
; For example, tame-compliant-unrestricted-lambdap was the pre-cursor to
; well-formed-lambda-objectp plus the compliance checks in
; maybe-re-validate-cl-cache-line.  The value of this experiment is
; questionable since it cannot be replicated!  But perhaps the reported results
; of the experiment may help future developers.

; For this experiment we used a slightly different fast home-grown cache, which
; was limited to three cache lines.  Our current cache is a bit faster
; (ignoring current consideration of non-trivial guards, etc.).  Consider the
; following three tests defined in community book
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
; apply$-lambda!  [Remember: these instructions cannot be followed any more!
; For example, we don't redefine apply$-lambda anymore, so you can't not
; redefine it!  But you can sort of guess what we mean just knowing that
; (concrete-apply$-lambda fn args) is raw Lisp for what you now see in the raw
; Lisp code of the defun apply$-lambda.]

;   (include-book "projects/apply/apply" :dir :system)
;   (defattach (badge-userfn doppelganger-badge-userfn)
;     :hints
;     (("Goal" :use doppelganger-badge-userfn-type)))
;   (defattach apply$-userfn doppelganger-apply$-userfn)
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
; defwarrant, badger, etc., in ACL2 Version_8.0 or later.  However, as always,
; we base our belief that ACL2 is sound on careful coding with attention to
; proofs like this.  When new features are added, we work out extensions of
; these proofs to explain those features, but we do not always re-write the
; entire proof.]

; Essay on Admitting a Model for Apply$ and the Functions that Use It

; Throughout the essay below we occasionally refer to books, e.g., apply.lisp.
; All such books are in community books directory books/projects/apply-model/.

; Goal:

; Our goal is to show that there is an evaluation theory that makes all
; warrants valid.  That evaluation theory is created by admitting the following
; events in an extension of the current chronology.

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
; dependent on APPLY$-USERFN!.

; Remark on attachments.  Recall our logical foundation for attachments, which
; shows that attachments preserve consistency by constructing an "evaluation
; chronology" whose theory is the evaluation theory for the given chronology.
; (For details, see the Essay on Defattach and, in particular, the theorem
; labeled "Evaluation History".)  How can we combine that construction
; appropriately with our doppelganger construction, to meet our goal to show
; that there is an evaluation theory making all warrants valid?  Two
; possibilities come to mind, and each incurs an obligation as shown below
; based on the requirement that defattach events do not introduce cycles in the
; extended ancestor relation.  (It is also required that no attached function
; is ancestral in any defaxiom, but that requirement is automatically enforced
; by explicit use of the two defattach displayed above.)

; (a) First extend the current chronology with the doppelganger construction.
;     Then admit the two defattach events above.

; Obligation: There must be no cycles introduced into the extended ancestor
; relation by those two defattach events.

; (b) First extend the current chronology to an evaluation chronology.  Then
;     perform the doppelganger construction.  Finally, admit the two defattach
;     events above.

; Obligation: As in (a), plus tameness must be preserved when moving to the
; evaluation chronology so that we can do the doppelganger construction.

; While the obligation for (b) seems plausible, the obligation for (a) seems
; simpler since we needn't think about tameness.  So let's focus on (a).

; Clearly (DEFATTACH BADGE-USERFN BADGE-USERFN!) does not introduce a cycle,
; since badge-userfn! is defined -- or at least, could be defined -- entirely
; using IF and CONS as the only function symbols.

; Now consider (DEFATTACH APPLY$-USERFN APPLY$-USERFN!).  Looking at community
; book books/projects/apply-model/ex1/doppelgangers.lisp for guidance, we see
; that apply$-userfn! simply calls apply$-userfn1!, which in turn is defined in
; the big doppelganger mutual-recursion.  Let f be a function symbol called in
; the body of a function g! defined in that mutual-recursion, such that f is
; not itself defined there.  Then f must be badged; otherwise g would not be
; badged, hence g! would not be defined.  Since f is badged, and it is not
; defined in that mutual-recursion, then f does not ancestrally depend on
; apply$-userfn, which implies that there is no cycle containing the link from
; apply$-userfn to apply$-userfn!.  End of Remark.

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

; Functions with badges are partitioned into primitives (e.g., CAR and
; BINARY-APPEND), boot functions (e.g., TAMEP and APPLY$), and user-defined
; (e.g., SQUARE and COLLECT).

; Non-primitive badged functions are partitioned into:
; G1 -- ancestrally independent of APPLY$-USERFN in both body and justification
;       (and ancestrally independent of inapplicable functions like sys-call
;       in the body -- a separate check since we don't require all functions in
;       G1 functions to be badged)

; G2 -- ancestrally independent of APPLY$-USERFN in justification but dependent
;       on APPLY$-USERFN in body

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
; introduced) G1 functions.  However, we do not exploit that belief (or prove
; it) here.

; If a formal has ilk :FN or has ilk :EXPR we call it a :FN/:EXPR formal or say
; it has ilk :FN/:EXPR.  That's technically a misnomer: there is no :FN/:EXPR
; formal because there is no ``:FN/:EXPR'' ilk.  The ilks are NIL, :FN, and
; :EXPR.

; Some important facts about any user-defined badged function, f, with formals
; (x1 ... xn), and body, b, include the following.  Note that the first bullet
; point applies to both G1 and G2 functions but the rest are relevant only to
; G2 functions (because no G1 function can call a function with :FN/:EXPR ilks
; or else it would be dependent on APPLY$-USERFN):

; - f's measure, well-founded relation and domain predicate are pre-apply$
;   definable.  See badger.  So we needn't worry about modeling measures as we
;   model apply$.

; - f's measure is natural number valued or is an LLIST expression (in both
;   cases, with the appropriate well-founded relation and domain).  This means
;   that the user's measures are all bounded ordinal and there is a largest
;   one, e.g., with k components.  We pretend all the user measures are
;   lexicographic with k components, with 0s in the more significant (but
;   unused) slots of user functions using fewer than k components.  To justify
;   the apply$! clique, we use a lexicographic measure of 4+k components.
;   Without loss of generality we can assume that the measure of f takes all of
;   the formals.

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
;   (defwarrant g) occurs.  But if g appears in, say, a lambda object in a :FN
;   slot in the definition of f after g has been defun'd but before g has been
;   warranted, that LAMBDA expression would not be tame and hence the function
;   f would not have a badge.  Clarification 2: the notion of the functions
;   mentioned in a quoted object is the obvious extension of the more familiar
;   notion of function symbols in pseudoterms.  By virtue of the fact that f
;   has a badge, we know these quoted objects are appropriately tame and the
;   tameness computation identifies which of the symbols in the quoted object
;   represent ``functions'' and checks that they have the appropriate badges
;   and thus that they have been defined.


; All of these facts (and others) are checked by (defwarrant f) which fails if
; any of the checks fail.

; We could loosen some of the restrictions.  Two relaxations have occurred to
; us.  One is to abandon the restriction that G2 functions be justified by
; LLIST measures (or naturals) and replace that restriction by recognition of a
; ``bounded ordinal.''  Then we'd have to replace the LLISTs measuring all of
; the functions in the apply$! clique with an ordinal subsumes that bounded
; ordinal and that behaves analogously to the current LLIST construction.

; The second relaxation would be to allow the badging of mutually recursive
; functions, but we'd have to extend the doppelganger construction to sweep in
; all the user-defined functions in the clique.

; In the evaluation theory, all G1 functions will be defined exactly as in the
; user's history, except that we omit any mention of guards.

; All G2 functions will have doppelgangers.

; The name of the doppelganger for a G2 function f is written f!.

; =================================================================
; The Standard Doppelganger Construction:

; The model construction is illustrated in books/projects/apply-model-2/,
; specifically in subdirectories ex1/ and ex2/, both of which contain a file
; named doppelganger.lisp, to which we refer below when examples are called
; for.

; In constructing the model we will define every G1 function exactly as the
; user did, except that we will omit any :guards because we don't need guards
; in this application.  We know that every G1 function is pre-apply$ definable.
; That means that if we just copy the user's unguarded G1 definitions down in
; the same order they will be admissible for the same reasons as before.  None
; of them rely on apply$ or G2 functions for admission.

; So now we describe how to define the doppelgangers for G2 functions.

; Suppose f is a user-defined G2 function with formals (v1 ... vn), and body b.
; Let (m v1 ... vn) be the measure used to admit f.  Note that the measure is
; pre-apply$ definable and so can be written after the G1 functions are
; defined.  (Indeed, G1 functions might be used in the measures, since they're
; all pre-apply$ definable.)  Then the definition of the doppelganger of f,
; namely f!, is (DEFUN f! (v1 ... vn) b''), where b'' is obtained in two steps
; as follows.  First, let b' be the result of renaming in b every G2 function
; called, replacing the called function by its doppelganger name.  (Here we
; truly mean only ACL2 function calls, not ``calls'' within lambda objects and
; terms.)  Next, consider a call of f! in b' ``marked'' if the measure
; conjecture for that call,

; (IMPLIES (AND t1 ... tn) (O< (m a1 ... an) (m v1 ... vn)))

; mentions a G2 function.  Create b'' by visiting every marked call, c, in b'
; and replacing c by

; (IF (rel (m a1 ... an)
;          (m v1 ... vn))
;     c
;     NIL).

; We call the rel term above the ``rel condition'' for the marked call.  Rel
; here is the well-founded relation used by the user's definition and is
; pre-apply$ definable and so is available.  The rel condition will be
; sufficient to justify call c during the admission of the clique.  These
; conditions cannot be proved until all the G2 functions are defined.  However,
; once all the G2 functions are defined, each rel condition is implied by the
; tests governing it.  Logically this follows from the proof that the
; doppelgangers are equivalent to their counterparts in the evaluation theory.
; But, practically speaking, to prove that equivalence may require
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

; While the measure shown above is numeric, assume the longest lexicographic
; measure among the G2 user functions is (LLIST x1 x2 x3), e.g., has length 3.

; To create the doppelganger definition we carry out the steps described.
; First, rename the G2 functions to their doppelgangers.  Note that the G2
; functions mentioned in PROW* are APPLY$, PROW, and PROW*.  Also, change the
; measure to that used by the apply$! clique, which is, in this case, an LLIST
; of length 4+3.  In the defun$ below we do not specify the first three or the
; last component and just write a1-a4 in those slots.  See The Measure for the
; APPLY$! Clique, below, for the actual expressions.  Here we're just
; interested in how we integrate the user's measure for PROW* to the measure
; used in PROW*!.  This produces:

; (DEFUN$ PROW*! (LST FN)
;   (DECLARE (XARGS :MEASURE (LLIST a1 a2 a3 0 0 (LEN LST) a4)
;                   :WELL-FOUNDED-RELATION L<))
;   (COND ((OR (ENDP LST)
;              (ENDP (CDR LST)))
;          (APPLY$! FN (LIST LST LST)))
;         (T (PROW*! (PROW! LST FN) FN))))

; Note that the user's measure, (LEN LST), is slotted into a 3-slot wide
; section of the larger measure.  Numeric user measures, as here, are in the
; least significant of the 3 slots.  In general, we add as many
; more-significant 0's as necessary to the user's measure to produce a measure
; of length 3.  This work is actually done in the file
; weights-and-measures.lisp of books/projects/apply-model-2/ and wrapped up in
; the macro standard-g2-userfn-measure.

; The call (PROW*! (PROW! LST FN) FN) is ``marked'' because the
; measure conjecture for that call is:

; (IMPLIES (AND (NOT (ENDP LST))
;               (NOT (ENDP (CDR LST))))
;          (O< (LEN (PROW! LST FN)) (LEN LST)))

; and involves the doppelganger of a G2 function, namely PROW.  So in the next
; step we replace the marked call by the IF expression described above and get
; the final definition of the doppelganger for prow*:

; (DEFUN$ PROW*! (LST FN)
;   (DECLARE (XARGS :MEASURE (LLIST a1 a2 a3 0 0 (LEN LST) a4)
;                   :WELL-FOUNDED-RELATION L<))
;   (COND ((OR (ENDP LST)
;              (ENDP (CDR LST)))
;          (APPLY$! FN (LIST LST LST)))
;         (T (IF (O< (LEN (PROW! LST FN)) (LEN LST))
;                (PROW*! (PROW! LST FN) FN)
;                NIL))))

; We claim that the rel condition inserted is implied by the governing tests --
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
; counterparts allow us to rewrite the rel conditions (which are stated in
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

; Let k be the length of the longest LLIST measure used by a user-defined G2
; function.

; Let f be a user-defined G2 function with doppelganger f!.

; The measure for f! is a lexicographic 4+k-tuple where the first three
; components are computed by the macro expressions given below.  The last
; component is always 1 (for user G2 functions).  The middle k components are
; the user-specified measure for f, padded on the left with 0s to make it k
; wide.  For example, if f is justified with a numeric measure, say m, and k is
; 3, then the middle k components are 0, 0, and m.  If f is justified with
; (LLIST m1 m2), then the middle k components are 0, m1, and m2.

; See standard-g2-userfn-measure defined in
; books/projects/apply-model-2/weights-and-measures.lisp for the code that
; generates the entire 4+k tuple for user-defined G2 functions.

; (tameness-bit f): 0 if all of the :FN/:EXPR formals of f are tame, 1
;    otherwise.  Here by ``tame'' we mean accepted by tamep-functionp! or
;    tamep!, respectively according to the ilk of the formal.

; (max-internal-weight f): maximal weight of the internals: see below

; (chronological-position f): the position of (defwarrant f) in the user's
;    chronology.  The position of APPLY$ and APPLY$-USERFN is 0, the positions
;    of EV$ and EV$-LIST are 1, the position of the first badged user-defined
;    function is 2, the next such function 3, etc.

; Implementation Note: Each component above requires knowledge of how f was
; defined and so requires looking at the world created by the user's
; chronology.  So in fact, the four macros mentioned above look at the constants
; described below:

; *USER-FNS*                      list of user-defined badged functions in
;                                  chronological order of their defwarrant
;                                  events

; *G2-FNS*                        list of all G2 functions, including APPLY$
;                                  and EV$, which are the first two elements,
;                                  listed in chronological order of their
;                                  defwarrants

; *G1-FNS*                        list of all G1 functions in chronological
;                                  order of their defwarrants

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

; *MAX-LEX-LENGTH*                length of the longest LLIST justifying a
;                                  user-defined G2 function

; *BIG-0*                         a list of *MAX-LEX-LENGTH* zeros to fill the
;                                  slots dedicated to user-defined functions in
;                                  measures for apply$!, ev$!, ev$!-list, and
;                                  apply$-userfn1!.

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

; iii. the quoted :FN/:EXPR actuals (i.e., lambda object to apply and terms to
;      evaluate) occurring in the body of f!.

; For example, consider the G2 function COLLECT-A, which maps over its ordinary
; argument, lst, applying its :FN argument, FN, and also calls the G2 function
; SUMLIST on a lambda object in a :FN position.  Note also that the lambda
; object mentions the G2 function FOLDR.  [Note: the terms in this example are
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
; iii. the lambda object, (LAMBDA (I) (FOLDR ...)).

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

; An important observation is that if a G2 function mentions a lambda object in
; a :FN position, then every function symbol occurring in the LAMBDA's body
; will have already been defined.  If a function g mentions a lambda object in
; a :FN position and the LAMBDA uses an undefined (or even an un-badged)
; symbol, then g would be un-badged and not be a G2 function.

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
; (except for APPLY$ and EV$) in chronological order of their defwarrants,
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
;          0 ... 0  ; e.g., ,@*BIG-0*
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
;          0 ... 0  ; e.g., ,@*BIG-0*
;          0))

; The measures of EV$! and EV$-LIST! are:

; (DEFUN EV$!-MEASURE (X A)
;   (LLIST 0 (WEIGHT X) (CHRONOLOGICAL-POSITION EV$) 0...0 1))

; (DEFUN EV$!-LIST-MEASURE (X A)
;   (LLIST 0 (WEIGHT X)  (CHRONOLOGICAL-POSITION EV$-LIST) 0...0 1))

; As already explained, the measure of each user-defined doppelganger, f!, is

; (DEFUN f!-MEASURE (...)
;   (LLIST (TAMENESS-BIT f)
;          (MAX-INTERNAL-WEIGHT f)
;          (CHRONOLOGICAL-POSITION f)
;          0 ... (ORIGINAL-MEASURE f) ; left-padded with 0s
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
;                          tame function symbol or lambda object, and every
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
; decided by the comparison of the so-called ``middle'' components in which the
; user's measure of f occupy the right-most (least significant) slots with 0s
; padding the left-most (more significant) slots.  The last component is always
; 1.  The original measure of f is either some numeric measure m or else (LLIST
; (m1 v_1 ... vn_n) ...).  Without loss of generality we can focus on the LLIST
; case, treating the numeric case as (LLIST m).  Thus, the conjecture above
; reduces to

; (IMPLIES tst
;          (L< (LLIST (m1 a_1 ... a_n) ...)
;              (LLIST (m1 v_1 ... v_n) ...)))

; If this formula involves any G2 function then the call of recursive f! was
; considered marked by the standard doppelganger construction and thus the
; concluding L< comparison is one of the tests governing the recursive call.
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

; This raw Lisp definition of apply$-lambda is the one that will be installed
; in ACL2, because the inclusion of apply$-lambda in
; *boot-strap-pass-2-acl2-loop-only-fns* avoids installation of the logical
; definition of apply$-lambda.

  (declare (ftype (function (t t) (values t))
                  ev$))
  (let* ((state *the-live-state*)
         (w (w state))
         (fn (if (and (consp fn)
                      (eq (car fn) *lambda$-marker*))
; See the Essay on Lambda Objects and Lambda$
                 (cdr (or (assoc-equal (cdr fn) (global-val 'lambda$-alist w))

; Preloading of compiled files causes the terms in some events -- defpkg,
; defconst, and macro bodies -- to be executed before the corresponding logical
; world exists.  If such an event contains a lambda$ that is applied during
; preloading, it would cause the error signalled below because we would not
; find the marked lambda$ on the lambda$-alist of the world.  We prevent
; lambda$ expressions from occurring in the critical events mentioned below.
; But there may be other events that are executed during preloading and so we
; detect and signal the error.

                          (er hard 'apply$-lambda
                              "Apply$-lambda has encountered an untranslated ~
                               lambda$ expression, ~x0, not resolved by ~
                               lambda-alist$.  We suspect this has occurred ~
                               during the pre-loading of a certified book.  ~
                               Lambda$ should not used in functions or terms ~
                               that might be evaluated during pre-loading of ~
                               books.  We check that there are no lambda$ ~
                               expressions ancestrally used in DEFCONST, ~
                               DEFPKG, and DEFMACRO events.  But we have ~
                               apparently not checked it for some other ~
                               context and so we have allowed a book to be ~
                               certified despite the use of a lambda$ in some ~
                               sensitive context.  Please advise the ACL2 ~
                               developers so we can catch this violation ~
                               earlier.  Meanwhile, you can work around this ~
                               by replacing the offending lambda$ expression ~
                               by its quoted translation and then recertify ~
                               the offending book.  One way to find the fully ~
                               translated form of this lambda$ expression is ~
                               to evaluate~%:trans ~x1~%and grab the quoted ~
                               lambda object in the result.  We can't do this ~
                               for you because we do not have access to the ~
                               logical world in which the lambda$ is supposed ~
                               to be translated.  Sorry!"
                              (cdr fn)
                              `(apply$ ,(cdr fn) args))))
                 fn))
         (line (and *aokp* (fetch-cl-cache-line fn nil))))

; Fetch-cl-cache-line returns a cache line that is valid for fn in the current
; world, or nil if attachments are not ok.  The line has a status, :GOOD, :BAD,
; or :UGLY.  If it is :GOOD, we apply the compiled :guard-code to the args to
; check the guard and if it is successful we apply the compiled :lambda-code
; to get the result.  If the status is not :GOOD or the guard check fails, we
; use the logical definition of apply$-lambda on fn.

; The above idealized description of what we do is actually modified to handle
; guard-checking-on by interspersing these two clauses.  If guard-checking-on
; is :NONE we just run the logical definition even if we have a good cache
; line.  Otherwise, if the guard doesn't hold but guard-checking-on is non-nil,
; we throw a standard guard error.

; Note that the fn we report as being apply$'d is not the original value of the
; fn formal above -- which might be an untranslated lambda$ marked with
; *lambda$-marker* -- but its logical translation obtained from lambda$-alist.

    (when (and line
               (eq (access cl-cache-line line :status) :GOOD)
               (not (eq (f-get-global 'guard-checking-on
                                      *the-live-state*)
                        :NONE)))
      (cond
       ((apply (access cl-cache-line line :guard-code) args)
        (return-from apply$-lambda
          (apply (access cl-cache-line line :lambda-code) args)))
       ((f-get-global 'guard-checking-on
                      *the-live-state*)
        (throw-raw-ev-fncall
         (list 'ev-fncall-guard-er
               fn
               args
               (untranslate ; guard of first splo-extracts-tuple
                (access splo-extracts-tuple
                        (car (access cl-cache-line line :extracts))
                        :guard)
                t
                (w *the-live-state*))
               (make-list ; stobjs-in = (nil ... nil)
                (length (lambda-formals fn)))
               nil ; stobjs-out
               )))))

; We fall through to the slow, logical way to apply$ a lambda expression.

    (apply$-lambda-logical fn args)))
