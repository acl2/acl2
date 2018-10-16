; ACL2 Version 8.1 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2018, Regents of the University of Texas

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

(mutual-recursion

(defun termp (x w)
  (declare (xargs :guard (plist-worldp-with-formals w)))
  (cond ((atom x) (legal-variablep x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((arity (arity (car x) w)))
           (and arity
                (term-listp (cdr x) w)
                (eql (length (cdr x)) arity))))
        ((and (consp (car x))
              (true-listp (car x))
              (eq (car (car x)) 'lambda)
              (eql 3 (length (car x)))
              (arglistp (cadr (car x)))
              (termp (caddr (car x)) w)
              (null (set-difference-eq
                     (all-vars (caddr (car x)))
                     (cadr (car x))))
              (term-listp (cdr x) w)
              (eql (length (cadr (car x)))
                   (length (cdr x))))
         t)
        (t nil)))

(defun term-listp (x w)
  (declare (xargs :guard (plist-worldp-with-formals w)))
  (cond ((atom x) (equal x nil))
        ((termp (car x) w) (term-listp (cdr x) w))
        (t nil)))

)

(defun term-list-listp (l w)
  (declare (xargs :guard (plist-worldp-with-formals w)))
  (if (atom l)
      (equal l nil)
    (and (term-listp (car l) w)
         (term-list-listp (cdr l) w))))

(defun computed-hint-tuple-listp (x wrld)
  (cond
   ((consp x)
    (let ((tuple (car x)))
      (and (true-listp tuple)
           (eq (car tuple) 'EVAL-AND-TRANSLATE-HINT-EXPRESSION)
           (booleanp (caddr tuple))
           (termp (cadddr tuple) wrld)
           (computed-hint-tuple-listp (cdr x) wrld))))
   (t (null x))))

(table default-hints-table nil nil
       :guard
       (case key
         ((t) (true-listp val))
         (:override (computed-hint-tuple-listp val world))
         (t nil)))

(table default-hints-table nil nil :clear)

(defun macro-args (x w)
  (declare (xargs :guard (and (symbolp x) (plist-worldp w))))
  (getpropc x 'macro-args
            '(:error "We thought macro-args was only called if there were ~
                      (zero or more) macro-args.")
            w))

(defconst *macro-expansion-ctx* "macro expansion")

(defun error-trace-suggestion (two-leading-spaces)

; Warning: Do not eliminate the message about print-gv without first reading
; the comment about it in ev-fncall-guard-er-msg.

  (declare (xargs :mode :program))
  (msg "~s0To debug see :DOC print-gv, see :DOC trace, and see :DOC wet."
       (if two-leading-spaces
           "  "
         "")))

(defun ignored-attachment-msg (ignored-attachment)
  (cond (ignored-attachment (msg "~|~%Note that because of logical ~
                                  considerations, attachments (including ~x0) ~
                                  must not be called in this context.  See ~
                                  :DOC ignored-attachment."
                                 ignored-attachment))
        (t "")))

(defun ev-fncall-null-body-er-msg (ignored-attachment fn args)
  (cond
   ((eq fn :non-exec)

; This is a special case for calls of (non-exec form), where in this case, args
; is form.

    (assert$
     (null ignored-attachment) ; This case has nothing to do with attachments.
     (msg "ACL2 has been instructed to cause an error because of an attempt ~
           to evaluate the following form (see :DOC non-exec):~|~%  ~
           ~x0.~|~%~@1"
          args ; actually, the form
          (error-trace-suggestion nil))))
   ((consp fn)

; This is a special case for errors detected by the code that supports the
; evaluation (at the top-level of the ACL2 loop) of terms ancestrally dependent
; upon the constrained functions in apply$ development.  In particular, if
; (consp fn) is true -- which only happens when we're executing the attachments
; for those constrained functions -- then fn is the msg we're supposed to
; return.  The basic idea is that those attachments detect a wide variety of
; errors and rather than produce a single generic error message (as we would do
; if this clause were eliminated) we let the caller formulate the message.

; Note:  We could assert (msgp fn) but it is weaker than the assertion below.

    (assert$
     (and (stringp (car fn))
          (alistp (cdr fn))) ; character-alistp isn't defined yet...
     fn))
   (t (msg "ACL2 cannot ev the call of non-executable function ~x0 on ~
            argument list:~|~%~x1~@2~|~%~@3"
           fn
           args
           (ignored-attachment-msg ignored-attachment)
           (error-trace-suggestion nil)))))

(defun ev-fncall-null-body-er (ignored-attachment fn args latches)
  (mv t
      (ev-fncall-null-body-er-msg ignored-attachment fn args)
      latches))

(defun ev-fncall-creator-er-msg (fn)
  (msg
   "An attempt has been made to call the stobj creator function ~x0.  This ~
    error is being reported even though guard-checking may have been turned ~
    off, because ACL2 does not support non-compliant live stobj manipulation. ~
    ~ If you did not explicitly call ~x0 then this error is probably due to ~
    an attempt to evaluate a with-local-stobj form directly in the top-level ~
    loop.  Such forms are only allowed in the bodies of functions and in ~
    theorems.  Also see :DOC with-local-stobj.~@1"
   fn
   (error-trace-suggestion t)))

(defun unknown-pkg-error-msg (fn pkg-name)
  (msg
   "The call ~x0 is illegal because the argument is not the name of a package ~
    currently known to ACL2."
   (list fn pkg-name)))

(defun illegal-msg ()
  (msg "Evaluation aborted.~@0"
       (error-trace-suggestion t)))

(defun program-only-er-msg (fn args safe-mode)
  (msg
   "The call ~x0~|is an illegal call of a function that has been marked as ~
    ``program-only,'' presumably because it has special raw Lisp code~@1.  ~
    See :DOC program-only for further explanation and a link to possible ~
    workarounds."
   (cons fn args)
   (if safe-mode
       " and safe-mode is active"
     "")))

(defconst *safe-mode-guard-er-addendum*

; We could add, as a reason for using safe-mode, the application of
; magic-ev-fncall to :program-mode functions.  But that might scare off
; beginners, and is sufficiently covered by "another operation">

  "  The guard is being checked because this function is a primitive and a ~
   \"safe\" mode is being used for defconst, defpkg, macroexpansion, or ~
   another operation where safe mode is required.")

(defun find-first-non-nil (lst)
  (cond ((endp lst) nil)
        (t (or (car lst)
               (find-first-non-nil (cdr lst))))))

; For a discussion of stobj latching, see Stobj Latching below.

(defun latch-stobjs1 (stobjs-out vals latches)
  (cond ((endp stobjs-out) latches)
        ((car stobjs-out)
         (let ((temp (assoc-eq (car stobjs-out) latches)))
           (cond

; Suppose (car stobjs-out) is some stobj, $st, and (car vals) is the
; new value, val.  We wish to bind '$st in latches to val.  It is an
; error if we can't find a binding for '$st.  Otherwise, put-assoc-eq
; will do the job.  But in the special, live, case, val is EQ to the
; current binding of '$st in latches, because all the objects are
; live.  In this case, we can avoid the put-assoc-eq and just leave
; latches unchanged.  The clause below is safe whether val is a live
; object or not: if it's the same thing as what is there, the
; put-assoc-eq won't change latches anyway.  But the real intent of
; this clause is make the final value of latches, in general, EQ to
; the original value of latches.


            ((not temp)
             (er hard! 'latch-stobjs
                 "We are trying to latch a value for the single-threaded ~
                  object named ~x0, but there is no entry for that name in ~
                  the stobj latches provided.  The possible latch names are ~
                  ~&1.~#2~[~/  This error most likely is caused by the ~
                  attempt to ev a form that is not ``supposed'' to mention ~
                  stobjs but does.  Often when dealing with forms that are ~
                  not supposed to mention stobjs we call ev with last ~
                  argument NIL and then ignore the resulting latches.~]"
                 (car stobjs-out)
                 (strip-cars latches)
                 (if latches 0 1)))
            #-acl2-loop-only
            ((eq (cdr temp) (car vals))
             (latch-stobjs1 (cdr stobjs-out)
                            (cdr vals)
                            latches))
            (t
             #-acl2-loop-only
             (er hard! 'latch-stobjs1
                 "We had thought that the values in user-stobj-alist match up ~
                  with the values of corresponding stobjs.  Please contact ~
                  the ACL2 implementors.")
             #+acl2-loop-only
             (latch-stobjs1 (cdr stobjs-out)
                            (cdr vals)
                            (put-assoc-eq (car stobjs-out)
                                          (car vals)
                                          latches))))))
        (t (latch-stobjs1 (cdr stobjs-out)
                          (cdr vals)
                          latches))))

(defun latch-stobjs (stobjs-out vals latches)

; Update the latches so that it contains the stobj objects returned in
; val.  Val is either a single value or a list of 2 or more values, as
; indicated by stobjs-out.  If stobjs-out is nil it is treated as a
; list of as many nils as necessary and no change is made to val.  If
; latches is nil, we do nothing.  This means that we are not recording
; the ``current'' stobjs and one must be careful to obey the
; restrictions in the Essay on EV.

  (cond ((null latches) latches)
        ((null stobjs-out) latches)
        ((null (cdr stobjs-out))
         (cond ((car stobjs-out)
; We call latch-stobjs1 rather than put-assoc-eq to get the error check.
                (latch-stobjs1 stobjs-out (list vals) latches))
               (t latches)))
        (t (latch-stobjs1 stobjs-out vals latches))))

(defun actual-stobjs-out1 (stobjs-in args user-stobj-alist)
  (cond ((endp stobjs-in)
         (assert$ (null args) nil))
        (t (let ((rest (actual-stobjs-out1 (cdr stobjs-in) (cdr args)
                                           user-stobj-alist)))
             (cond ((or (null (car stobjs-in))
                        (eq (car stobjs-in) 'state))
                    rest)
                   (t (let ((pair (rassoc-equal (car args) user-stobj-alist)))
                        (assert$ pair
                                 (cond ((eq (car stobjs-in) (car pair))
                                        rest)
                                       (t (acons (car stobjs-in)
                                                 (car pair)
                                                 rest)))))))))))

(defun apply-symbol-alist (alist lst acc)

; Alist represents a function to apply to each element of lst, a list of
; symbols.  (This function is the identity on elements not in the domain of
; alist.)  The resulting list is accumulated into acc and reversed.

  (cond ((endp lst) (reverse acc))
        (t (apply-symbol-alist alist
                               (cdr lst)
                               (cons (let ((pair (assoc-eq (car lst) alist)))
                                       (cond (pair (cdr pair))
                                             (t (car lst))))
                                     acc)))))

(defun apply-inverse-symbol-alist (alist lst acc)

; See apply-symbol-alist.  Here, though, we apply the inverse of the mapping
; represented by alist.  We assume that the cdrs of alist are suitable for
; testing with eq (i.e., symbols or stobjs).

  (cond ((endp lst) (reverse acc))
        (t (apply-inverse-symbol-alist
            alist
            (cdr lst)
            (cons (let ((pair (rassoc-eq (car lst) alist)))
                    (cond (pair (car pair))
                          (t (car lst))))
                  acc)))))

(defun actual-stobjs-out (fn args wrld user-stobj-alist)
  (let ((stobjs-out (stobjs-out fn wrld)))
    (cond ((all-nils stobjs-out) ; optimization for common case
           stobjs-out)
          (t (let ((stobjs-in (stobjs-in fn wrld)))
               (let ((alist
                      (actual-stobjs-out1 stobjs-in args user-stobj-alist)))
                 (cond (alist (apply-symbol-alist alist stobjs-out nil))
                       (t stobjs-out))))))))

#-acl2-loop-only
(defvar **1*-as-raw*

; When a *1* function is called and this variable is true, that function should
; behave as its corresponding raw Lisp function, except that critical guards
; for stobj updaters are checked.  We can live with that rather vague
; specification because this variable is nil unless we are under the call of a
; program mode function.

; For the sake of simplicity in the discussion below, we ignore the possibility
; that guard-checking is set to :none or :all and we ignore safe-mode.  Also,
; we assume that the value of state global 'check-invariant-risk is non-nil, as
; should always be the case unless someone is hacking; otherwise, the effect of
; this variable is defeated.

; Oneify-cltl-code uses this variable, **1*-as-raw*, to arrange that when a
; *1* :logic-mode function that calls mbe is itself called under a *1*
; :program-mode function, then the :exec code of that mbe call is evaluated,
; not the :logic code.  Our approach is basically as follows.  Globally,
; **1*-as-raw* is nil.  But we arrange the following, and explain below.
;
; (a) The *1* code for an invariant-risk :program mode function binds
;     **1*-as-raw* to t.
;
; (b) The *1* code for an mbe call reduces to its *1* :exec code when
;     **1*-as-raw* is true.
;
; (c) Raw-ev-fncall binds **1*-as-raw* to nil for :logic mode functions.
;
; (d) Oneify binds **1*-as-raw* to nil when ec-call is applied to a :logic
;     mode function.

; Without invariant-risk, none of this would be necessary: a :program mode
; function call would lead to raw Lisp evaluation, where each mbe call
; macroexpands to its :exec code.  But with invariant-risk, we need to stick
; with *1* execution in order to avoid making ill-guarded stobj updater calls,
; in which case (a) and (b) save us from execution of :logic code from an mbe
; call.  Note that the use of :exec code from mbe calls can be important for
; performance, as pointed out by Jared Davis.

; To see why we need (c), consider the following example.

;   (defstobj st (fld :type integer :initially 0))
;
;   (defun lgc (st)
;     (declare (xargs :mode :logic
;                     :stobjs st
;                     :verify-guards nil))
;     (mbe :logic (prog2$ (cw "@@@LOGIC@@@~%")
;                         (update-fld 3 st))
;          :exec (prog2$ (cw "@@@EXEC@@@~%")
;                        (update-fld 4 st))))
;
;   (defun foo (state st)
;     (declare (xargs :mode :program :stobjs (state st)))
;     (let ((st (update-fld 7 st)))
;       (mv-let (erp val state)
;               (trans-eval
;                '(thm (equal (with-local-stobj
;                              st
;                              (mv-let (val st)
;                                      (let ((st (lgc st)))
;                                        (mv (fld st) st))
;                                      val))
;                             4)) 'top state t)
;               (mv erp val state st))))

; The proof should fail when calling (foo state st), since logically, the value
; of the with-local-stobj form is 3, not 4.  But since foo has invariant-risk,
; **1*-as-raw* is bound to t when calling *1*foo, so we might expect that
; evaluation of the mbe form under (lgc st) would use the :exec form, leading
; erroneously to a successful proof!  However, we bind **1*-as-raw* to nil in
; raw-ev-fncall precisely to avoid such a problem.

; To see why we need (d), see the example in a comment in oneify that starts
; with "(defun f-log".

  nil)

(defun translated-acl2-unwind-protectp4 (term)

; This hideous looking function recognizes those terms that are the
; translations of (acl2-unwind-protect "expl" body cleanup1 cleanup2).  The
; acl2-unwind-protect macro expands into an MV-LET and that MV-LET is
; translated in one of two ways, depending on whether or not the two cleanup
; forms are equal.  We look for both translations.  We return 4 results.  The
; first is t or nil according to whether term is of one of the two forms.  If
; nil, the other results are nil.  If term is of either form, we return in the
; other three results: body, cleanup1 and cleanup2 such that term is equivalent
; to (acl2-unwind-protect "expl" body cleanup1 cleanup2).

; WARNING: This function must be kept in sync with the defmacro of
; acl2-unwind-protect, the translate1 clauses dealing with mv-let and let, and
; the defmacro of mv-let.

  (case-match
   term
   ((('LAMBDA (mv . vars)
      (('LAMBDA ('ACL2-UNWIND-PROTECT-ERP
                 'ACL2-UNWIND-PROTECT-VAL 'STATE . vars)
        ('IF 'ACL2-UNWIND-PROTECT-ERP
             ('(LAMBDA (STATE ACL2-UNWIND-PROTECT-VAL
                              ACL2-UNWIND-PROTECT-ERP)
                       (CONS ACL2-UNWIND-PROTECT-ERP
                             (CONS ACL2-UNWIND-PROTECT-VAL
                                   (CONS STATE 'NIL))))
              cleanup1 'ACL2-UNWIND-PROTECT-VAL 'ACL2-UNWIND-PROTECT-ERP)
             ('(LAMBDA (STATE ACL2-UNWIND-PROTECT-VAL
                              ACL2-UNWIND-PROTECT-ERP)
                       (CONS ACL2-UNWIND-PROTECT-ERP
                             (CONS ACL2-UNWIND-PROTECT-VAL
                                   (CONS STATE 'NIL))))
              cleanup2 'ACL2-UNWIND-PROTECT-VAL 'ACL2-UNWIND-PROTECT-ERP)))
       '(MV-NTH '0 mv)
       '(MV-NTH '1 mv)
       '(MV-NTH '2 mv)
       . vars))
     body . vars)
    (declare (ignore mv vars))

; Does it matter what mv is?  In principle it surely does: if mv is some
; screwy variable then it might be that this term doesn't actually have the
; semantics we are about to ascribe to it.  We know mv is not in vars since
; this is a termp and mv and vars are used in the same lambda arglist.  But
; what if mv is, say, ACL2-UNWIND-PROTECT-ERP?  Is the semantics affected?
; No: mv's binding, no matter what name we chose outside of vars, is
; unaffected.  Similarly, the names in vars are irrelevant, given that we know
; they don't include ACL2-UNWIND-PROTECT-ERP, etc., which is assured by the
; same observation that term is a termp.

    (mv t body cleanup1 cleanup2))
   ((('LAMBDA (mv . vars)
      (('LAMBDA ('ACL2-UNWIND-PROTECT-ERP
                 'ACL2-UNWIND-PROTECT-VAL 'STATE . vars)
                ('(LAMBDA (STATE ACL2-UNWIND-PROTECT-VAL
                                 ACL2-UNWIND-PROTECT-ERP)
                          (CONS ACL2-UNWIND-PROTECT-ERP
                                (CONS ACL2-UNWIND-PROTECT-VAL
                                      (CONS STATE 'NIL))))
                 cleanup1 'ACL2-UNWIND-PROTECT-VAL 'ACL2-UNWIND-PROTECT-ERP))
       '(MV-NTH '0 mv)
       '(MV-NTH '1 mv)
       '(MV-NTH '2 mv)
       . vars))
     body . vars)
    (declare (ignore mv vars))

; See comment above.

    (mv t body cleanup1 cleanup1))
   (& (mv nil nil nil nil))))

(defun translated-acl2-unwind-protectp (term)

; Just for convenience we define the predicate version of translated-acl2-
; unwind-protectp4 to return t or nil according to whether term is the
; translation of an acl2-unwind-protect expression.

  (mv-let (ans body cleanup1 cleanup2)
          (translated-acl2-unwind-protectp4 term)
          (declare (ignore body cleanup1 cleanup2))
          ans))

; Essay on EV

; Ev, below, will take the following arguments:

; (ev form alist state latches hard-error-returns-nilp aok)

; It returns (mv erp val latches').

; Ev is actually defined in terms of ev-rec, an analogous function that
; takes the ACL2 world rather than state.

; Hard-error-returns-nil is explained in the comment in hard-error.
; We do not deal with it further below.

; Aok is short for "Attachments are OK", and as the name suggests,
; allows the use of attachments when non-nil.  This parameter is discussed at
; some length near the end of this Essay.  Till then, we assume that its value
; is nil.

; Imprecise Spec: If erp is t, some evaluation error occurred (e.g.,
; an unbound variable was encountered).  Otherwise, erp is nil, val is
; the value of form under alist, and latches' is the final value of
; all the single-threaded objects after the evaluation of form.

; But there are many subtle issues here having to do with the handling
; of single-threaded objects.  In the following discussion we use
; (bump state) as a generic function that changes state, as by
; incrementing a global variable in state and returning the modified
; state.

; Assumptions on the input to EV:

; (0) If latches is nil, then either form is known not to modify any
;     stobjs (in which case it really doesn't matter what latches is) or
;     else there are no live stobjs in alist.  In short, if latches is
;     nil, we don't keep track of the current values of the stobjs but you
;     better not ev a form on a live object (because it will actually
;     change the object but not record the new current value on latches).

; (1) If latches is non-nil, then if a stobj name, such as STATE, is bound
;     in alist to some value s then
;     (1a) s is of the correct shape for that stobj and
;     (1b) that stobj name is bound in latches to s.
;     Informally, the initial values of the stobjs in alist are identical
;     to their initial current values and consistent with the stobj
;     definitions.

; (2) If alist binds a stobj name to a live object, then form must be
;     single-threaded.

; Clarification of the output spec:

; If no stobj names are bound in alist to live objects, then the
; latches on input may be nil and the final latches may
; be ignored.

; If form is not single-threaded, the meaning of the final latches
; is essentially random.

; In the most common case (where we are using ev to evaluate a form
; typed by the user at the top-level), state is *the-live-state*, all
; the stobj names are bound in alist to their current live objects
; (including 'state to *the-live-state*), and form is single-threaded.

; Observations about the Assumptions

; The only way alist can bind a stobj name to a live object is if we
; did that in our own source code.  In particular, a user cannot write
; (list (cons 'state state) (cons '$s $s)), unless the user has access to
; something like coerce-state-to-object.  These comments assume such
; magic functions have been made untouchable.

; No live object can be in the final latches unless they were
; there to begin with.  If a live object is in the final current
; stobjs, then it was put there by a stobj producing fncall.  But that
; would mean there was a live stobj in alist.  That, in turn, means
; the same live object was originally in the initial current stobjs.

; Thus, the only time live objects appear in the final latches
; is if we're in our own source code.

; We guarantee, via functions like trans-eval, that assumptions (1)
; and (2) are met in all our calls of ev.

; Further Discussion of the Assumptions:

; Suppose that the symbol 'state is bound in alist to s.  Suppose the
; value of the formal parameter state is d.  Both s and d are
; state-ps.  We call the latter state d because it is the state from
; which ev obtains the definitions of the functions.  We also use d to
; determine whether guards should be checked.  D is not changed in ev,
; except to decrement the big clock in it to ensure termination.

; By assumption (1), we know that the binding of state in
; latches is s, initially.  But in general, the two bindings
; can differ: the binding of state in alist is the initial value of
; state and the binding in the final latches is the final value
; of state.

; Generally speaking, d is *the-live-state*.  Indeed, at one point we
; believed:

; The Bogus Live State Claim for :Program Mode Functions: If a
; :program mode function takes STATE as an argument then the function
; can only be evaluated on the live state.

; Below I give a ``proof'' of this claim, for a call of ev stemming
; from a legal form typed by the user to the top-level ACL2 loop.
; Then I give a counterexample!

; ``PROOF:'' The call was translated.  Since ev is a :program mode
; function, the call cannot appear in a theorem or other context in
; which the stobj restrictions were not enforced.  Hence, the only
; allowable term in the state slot is state itself.  Hence, state must
; be *the-live-state*, as it is at the top of LP.

; Now here is a way to run ev from within the loop on a state other
; than the live state: Ev a call of ev.  Here is a concrete form.
; First, go outside the loop and call (build-state) to obtain a dummy
; state.  I will write that '(NIL ... NIL).  At present, it has 15
; components, most of which are nil, but some, like the initial global
; table, are non-trivial.  Then inside the loop execute:

; (let ((st (build-state)))
;    (ev `(ev 'a '((a . 1)) ',st 'nil 'nil 't) nil state nil nil t))

; The outermost state above is indeed the live one, but the inner ev is
; executed on a dummy state.  The computation above produces the result
; (NIL (NIL 1 NIL) NIL).

; The inner state object has to pass the state-p predicate if guard
; checking is enabled in the outer state.  If guard checking is turned
; off in the live state, the following example shows the inner ev
; running on something that is not even a state-p.  To make this
; example work, first evaluate :set-guard-checking nil.

; (ev '(ev 'a '((a . 1)) '(nil nil nil nil nil 0) 'nil 'nil 't)
;     nil state nil nil t)

; The 0, above, is the big-clock-entry and must be a non-negative
; integer.  The result is (NIL (NIL 1 NIL) NIL).

; Finally, the example below shows the inner ev running a function,
; foo, defined in the dummy world.  It doesn't matter if foo is
; defined in the live state or not.  The example below shows the state
; returned by build-state at the time of this writing, but modified to
; have a non-trivial CURRENT-ACL2-WORLD setting giving FORMALS and a
; BODY to the symbol FOO.

;   (ev '(ev '(foo a)
;            '((a . 1))
;            '(NIL NIL
;                  ((ACCUMULATED-TTREE)
;                   (AXIOMSP)
;                   (BDDNOTES)
;                   (CERTIFY-BOOK-FILE)
;                   (CONNECTED-BOOK-DIRECTORY)
;                   (CURRENT-ACL2-WORLD
;                    . ((foo formals . (x)) (foo body . (cons 'dummy-foo x))))
;                   (CURRENT-PACKAGE . "ACL2")
;                   (EVISCERATE-HIDE-TERMS)
;                   (FMT-HARD-RIGHT-MARGIN . 77)
;                   (FMT-SOFT-RIGHT-MARGIN . 65)
;                   (GSTACKP)
;                   (GUARD-CHECKING-ON . T)
;                   #+acl2-infix (INFIXP)
;                   (INHIBIT-OUTPUT-LST SUMMARY)
;                   (IN-LOCAL-FLG . NIL)
;                   (LD-LEVEL . 0)
;                   (LD-REDEFINITION-ACTION)
;                   (LD-SKIP-PROOFSP)
;                   (PROMPT-FUNCTION . DEFAULT-PRINT-PROMPT)
;                   (PROOF-TREE-CTX)
;                   (PROOFS-CO
;                    . ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
;                   (SKIPPED-PROOFSP)
;                   (STANDARD-CO
;                    . ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0)
;                   (STANDARD-OI
;                    . ACL2-OUTPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
;                   (TIMER-ALIST)
;                   (TRIPLE-PRINT-PREFIX . " ")
;                   (UNDONE-WORLDS-KILL-RING NIL NIL NIL)
;                   (UNTOUCHABLE-FNS)
;                   (UNTOUCHABLE-VARS)
;                   (WINDOW-INTERFACEP)
;                   (WORMHOLE-NAME))
;                  NIL NIL 4000000
;                  NIL NIL 1 NIL NIL NIL NIL NIL NIL)
;            'nil 'nil 't) nil state nil nil t)

; The output of the ev above is (NIL (NIL (DUMMY-FOO . 1) NIL) NIL).

; The above example can be made slightly more interesting by replacing
; the three occurrences of FOO by EV.  It still produces the same
; thing and illustrate the fact that EV doesn't mean what you might
; think it means once you get into an EV!

; The intuition that ``d must be *the-live-state*'' is only true at
; the outermost call of EV.  But things take care of themselves inside
; subsequent calls because, if d is not *the-live-state*, EV just runs
; as defined, whatever that means.

; Stobj Latching:  How Do We Compute the Final Latches?

; This is simpler than it at first appears: First, we map over the
; term in evaluation order.  Every time we apply a function symbol to
; a list of (evaluated) terms, we ``latch'' into latches each of
; the stobj values indicated by the symbol's stobjs-out.

; The order of the sweep is controlled by ev and ev-lst.  But all the
; latching is done by ev-fncall.  This is surprising because ev-fncall
; does not handle LAMBDAs and translation has entirely eliminated all
; MV-LETs and MVs.

; Let us consider some examples to see why this works -- and to drive
; home some points it took me a while to see.  In the following,

; (defun bump (state) (f-put-global 'bump (@ bump) state))
; (defun bump3 (x state) (let ((state (bump state))) (mv nil x state)))

; Consider the translate (==>) of

; :trans (let ((state (bump state)))
;             (mv a state b))
; ==>
; ((LAMBDA (STATE B A)
;          (CONS A (CONS STATE (CONS B 'NIL))))
;  (BUMP STATE)
;  B A)

; Sweep order is (BUMP STATE), B, A, and then the CONS nest.  Of these, only
; the BUMP has a non-trivial stobjs-out.  We latch the state coming out of
; (BUMP STATE).

; :trans (mv-let (erp val state)
;                (bump3 x state)
;                (mv (and erp val) (cons erp val) state))

; ==>
; ((LAMBDA (MV)
;          ((LAMBDA (ERP VAL STATE)
;                   (CONS (IF ERP VAL 'NIL)
;                         (CONS (CONS ERP VAL)
;                               (CONS STATE 'NIL))))
;           (MV-NTH '0 MV)
;           (MV-NTH '1 MV)
;           (MV-NTH '2 MV)))
;  (BUMP3 X STATE))

; We latch the third value of (BUMP3 X STATE), when we ev-fncall
; BUMP3.  No other function causes us to latch, so that is the final
; latches.

; :trans (mv-let (erp val state)
;                (bump3 x state)
;                (let ((state (bump state)))
;                  (mv erp val state)))
; ==>
; ((LAMBDA (MV)
;          ((LAMBDA (ERP VAL STATE)
;                   ((LAMBDA (STATE VAL ERP)
;                            (CONS ERP (CONS VAL (CONS STATE 'NIL))))
;                    (BUMP STATE)
;                    VAL ERP))
;           (MV-NTH '0 MV)
;           (MV-NTH '1 MV)
;           (MV-NTH '2 MV)))
;  (BUMP3 X STATE))

; We latch the third value of (BUMP3 X STATE), when we ev-fncall BUMP3.
; The next non-trivial stobjs-out function we ev-fncall is the BUMP.
; We latch its result, which gives us the final latches.

; The restrictions imposed by translate ensure that we will never
; encounter terms like (fn a (bump state) b (bump state) c) where
; there is more than one latched stobj coming out of an arglist.  But
; we do not exploit this fact.  We just latch every stobj-out as we go
; across the args.  Similarly, the translate restrictions ensure that
; if a stobj is returned by some function, then it gets out.  So we
; can latch it when it is returned by the function, even though it
; apparently goes into a CONS nest, say, from which it may not, a
; priori, get out.

; We close with a discussion of the final argument of ev and many other
; evaluator functions, aok.  In short: The safe value for aok is nil, but it is
; more powerful (fewer aborts) to use t rather than nil for aok, if that is
; sound.  Unless you are writing ACL2 system code, it probably is sound to use
; t.  But now we discuss in more depth the question of assigning a value to
; aok.

; Most or all of the evaluator functions (ev, ev-fncall, trans-eval,
; simple-translate-and-eval, etc.) have a final argument called aok, which is
; mnemonic for "attachments OK".  The conservative value to use is nil, which
; means that no attachments (in the sense of defattach) will be used by the
; evaluator.  But if you want attachments to be allowed by the evaluator, then
; use aok = t.

; In ACL2's own source code, aok is usually t, but it is (and must of course,
; be) nil whenever we are simplifying terms during a proof.  See the Essay on
; Defattach for related discussion.

; Here, in brief, is the logical story (which is important to understand when
; deciding to use aok=t).  The evaluator functions can all be thought of as
; producing a result that is provably equal to a given term.  But the question
; is: Provably equal in what formal theory?  The "official" theory of the
; current ACL2 world has nothing to do with attachments, and is the theory for
; which we have a prover.  So if the rewriter, say, wants to use ev-fncall to
; replace one term by another, the input and output terms should be provably
; equal without attachments, which is why we use aok=nil in the call of
; ev-fncall under rewrite.  On the other hand, in the top-level loop we
; presumably want to use all attachments -- the whole point of (defattach f g)
; for an encapsulated f and defined g is to evaluate under the equation (equal
; (f x) (g x)).  So the call of trans-eval under ld-read-eval-print has aok=t.

; Thus, if you are calling simple-translate-and-eval for something like hints,
; then probably it's fine to use aok=t -- hints don't affect soundness and one
; might want to take advantage of attachments.  As ACL2 evolves, many of its
; system functions may be encapsulated with default attachments, so one will
; want to use aok=t whenever possible in order to avoid an "undefined function"
; error when such a system function is called.

(defun acl2-system-namep (name wrld)

; Warning: keep this in sync with acl2-system-namep-state.

; Name is a name defined in wrld.  We determine whether it is one of ours or is
; user-defined.

; If name is not defined -- more precisely, if we have not yet laid down an
; 'absolute-event-number property for it -- then we return nil except in the
; boot-strap world.

  (declare (xargs :guard (and (symbolp name) (plist-worldp wrld))))
  (cond ((global-val 'boot-strap-flg wrld) t)
        (t (getpropc name 'predefined nil wrld))))

(defun acl2-system-namep-state (name state)

; Warning: keep this in sync with acl2-system-namep.  See comments there.

  (cond ((f-get-global 'boot-strap-flg state) t)
        (t (getpropc name 'predefined))))

#+acl2-loop-only
(encapsulate

; We introduce big-n and decrement-big-n with no axioms.  We could certainly
; add axioms, namely that (big-n) is a positive integer and decrement-big-n
; decrements, but we choose not to do so.  Instead, we keep these axiom-free
; and introduce executable versions in program mode, just below.  We imagine
; that n is a positive integer larger than the lengths of all computations that
; will ever take place with ACL2, and that decrement-big-n is 1-.  We also make
; big-n untouchable, since without that we have been able to prove nil, as
; follows:

;  (in-package "ACL2")
;  (defun foo () (big-n))
;  (defthm bad1 (equal (foo) '(nil)) :rule-classes nil)
;  (defthm bad2
;    (equal (big-n) '(nil))
;    :hints (("Goal" :use bad1 :in-theory (disable (foo))))
;    :rule-classes nil)
;  (defun bar () 0)
;  (defthm bad3
;    (equal (bar) '(nil))
;    :hints (("Goal" :by (:functional-instance bad2 (big-n bar))))
;    :rule-classes nil)
;  (defthm bad
;    nil
;    :hints (("Goal" :use bad3))
;    :rule-classes nil)

; We also make decrement-big-n and zp-big-n untouchable, just because we are a
; bit paranoid here.

 (((big-n) => *)
  ((decrement-big-n *) => *)
  ((zp-big-n *) => *))
 (local (defun big-n ()
          0))
 (local (defun decrement-big-n (n)
          (declare (ignore n))
          0))
 (local (defun zp-big-n (n)
          (declare (ignore n))
          nil)))

#-acl2-loop-only
(progn

; (defconstant *big-n-special-object* '(nil . nil)) has been moved to
; acl2.lisp, to avoid a CLISP compiler warning.

  (defun big-n () *big-n-special-object*)
  (defmacro decrement-big-n (n)
    `(if (eq ,n *big-n-special-object*)
         *big-n-special-object*
       (1- ,n)))
  (defmacro zp-big-n (n)
    `(if (eq ,n *big-n-special-object*)
         nil
       (zp ,n))))

#-acl2-loop-only
(defparameter *ev-shortcut-okp*

; The code for ev-fncall-rec has a shortcut, calling raw-ev-fncall to execute
; using *1* functions.  Because the *1* functions use (live) state globals
; guard-checking-on and safe-mode, these need to agree with the corresponding
; parameters of ev-fncall-rec in order for it to be sound to call
; raw-ev-fncall.  We may bind *ev-shortcut-okp* to t when we know that this
; agreement is ensured.

; There are times where avoiding the shortcut can get us into trouble.  In
; particular, we have seen a case where the logic code for an ev-nest function
; produced nil for a call of state-p or state-p1 on *the-live-state*.

  nil)

(defun w-of-any-state (st)

; This returns (w state) but, unlike w, st is not (known to be)
; single-threaded, so it can be used on the binding of 'STATE in the latches of
; a call of a function in the ev nest.  In the raw Lisp case, we have the same
; f-get-global code as in the definition of w.  For the logic, we open up
; f-get-global and then get-global to get the body below.

  #-acl2-loop-only
  (cond ((live-state-p st)
        (return-from w-of-any-state (f-get-global 'current-acl2-world st))))
  (cdr (assoc 'current-acl2-world (global-table st))))

(defun untranslate-preprocess-fn (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (cdr (assoc-eq 'untranslate-preprocess (table-alist
                                          'user-defined-functions-table
                                          wrld))))

(defmacro untranslate* (term iff-flg wrld)

; We need to call untranslate in ev-fncall-guard-er and ev-fncall-msg, where we
; have not yet called ev-fncall.  So we define this version of untranslate now
; and defer untranslate (and untranslate-lst) until after defining the ev
; family of functions.  We document in the guard below our expectation that
; wrld is a symbol, in order to avoid any overhead (e.g., from defabbrev).

  (declare (xargs :guard (symbolp wrld)))
  `(untranslate1 ,term
                 ,iff-flg
                 (untrans-table ,wrld)
                 (untranslate-preprocess-fn ,wrld)
                 ,wrld))

(defun save-ev-fncall-guard-er (fn guard stobjs-in args)

; Warning: If you change this definition, consider changing :doc
; make-wormhole-status, which references this definition.

  (wormhole-eval 'ev-fncall-guard-er-wormhole
                 '(lambda ()
                    (make-wormhole-status

; Here we pass nil for the old "status", so that we will update the status
; unconditionally.  That can avoid an expensive equality test when a logical
; world or other large structure belongs to args.

                     nil
                     :ENTER
                     (list fn guard stobjs-in args)))
                 nil))

(defrec attachment

; See the Essay on Merging Attachment Records.

  ((g . ext-succ) . (components . pairs))
  nil)

(defrec attachment-component

; See the Essay on Merging Attachment Records.

  ((ext-anc . ord-anc) . path)
  nil)

(defun attachment-record-pairs (records acc)
  (cond ((endp records)
         acc)
        (t (attachment-record-pairs
            (cdr records)
            (append (access attachment (car records) :pairs)
                    acc)))))

(defun all-attachments (wrld)
  (attachment-record-pairs (global-val 'attachment-records wrld)
                           nil))

(defun gc-off1 (guard-checking-on)
  (member-eq guard-checking-on
             '(nil :none)))

(defun gc-off (state)
  (gc-off1 (f-get-global 'guard-checking-on state)))

#-acl2-loop-only
(progn
  (defvar *return-last-arg2*)
  (defvar *return-last-arg3*)
  (defvar *return-last-alist*)
  (defvar *return-last-fn-w*)
  (defvar *return-last-fn-user-stobj-alist*)
  (defvar *return-last-fn-big-n*)
  (defvar *return-last-fn-safe-mode*)
  (defvar *return-last-fn-gc-off*)
  (defvar *return-last-fn-latches*)
  (defvar *return-last-fn-hard-error-returns-nilp*)
  (defvar *return-last-fn-aok*))

(defun return-last-lookup (sym wrld)

; Keep this in sync with chk-return-last-entry and with the comment about these
; macros in *initial-return-last-table*.

  (assert$
   (and (symbolp sym) sym) ; otherwise we shouldn't call return-last-lookup
   (case sym
     (progn 'prog2$)
     (mbe1-raw 'mbe1)
     (ec-call1-raw 'ec-call1)
     (with-guard-checking1-raw 'with-guard-checking1)
     (otherwise
      (cdr (assoc-eq sym (table-alist 'return-last-table wrld)))))))

(defun make-let-or-let* (bindings body)
  (declare (xargs :guard (doublet-listp bindings)))
  (cond ((and bindings (null (cdr bindings)))
         (case-match body
           (('let ((& &)) x)
            `(let* (,@bindings
                    ,@(cadr body))
               ,x))
           (('let* rest-bindings x)
            `(let* ,(cons (car bindings) rest-bindings)
               ,x))
           (& (make-let bindings body))))
        (t (make-let bindings body))))

(defmacro untranslate*-lst (lst iff-flg wrld)

; See untranslate*.

  (declare (xargs :guard (symbolp wrld)))
  `(untranslate1-lst ,lst
                     ,iff-flg
                     (untrans-table ,wrld)
                     (untranslate-preprocess-fn ,wrld)
                     ,wrld))

(defun live-state-symbolp (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (equal (symbol-package-name x)
              "ACL2_INVISIBLE")
       (equal (symbol-name x)
              "The Live State Itself")))

(defun apply-user-stobj-alist-or-kwote (user-stobj-alist lst acc)

; This function accumulates into acc (eventually reversing the accumulation)
; the result of replacing each element of lst with:

; - state, if it is *the-live-state*;

; - with its reverse lookup in user-stobj-alist, if it is
;   a bad-atom (i.e., a stobj); else,

; - with the result of quoting that element.

; We considered using rassoc-eq in place of rassoc-equal below, but that would
; prevent guard verification down the road (unless we change to guard of eq to
; allow bad-atoms in place of symbols).  So we are content to use rassoc-equal,
; which may be quite fast on bad atoms, and since (as of this writing) we only
; use this function for occasional user-level error and debug messages.

  (cond ((endp lst) (reverse acc))
        (t (apply-user-stobj-alist-or-kwote
            user-stobj-alist
            (cdr lst)
            (cons (cond ((live-state-symbolp (car lst))
			 'state)
			((bad-atom (car lst))
                         (let ((pair (rassoc-equal (car lst)
                                                   user-stobj-alist)))
                           (cond (pair (car pair))
                                 (t

; We are looking at a local stobj or a stobj bound by stobj-let.

                                  '|<some-stobj>|))))
                        (t (kwote (car lst))))
                  acc)))))

; Next, we introduce many events to support the definition of
; ev-fncall-rec-logical -- specifically, the definition of function guard-raw,
; which is called by ev-fncall-guard-er, which in turn is called by
; ev-fncall-rec-logical.  Most of these events were previously located in file
; history-management.lisp.

; Event Tuples

; Every time an event occurs we store a new 'global-value for the
; variable 'event-landmark in stop-event.  The value of
; 'event-landmark is an "event tuple."  Abstractly, an event tuple
; contains the following fields:

; n:     the absolute event number
; d:     the embedded event depth (the number of events containing the event)
; form:  the form evaluated that created the event.  (This is often a form
;        typed by the user but might have been a form generated by a macro.
;        The form may be a call of a primitive event macro, e.g., defthm,
;        or may be itself a macro call, e.g., prove-lemma.)
; type:  the name of the primitive event macro we normally use, e.g.,
;        defthm, defuns, etc.
; namex: the name or names of the functions, rules, etc., introduced by
;        the event.  This may be a single object, e.g., 'APP, or "MY-PKG",
;        or may be a true list of objects, e.g., '(F1 F2 F3) as in the case
;        of a mutually recursive clique.  0 (zero) denotes the empty list of
;        names.  The unusual event enter-boot-strap-mode has a namex containing
;        both symbols and strings.
; symbol-class:
;        One of nil, :program, :ideal, or :compliant-common-lisp, indicating
;        the symbol-class of the namex.  (All names in the namex have the same
;        symbol-class.)

; All event tuples are constructed by make-event-tuple, below.  By searching
; for all calls of that function you will ascertain all possible event types
; and namex combinations.  You will find the main call in add-event-landmark,
; which is used to store an event landmark in the world.  There is another call
; in primordial-world-globals, where the bogus initial value of the
; 'event-landmark 'global-value is created with namex 0 and event type nil.
; Add-event-landmark is called in install-event, which is the standard (only)
; way to finish off an ACL2 event.  If you search for calls of install-event
; you will find the normal combinations of event types and namex.  There are
; two other calls of add-event-landmark.  One, in in primordial-world where it
; is called to create the enter-boot-strap-mode event type landmark with namex
; consisting of the primitive functions and known packages.  The other, in
; end-prehistoric-world, creates the exit-boot-strap-mode event type landmark
; with namex 0.

; As of this writing the complete list of type and namex pairs
; is shown below, but the algorithm described above will generate
; it for you if you wish to verify this.

;               type                namex
;           enter-boot-strap-mode    *see below
;           verify-guards            0 (no names introduced)
;           defun                    fn
;           defuns                   (fn1 ... fnk)
;           defaxiom                 name
;           defthm                   name
;           defconst                 name
;           defstobj                 (name the-live-var fn1 ... fnk)
;             [Note: defstobj is the type used for both defstobj and
;              defabsstobj events.]
;           defmacro                 name
;           defpkg                   "name"
;           deflabel                 name
;           deftheory                name
;           in-theory                0 (no name introduced)
;           in-arithmetic-theory     0 (no name introduced)
;           push-untouchable         0
;           regenerate-tau-database  0 (no name introduced)
;           remove-untouchable       0
;           reset-prehistory         0
;           set-body                 0 (no name introduced)
;           table                    0 (no name introduced)
;           encapsulate              (fn1 ... fnk) - constrained fns
;           include-book             "name"
;           exit-boot-strap-mode     0

; *Enter-boot-strap-mode introduces the names in *primitive-formals-and-guards*
; and *initial-known-package-alist*.  So its namex is a proper list containing
; both symbols and strings.

; To save space we do not actually represent each event tuple as a 6-tuple but
; have several different forms.  The design of our forms makes the following
; assumptions, aimed at minimizing the number of conses in average usage.  (1)
; Most events are not inside other events, i.e., d is often 0.  (2) Most events
; use the standard ACL2 event macros, e.g., defun and defthm rather than user
; macros, e.g., DEFN and PROVE-LEMMA.  (3) Most events are introduced with the
; :program symbol-class.  This last assumption is just the simple observation
; that until ACL2 is reclassified from :program to :logic, the ACL2
; system code will outweigh any application.

(defun signature-fns (signatures)

; Assuming that signatures has been approved by chk-signatures, we
; return a list of the functions signed.  Before we added signatures
; of the form ((fn * * STATE) => *) this was just strip-cars.
; Signatures is a list of elements, each of which is either of the
; form ((fn ...) => val) or of the form (fn ...).

  (cond ((endp signatures) nil)
        ((consp (car (car signatures)))
         (cons (car (car (car signatures)))
               (signature-fns (cdr signatures))))
        (t (cons (car (car signatures))
                 (signature-fns (cdr signatures))))))

(defun make-event-tuple (n d form ev-type namex symbol-class skipped-proofs-p)

; An event tuple is always a cons.  Except in the initial case created by
; primordial-world-globals, the car is always either a natural (denoting n and
; implying d=0) or a cons of two naturals, n and d.  Its cadr is either a
; symbol, denoting its type and signaling that the cdr is the form, the
; symbol-class is :program and that the namex can be recovered from the form,
; or else the cadr is the pair (ev-type namex . symbol-class) signaling that
; the form is the cddr.

; Generally, the val encodes:
;  n - absolute event number
;  d - embedded event depth
;  form - form that created the event
;  ev-type - name of the primitive event macro we use, e.g., defun, defthm, defuns
;  namex - name or names introduced (0 is none)
;  symbol-class - of names (or nil)
;  skipped-proofs-p - t when the symbol-class is not :program (for simplicity
;                     of implementation, below) and skipped-proofs-p is t; else
;                     nil.  Note that skipped-proofs-p will be nil for certain
;                     events that cannot perform proofs (see install-event) and
;                     otherwise indicates that proofs were skipped (except by
;                     the system only, as for include-book).

; In what we expect is the normal case, where d is 0 and the form is one of our
; standard ACL2 event macros, this concrete representation costs one cons.  If
; d is 0 but the user has his own event macros, it costs 3 conses.

; Warning: If we change the convention that n is the car of a concrete event
; tuple if the car is an integer, then change the default value given getprop
; in max-absolute-event-number.

  (cons (if (= d 0) n (cons n d))
        (if (and (eq symbol-class :program)
                 (consp form)
                 (or (eq (car form) ev-type)
                     (and (eq ev-type 'defuns)
                          (eq (car form) 'mutual-recursion)))
                 (equal namex
                        (case (car form)
                              (defuns (strip-cars (cdr form)))
                              (mutual-recursion (strip-cadrs (cdr form)))
                              ((verify-guards in-theory
                                              in-arithmetic-theory
                                              regenerate-tau-database
                                              push-untouchable
                                              remove-untouchable
                                              reset-prehistory
                                              set-body
                                              table)
                               0)
                              (encapsulate (signature-fns (cadr form)))
                              (otherwise (cadr form)))))
            form
          (cons (cons (cons ev-type
                            (and (not (eq symbol-class :program))
                                 skipped-proofs-p))
                      (cons namex symbol-class))
                form))))

(defun access-event-tuple-number (x)

; Warning: If we change the convention that n is (car x) when (car x)
; is an integerp, then change the default value given getprop in
; max-absolute-event-number.

  (if (integerp (car x)) (car x) (caar x)))

(defun access-event-tuple-depth (x)
  (if (integerp (car x)) 0 (cdar x)))

(defun access-event-tuple-type (x)
  (cond ((symbolp (cdr x)) ;eviscerated event
         nil)
        ((symbolp (cadr x))
         (if (eq (cadr x) 'mutual-recursion)
             'defuns
           (cadr x)))
        (t (caaadr x))))

(defun access-event-tuple-skipped-proofs-p (x)
  (cond ((symbolp (cdr x)) ;eviscerated event
         nil)
        ((symbolp (cadr x))
         nil)
        (t (cdaadr x))))

(defun access-event-tuple-namex (x)

; Note that namex might be 0, a single name, or a list of names.  Included in
; the last case is the possibility of the list being nil (as from an
; encapsulate event introducing no constrained functions).

  (cond
   ((symbolp (cdr x)) ;eviscerated event
    nil)
   ((symbolp (cadr x))
    (case (cadr x)
          (defuns (strip-cars (cddr x)))
          (mutual-recursion (strip-cadrs (cddr x)))
          ((verify-guards in-theory
                          in-arithmetic-theory
                          regenerate-tau-database
                          push-untouchable remove-untouchable reset-prehistory
                          set-body table)
           0)
          (encapsulate (signature-fns (caddr x)))
          (t (caddr x))))
   (t (cadadr x))))

(defun access-event-tuple-form (x)
  (if (symbolp (cadr x))
      (cdr x)
    (cddr x)))

(defun access-event-tuple-symbol-class (x)
  (if (symbolp (cadr x))
      :program
    (cddadr x)))

; Essay on Command Tuples

; When LD has executed a world-changing form, it stores a "command tuple" as
; the new 'global-value of 'command-landmark.  These landmarks divide the world
; up into "command blocks" and each command block contains one or or event
; blocks.  Command blocks are important when the user queries the system about
; his current state, wishes to undo, etc.  Commands are enumerated sequentially
; from 0 with "absolute command numbers."

; We define command tuples in a way analogous to event tuples, although
; commands are perhaps simpler because most of their characteristics are
; inherited from the event tuples in the block.  We must store the current
; default-defun-mode so that we can offer to redo :program functions after ubt.
; (A function is offered for redoing if its defun-mode is :program.  But the
; function is redone by executing the command that created it.  The command may
; recreate many functions and specify a :mode for each.  We must re-execute the
; command with the same default-defun-mode we did last to be sure that the
; functions it creates have the same defun-mode as last time.)

(defrec command-tuple

; Warning: Keep this in sync with the definitions of
; safe-access-command-tuple-number and pseudo-command-landmarkp in community
; book books/system/pseudo-good-worldp.lisp, and function
; safe-access-command-tuple-form in the ACL2 sources.

; See make-command-tuple for a discussion of defun-mode/form.

; If form is an embedded event form, then last-make-event-expansion is nil
; unless form contains a call of make-event whose :check-expansion field is not
; a cons, in which case last-make-event-expansion is the result of removing all
; make-event calls from form.

  (number defun-mode/form cbd . last-make-event-expansion)
  t)

(defun make-command-tuple (n defun-mode form cbd last-make-event-expansion)

; Defun-Mode is generally the default-defun-mode of the world in which this
; command is being executed.  But there are two possible exceptions.  See
; add-command-tuple.

; We assume that most commands are executed with defun-mode :program.  So we
; optimize our representation of command tuples accordingly.  No form that
; creates a function can have a keyword as its car.

  (make command-tuple
        :number n ; the absolute command number
        :defun-mode/form (if (eq defun-mode :program)
                             form
                           (cons defun-mode form))
        :cbd cbd
        :last-make-event-expansion last-make-event-expansion))

(defun access-command-tuple-number (x)
  (declare (xargs :guard (weak-command-tuple-p x)))
  (access command-tuple x :number))

(defun access-command-tuple-defun-mode (x)
  (let ((tmp (access command-tuple x :defun-mode/form)))
    (if (keywordp (car tmp))
        (car tmp)
      :program)))

(defun access-command-tuple-form (x)

; See also safe-access-command-tuple-form for a safe version (i.e., with guard
; t).

  (let ((tmp (access command-tuple x :defun-mode/form)))
    (if (keywordp (car tmp))
        (cdr tmp)
      tmp)))

(defun safe-access-command-tuple-form (x)

; This is just a safe version of access-command-tuple-form.

  (declare (xargs :guard t))
  (let ((tmp (and (consp x)
                  (consp (cdr x))
                  (access command-tuple x :defun-mode/form))))
    (if (and (consp tmp)
             (keywordp (car tmp)))
        (cdr tmp)
      tmp)))

(defun access-command-tuple-last-make-event-expansion (x)
  (access command-tuple x :last-make-event-expansion))

(defun access-command-tuple-cbd (x)
  (access command-tuple x :cbd))

; Absolute Event and Command Numbers

(defun max-absolute-event-number (wrld)

; This is the maximum absolute event number in use at the moment.  It
; is just the number found in the most recently completed event
; landmark.  We initialize the event-landmark with number -1 (see
; primordial-world-globals) so that next-absolute-event-number returns
; 0 the first time.

  (access-event-tuple-number (global-val 'event-landmark wrld)))

(defun next-absolute-event-number (wrld)
  (1+ (max-absolute-event-number wrld)))

(defun max-absolute-command-number (wrld)

; This is the largest absolute command number in use in wrld.  We
; initialize it to -1 (see primordial-world-globals) so that
; next-absolute-command-number works.

  (access-command-tuple-number (global-val 'command-landmark wrld)))

(defun next-absolute-command-number (wrld)
  (1+ (max-absolute-command-number wrld)))

(defun scan-to-landmark-number (flg n wrld)

; We scan down wrld looking for a binding of 'event-landmark with n as
; its number or 'command-landmark with n as its number, depending on
; whether flg is 'event-landmark or 'command-landmark.

  (declare (xargs :guard (and (natp n)
                              (plist-worldp wrld))))
  #+acl2-metering
  (setq meter-maid-cnt (1+ meter-maid-cnt))
  (cond ((endp wrld)
         (er hard 'scan-to-landmark-number
             "We have scanned the world looking for absolute ~
              ~#0~[event~/command~] number ~x1 and failed to find it. ~
               There are two likely errors.  Either ~#0~[an event~/a ~
              command~] with that number was never stored or the ~
              index has somehow given us a tail in the past rather ~
              than the future of the target world."
             (if (equal flg 'event-landmark) 0 1)
             n))
        ((and (eq (caar wrld) flg)
              (eq (cadar wrld) 'global-value)
              (= n (if (eq flg 'event-landmark)
                       (access-event-tuple-number (cddar wrld))
                       (access-command-tuple-number (cddar wrld)))))
         #+acl2-metering
         (meter-maid 'scan-to-landmark-number 500 flg n)
         wrld)
        (t (scan-to-landmark-number flg n (cdr wrld)))))

; For information about the next few events, through lookup-world-index, see
; "The Event and Command Indices" in history-management.lisp.  As noted above,
; events below were originally located in that file, but are needed here to
; support ev-fncall-rec-logical.

(defun add-to-zap-table (val zt)

; Given a zap table, zt, that associates values to the indices
; 0 to n, we extend the table to associate val to n+1.

  (cond ((null zt) (list 0 val))
        (t (cons (1+ (car zt)) (cons val (cdr zt))))))

(defun fetch-from-zap-table (n zt)

; Retrieve the value associated with n in the zap table zt, or
; nil if there is no such association.

  (cond ((null zt) nil)
        ((> n (car zt)) nil)
        (t (nth (- (car zt) n) (cdr zt)))))

; These 7 lines of code took 3 days to write -- because we first implemented
; balanced binary trees and did the experiments described in the discussion on
; "The Event and Command Indices" found in history-management.lisp.

; Using zap tables we'll keep an index mapping absolute event numbers
; to tails of world.  We'll also keep such an index for commands typed
; by the user at the top-level of the ld loop.  The following two
; constants determine how often we save events and commands in their
; respective indices.

(defconst *event-index-interval* 10)
(defconst *command-index-interval* 10)

(defun lookup-world-index1 (n interval index wrld)

; Let index be a zap table that maps the integers 0 to k to worlds.
; Instead of numbering those worlds 0, 1, 2, ..., number them 0,
; 1*interval, 2*interval, etc.  So for example, if interval is 10 then
; the worlds are effectively numbered 0, 10, 20, ...  Now n is some
; world number (but not necessarily a multiple of interval).  We wish
; to find the nearest world in the index that is in the future of the
; world numbered by n.

; For example, if n is 2543 and interval is 10, then we will look for
; world 2550, which will be found in the table at 255.  Of course, the
; table might not contain an entry for 255 yet, in which case we return
; wrld.

  (let ((i (floor (+ n (1- interval))
                  interval)))
    (cond ((or (null index)
               (> i (car index)))
           wrld)
          (t (fetch-from-zap-table i index)))))

(defun lookup-world-index (flg n wrld)

; This is the general-purpose function that takes an arbitrary
; absolute command or event number (flg is 'COMMAND or 'EVENT) and
; returns the world that starts with the indicated number.

  (cond ((eq flg 'event)
         (let ((n (min (max-absolute-event-number wrld)
                       (max n 0))))
           (scan-to-landmark-number 'event-landmark
                                    n
                                    (lookup-world-index1
                                     n
                                     *event-index-interval*
                                     (global-val 'event-index wrld)
                                     wrld))))
        (t
         (let ((n (min (max-absolute-command-number wrld)
                       (max n 0))))
           (scan-to-landmark-number 'command-landmark
                                    n
                                    (lookup-world-index1
                                     n
                                     *command-index-interval*
                                     (global-val 'command-index wrld)
                                     wrld))))))

(defconst *unspecified-xarg-value*

; Warning: This must be a consp.  See comments in functions that use this
; constant.

  '(unspecified))

(defun get-unambiguous-xargs-flg1/edcls1 (key v edcls event-msg)

; V is the value specified so far for key in the XARGSs of this or previous
; edcls, or else the consp *unspecified-xarg-value* if no value has been
; specified yet.  We return an error message if any non-symbol is used for the
; value of key or if a value different from that specified so far is specified.
; Otherwise, we return either *unspecified-xarg-value* or the uniformly agreed
; upon value.  Event-msg is a string or message for fmt's tilde-atsign and is
; used only to indicate the event in an error message; for example, it may be
; "DEFUN" to indicate a check for a single definition, or "DEFUN event" or
; "MUTUAL-RECURSION" to indicate a check that is made for an entire clique.

  (cond
   ((null edcls) v)
   ((eq (caar edcls) 'xargs)
    (let ((temp (assoc-keyword key (cdar edcls))))
      (cond ((null temp)
             (get-unambiguous-xargs-flg1/edcls1 key v (cdr edcls) event-msg))
            ((not (symbolp (cadr temp)))
             (msg "It is illegal to specify ~x0 to be ~x1.  The value must be ~
                   a symbol."
                  key (cadr temp)))
            ((or (consp v)
                 (eq v (cadr temp)))
             (get-unambiguous-xargs-flg1/edcls1 key (cadr temp) (cdr edcls)
                                                event-msg))
            (t
             (msg "It is illegal to specify ~x0 ~x1 in one place and ~x2 in ~
                   another within the same ~@3.  The functionality controlled ~
                   by that flag operates on the entire ~@3."
                  key v (cadr temp) event-msg)))))
   (t (get-unambiguous-xargs-flg1/edcls1 key v (cdr edcls) event-msg))))

(defun get-unambiguous-xargs-flg1/edcls (key v edcls event-msg ctx state)

; This is just a version of get-unambiguous-xargs-flg1/edcls1 that returns an
; error triple.

  (let ((ans (get-unambiguous-xargs-flg1/edcls1 key v edcls event-msg)))
    (cond ((or (equal ans *unspecified-xarg-value*)
               (atom ans))
           (value ans))
          (t (er soft ctx "~@0" ans)))))

(defun get-unambiguous-xargs-flg1 (key lst event-msg ctx state)

; We scan the edcls of lst and either extract a single uniformly agreed upon
; value for key among the XARGS and return that value, or else no value is
; specified and we return the consp *unspecified-xarg-value*, or else two or
; more values are specified and we cause an error.  We also cause an error if
; any edcls specifies a non-symbol for the value of key.  Thus, if we return a
; symbol it is the uniformly agreed upon value and if we return a consp there
; was no value specified.

  (cond ((null lst) (value *unspecified-xarg-value*))
        (t (er-let*
               ((v (get-unambiguous-xargs-flg1 key (cdr lst) event-msg ctx
                                               state))
             (ans (get-unambiguous-xargs-flg1/edcls key v (fourth (car lst))
                                                    event-msg ctx state)))
            (value ans)))))

(defun get-unambiguous-xargs-flg (key lst default ctx state)

; Lst is a list of mutually recursive defun tuples of the form (name args doc
; edcls body).  We scan the edcls for the settings of the XARGS keyword key.
; If at least one entry specifies a setting, x, and all entries that specify a
; setting specify x, we return x.  If no entry specifies a setting, we return
; default.  If two or more entries specify different settings, we cause an
; error.

; See also get-unambiguous-xargs-flg-lst for a similar function that instead
; allows a different value for each defun tuple, and returns the list of these
; values instead of a single value.

; We assume every legal value of key is a symbol.  If you supply a consp
; default and the default is returned, then no value was specified for key.

; Just to be concrete, suppose key is :mode and default is :logic.  The
; user has the opportunity to specify :mode in each element of lst, i.e., he
; may say to make the first fn :logic and the second fn :program.  But
; that is nonsense.  We have to process the whole clique or none at all.
; Therefore, we have to meld all of his various :mode specs together to come
; up with a setting for the DEFUNS event.  This function explores lst and
; either comes up with an unambiguous :mode or else causes an error.

  (let ((event-msg (if (cdr lst) "MUTUAL-RECURSION" "DEFUN event")))
    (er-let* ((x (get-unambiguous-xargs-flg1 key lst event-msg ctx state)))
      (cond ((consp x) (value default))
            (t (value x))))))

(defun get-unambiguous-xargs-flg-lst (key lst default ctx state)

; See get-unambiguous-xargs-flg.  Unlike that function, this function allows a
; different value for each defun tuple, and returns the list of these values
; instead of a single value.

  (cond ((null lst) (value nil))
        (t (er-let*
               ((ans (get-unambiguous-xargs-flg1/edcls key
                                                       *unspecified-xarg-value*
                                                       (fourth (car lst))
                                                       "DEFUN"
                                                       ctx
                                                       state))
                (rst (get-unambiguous-xargs-flg-lst key (cdr lst) default ctx
                                                    state)))
             (value (cons (if (consp ans) ; ans = *unspecified-xarg-value*
                              default
                            ans)
                          rst))))))

(defun remove-strings (l)
  (cond ((null l) nil)
        ((stringp (car l))
         (remove-strings (cdr l)))
        (t (cons (car l) (remove-strings (cdr l))))))

(defun rev-union-equal (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (cond ((endp x) y)
        ((member-equal (car x) y)
         (rev-union-equal (cdr x) y))
        (t
         (rev-union-equal (cdr x) (cons (car x) y)))))

(defun translate-declaration-to-guard-var-lst (x var-lst wrld)

; It is assumed that (translate-declaration-to-guard x 'var wrld) is
; non-nil.  This function translates the declaration x for each of the
; vars in var-lst and returns the list of translations.

  (declare (xargs :guard (and (true-listp var-lst)
                              (plist-worldp wrld))))
  (cond ((null var-lst) nil)
        (t (cons (translate-declaration-to-guard x (car var-lst) wrld)
                 (translate-declaration-to-guard-var-lst x
                                                         (cdr var-lst)
                                                         wrld)))))

(defun get-guards2 (edcls targets wrld stobjs-acc guards-acc)

; Targets is a subset of (GUARDS TYPES), where we pick up expressions from
; :GUARD and :STOBJS XARGS declarations if GUARDS is in the list and we pick up
; expressions corresponding to TYPE declarations if TYPES is in the list.

; See get-guards for an example of what edcls looks like.  We require that
; edcls contains only valid type declarations, as explained in the comment
; below about translate-declaration-to-guard-var-lst.

; We are careful to preserve the order, except that we consider :stobjs as
; going before :guard.  (An example is (defun load-qs ...) in community book
; books/defexec/other-apps/qsort/programs.lisp.)  Before Version_3.5, Jared
; Davis sent us the following example, for which guard verification failed on
; the guard of the guard, because the :guard conjuncts were unioned into the
; :type contribution to the guard, leaving a guard of (and (natp n) (= (length
; x) n) (stringp x)).  It seems reasonable to accumulate the guard conjuncts in
; the order presented by the user.

; (defun f (x n)
;   (declare (xargs :guard (and (stringp x)
;                               (natp n)
;                               (= (length x) n)))
;            (type string x)
;            (ignore x n))
;   t)

  (cond ((null edcls)
         (revappend stobjs-acc (reverse guards-acc)))
        ((and (eq (caar edcls) 'xargs)
              (member-eq 'guards targets))

; We know (from chk-dcl-lst) that (cdar edcls) is a "keyword list"
; and so we can assoc-keyword up it looking for :GUARD.  We also know
; that there is at most one :GUARD entry.

         (let* ((temp1 (assoc-keyword :GUARD (cdar edcls)))
                (guard-conjuncts
                 (if temp1
                     (if (and (true-listp (cadr temp1))
                              (eq (car (cadr temp1)) 'AND))
                         (or (cdr (cadr temp1))
; The following (list t) avoids ignoring :guard (and).
                             (list t))
                       (list (cadr temp1)))
                   nil))
                (temp2 (assoc-keyword :STOBJS (cdar edcls)))
                (stobj-conjuncts
                 (if temp2
                     (stobj-recognizer-terms
                      (cond
                       ((symbol-listp (cadr temp2))
                        (cadr temp2))
                       ((and (cadr temp2)
                             (symbolp (cadr temp2)))
                        (list (cadr temp2)))
                       (t nil))
                      wrld)
                   nil)))
           (get-guards2 (cdr edcls)
                        targets
                        wrld
                        (rev-union-equal stobj-conjuncts
                                         stobjs-acc)
                        (rev-union-equal guard-conjuncts
                                         guards-acc))))
        ((and (eq (caar edcls) 'type)
              (member-eq 'types targets))
         (get-guards2 (cdr edcls)
                      targets
                      wrld

; The call of translate-declaration-to-guard-var-lst below assumes that
; (translate-declaration-to-guard (cadr (car edcls)) 'var wrld) is non-nil.
; This is indeed the case, because edcls is as created by chk-defuns-tuples,
; which leads to a call of chk-dcl-lst to check that the type declarations are
; legal.

                      stobjs-acc
                      (rev-union-equal (translate-declaration-to-guard-var-lst
                                        (cadr (car edcls))
                                        (cddr (car edcls))
                                        wrld)
                                       guards-acc)))
        (t (get-guards2 (cdr edcls) targets wrld stobjs-acc guards-acc))))

(defun get-guards1 (edcls targets args name wrld)

; We compute the guards but add (state-p name) when necessary:

; When a function definition has a state argument but does not explicitly
; include state among its :stobjs declarations (presumably because
; (set-state-ok t) has been executed), the conjuncts returned by get-guards2 do
; not include (state-p state).  Thus, we add this conjunct when (1) targets
; includes the symbol, guards; (2) the formal arguments, args, include state;
; (3) (state-p state) is not already in the result of get-guards2; and (4) the
; function symbol in question, name, is not state-p itself, whose guard is
; truly t.  If the (state-p state) conjunct is added, it is added in front of
; the other conjuncts, consistently with the order described in :DOC
; guard-miscellany.

; Note that we may pass in args = nil to avoid adding a state-p call, for
; example when defining a macro.  In that case name is ignored, so it is safe
; to pass in name = nil.

  (let ((conjuncts (get-guards2 edcls targets wrld nil nil)))
    (cond ((and (member-eq 'guards targets) ; (1)
                (member-eq 'state args) ; (2)
                (not (member-equal '(state-p state) conjuncts)) ; (3)
                (not (eq name 'state-p))) ; (4)
           (cons (fcons-term* 'state-p 'state) conjuncts))
          (t conjuncts))))

(defun get-guards (lst split-types-lst split-types-p wrld)

; Warning: see :DOC guard-miscellany for a specification of how conjuncts are
; ordered when forming the guard from :xargs and type declarations.

; Each element of lst is a 5-tuple (name args doc edcls body), where every TYPE
; declaration in edcls is valid (see get-guards2 for an explanation of why that
; is important).  We return a list in 1:1 correspondence with lst.  Each
; element is the untranslated guard or type expressions extracted from the
; edcls of the corresponding element of lst.  A typical value of edcls might be

; '((IGNORE X Y)
;   (XARGS :GUARD g1 :MEASURE m1 :HINTS ((id :USE ... :IN-THEORY ...)))
;   (TYPE ...)
;   (XARGS :GUARD g2 :MEASURE m2))

; The guard extracted from such an edcls is the conjunction of all the guards
; mentioned.

; We extract only the split-types expressions if split-types-p is true.
; Otherwise, we extract the guard expressions.  In both of these cases, the
; result depends on whether or not :split-types was assigned value t in the
; definition for the corresponding member of lst.

  (cond ((null lst) nil)
        (t (cons (let ((targets
                        (cond (split-types-p

; We are collecting type declarations for 'split-types-term properties.  Thus,
; we only collect these when the user has specified :split-types for a
; definition.

                               (and (car split-types-lst) '(types)))

; Otherwise, we are collecting terms for 'guard properties.  We skip type
; declarations when the user has specified :split-types for a definition.

                              ((car split-types-lst) '(guards))
                              (t '(guards types)))))
                   (conjoin-untranslated-terms
                    (and targets ; optimization
                         (get-guards1 (fourth (car lst))
                                      targets
                                      (second (car lst))
                                      (first (car lst))
                                      wrld))))
                 (get-guards (cdr lst) (cdr split-types-lst) split-types-p
                             wrld)))))

(defun dcls-guard-raw-from-def (def wrld)
  (let* ((dcls (append-lst (strip-cdrs (remove-strings
                                        (butlast (cddr def) 1)))))
         (split-types (get-unambiguous-xargs-flg1/edcls1
                       :split-types
                       *unspecified-xarg-value*
                       dcls
                       "irrelevant-error-string"))
         (guards (get-guards1
                  dcls
                  (cond ((or (equal split-types
                                    *unspecified-xarg-value*) ; default
                             (eq split-types nil))
                         '(guards types))
                        (t (assert$ (eq split-types t)

; By the time we get here, we have already done our checks for the defun,
; including the check that split-types above is not an error message, and is
; Boolean.  So if the assertion just above fails, then something has gone
; terribly wrong!

                                    '(guards))))
                  (cadr def) ; args
                  (car def) ; name
                  wrld))
         (guard (cond ((null guards) t)
                      ((null (cdr guards)) (car guards))
                      (t (cons 'and guards)))))
    (mv dcls guard)))

(defun get-event (name wrld)

; This function returns nil when name was not introduced by an ACL2 event.  For
; primitives without definitions, we believe that the absolute-event-number is
; 0 and, as laid down in primordial-world, the corresponding event-tuple is
; (list 'enter-boot-strap-mode operating-system).

  (let ((index (getpropc name 'absolute-event-number nil wrld)))
    (and index
         (access-event-tuple-form
          (cddr
           (car
            (lookup-world-index 'event index wrld)))))))

(defun get-skipped-proofs-p (name wrld)

; Keep this in sync with get-event.

  (declare (xargs :mode :program))
  (let ((index (getpropc name 'absolute-event-number nil wrld)))
    (and index
         (access-event-tuple-skipped-proofs-p
          (cddr
           (car
            (lookup-world-index 'event index wrld))))
         (not (getpropc name 'predefined nil wrld)))))

(defun negate-untranslated-form (x iff-flg)
  (cond ((and iff-flg
              (consp x)
              (eq (car x) 'not))
         (assert$ (consp (cdr x))
                  (cadr x)))
        (t (list 'not x))))

(defun event-tuple-fn-names (ev-tuple)
  (case (access-event-tuple-type ev-tuple)
    ((defun)
     (list (access-event-tuple-namex ev-tuple)))
    ((defuns defstobj)
     (access-event-tuple-namex ev-tuple))
    (otherwise nil)))

#-acl2-loop-only
(progn

(defvar *fncall-cache*
  '(nil))

(defun raw-ev-fncall-okp (wrld aokp &aux (w-state (w *the-live-state*)))
  (when (eq wrld w-state)
    (return-from raw-ev-fncall-okp :live))
  (let* ((fncall-cache *fncall-cache*)
         (cached-w (car fncall-cache)))
    (cond ((and wrld
                (eq wrld cached-w))
           t)
          (t
           (let ((fns nil))
             (loop for tail on wrld
                   until (eq tail w-state)
                   do (let ((trip (car tail)))
                        (cond
                         ((member-eq (cadr trip)
                                     '(unnormalized-body
                                       stobjs-out

; 'Symbol-class supports the programp call in ev-fncall-guard-er-msg.

                                       symbol-class
                                       table-alist))
                          (setq fns (add-to-set-eq (car trip) fns)))
                         ((and (eq (car trip) 'guard-msg-table)
                               (eq (cadr trip) 'table-alist))

; The table, guard-msg-table, is consulted in ev-fncall-guard-er-msg.

                          (return-from raw-ev-fncall-okp nil))
                         ((and (eq (car trip) 'event-landmark)
                               (eq (cadr trip) 'global-value))

; This case is due to the get-event call in guard-raw.

                          (setq fns
                                (union-eq (event-tuple-fn-names (cddr trip))
                                          fns)))
                         ((and aokp
                               (eq (car trip) 'attachment-records)
                               (eq (cadr trip) 'global-value))
                          (return-from raw-ev-fncall-okp nil))))
                   finally
                   (cond (tail (setf (car fncall-cache) nil
                                     (cdr fncall-cache) fns
                                     (car fncall-cache) wrld))
                         (t (return-from raw-ev-fncall-okp nil)))))
           t))))

(defun chk-raw-ev-fncall (fn wrld aokp)
  (let ((ctx 'raw-ev-fncall)
        (okp (raw-ev-fncall-okp wrld aokp)))
    (cond ((eq okp :live) nil)
          (okp
           (when (member-eq fn (cdr *fncall-cache*))
             (er hard ctx
                 "Implementation error: Unexpected call of raw-ev-fncall for ~
                  function ~x0 (the world is sufficiently close to (w state) ~
                  in general, but not for that function symbol)."
                 fn)))
          (t
           (er hard ctx
               "Implementation error: Unexpected call of raw-ev-fncall (the ~
                world is not sufficiently close to (w state)).")))))

(defun raw-ev-fncall (fn args latches w user-stobj-alist
                         hard-error-returns-nilp aok)

; Warning: Keep this in sync with raw-ev-fncall-simple.

; Here we assume that w is "close to" (w *the-live-state*), as implemented by
; chk-raw-ev-fncall.

  (the #+acl2-mv-as-values (values t t t)
       #-acl2-mv-as-values t
       (let* ((*aokp*

; We expect the parameter aok, here and in all functions in the "ev family"
; that take aok as an argument, to be Boolean.  If it's not, then there is no
; real harm done: *aokp* would be bound here to a non-Boolean value, suggesting
; that an attachment has been used when that isn't necessarily the case; see
; *aokp*.

               aok)
              (pair (assoc-eq 'state latches))
              (w (if pair (w (cdr pair)) w)) ; (cdr pair) = *the-live-state*
              (throw-raw-ev-fncall-flg t)
              (**1*-as-raw*

; We defeat the **1*-as-raw* optimization so that when we use raw-ev-fncall to
; evaluate a call of a :logic mode term, all of the evaluation will take place
; in the logic.  Note that we don't restrict this special treatment to
; :common-lisp-compliant functions, because such a function might call an
; :ideal mode function wrapped in ec-call.  But we do restrict to :logic mode
; functions, since they cannot call :program mode functions and hence there
; cannot be a subsidiary rebinding of **1*-as-raw* to t.

               (if (logicp fn w)
                   nil
                 **1*-as-raw*))
              (*1*fn (*1*-symbol fn))
              (applied-fn (cond
                           ((fboundp *1*fn) *1*fn)
                           ((and (global-val 'boot-strap-flg w)
                                 (not (global-val 'boot-strap-pass-2 w)))
                            fn)
                           (t
                            (er hard 'raw-ev-fncall
                                "We had thought that *1* functions were ~
                                 always defined outside the first pass of ~
                                 initialization, but the *1* function for ~
                                 ~x0, which should be ~x1, is not."
                                fn *1*fn))))
              (stobjs-out
               (cond ((eq fn 'return-last)

; Things can work out fine if we imagine that return-last returns a single
; value: in the case of (return-last ... (mv ...)), the mv returns a list and
; we just pass that along.

                      '(nil))
; The next form was originally conditionalized with #+acl2-extra-checks, but we
; want to do this unconditionally.
                     (latches ; optimization
                      (actual-stobjs-out fn args w user-stobj-alist))
                     (t (stobjs-out fn w))))
              (val (catch 'raw-ev-fncall
                     (chk-raw-ev-fncall fn w aok)
                     (cond ((not (fboundp fn))
                            (er hard 'raw-ev-fncall
                                "A function, ~x0, that was supposed to be ~
                                 defined is not.  Supposedly, this can only ~
                                 arise because of aborts during undoing.  ~
                                 There is no recovery from this erroneous ~
                                 state."
                                fn)))
                     (prog1
                         (let ((*hard-error-returns-nilp*
                                hard-error-returns-nilp))
                           #-acl2-mv-as-values
                           (apply applied-fn args)
                           #+acl2-mv-as-values
                           (cond ((null (cdr stobjs-out))
                                  (apply applied-fn args))
                                 (t (multiple-value-list
                                     (apply applied-fn args)))))
                       (setq throw-raw-ev-fncall-flg nil))))

; It is important to rebind w here, since we may have updated state since the
; last binding of w.

              (w (if pair

; We use the live state now if and only if we used it above, in which case (cdr
; pair) = *the-live-state*.

                     (w (cdr pair))
                   w)))

; Observe that if a throw to 'raw-ev-fncall occurred during the
; (apply fn args) then the local variable throw-raw-ev-fncall-flg
; is t and otherwise it is nil.  If a throw did occur, val is the
; value thrown.

         (cond
          (throw-raw-ev-fncall-flg
           (mv t (ev-fncall-msg val w user-stobj-alist) latches))
          (t #-acl2-mv-as-values ; adjust val for the multiple value case
             (let ((val
                    (cond
                     ((null (cdr stobjs-out)) val)
                     (t (cons val
                              (mv-refs (1- (length stobjs-out))))))))
               (mv nil
                   val
; The next form was originally conditionalized with #+acl2-extra-checks, with
; value latches when #-acl2-extra-checks; but we want this unconditionally.
                   (latch-stobjs stobjs-out ; adjusted to actual-stobjs-out
                                 val
                                 latches)))
             #+acl2-mv-as-values ; val already adjusted for multiple value case
             (mv nil
                 val
; The next form was originally conditionalized with #+acl2-extra-checks, with
; value latches when #-acl2-extra-checks; but we want this unconditionally.
                 (latch-stobjs stobjs-out ; adjusted to actual-stobjs-out
                               val
                               latches)))))))
)

(defun cltl-def-from-name2 (fn stobj-function axiomatic-p wrld)

; Normally we expect to find the cltl definition of fn at the first
; 'cltl-command 'global-value triple.  But if fn is introduced by encapsulate
; then we may have to search further.  Try this, for example:

; (encapsulate ((f (x) x))
;              (local (defun f (x) x))
;              (defun g (x) (f x)))
; (cltl-def-from-name 'f nil (w state))

  (cond ((endp wrld)
         nil)
        ((and (eq 'cltl-command (caar wrld))
              (eq 'global-value (cadar wrld))
              (let ((cltl-command-value (cddar wrld)))
                (assoc-eq fn
                          (if stobj-function
                              (nth (if axiomatic-p 6 4)
                                   cltl-command-value)
                            (cdddr cltl-command-value))))))
        (t (cltl-def-from-name2 fn stobj-function axiomatic-p (cdr wrld)))))

(defun cltl-def-from-name1 (fn stobj-function axiomatic-p wrld)

; See cltl-def-from-name, which is a wrapper for this function in which
; axiomatic-p is nil.  When axiomatic-p is t, then we are to return a function
; suitable for oneify, which in the stobj case is the axiomatic definition
; rather than the raw Lisp definition.

  (and (function-symbolp fn wrld)
       (let* ((event-number
               (getpropc (or stobj-function fn) 'absolute-event-number nil
                         wrld))
              (wrld
               (and event-number
                    (lookup-world-index 'event event-number wrld)))
              (def
               (and wrld
                    (cltl-def-from-name2 fn stobj-function axiomatic-p wrld))))
         (and def
              (or (null stobj-function)
                  (and (not (member-equal *stobj-inline-declare* def))
                       (or axiomatic-p
                           (not (getpropc stobj-function 'absstobj-info nil
                                          wrld)))))
              (cons 'defun def)))))

(defun cltl-def-from-name (fn wrld)

; This function returns the raw Lisp definition of fn.  If fn does not have a
; 'stobj-function property in wrld, then the returned definition is also the
; definition that is oneified to create the corresponding *1* function.

  (cltl-def-from-name1 fn
                       (getpropc fn 'stobj-function nil wrld)
                       nil
                       wrld))

(defun unmake-true-list-cons-nest (formal-args)

; Formal-args is a term.  We return a list of term t1, ..., tn such that
; formal-args is the translation of (list t1 ... tn), unless that is impossible
; in which case we return :fail.

  (cond ((equal formal-args *nil*) nil)
        ((quotep formal-args)
         (let ((lst (unquote formal-args)))
           (if (true-listp lst)
               (kwote-lst lst)
             :fail)))
        ((ffn-symb-p formal-args 'cons)
         (let ((rest (unmake-true-list-cons-nest (fargn formal-args 2))))
           (if (eq rest :fail)
               :fail
             (cons (fargn formal-args 1)
                   rest))))
        (t :fail)))

(defun unmake-formal-pairlis2 (term digits)

; Term is the second argument, possibly simplified, of a call of
; fmt-to-comment-window that arises from expanding a call of cw.  Thus, term
; can be of the form (pairlis2 (quote alist) formal-args), or a quoted list, or
; even a formal cons.  We return the list of terms corresponding to the cw
; call.

  (case-match term
    (('pairlis2 ('quote !digits)
                formal-args)
     (unmake-true-list-cons-nest formal-args))
    (('quote args-alist)
     (let ((len (length args-alist)))
       (if (and (<= len (length digits))
                (alistp args-alist)
                (equal (strip-cars args-alist)
                       (take len digits)))
           (kwote-lst (strip-cdrs args-alist))
         :fail)))
    (('cons ('quote (digit . x)) rest)
     (if (and (consp digits)
              (eql digit (car digits)))
         (let ((y (unmake-formal-pairlis2 rest (cdr digits))))
           (if (eq y :fail)
               :fail
             (cons (kwote x) y)))
       :fail))
    (('cons ('cons ('quote digit) x) rest)
     (if (and (consp digits)
              (eql digit (car digits)))
         (let ((y (unmake-formal-pairlis2 rest (cdr digits))))
           (if (eq y :fail)
               :fail
             (cons x y)))
       :fail))
    (& :fail)))

(defun collect-ignored-mv-vars (mv-var i bound vars/rest mv-nths/rest)

; For context, see the call of this function in untranslate1.  This function is
; called to check that a given lambda may be reasonably construed as an mv-let.
; It assumes that the mv-let was created using translate11-mv-let.

  (cond ((= i bound)
         (mv t nil))
        (t (mv-let (flg ignored-vars)
             (collect-ignored-mv-vars
              mv-var (1+ i) bound (cdr vars/rest) (cdr mv-nths/rest))
             (cond ((null flg) (mv nil nil))
                   (t (let ((next (car mv-nths/rest)))
                        (case-match next
                          (('hide ('mv-nth ('quote !i) !mv-var))
                           (mv t (cons (car vars/rest) ignored-vars)))
                          (('mv-nth ('quote !i) !mv-var)
                           (mv t ignored-vars))
                          (& (mv nil nil))))))))))

(mutual-recursion

; These functions assume that the input world is "close to" the installed
; world, (w *the-live-state*), since ultimately they typically lead to calls of
; the check chk-raw-ev-fncall within raw-ev-fncall.

; Here we combine what may naturally be thought of as two separate
; mutual-recursion nests: One for evaluation and one for untranslate.  However,
; functions in the ev nest call untranslate1 for error messages, and
; untranslate1 calls ev-fncall-w.  We are tempted to place the definitions of
; the untranslate functions first, but Allegro CL (6.2 and 7.0) produces a
; bogus warning in that case (which goes away if the char-code case is
; eliminated from ev-fncall-rec-logical!).

(defun guard-raw (fn wrld)

; Fn is a function symbol of wrld that is a primitive or is defined, hence is
; not merely constrained.  This function is responsible for returning a guard
; expression, g, suitable to print in messages reporting guard violations for
; calls of fn.

  (let ((trip (assoc-eq fn *primitive-formals-and-guards*)))
    (cond
     (trip (untranslate* (caddr trip) t wrld))
     (t (let ((ev (get-event fn wrld)))
          (cond
           ((atom ev)
            (er hard! 'guard-raw
                "Unable to find defining event for ~x0."
                fn))
           (t (let ((def ; strip off leading defun
                     (case (car ev)
                       (defun (cdr ev))
                       (mutual-recursion (assoc-eq fn (strip-cdrs (cdr ev))))
                       (verify-termination-boot-strap
; For some functions, like apply$, we wind up in this case.
                        (cdr (cltl-def-from-name fn wrld)))
                       (otherwise (er hard! 'guard-raw
                                      "Implementation error for ~x0: ~
                                       Unexpected event type, ~x1"
                                      `(guard-raw ',fn <wrld>)
                                      (car ev))))))
                (mv-let
                 (dcls guard)
                 (dcls-guard-raw-from-def def wrld)
                 (declare (ignore dcls))
                 guard)))))))))

(defun ev-fncall-guard-er (fn args w user-stobj-alist latches extra)

; This function is called only by ev-fncall-rec-logical, which do not expect to
; be executed.

; Note that user-stobj-alist is only used for error messages, so this function
; may be called in the presence of local stobjs.

  (mv t
      (ev-fncall-guard-er-msg fn

; We call guard-raw both here and in oneify-cltl-code (more precisely, the
; subroutine dcls-guard-raw-from-def of guard-raw is called in
; oneify-cltl-code), so that the logical behavior for guard violations agrees
; with what is actually executed.

                              (guard-raw fn w)
                              (stobjs-in fn w) args w user-stobj-alist extra)
      latches))

(defun ev-fncall-rec-logical (fn args w user-stobj-alist big-n safe-mode gc-off
                                 latches hard-error-returns-nilp aok)

; This is the "slow" code for ev-fncall-rec, for when raw-ev-fncall is not
; called.

; The following guard is simply a way to trick ACL2 into not objecting
; to the otherwise irrelevant hard-error-returns-nilp.  See the comment
; in ev, below, for a brief explanation.  See hard-error for a more
; elaborate one.

; Keep this function in sync with *primitive-formals-and-guards*.

  (declare (xargs :guard (and (plist-worldp w)
                              (equal hard-error-returns-nilp
                                     hard-error-returns-nilp))))
  (cond
   ((zp-big-n big-n)
    (mv t
        (cons "Evaluation ran out of time." nil)
        latches))
   (t
    (let* ((x (car args))
           (y (cadr args))
           (pair (assoc-eq 'state latches))
           (w (if pair (w-of-any-state (cdr pair)) w))
           (safe-mode-requires-check
            (and safe-mode
                 (acl2-system-namep fn w)
                 (not (equal (symbol-package-name fn) "ACL2"))))
           (stobj-primitive-p
            (let ((st (getpropc fn 'stobj-function nil w)))
              (and st
                   (member-eq st (stobjs-in fn w)))))
           (guard-checking-off
            (and gc-off

; Safe-mode defeats the turning-off of guard-checking, as does calling a stobj
; primitive that takes its live stobj as an argument.  If the latter changes,
; consider also changing oneify-cltl-code.

                 (not safe-mode-requires-check)
                 (not stobj-primitive-p)))
           (extra (if gc-off
                      (cond (safe-mode-requires-check t)
                            ((not guard-checking-off)
                             :live-stobj)
                            (t nil))
                    (and stobj-primitive-p
                         :live-stobj-gc-on))))

; Keep this in sync with *primitive-formals-and-guards*.

      (case fn
        (ACL2-NUMBERP
         (mv nil (acl2-numberp x) latches))
        (BAD-ATOM<=
         (cond ((or guard-checking-off
                    (and (bad-atom x)
                         (bad-atom y)))
                (mv nil (bad-atom<= x y) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (BINARY-*
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (acl2-numberp y)))
                (mv nil
                    (* x y)
                    latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (BINARY-+
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (acl2-numberp y)))
                (mv nil (+ x y) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (UNARY--
         (cond ((or guard-checking-off
                    (acl2-numberp x))
                (mv nil (- x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (UNARY-/
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (not (= x 0))))
                (mv nil (/ x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (<
         (cond ((or guard-checking-off
                    (and (real/rationalp x)
                         (real/rationalp y)))
                (mv nil (< x y) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (CAR
         (cond ((or guard-checking-off
                    (or (consp x)
                        (eq x nil)))
                (mv nil (car x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (CDR
         (cond ((or guard-checking-off
                    (or (consp x)
                        (eq x nil)))
                (mv nil (cdr x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (CHAR-CODE
         (cond ((or guard-checking-off
                    (characterp x))
                (mv nil (char-code x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (CHARACTERP
         (mv nil (characterp x) latches))
        (CODE-CHAR
         (cond ((or guard-checking-off
                    (and (integerp x)
                         (<= 0 x)
                         (< x 256)))
                (mv nil (code-char x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (COMPLEX
         (cond ((or guard-checking-off
                    (and (real/rationalp x)
                         (real/rationalp y)))
                (mv nil (complex x y) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (COMPLEX-RATIONALP
         (mv nil (complex-rationalp x) latches))
        #+:non-standard-analysis
        (COMPLEXP
         (mv nil (complexp x) latches))
        (COERCE
         (cond ((or guard-checking-off
                    (or (and (stringp x)
                             (eq y 'list))
                        (and (character-listp x)
                             (eq y 'string))))
                (mv nil (coerce x y) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (CONS
         (mv nil (cons x y) latches))
        (CONSP
         (mv nil (consp x) latches))
        (DENOMINATOR
         (cond ((or guard-checking-off
                    (rationalp x))
                (mv nil (denominator x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (EQUAL
         (mv nil (equal x y) latches))
        #+:non-standard-analysis
        (FLOOR1
         (cond ((or guard-checking-off
                    (realp x))
                (mv nil (floor x 1) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (IF
         (mv nil
             (er hard 'ev-fncall-rec
                 "This function should not be called with fn = 'IF!")
             latches))
        (IMAGPART
         (cond ((or guard-checking-off
                    (acl2-numberp x))
                (mv nil (imagpart x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (INTEGERP
         (mv nil (integerp x) latches))
        (INTERN-IN-PACKAGE-OF-SYMBOL
         (cond ((or guard-checking-off
                    (and (stringp x)
                         (symbolp y)))
                (mv nil (intern-in-package-of-symbol x y) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (NUMERATOR
         (cond ((or guard-checking-off
                    (rationalp x))
                (mv nil (numerator x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (PKG-IMPORTS
         (cond ((or guard-checking-off
                    (stringp x))
                (mv nil (pkg-imports x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (PKG-WITNESS
         (cond ((or guard-checking-off
                    (and (stringp x) (not (equal x ""))))
                (mv nil (pkg-witness x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (RATIONALP
         (mv nil (rationalp x) latches))
        #+:non-standard-analysis
        (REALP
         (mv nil (realp x) latches))
        (REALPART
         (cond ((or guard-checking-off
                    (acl2-numberp x))
                (mv nil (realpart x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (STRINGP
         (mv nil (stringp x) latches))
        (SYMBOL-NAME
         (cond ((or guard-checking-off
                    (symbolp x))
                (mv nil (symbol-name x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (SYMBOL-PACKAGE-NAME
         (cond ((or guard-checking-off
                    (symbolp x))
                (mv nil (symbol-package-name x) latches))
               (t (ev-fncall-guard-er fn args w user-stobj-alist latches
                                      extra))))
        (SYMBOLP
         (mv nil (symbolp x) latches))

; The next two functions have the obvious behavior on standard objects, which
; are the only ones ever present inside ACL2.

        #+:non-standard-analysis
        (STANDARDP
         (mv nil t latches))
        #+:non-standard-analysis
        (STANDARD-PART
         (mv nil x latches))
        #+:non-standard-analysis
        (I-LARGE-INTEGER ; We could omit this case, allowing a fall-through.
         (ev-fncall-null-body-er nil fn nil latches))
        (otherwise
         (cond
          ((and (null args)
                (car (stobjs-out fn w)))
           (mv t
               (ev-fncall-creator-er-msg fn)
               latches))
          (t
           (let ((alist (pairlis$ (formals fn w) args))
                 (body (body fn nil w))
                 (attachment (and aok
                                  (cdr (assoc-eq fn (all-attachments w))))))
             (mv-let
              (er val latches)
              (ev-rec (if guard-checking-off
                          ''t
                        (guard fn nil w))
                      alist w user-stobj-alist
                      (decrement-big-n big-n) (eq extra t) guard-checking-off
                      latches
                      hard-error-returns-nilp
                      aok)
              (cond
               (er (mv er val latches))
               ((null val)
                (ev-fncall-guard-er fn args w user-stobj-alist latches extra))
               ((and (eq fn 'hard-error)
                     (not hard-error-returns-nilp))

; Before we added this case, the following returned nil even though the result
; was t if we replaced ev-fncall-rec-logical by ev-fncall-rec.  That wasn't
; quite a soundness bug, event though the latter is defined to be the former,
; because ev-fncall-rec is untouchable; nevertheless the discrepancy was
; troubling.

;   (mv-let (erp val ign)
;           (ev-fncall-rec-logical 'hard-error '(top "ouch" nil) (w state)
;                                  (user-stobj-alist state)
;                                  100000 nil nil nil nil t)
;           (declare (ignore ign val))
;           erp)


                (mv t (illegal-msg) latches))
               ((eq fn 'throw-nonexec-error)
                (ev-fncall-null-body-er nil
                                        (car args)  ; fn
                                        (cadr args) ; args
                                        latches))
               ((member-eq fn '(pkg-witness pkg-imports))
                (mv t (unknown-pkg-error-msg fn (car args)) latches))
               (attachment
                (ev-fncall-rec-logical attachment args w user-stobj-alist
                                       (decrement-big-n big-n)
                                       safe-mode gc-off latches
                                       hard-error-returns-nilp aok))
               ((null body)
                (ev-fncall-null-body-er
                 (and (not aok) attachment)
                 fn args latches))
               (t
                (mv-let
                 (er val latches)
                 (ev-rec body alist w user-stobj-alist
                         (decrement-big-n big-n) (eq extra t)
                         guard-checking-off
                         latches
                         hard-error-returns-nilp
                         aok)
                 (cond
                  (er (mv er val latches))
                  ((eq fn 'return-last) ; avoid stobjs-out for return-last
                   (mv nil val latches))
                  (t (mv nil
                         val
                         (latch-stobjs
                          (actual-stobjs-out fn args w user-stobj-alist)
                          val
                          latches)))))))))))))))))

(defun ev-fncall-rec (fn args w user-stobj-alist big-n safe-mode gc-off latches
                         hard-error-returns-nilp aok)
  (declare (xargs :guard (plist-worldp w)))
  #-acl2-loop-only
  (cond (*ev-shortcut-okp*
         (cond ((fboundp fn)

; If fn is unbound and we used the logical code below, we'd get a
; hard error as caused by (formals fn w).

                (return-from ev-fncall-rec
                             (raw-ev-fncall fn args latches w user-stobj-alist
                                            hard-error-returns-nilp aok)))))
        (t
         (let ((pair (assoc-eq 'state latches)))
           (if (and pair
                    (eq (cdr pair) *the-live-state*))
               (progn
                 (er hard 'ev-fncall-rec
                     "ACL2 implementation error:  An attempt is being made to ~
                      evaluate a form involving the live state when ~
                      *ev-shortcut-okp* is nil. Please contact the ACL2 ~
                      implementors.")
                 (return-from ev-fncall-rec
                              (mv t
                                  (cons "Implementation error" nil)
                                  latches)))))))
  (ev-fncall-rec-logical fn args w user-stobj-alist big-n safe-mode gc-off
                         latches hard-error-returns-nilp aok))

#-acl2-loop-only
(progn
  (defvar *return-last-arg2*)
  (defvar *return-last-arg3*)
  (defvar *return-last-alist*)
  (defvar *return-last-fn-w*)
  (defvar *return-last-fn-user-stobj-alist*)
  (defvar *return-last-fn-big-n*)
  (defvar *return-last-fn-safe-mode*)
  (defvar *return-last-fn-gc-off*)
  (defvar *return-last-fn-latches*)
  (defvar *return-last-fn-hard-error-returns-nilp*)
  (defvar *return-last-fn-aok*))

(defun ev-rec-return-last (fn arg2 arg3 alist w user-stobj-alist big-n
                              safe-mode gc-off latches hard-error-returns-nilp
                              aok)

; This function should only be called when fn is a key of return-last-table,
; and is not mbe1-raw (which is handled directly in ev-rec, to avoid executing
; the :exec code).  Moreover, we get here only when the original return-last
; form is given a quoted first argument, so that ev-rec evaluation will treat
; return-last similarly to how it is treated in raw Lisp.  See the comment in
; ev-rec about how we leave it to the user not to remove a key from
; return-last-table before passing quotation of that key as the first argument
; of a return-last call.

  (assert$
   (not (eq fn 'mbe1-raw))
   (mv-let
    (er arg2-val latches)
    (let (#-acl2-loop-only (*aokp*

; See the #-acl2-loop-only definition of return-last and the comment just
; below.  Note that fn is not mbe1-raw, so this binding is appropriate.
; We are being a bit more generous here in our binding of *aokp*, but it seems
; fine to keep it simple here, and for since evaluation of arg2 does not affect
; the logical result, there is no soundness issue here.

                            t))
      (ev-rec arg2 alist w user-stobj-alist
              (decrement-big-n big-n)
              safe-mode gc-off latches hard-error-returns-nilp

; There is no logical problem with using attachments when evaluating the second
; argument of return-last, because logically the third argument provides the
; value(s) of a return-last call.  See related treatment of aokp in the
; #-acl2-loop-only definition of return-last.

              t))
    (cond (er (mv er arg2-val latches))
          (t (case fn

; We provide efficient handling for some common primitive cases.  Keep these
; cases in sync with corresponding cases in the #-acl2-loop-only definition of
; return-last.  Note however that mbe1-raw is already handled in ev-rec; we
; thus know that fn is not mbe1-raw.

; In the case of ec-call1 we expect ev-rec to call the appropriate *1* function
; anyhow, so we can treat it as a progn.

               ((progn ec-call1-raw)
                (ev-rec arg3 alist w user-stobj-alist
                        (decrement-big-n big-n)
                        safe-mode gc-off latches hard-error-returns-nilp aok))
               (with-guard-checking1-raw
                (return-last
                 'with-guard-checking1-raw
                 arg2-val
                 (ev-rec arg3 alist w user-stobj-alist
                         (decrement-big-n big-n)
                         safe-mode
                         (gc-off1 arg2-val)
                         latches hard-error-returns-nilp aok)))
               (otherwise
                #+acl2-loop-only
                (ev-rec arg3 alist w user-stobj-alist
                        (decrement-big-n big-n)
                        safe-mode gc-off latches hard-error-returns-nilp aok)

; The following raw Lisp code is a bit odd in its use of special variables.
; Our original motivation was to work around problems that SBCL had with large
; quoted constants in terms passed to eval (SBCL bug 654289).  While this issue
; was fixed in SBCL 1.0.43.19, nevertheless we believe that it is still an
; issue for CMUCL and, for all we know, it could be an issue for future Lisps.
; The use of special variables keeps the terms small that are passed to eval.

                #-acl2-loop-only
                (let ((*return-last-arg2* arg2-val)
                      (*return-last-arg3* arg3)
                      (*return-last-alist* alist)
                      (*return-last-fn-w* w)
                      (*return-last-fn-user-stobj-alist* user-stobj-alist)
                      (*return-last-fn-big-n* big-n)
                      (*return-last-fn-safe-mode* safe-mode)
                      (*return-last-fn-gc-off* gc-off)
                      (*return-last-fn-latches* latches)
                      (*return-last-fn-hard-error-returns-nilp*
                       hard-error-returns-nilp)
                      (*return-last-fn-aok* aok))
                  (eval `(,fn *return-last-arg2*
                              (ev-rec *return-last-arg3*
                                      *return-last-alist*
                                      *return-last-fn-w*
                                      *return-last-fn-user-stobj-alist*
                                      *return-last-fn-big-n*
                                      *return-last-fn-safe-mode*
                                      *return-last-fn-gc-off*
                                      *return-last-fn-latches*
                                      *return-last-fn-hard-error-returns-nilp*
                                      *return-last-fn-aok*)))))))))))

(defun ev-rec (form alist w user-stobj-alist big-n safe-mode gc-off latches
                    hard-error-returns-nilp aok)

; See also ev-respecting-ens.

; Note: Latches includes a binding of 'state.  See the Essay on EV.
; If you provide no latches and form changes some stobj, a hard error
; occurs.  Thus, if you provide no latches and no error occurs, you
; may ignore the output latches.

; Hard-error-returns-nilp is explained in the comment in hard-error.
; Essentially, two behaviors of (hard-error ...) are possible: return
; nil or signal an error.  Both are sound.  If hard-error-returns-nilp
; is t then hard-error just returns nil; this is desirable setting if
; you are evaluating a form in a conjecture being proved: its logical
; meaning really is nil.  But if you are evaluating a form for other
; reasons, e.g., to compute something, then hard-error should probably
; signal an error, because something is wrong.  In that case,
; hard-error-returns-nilp should be set to nil.  Nil is the
; conservative setting.

  (declare (xargs :guard (and (plist-worldp w)
                              (termp form w)
                              (symbol-alistp alist))))
  (cond ((zp-big-n big-n)
         (mv t (cons "Evaluation ran out of time." nil) latches))
        ((variablep form)
         (let ((pair (assoc-eq form alist)))
           (cond (pair (mv nil (cdr pair) latches))
                 (t (mv t
                        (msg "Unbound var ~x0."
                             form)
                        latches)))))
        ((fquotep form)
         (mv nil (cadr form) latches))
        ((translated-acl2-unwind-protectp form)

; We relegate this special case to a separate function, even though it could be
; open-coded, because it is so distracting.

         (ev-rec-acl2-unwind-protect form alist w user-stobj-alist
                                     (decrement-big-n big-n)
                                     safe-mode gc-off
                                     latches
                                     hard-error-returns-nilp
                                     aok))
        ((eq (ffn-symb form) 'wormhole-eval)

; Because this form has been translated, we know it is of the form
; (wormhole-eval 'name '(lambda ...) term) where the quoted lambda is either
; (lambda (whs) body) or (lambda () body), where body has also been translated.
; Furthermore, we know that all the free variables of the lambda are bound in
; the current environment.  Logically this term returns nil.  Actually, it
; applies the lambda expression to the most recent output of the named wormhole
; and stores the result as the most recent output.

         #+acl2-loop-only
         (mv nil nil latches)
         #-acl2-loop-only
         (progn
           (cond (*wormholep*
                  (setq *wormhole-status-alist*
                        (put-assoc-equal
                         (f-get-global 'wormhole-name
                                       *the-live-state*)
                         (f-get-global 'wormhole-status
                                       *the-live-state*)
                         *wormhole-status-alist*))))
           (let* ((*wormholep* t)
                  (name (cadr (fargn form 1)))
                  (formals (lambda-formals (cadr (fargn form 2))))
                  (whs (car formals)) ; will be nil if formals is nil!
                  (body (lambda-body (cadr (fargn form 2))))
                  (alist (if formals
                             (cons (cons whs
                                         (cdr (assoc-equal
                                               name
                                               *wormhole-status-alist*)))
                                   alist)
                             alist)))
             (mv-let (body-er body-val latches)
                     (ev-rec body alist w user-stobj-alist
                             (decrement-big-n big-n) safe-mode gc-off latches
                             hard-error-returns-nilp
                             aok)
                     (cond
                      (body-er (mv t body-val latches))
                      (t (setq *wormhole-status-alist*
                               (put-assoc-equal name body-val
                                                *wormhole-status-alist*))
                         (mv nil nil latches)))))))
        ((eq (ffn-symb form) 'if)
         (mv-let (test-er test latches)
                 (ev-rec (fargn form 1) alist w user-stobj-alist
                         (decrement-big-n big-n) safe-mode gc-off
                         latches
                         hard-error-returns-nilp
                         aok)
                 (cond
                  (test-er (mv t test latches))
                  (test
                   (ev-rec (fargn form 2) alist w user-stobj-alist
                           (decrement-big-n big-n) safe-mode gc-off
                           latches
                           hard-error-returns-nilp
                           aok))
                  (t (ev-rec (fargn form 3) alist w user-stobj-alist
                             (decrement-big-n big-n) safe-mode gc-off
                             latches
                             hard-error-returns-nilp
                             aok)))))
        ((eq (ffn-symb form) 'mv-list)
         (ev-rec (fargn form 2) alist w user-stobj-alist
                 (decrement-big-n big-n) safe-mode gc-off
                 latches hard-error-returns-nilp aok))
        ((and (eq (ffn-symb form) 'return-last)
              (not (and (equal (fargn form 1) ''mbe1-raw)

; We generally avoid running the :exec code for an mbe call.  But in safe-mode,
; it is critical to run the exec code and check its equality to the logic code
; (respecting the guard of return-last in the case that the first argument is
; 'mbe1-raw).  See the comments in note-4-3 for an example showing why it is
; unsound to avoid this check in safe-mode, and see (defun-*1* return-last ...)
; for a discussion of why we do not consider the case (not gc-off) here.

                        safe-mode)))
         (let ((fn (and (quotep (fargn form 1))
                        (unquote (fargn form 1)))))
           (cond
            ((and fn (symbolp fn))

; Translate11 will generally ensure that the value of (return-last-lookup fn w)
; is not nil.  What happens if the user (with an active trust tag) removes the
; association of a key in return-last-table with a non-nil value?  The
; resulting state will be a weird one, in which a direct evaluation of the
; return-last form in raw Lisp will continue to take effect.  So we match that
; behavior here, rather than requiring (return-last-lookup fn w) to be non-nil.
; We leave it to translate11 to enforce this requirement on return-last calls,
; and we leave it to the user not to remove a key from return-last-table before
; passing quotation of that key as the first argument of a return-last call.

             (cond
              ((eq fn 'mbe1-raw)

; We avoid running the exec code (see comment above).

               (ev-rec (fargn form 3) ; optimization: avoid exec argument
                       alist w user-stobj-alist
                       (decrement-big-n big-n) safe-mode gc-off latches
                       hard-error-returns-nilp aok))
              (t (ev-rec-return-last fn (fargn form 2) (fargn form 3)
                                     alist w user-stobj-alist
                                     big-n safe-mode gc-off latches
                                     hard-error-returns-nilp aok))))
            (t ; first arg is not quotep with special behavior; treat as progn
             (mv-let (args-er args latches)
                     (ev-rec-lst (fargs form) alist w user-stobj-alist
                                 (decrement-big-n big-n) safe-mode gc-off
                                 latches
                                 hard-error-returns-nilp
                                 aok)
                     (cond (args-er (mv t args latches))
                           (t (mv nil (car (last args)) latches))))))))
        (t (mv-let (args-er args latches)
                   (ev-rec-lst (fargs form) alist w user-stobj-alist
                               (decrement-big-n big-n) safe-mode gc-off
                               latches
                               hard-error-returns-nilp
                               aok)
                   (cond
                    (args-er (mv t args latches))
                    ((flambda-applicationp form)
                     (ev-rec (lambda-body (ffn-symb form))
                             (pairlis$ (lambda-formals (ffn-symb form)) args)
                             w user-stobj-alist
                             (decrement-big-n big-n) safe-mode gc-off
                             latches
                             hard-error-returns-nilp
                             aok))
                    (t (ev-fncall-rec (ffn-symb form) args w user-stobj-alist
                                      (decrement-big-n big-n)
                                      safe-mode gc-off latches
                                      hard-error-returns-nilp aok)))))))

(defun ev-rec-lst (lst alist w user-stobj-alist big-n safe-mode gc-off latches
                       hard-error-returns-nilp aok)
  (declare (xargs :guard (and (plist-worldp w)
                              (term-listp lst w)
                              (symbol-alistp alist))))
  (cond
   ((zp-big-n big-n)
    (mv t (cons "Evaluation ran out of time." nil) latches))
   ((null lst) (mv nil nil latches))
   (t (mv-let (first-er first-val first-latches)
              (ev-rec (car lst) alist w user-stobj-alist
                      (decrement-big-n big-n) safe-mode gc-off
                      latches
                      hard-error-returns-nilp
                      aok)
              (cond
               (first-er (mv first-er first-val first-latches))
               (t
                (mv-let (rest-er rest-val rest-latches)
                        (ev-rec-lst (cdr lst) alist w user-stobj-alist
                                    (decrement-big-n big-n) safe-mode gc-off
                                    first-latches
                                    hard-error-returns-nilp
                                    aok)
                        (cond
                         (rest-er (mv rest-er rest-val rest-latches))
                         (t (mv nil
                                (cons first-val rest-val)
                                rest-latches))))))))))

(defun ev-rec-acl2-unwind-protect (form alist w user-stobj-alist big-n
                                        safe-mode gc-off latches
                                        hard-error-returns-nilp aok)

; Sketch: We know that form is a termp wrt w and that it is recognized by
; translated-acl2-unwind-protectp.  We therefore unpack it into its body and
; two cleanup forms and give it special attention.  If the body evaluates
; without either an abort or any kind of "evaluation error" (e.g., ubv, udf, or
; guard error) then we return exactly what we would have returned had we
; evaluated form without special treatment.  But if body causes an evaluation
; error we run the cleanup1 code, just as Common Lisp would had the body been
; compiled and caused a hard lisp error.  Furthermore, if the evaluation of
; body is aborted, we ensure that the cleanup1 code is EV'd upon unwinding.

; See the Essay on Unwind-Protect in axioms.lisp.

  (declare (xargs :guard (and (plist-worldp w)
                              (termp form w)
                              (symbol-alistp alist))))
  (let ((temp nil))
    #+acl2-loop-only
    (declare (ignore temp))
    (mv-let
     (ans body cleanup1 cleanup2)
     (translated-acl2-unwind-protectp4 form)
     (declare (ignore ans))
     #-acl2-loop-only
     (cond ((live-state-p (cdr (assoc-eq 'STATE alist)))

; This code implements our unwind-protection from aborts.  Intuitively, we wish
; to push the cleanup form onto the unwind-protect stack provided the STATE
; being modified is the live state.  It is possible that STATE is not bound in
; alist.  If this happens then it is certainly not the live state and we do not
; push anything.

; The next problem, however, is what do we push?  In normal circumstances --
; i.e., body terminating without an evaluation error but signaling an error --
; cleanup1 is evaluated by ev.  But cleanup1 is evaluated in w, which may or
; may not be the installed world.  Hence, the meaning in w of the function
; symbol in the car of cleanup1 may be different from the raw lisp definition
; (if any) of that symbol.  So we can't do the usual and just push the car of
; cleanup1 and the values (in alist) of the arguments.  Furthermore, there is
; delicacy concerning the possibility that not all of the argument variables
; are bound in alist.  To make matters slightly worse, we can't cause any
; errors right now, no matter how screwed up cleanup1 might be, because no
; abort has happened and we are obliged to respect the semantics unless an
; abort happens.  To make a long story short, we do what is pretty obvious: we
; push onto the undo stack a form that calls EV to do the cleanup!  We use
; FUNCTION to capture the local environment, e.g., alist, which contains the
; values of all the variables occurring in the cleanup form.

            (setq temp
                  (cons "ev-rec-acl2-unwind-protect"
                        #'(lambda nil

; The Essay on Unwind-Protect says that we have the freedom to give arbitrary
; semantics to acl2-unwind-protect in the face of an abort.  So in this raw
; Lisp code, we take the liberty of binding *ev-shortcut-okp* to t even though
; when this cleanup code is executed, we may violate the requirement that the
; values of state globals guard-checking-on and safe-mode are respected in the
; arguments to ev-rec when *ev-shortcut-okp* is t.  This seems like quite a
; minor violation when doing cleanup.

                            (let ((*ev-shortcut-okp* t))
                              (mv-let (erp val latches)
                                (ev-rec cleanup1 alist
                                        w user-stobj-alist
                                        big-n safe-mode gc-off
                                        latches
                                        hard-error-returns-nilp
                                        aok)
                                (declare (ignore latches))
; Since 'STATE in alist is the live state, latches must be too.
                                (cond
                                 (erp
                                  (let ((state *the-live-state*))
                                    (er soft 'acl2-unwind-protect "~@0" val))))))
                            *the-live-state*)))
            (push-car temp
                      *acl2-unwind-protect-stack*
                      'ev-rec-acl2-unwind-protect)))
     (mv-let
      (body-erp body-val body-latches)
      (ev-rec body alist w user-stobj-alist big-n safe-mode gc-off latches
              hard-error-returns-nilp aok)
      (cond
       (body-erp ; "hard error", e.g., guard error in body

; It is possible that the evaluation of body pushed some additional
; cleanup forms before the abort occurred.  We must get back down to
; the form we pushed.  This is analogous to the similar situation in
; acl2-unwind-protect itself.

        #-acl2-loop-only
        (cond (temp (acl2-unwind -1 temp)))

        (mv-let
         (clean-erp clean-val clean-latches)
         (ev-rec cleanup1
                 (put-assoc-eq 'state
                               (cdr (assoc-eq 'state body-latches))
                               alist)
                 w user-stobj-alist big-n safe-mode gc-off
                 body-latches hard-error-returns-nilp aok)

         #-acl2-loop-only
         (cond (temp
                (pop (car *acl2-unwind-protect-stack*))))
         (cond
          (clean-erp ; "hard error," e.g., guard error in cleanup!
           (mv t
               (msg "An evaluation error, ``~@0'', occurred while ~
                     evaluating the body of an acl2-unwind-protect ~
                     form.  While evaluating the first cleanup form a ~
                     second evaluation error occurred, ``~@1''.  The ~
                     body of the acl2-unwind-protect is ~p2 and the ~
                     first cleanup form is ~p3.  Because the cleanup ~
                     form failed, the state being returned may not be ~
                     fully cleaned up."
                    body-val
                    clean-val
                    (untranslate* body nil w)
                    (untranslate* cleanup1 nil w))
               clean-latches))
          (t

; In this case, clean-val is the binding of 'state in
; clean-latches because the cleanup form produces a state.

           (mv body-erp body-val clean-latches)))))
       ((car body-val) ; "soft error," i.e., body signaled error

; We think this call of acl2-unwind is unnecessary.  It is here in
; case the evaluation of body pushed some additional forms onto the
; unwind protect stack and it removes those forms down to the one we
; pushed.  But if a soft error has arisen, any forms pushed would have
; been popped on the way back to here.  But this code is safer.

        #-acl2-loop-only
        (cond (temp (acl2-unwind -1 temp)))

; Because body is known to produce an error triple we know its car is
; the error flag, the cadr is the value, and the caddr is a state
; The test above therefore detects that the body signaled an error.

        (mv-let
         (clean-erp clean-val clean-latches)
         (ev-rec cleanup1
                 (put-assoc-eq 'state
                               (cdr (assoc-eq 'state body-latches))
                               alist)
                 w user-stobj-alist big-n safe-mode gc-off
                 body-latches hard-error-returns-nilp aok)
         #-acl2-loop-only
         (cond (temp
                (pop (car *acl2-unwind-protect-stack*))))
         (cond
          (clean-erp ; "hard error," e.g., guard error in cleanup!
           (mv t
               (msg "An evaluation error, ``~@0'', occurred while ~
                     evaluating the first cleanup form of an ~
                     acl2-unwind-protect.  The body of the ~
                     acl2-unwind-protect is ~p1 and the first cleanup ~
                     form is ~p2.  Because the cleanup form failed, ~
                     the state being returned may not be fully cleaned ~
                     up."
                    clean-val
                    (untranslate* body nil w)
                    (untranslate* cleanup1 nil w))
               clean-latches))
          (t

; We pass a SOFT error up, containing the cleaned up state.

           (mv nil
               (list (car body-val)
                     (cadr body-val)
                     (cdr (assoc-eq 'state clean-latches)))
               clean-latches)))))
       (t ; no hard or soft error

; Same safety check described above.

        #-acl2-loop-only
        (cond (temp (acl2-unwind -1 temp)))

        (mv-let
         (clean-erp clean-val clean-latches)
         (ev-rec cleanup2
                 (put-assoc-eq 'state
                               (cdr (assoc-eq 'state body-latches))
                               alist)
                 w user-stobj-alist big-n safe-mode gc-off
                 body-latches hard-error-returns-nilp aok)

         #-acl2-loop-only
         (cond (temp
                (pop (car *acl2-unwind-protect-stack*))))
         (cond
          (clean-erp ; "hard error," e.g., guard error in cleanup!
           (mv t
               (msg "An evaluation error, ``~@0'', occurred while ~
                     evaluating the second cleanup form of an ~
                     acl2-unwind-protect.  The body of the ~
                     acl2-unwind-protect is ~p1 and the second cleanup ~
                     form is ~p2.  Because the cleanup form failed, ~
                     the state being returned may not be fully cleaned ~
                     up."
                    clean-val
                    (untranslate* body nil w)
                    (untranslate* cleanup2 nil w))
               clean-latches))
          (t
           (mv nil
               (list (car body-val)
                     (cadr body-val)
                     (cdr (assoc-eq 'state clean-latches)))
               clean-latches))))))))))

(defun ev-fncall-w-body (fn args w user-stobj-alist safe-mode gc-off
                            hard-error-returns-nilp aok)

; There is no guard specified for this :program mode function.

; WARNING: Do not call this function if args contains the live state
; or any other live stobjs and evaluation of form could modify any of
; those stobjs.  Otherwise, the calls of ev-fncall-rec below violate
; requirement (1) in The Essay on EV, which is stated explicitly for
; ev but, in support of ev, is applicable to ev-fncall-rec as well.
; Note that users cannot make such a call because they cannot put live
; stobjs into args.

; It may see inappropriate that we temporarily modify state in a
; function that does not take state.  But what we are really doing is
; writing a function that has nothing to do with state, yet handles
; guards in a way appropriate to the current world.  We need to modify
; the state to match the inputs safe-mode and gc-off.

; Keep the two ev-fncall-rec calls below in sync.

  #-acl2-loop-only
  (let ((*ev-shortcut-okp* t))
    (state-free-global-let*
     ((safe-mode safe-mode)
      (guard-checking-on

; Guard-checking-on will be t or nil -- not :nowarn, :all, or :none, but it
; doesn't seem that this would be a problem.

       (not gc-off)))
     (mv-let
      (erp val latches)
      (ev-fncall-rec fn args w user-stobj-alist (big-n) safe-mode gc-off
                     nil ; latches
                     hard-error-returns-nilp
                     aok)
      (progn (when latches
               (er hard 'ev-fncall-w
                   "The call ~x0 returned non-nil latches."
                   (list 'ev-fncall-w
                         fn
                         args
                         '<wrld>
                         (if user-stobj-alist
                             '<user-stobj-alist>
                           nil)
                         safe-mode gc-off hard-error-returns-nilp aok)))
             (mv erp val)))))
  #+acl2-loop-only
  (mv-let
   (erp val latches)
   (ev-fncall-rec fn args w user-stobj-alist (big-n) safe-mode gc-off
                  nil ; latches
                  hard-error-returns-nilp
                  aok)
   (declare (ignore latches))
   (mv erp val)))

(defun ev-fncall-w (fn args w user-stobj-alist safe-mode gc-off
                       hard-error-returns-nilp aok)

; See the warning in ev-fncall-w-body.

  (declare (xargs :guard (ev-fncall-w-guard fn args w nil)))
  (ev-fncall-w-body fn args w user-stobj-alist safe-mode gc-off
                    hard-error-returns-nilp aok))

(defun ev-fncall-w! (fn args w user-stobj-alist safe-mode gc-off
                        hard-error-returns-nilp aok)

; See the warning in ev-fncall-w-body.

  (declare (xargs :guard t))
  (if (ev-fncall-w-guard fn args w nil)
      (ev-fncall-w-body fn args w user-stobj-alist safe-mode gc-off
                        hard-error-returns-nilp aok)
    (mv t (msg "Guard failure for ~x0 in a call of ~x1: fn = ~x2, args = ~X34"
               'ev-fncall-w-guard
               'ev-fncall-w!
               fn args
               (evisc-tuple 5 ; print-level
                            7 ; print-length
                            (list (cons w *evisceration-world-mark*)) ; alist
                            nil ; hiding-cars
                            )))))

(defun ev-w (form alist w user-stobj-alist safe-mode gc-off
                  hard-error-returns-nilp aok)

; WARNING: Do not call this function if alist contains the live state or any
; other live stobjs and evaluation of form could modify any of those stobjs.
; Otherwise, the calls of ev-rec below violate requirement (1) in The Essay on
; EV, which is stated explicitly for ev but, in support of ev, is applicable to
; ev-rec as well.  Note that users cannot make such a call because they cannot
; put live stobjs into alist.

; Also see related functions ev-fncall-w and magic-ev-fncall, which pay
; attention to avoiding calls of untouchable functions, and hence are not
; themselves untouchable.  But ev-w is untouchable because we don't make any
; such check, even in the guard.

; Note that user-stobj-alist is only used for error messages, so this function
; may be called in the presence of local stobjs.  Probably user-stobj-alist
; could be replaced as nil because of the stobj restriction on alist.

  (declare (xargs :guard (and (plist-worldp w)
                              (termp form w)
                              (symbol-alistp alist))))

; See the comment in ev for why we don't check the time limit here.

  #-acl2-loop-only
  (let ((*ev-shortcut-okp* t))
    (state-free-global-let*
     ((safe-mode safe-mode)
      (guard-checking-on

; Guard-checking-on will be t or nil -- not :nowarn, :all, or :none -- but it
; doesn't seem that this would be a problem, provided the call is made with
; gc-off set to t if guard-checking-on is either nil or :none (don't forget
; :none!).

       (not gc-off)))
     (mv-let
      (erp val latches)
      (ev-rec form alist w user-stobj-alist (big-n) safe-mode gc-off
              nil ; latches
              hard-error-returns-nilp
              aok)
      (progn (when latches
               (er hard! 'ev-w
                   "The call ~x0 returned non-nil latches."
                   (list 'ev-w form alist '<wrld>
                         (if user-stobj-alist '<user-stobj-alist> nil)
                         safe-mode gc-off
                         hard-error-returns-nilp aok)))
             (mv erp val)))))
  #+acl2-loop-only
  (mv-let (erp val latches)
          (ev-rec form alist w user-stobj-alist (big-n) safe-mode gc-off
                  nil ; latches
                  hard-error-returns-nilp
                  aok)
          (declare (ignore latches))
          (mv erp val)))

(defun guard-er-message-coda (fn stobjs-in args w extra erp)
  (msg "~@0~@1~@2~@3"
       (cond ((and (eq fn 'return-last)
                   (eq (car args) 'mbe1-raw))
              (msg "  This offending call is equivalent to the more common ~
                    form, ~x0."
                   `(mbe :logic
                         ,(untranslate* (kwote (caddr args)) nil w)
                         :exec
                         ,(untranslate* (kwote (cadr args)) nil w))))
             (t ""))
       (cond ((eq extra :live-stobj)

; This case occurs if we attempt to execute the call of a "oneified" function
; on a live stobj (including state) when the guard of the fn is not satisfied,
; where the function is either a primitive listed in *super-defun-wart-table*
; or is defined by defstobj or defabsstobj.

; Warning: Before removing this error, consider that in general guard-checking
; may be defeated by :set-guard-checking :none, so we may be relying on this
; error for built-in functions like aset-t-stack that rely on guard-checking to
; validate their arguments.

              (msg "~|This error is being reported even though guard-checking ~
                    has been turned off, because a stobj argument of ~x0 is ~
                    the ``live'' ~p1 and ACL2 does not support non-compliant ~
                    live stobj manipulation."
                   fn
                   (find-first-non-nil stobjs-in)))
             ((eq extra :live-stobj-gc-on)
              (msg "~|This error will be reported even if guard-checking is ~
                    turned off, because a stobj argument of ~x0 is the ~
                    ``live'' ~p1 and ACL2 does not support non-compliant live ~
                    stobj manipulation."
                   fn
                   (find-first-non-nil stobjs-in)))
             ((eq extra :no-extra) "") ; :no-extra is unused as of late 10/2013
             (extra *safe-mode-guard-er-addendum*)
             (t "~|See :DOC set-guard-checking for information about ~
                 suppressing this check with (set-guard-checking :none), as ~
                 recommended for new users."))
       (error-trace-suggestion t)
       (if erp
           (msg "~|~%Note: Evaluation has resulted in an error for the form ~
                 associated with ~x0 in the table, ~x1, to obtain a custom ~
                 guard error message.  Consider modifying that table entry; ~
                 see :doc set-guard-msg."
                fn
                'guard-msg-table)
         "")))

(defun ev-fncall-guard-er-msg (fn guard stobjs-in args w user-stobj-alist
                                  extra)

; Guard is printed directly, so should generally be in untranslated form.

; Note that user-stobj-alist is only used for error messages, so this function
; may be called in the presence of local stobjs.

  (prog2$
   (save-ev-fncall-guard-er fn guard stobjs-in args)
   (let ((form (cdr (assoc-eq fn (table-alist 'guard-msg-table w)))))
     (mv-let
      (erp msg)
      (cond (form (ev-w form
                        (list (cons 'world w)
                              (cons 'args args)
                              (cons 'coda
                                    (guard-er-message-coda
                                     fn
                                     stobjs-in
                                     args
                                     w
                                     extra
                                     nil ; erp [no error yet!]
                                     )))
                        w
                        user-stobj-alist
                        nil ; safe-mode
                        t   ; gc-off
                        t   ; hard-error-returns-nilp
                        t   ; aok
                        ))
            (t (mv nil nil)))
      (or msg
          (msg
           "The guard for the~#0~[ :program~/~] function call ~x1, which is ~
            ~P23, is violated by the arguments in the call ~P45.~@6"
           (if (programp fn w) 0 1)
           (cons fn (formals fn w))
           guard
           nil ; might prefer (term-evisc-tuple nil state) if we had state here
           (cons fn
                 (untranslate*-lst
                  (apply-user-stobj-alist-or-kwote user-stobj-alist args nil)
                  nil
                  w))
           (evisc-tuple 3 4 nil nil)
           (guard-er-message-coda fn stobjs-in args w extra erp)))))))

(defun ev-fncall-msg (val wrld user-stobj-alist)

; Warning: Keep this in sync with ev-fncall-rec-logical.

; Note that user-stobj-alist is only used for error messages, so this function
; may be called in the presence of local stobjs.

  (cond
   ((and (consp val)
         (eq (car val) 'ev-fncall-null-body-er))
    (ev-fncall-null-body-er-msg (cadr val) (caddr val) (cdddr val)))
   ((and (consp val)
         (eq (car val) 'ev-fncall-guard-er))

; We get here if val is of the form (ev-fncall-guard-er fn args guard
; stobjs-in safep).  This happens if a :program function finds its
; guard violated or a :logic function finds its guard violated while
; guard-checking is on.

    (ev-fncall-guard-er-msg (cadr val) (cadddr val) (car (cddddr val))
                            (caddr val) wrld user-stobj-alist
                            (cadr (cddddr val))))
   ((and (consp val)
         (eq (car val) 'ev-fncall-creator-er))

; This is similar to the preceding case, except that there are no stobjs-in.

    (ev-fncall-creator-er-msg
     (cadr val)))
   ((and (consp val)
         (member-eq (car val) '(pkg-witness pkg-imports)))
    (unknown-pkg-error-msg (car val) (cadr val)))

; At one time we had the following case:

;  ((and (consp val)
;        (eq (car val) 'program-only-er))

; In this case we (essentially) returned (program-only-er-msg (cadr val) (caddr
; val) (cadr (cddddr val))).  But we get here by catching a throw of val, which
; no longer is of the form (program-only-er ...); see the comment about the
; call of oneify-fail-form on 'program-only-er (and other arguments) in
; oneify-cltl-code.

   ((eq val 'illegal)
    (illegal-msg))
   (t (er hard 'raw-ev-fncall
          "An unrecognized value, ~x0, was thrown to 'raw-ev-fncall.~@1"
          val
          (error-trace-suggestion t)))))

(defun untranslate1 (term iff-flg untrans-tbl preprocess-fn wrld)

; Warning: It would be best to keep this in sync with
; obviously-iff-equiv-terms, specifically, giving similar attention in both to
; functions like implies, iff, and not, which depend only on the propositional
; equivalence class of each argument.

; Warning: Consider keeping in sync with community book
; books/misc/rtl-untranslate.lisp.

; We return a Lisp form that translates to term if iff-flg is nil and
; that translates to a term iff-equivalent to term if iff-flg is t.
; Wrld is an ACL2 logical world, which may be used to improve the
; appearance of the result, in particular to allow (nth k st) to be
; printed as (nth *field-name* st) if st is a stobj name and
; field-name is the kth field name of st; similarly for update-nth.
; It is perfectly appropriate for wrld to be nil if such extra
; information is not important.

; Note: The only reason we need the iff-flg is to let us translate (if
; x1 t x2) into (or x1 x2) when we are in an iff situation.  We could
; ask type-set to check that x1 is Boolean, but that would require
; passing wrld into untranslate.  That, in turn, would require passing
; wrld into such syntactic places as prettyify-clause and any other
; function that might want to print a term.

; Warning: This function may not terminate.  We should consider making it
; primitive recursive by adding a natural number ("count") parameter.

  (let ((term (if preprocess-fn
                  (mv-let (erp term1)
                          (ev-fncall-w preprocess-fn
                                       (list term wrld)
                                       wrld
                                       nil ; user-stobj-alist
                                       nil ; safe-mode
                                       nil ; gc-off
                                       nil ; hard-error-returns-nilp
                                       t   ; aok
                                       )
                          (or (and (null erp) term1)
                              term))
                term)))
    (cond ((variablep term) term)
          ((fquotep term)
           (cond ((or (acl2-numberp (cadr term))
                      (stringp (cadr term))
                      (characterp (cadr term))
                      (eq (cadr term) nil)
                      (eq (cadr term) t)
                      (keywordp (cadr term)))
                  (cadr term))
                 (t term)))
          ((flambda-applicationp term)
           (or (case-match term
                 ((('lambda (mv-var . rest)
                     (('lambda vars/rest body)
                      . mv-nths/rest))
                   tm
                   . rest)

; Here we are attempting to reconstruct an mv-let:

;   (mv-let (v0 ... vn)
;     tm
;     (declare (ignore ...)) ; if any of the vi are ignored
;     body)

; So term is, we expect, as follows, where w1, ... wk enumerates the variables
; occurring free in body that are not among v0, ..., vn.  Here we ignore the
; distinction between translated and untranslated terms for tm and body, and
; we also ignore the effects of type declarations.

;   ((lambda (mv w1 ... wk)
;            ((lambda (v0 ... vn w1 ... wk) body)
;             (mv-nth '0 mv) ; instead (hide (mv-nth '0 mv)) if v0 is ignored
;             ...
;             (mv-nth 'n mv) ; instead (hide (mv-nth 'n mv)) if vn is ignored
;             w1 ... wk))
;    tm
;    w1 ... wk)

                  (let* ((len-rest (len rest))
                         (len-vars/rest (len vars/rest))
                         (len-vars (- len-vars/rest len-rest)))
                    (and (true-listp rest)
                         (true-listp mv-nths/rest)
                         (true-listp vars/rest)
                         (<= 0 len-vars)
                         (equal len-vars/rest (len mv-nths/rest))
                         (equal (nthcdr len-vars vars/rest)
                                rest)
                         (equal (nthcdr len-vars mv-nths/rest)
                                rest)
                         (mv-let (flg ignores)
                           (collect-ignored-mv-vars mv-var 0 len-vars
                                                    vars/rest mv-nths/rest)
                           (and flg
                                (let* ((uterm
                                        (untranslate1 tm nil untrans-tbl
                                                      preprocess-fn wrld))
                                       (uterm
                                        (if (and (consp uterm) ; always true?
                                                 (eq (car uterm) 'list))
                                            (cons 'mv (cdr uterm))
                                          uterm))
                                       (ubody
                                        (untranslate1 body iff-flg
                                                      untrans-tbl
                                                      preprocess-fn wrld)))
                                  `(mv-let ,(take len-vars vars/rest)
                                     ,uterm
                                     ,@(and ignores
                                            `((declare (ignore ,@ignores))))
                                     ,ubody))))))))
               (make-let-or-let*
                (collect-non-trivial-bindings (lambda-formals (ffn-symb term))
                                              (untranslate1-lst (fargs term)
                                                                nil
                                                                untrans-tbl
                                                                preprocess-fn
                                                                wrld))
                (untranslate1 (lambda-body (ffn-symb term)) iff-flg untrans-tbl
                              preprocess-fn wrld))))
          ((eq (ffn-symb term) 'if)
           (case-match term
             (('if x1 *nil* *t*)
              (negate-untranslated-form
               (untranslate1 x1 t untrans-tbl preprocess-fn wrld)
               iff-flg))
             (('if x1 x2  *nil*)
              (untranslate-and (untranslate1 x1 t untrans-tbl preprocess-fn wrld)
                               (untranslate1 x2 iff-flg untrans-tbl preprocess-fn
                                             wrld)
                               iff-flg))
             (('if x1 *nil* x2) ; (thm (equal (and (not (not x)) y) (and x y)))
              (untranslate-and (negate-untranslated-form
                                (untranslate1 x1 t untrans-tbl preprocess-fn
                                              wrld)
                                t)
                               (untranslate1 x2 iff-flg untrans-tbl preprocess-fn
                                             wrld)
                               iff-flg))
             (('if x1 x1 x2)
              (untranslate-or (untranslate1 x1 iff-flg untrans-tbl preprocess-fn
                                            wrld)
                              (untranslate1 x2 iff-flg untrans-tbl preprocess-fn
                                            wrld)))
             (('if x1 x2 *t*)

; Observe that (if x1 x2 t) = (if x1 x2 (not nil)) = (if x1 x2 (not x1)) =
; (if (not x1) (not x1) x2) = (or (not x1) x2).

              (untranslate-or (negate-untranslated-form
                               (untranslate1 x1 t untrans-tbl preprocess-fn
                                             wrld)
                               iff-flg)
                              (untranslate1 x2 iff-flg untrans-tbl preprocess-fn
                                            wrld)))
             (('if x1 *t* x2)
              (cond
               ((or iff-flg
                    (and (nvariablep x1)
                         (not (fquotep x1))
                         (member-eq (ffn-symb x1)
                                    *untranslate-boolean-primitives*)))
                (untranslate-or (untranslate1 x1 t untrans-tbl
                                              preprocess-fn wrld)
                                (untranslate1 x2 iff-flg untrans-tbl
                                              preprocess-fn wrld)))
               (t (untranslate-if term iff-flg untrans-tbl preprocess-fn wrld))))
             (& (untranslate-if term iff-flg untrans-tbl preprocess-fn wrld))))
          ((and (eq (ffn-symb term) 'not)
                (nvariablep (fargn term 1))
                (not (fquotep (fargn term 1)))
                (member-eq (ffn-symb (fargn term 1)) '(< o<)))
           (list (if (eq (ffn-symb (fargn term 1)) '<) '<= 'o<=)
                 (untranslate1 (fargn (fargn term 1) 2) nil untrans-tbl
                               preprocess-fn wrld)
                 (untranslate1 (fargn (fargn term 1) 1) nil untrans-tbl
                               preprocess-fn wrld)))
          ((member-eq (ffn-symb term) '(implies iff))
           (fcons-term* (ffn-symb term)
                        (untranslate1 (fargn term 1) t untrans-tbl preprocess-fn
                                      wrld)
                        (untranslate1 (fargn term 2) t untrans-tbl preprocess-fn
                                      wrld)))
          ((eq (ffn-symb term) 'cons) (untranslate-cons term untrans-tbl
                                                        preprocess-fn wrld))
          ((and (eq (ffn-symb term) 'synp)

; Even though translate insists that the second argument of synp is quoted, can
; we really guarantee that every termp given to untranslate came through
; translate?  Not necessarily; for example, maybe substitution was performed
; for some reason (say, in the proof-builder one replaces the quoted argument
; by a variable known to be equal to it).

                (quotep (fargn term 2)))

; We store the quotation of the original form of a syntaxp or bind-free
; hypothesis in the second arg of its expansion.  We do this so that we
; can use it here and output something that the user will recognize.

           (cadr (fargn term 2)))
          ((and (eq (ffn-symb term) 'return-last)
                (quotep (fargn term 1))
                (let* ((key (unquote (fargn term 1)))
                       (fn (and (symbolp key)
                                key
                                (let ((tmp (return-last-lookup key
                                                               wrld)))
                                  (if (consp tmp) (car tmp) tmp))))
                       (args (and fn
                                  (untranslate1-lst (cdr (fargs term)) nil
                                                    untrans-tbl preprocess-fn
                                                    wrld))))
                  (and fn
                       (case fn
                         (mbe1 (let ((exec (car args))
                                     (logic (cadr args)))
                                 (cond
                                  ((eq exec t) `(mbt ,logic))
                                  (t `(mbe :logic ,logic :exec ,exec)))))
                         (ec-call1
                          (cond ((eq (car args) nil)
                                 `(ec-call ,(cadr args)))
                                (t (cons fn args))))
                         (time$1

; Warning: Keep this in sync with time$.

; Here we handle the most common case, where we are untranslating the
; translation of (time$ ...).  With some effort we could also handle supplied
; keyword arguments for time$ calls.  It should be reasonable rare to hit this
; case, since remove-guard-holders often eliminates calls of return-last before
; untranslate is called, and for the remaining cases it is probably infrequent
; to have calls of time$ with keyword arguments.

                          (or (and (eq key 'time$1-raw)
                                   (let ((car-args (car args))
                                         (cadr-args (cadr args)))
                                     (mv-let (real-mintime
                                              run-mintime
                                              minalloc
                                              msg
                                              msg-args)
                                       (case-match car-args
                                         (('LIST ; already untranslated
                                           real-mintime
                                           run-mintime
                                           minalloc
                                           msg
                                           msg-args)
                                          (mv real-mintime
                                              run-mintime
                                              minalloc
                                              msg
                                              msg-args))
                                         (('quote (real-mintime
                                                   run-mintime
                                                   minalloc
                                                   msg
                                                   msg-args))
                                          (mv (maybe-kwote real-mintime)
                                              (maybe-kwote run-mintime)
                                              (maybe-kwote minalloc)
                                              (maybe-kwote msg)
                                              (maybe-kwote msg-args)))
                                         (& (mv :fail nil nil nil nil)))
                                       (cond
                                        ((eq real-mintime :fail)
                                         (cons fn args))
                                        (t
                                         `(time$ ,cadr-args
                                                 ,@(and (not (eql real-mintime
                                                                  0))
                                                        `(:real-mintime
                                                          ,real-mintime))
                                                 ,@(and run-mintime
                                                        `(:run-mintime
                                                          ,run-mintime))
                                                 ,@(and minalloc
                                                        `(:minalloc ,minalloc))
                                                 ,@(and msg
                                                        `(:msg ,msg))
                                                 ,@(and msg-args
                                                        `(:args ,msg-args))))))))
                              (cons fn args)))
                         (otherwise (cons fn args)))))))
          (t (or (case-match term
                   ((fmt-to-comment-window ('quote str)
                                           x
                                           ('quote '0)
                                           ('quote 'nil)
                                           base/radix)
                    (and (member-eq fmt-to-comment-window
                                    '(fmt-to-comment-window
                                      fmt-to-comment-window!))
                         (let ((y (unmake-formal-pairlis2 x *base-10-chars*)))
                           (cond ((eq y :fail) nil)
                                 ((equal base/radix *nil*)
                                  (list* (if (eq fmt-to-comment-window
                                                 'fmt-to-comment-window)
                                             'cw
                                           'cw!)
                                         str
                                         (untranslate1-lst y nil untrans-tbl
                                                           preprocess-fn
                                                           wrld)))
                                 (t
                                  (list* (if (eq fmt-to-comment-window
                                                 'fmt-to-comment-window)
                                             'cw-print-base-radix
                                           'cw-print-base-radix!)
                                         (untranslate1 base/radix nil untrans-tbl
                                                       preprocess-fn
                                                       wrld)
                                         str
                                         (untranslate1-lst y nil untrans-tbl
                                                           preprocess-fn
                                                           wrld)))))))
                   (& nil))
                 (let* ((pair (cdr (assoc-eq (ffn-symb term)
                                             untrans-tbl)))
                        (op (car pair))
                        (flg (cdr pair))
                        (const
                         (and (member-eq (ffn-symb term)
                                         '(nth update-nth update-nth-array))
                              (quotep (fargn term 1))
                              (integerp (cadr (fargn term 1)))
                              (<= 0 (cadr (fargn term 1)))
                              (accessor-root (cadr (fargn term 1))
                                             (case (ffn-symb term)
                                               (nth (fargn term 2))
                                               (update-nth (fargn term 3))
                                               (t ; update-nth-array
                                                (fargn term 4)))
                                             wrld))))
                   (cond
                    (op (cons op
                              (cond
                               (const ; ignoring flg, which is presumably nil
                                (cons const
                                      (untranslate1-lst
                                       (cdr (fargs term))
                                       nil untrans-tbl preprocess-fn wrld)))
                               (t
                                (untranslate1-lst
                                 (cond
                                  ((and flg
                                        (cdr (fargs term))
                                        (null (cddr (fargs term))))
                                   (right-associated-args (ffn-symb term)
                                                          term))
                                  (t (fargs term)))
                                 nil untrans-tbl preprocess-fn wrld)))))
                    (const
                     (list* (ffn-symb term)
                            const
                            (untranslate1-lst (cdr (fargs term)) nil
                                              untrans-tbl
                                              preprocess-fn
                                              wrld)))
                    (t
                     (mv-let
                       (ad-list base)
                       (make-reversed-ad-list term nil)
                       (cond (ad-list
                              (pretty-parse-ad-list
                               ad-list '(#\R) 1
                               (untranslate1 base nil untrans-tbl preprocess-fn
                                             wrld)))
                             (t (cons (ffn-symb term)
                                      (untranslate1-lst (fargs term) nil
                                                        untrans-tbl
                                                        preprocess-fn
                                                        wrld)))))))))))))

(defun untranslate-cons1 (term untrans-tbl preprocess-fn wrld)

; This function digs through a 'cons nest, untranslating each of the
; elements and the final non-cons cdr.  It returns two results:  the
; list of untranslated elements and the untranslated final term.

  (cond ((variablep term) (mv nil (untranslate1 term nil untrans-tbl
                                                preprocess-fn wrld)))
        ((fquotep term) (mv nil (untranslate1 term nil untrans-tbl preprocess-fn
                                              wrld)))
        ((eq (ffn-symb term) 'cons)
         (mv-let (elements x)
                 (untranslate-cons1 (fargn term 2) untrans-tbl preprocess-fn
                                    wrld)
                 (mv (cons (untranslate1 (fargn term 1) nil untrans-tbl
                                         preprocess-fn wrld)
                           elements)
                     x)))
        (t (mv nil (untranslate1 term nil untrans-tbl preprocess-fn wrld)))))

(defun untranslate-cons (term untrans-tbl preprocess-fn wrld)

; Term is a non-quote term whose ffn-symb is 'cons.  We untranslate
; it into a CONS, a LIST, or a LIST*.

  (mv-let (elements x)
          (untranslate-cons1 term untrans-tbl preprocess-fn wrld)
          (cond ((eq x nil) (cons 'list elements))
                ((null (cdr elements)) (list 'cons (car elements) x))
                (t (cons 'list* (append elements (list x)))))))

(defun untranslate-if (term iff-flg untrans-tbl preprocess-fn wrld)
  (cond ((> (case-length nil term) 2)
         (case-match term
                     (('if (& key &) & &)
                      (list* 'case key
                             (untranslate-into-case-clauses
                              key term iff-flg untrans-tbl preprocess-fn
                              wrld)))))
        ((> (cond-length term) 2)
         (cons 'cond (untranslate-into-cond-clauses term iff-flg untrans-tbl
                                                    preprocess-fn
                                                    wrld)))
        (t (list 'if
                 (untranslate1 (fargn term 1) t untrans-tbl preprocess-fn wrld)
                 (untranslate1 (fargn term 2) iff-flg untrans-tbl preprocess-fn
                               wrld)
                 (untranslate1 (fargn term 3) iff-flg untrans-tbl preprocess-fn
                               wrld)))))

(defun untranslate-into-case-clauses (key term iff-flg untrans-tbl preprocess-fn
                                          wrld)

; We generate the clauses of a (case key ...) stmt equivalent to term.
; We only call this function when the case-length of term is greater
; than 1.  If we called it when case-length were 1, it would not
; terminate.

  (case-match term
              (('if (pred !key ('quote val)) x y)
               (cond ((and (or (eq pred 'equal)
                               (eq pred 'eql))
                           (eqlablep val))
                      (cond ((or (eq val t)
                                 (eq val nil)
                                 (eq val 'otherwise))
                             (cons (list (list val)
                                         (untranslate1 x iff-flg untrans-tbl
                                                       preprocess-fn wrld))
                                   (untranslate-into-case-clauses
                                    key y iff-flg untrans-tbl preprocess-fn wrld)
                                  ))
                            (t (cons (list val (untranslate1 x iff-flg
                                                             untrans-tbl
                                                             preprocess-fn
                                                             wrld))
                                     (untranslate-into-case-clauses
                                      key y iff-flg untrans-tbl preprocess-fn
                                      wrld)))))
                     ((and (eq pred 'member)
                           (eqlable-listp val))
                      (cons (list val (untranslate1 x iff-flg untrans-tbl
                                                    preprocess-fn wrld))
                            (untranslate-into-case-clauses
                             key y iff-flg untrans-tbl preprocess-fn wrld)))
                     (t (list (list 'otherwise
                                    (untranslate1 term iff-flg untrans-tbl
                                                  preprocess-fn wrld))))))
              (& (list (list 'otherwise
                             (untranslate1 term iff-flg untrans-tbl preprocess-fn
                                           wrld))))))

(defun untranslate-into-cond-clauses (term iff-flg untrans-tbl preprocess-fn
                                           wrld)

; We know cond-length is greater than 1; else this doesn't terminate.

  (case-match term
              (('if x1 x2 x3)
               (cons (list (untranslate1 x1 t untrans-tbl preprocess-fn wrld)
                           (untranslate1 x2 iff-flg untrans-tbl preprocess-fn
                                         wrld))
                     (untranslate-into-cond-clauses x3 iff-flg untrans-tbl
                                                    preprocess-fn wrld)))
              (& (list (list t (untranslate1 term iff-flg untrans-tbl
                                             preprocess-fn wrld))))))

(defun untranslate1-lst (lst iff-flg untrans-tbl preprocess-fn wrld)
  (cond ((null lst) nil)
        (t (cons (untranslate1 (car lst) iff-flg untrans-tbl preprocess-fn wrld)
                 (untranslate1-lst (cdr lst) iff-flg untrans-tbl preprocess-fn
                                   wrld)))))

;; Historical Comment from Ruben Gamboa:
;; I relaxed the guards for < and complex to use realp instead
;; of rationalp.  I also added complexp, realp, and floor1.

)

(defun ev-fncall (fn args state latches hard-error-returns-nilp aok)
  (declare (xargs :guard (state-p state)))
  (let #-acl2-loop-only ((*ev-shortcut-okp* (live-state-p state)))
       #+acl2-loop-only ()

; See the comment in ev for why we don't check the time limit here.

       (ev-fncall-rec fn args (w state) (user-stobj-alist state) (big-n)
                      (f-get-global 'safe-mode state)
                      (gc-off state)
                      latches hard-error-returns-nilp aok)))

(defun ev (form alist state latches hard-error-returns-nilp aok)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately, t
; has raw Lisp code and is thus (as of this writing) prevented from being
; promoted to :logic mode.

  (declare (xargs :guard (and (state-p state)
                              (termp form (w state))
                              (symbol-alistp alist))))
  (let #-acl2-loop-only ((*ev-shortcut-okp* (live-state-p state)))
       #+acl2-loop-only ()

; At one time we called time-limit5-reached-p here so that we can quit if we
; are out of time.  But we were then able to get into an infinite loop as
; follows:

; (defun foo (x) (cons x x))
; :brr t
; :monitor (:definition foo) t
; (ld '((thm (equal (foo x) (cons x x)))))
; [Hit control-c repeatedly.]

; We didn't analyze this issue completely (presumably has something to do with
; cleaning up), but a simple solution is to avoid this time-limit check.

;       (cond
;        ((time-limit5-reached-p
;          "Out of time in the evaluator (ev).") ; nil, or throws
;         (mv t ; value shouldn't matter
;             (cons "Implementation error" nil)
;             latches))
;        (t
       (ev-rec form alist
               (w state) (user-stobj-alist state) (big-n)
               (f-get-global 'safe-mode state)
               (gc-off state)
               latches hard-error-returns-nilp aok)))

(defun ev-lst (lst alist state latches hard-error-returns-nilp aok)
  (declare (xargs :guard (and (state-p state)
                              (term-listp lst (w state))
                              (symbol-alistp alist))))
  (let #-acl2-loop-only ((*ev-shortcut-okp* (live-state-p state)))
       #+acl2-loop-only ()

; See the comment in ev for why we don't check the time limit here.

       (ev-rec-lst lst alist
                   (w state)
                   (user-stobj-alist state)
                   (big-n)
                   (f-get-global 'safe-mode state)
                   (gc-off state)
                   latches hard-error-returns-nilp aok)))

(defun untranslate (term iff-flg wrld)
  (let ((user-untranslate
         (cdr (assoc-eq 'untranslate (table-alist 'user-defined-functions-table
                                                  wrld)))))
    (if user-untranslate
        (mv-let
         (erp val)
         (ev-fncall-w user-untranslate
                      (list term iff-flg wrld)
                      wrld
                      nil ; user-stobj-alist
                      nil ; safe-mode
                      nil ; gc-off
                      nil ; hard-error-returns-nilp
                      t)
         (cond
          (erp #-acl2-loop-only
               (progn (error-fms t user-untranslate (car val) (cdr val)
                                 *the-live-state*)
                      (er hard 'untranslate
                          "Please fix ~x0 (see message above and see :doc ~
                           user-defined-functions-table)."
                          user-untranslate))
               (untranslate* term iff-flg wrld))
          (t val)))
      (untranslate* term iff-flg wrld))))

(defun untranslate-lst (lst iff-flg wrld)
  (let ((user-untranslate-lst
         (cdr (assoc-eq 'untranslate-lst (table-alist
                                          'user-defined-functions-table
                                          wrld)))))
    (if user-untranslate-lst
        (mv-let
         (erp val)
         (ev-fncall-w user-untranslate-lst
                      (list lst iff-flg wrld)
                      wrld
                      nil ; user-stobj-alist
                      nil ; safe-mode
                      nil ; gc-off
                      nil ; hard-error-returns-nilp
                      t)
         (cond
          (erp #-acl2-loop-only
               (progn (error-fms t user-untranslate-lst (car val) (cdr val)
                                 *the-live-state*)
                      (er hard 'untranslate-lst
                          "Please fix ~x0 (see message above and see :doc ~
                           user-defined-functions-table)."
                          user-untranslate-lst
                          #+acl2-loop-only
                          nil))
               (untranslate1-lst lst
                                 iff-flg
                                 (untrans-table wrld)
                                 (untranslate-preprocess-fn wrld)
                                 wrld))
          (t val)))
      (untranslate1-lst lst
                        iff-flg
                        (untrans-table wrld)
                        (untranslate-preprocess-fn wrld)
                        wrld))))

(defun ev-w-lst (lst alist w user-stobj-alist safe-mode gc-off
                     hard-error-returns-nilp aok)

; WARNING: See the warning in ev-w, which explains that live stobjs must not
; occur in alist.

; Note that user-stobj-alist is only used for error messages, so this function
; may be called in the presence of local stobjs.  Probably user-stobj-alist
; could be replaced as nil because of the stobj restriction on alist.

; See the comment in ev-w about untouchables.

  (declare (xargs :guard (and (plist-worldp w)
                              (term-listp lst w)
                              (symbol-alistp alist))))

; See the comment in ev for why we don't check the time limit here.

  #-acl2-loop-only
  (let ((*ev-shortcut-okp* t))
    (state-free-global-let*
     ((safe-mode safe-mode)
      (guard-checking-on

; Guard-checking-on will be t or nil -- not :nowarn, :all, or :none -- but it
; doesn't seem that this would be a problem, provided the call is made with
; gc-off set to t if guard-checking-on is either nil or :none (don't forget
; :none!).

       (not gc-off)))
     (mv-let
      (erp val latches)
      (ev-rec-lst lst alist w user-stobj-alist (big-n) safe-mode gc-off
                  nil ; latches
                  hard-error-returns-nilp
                  aok)
      (progn (when latches
               (er hard 'ev-w-lst
                   "The call ~x0 returned non-nil latches."
                   (list 'ev-w-lst lst alist '<wrld>
                         (if user-stobj-alist '<user-stobj-alist> nil)
                         safe-mode gc-off
                         hard-error-returns-nilp aok)))
             (mv erp val)))))
  #+acl2-loop-only
  (mv-let (erp val latches)
          (ev-rec-lst lst alist w user-stobj-alist (big-n) safe-mode gc-off
                      nil ; latches
                      hard-error-returns-nilp
                      aok)
          (declare (ignore latches))
          (mv erp val)))

; Essay on Other Worlds

; In Version 1.7 and earlier, ev and its supporters were coded so that
; they took both a world and a state as input.  The world supplied the
; definitions of the functions.  The state was used for nothing but a
; termination argument -- but we did slip into raw Lisp when that was
; thought appropriate.  The code was was (supposed to be) sound when
; evaluated on states other than the live state.  This was imagined to
; be possible if ground calls of ev-fncall arose in terms being
; proved.  The raw lisp counterpart of ev verified that the world in
; the given state is properly related to the world in the live state.

; The following pre-Version 1.8 comment addresses concerns related to
; the evaluation of a fn in a world other than the one installed in
; state.  These comments are now outdated, but are left here because
; we gave the issue some careful thought at the time.

;   We wish to jump into Common Lisp to compute the value of fn on
;   args.  We know that fn is a function symbol in w because the guard
;   for ev requires that we only evaluate terms.  But the Common Lisp
;   state reflects the definitions of the currently installed world,
;   inst-w, while we have to compute fn by the definitions in world w.
;   In addition, we can use the Common Lisp code only if the guards
;   have been verified.  So we need to know two things: (a) that the
;   two worlds w and inst-w are in an appropriate relationship, and
;   (b) that the guards for fn are all satisfied.

;   We address (a) first.  It is clear that inst-w can be used to
;   compute fn in w if every function ancestral to fn in w is defined
;   exactly the same way in inst-w.  When this condition holds, we say
;   "inst-w is sufficient to compute fn in w."  This sufficiency
;   condition is too expensive to check explicitly.  Note, however,
;   that if inst-w is an extension of w, then inst-w is sufficient.
;   Note also that if w is an extension of inst-w and fn is defined in
;   inst-w, then inst-w is sufficient.  Now if w is an extension of
;   inst-w and fn is defined in w then it is defined in inst-w iff it
;   is fboundp.  Proof: Suppose fn is not defined in inst-w but is
;   fboundp.  Then fn is some function like RPLACA or LP.  But in that
;   case, fn couldn't be defined in w because to define it would
;   require that we smash its symbol-function.  Q.E.D.  So in fact, we
;   check that one of the two worlds is an extension of the other and
;   that fn is fboundp.

;   Now for (b).  We wish to check that the guards for fn are all
;   valid.  Of course, all we can do efficiently is see whether the
;   'guards-checked property has been set.  But it doesn't matter
;   which world we check that in because if the guards have been
;   checked in either then they are valid in both.  So we just see if
;   they have been checked in whichever of the two worlds is the
;   extension.

; Essay on Context-message Pairs

; Recall that translate returns state, which might be modified.  It can be
; useful to have a version of translate that does not return state, for example
; in development of a parallel version of the waterfall (Ph.D. research by
; David Rager ongoing in 2010).  Starting after Version_4.1, we provide a
; version of translate that does not return state.  More generally, we support
; an analogy of the "error triples" programming idiom: rather than passing
; around triples (mv erp val state), we pass around pairs (mv ctx msg), as
; described below.  If foo is a function that returns an error triple, we may
; introduce foo-cmp as the analogous function that returns a message pair.  We
; try to avoid code duplication, for example by using the wrapper
; cmp-to-error-triple.

; An error is indicated when the context (first) component of a context-message
; pair is non-nil.  There are two possibilities in this case.  The second
; component can be nil, indicating that the error does not cause a message to
; be printed.  Otherwise, the first component is a context suitable for er and
; such, while the second component is a message (fmt-string . fmt-args),
; suitable as a ~@ fmt argument.

(defun silent-error (state)
  (mv t nil state))

(defmacro cmp-to-error-triple (form)

; Here we convert a context-message pair (see the Essay on Context-message
; Pairs) to an error triple, printing an error message if one is called for.

; Keep in sync with cmp-to-error-triple@par.

  `(mv-let (ctx msg-or-val)
           ,form
           (cond (ctx (cond (msg-or-val
                             (assert$ (not (eq ctx t))
                                      (er soft ctx "~@0" msg-or-val)))
                            (t (silent-error state))))
                 (t (value msg-or-val)))))

#+acl2-par
(defmacro cmp-to-error-triple@par (form)

; Here we convert a context-message pair (see the Essay on Context-message
; Pairs) to the #+acl2-par version of an error triple, printing an error
; message if one is called for.

; Keep in sync with cmp-to-error-triple.

  `(mv-let (ctx msg-or-val)
           ,form
           (cond (ctx (cond (msg-or-val
                             (assert$ (not (eq ctx t))
                                      (er@par soft ctx "~@0" msg-or-val)))
                            (t (mv@par t nil state))))
                 (t (value@par msg-or-val)))))

(defmacro cmp-to-error-double (form)

; This is a variant of cmp-to-error-triple that returns (mv erp val) rather
; than (mv erp val state).

  `(mv-let (ctx msg-or-val)
           ,form
           (cond (ctx (prog2$ (cond (msg-or-val
                                     (assert$ (not (eq ctx t))
                                              (error-fms-cw
                                               nil ctx "~@0"
                                               (list (cons #\0 msg-or-val)))))
                                    (t nil))
                              (mv t nil)))
                 (t (mv nil msg-or-val)))))

(defmacro cmp-and-value-to-error-quadruple (form)

; We convert a context-message pair and an extra-value (see the Essay on
; Context-message Pairs) to an error quadruple (mv t value extra-value state),
; printing an error message if one is called for.

; Keep in sync with cmp-and-value-to-error-quadruple@par.

  `(mv-let (ctx msg-or-val extra-value)
           ,form
           (cond
            (ctx (cond (msg-or-val
                        (assert$ (not (eq ctx t))
                                 (mv-let (erp val state)
                                         (er soft ctx "~@0"
                                             msg-or-val)
                                         (declare (ignore erp val))
                                         (mv t nil extra-value state))))
                       (t (mv t nil extra-value state))))
            (t (mv nil msg-or-val extra-value state)))))

#+acl2-par
(defmacro cmp-and-value-to-error-quadruple@par (form)

; We convert a context-message pair and an extra value (see the Essay on
; Context-message Pairs) to the #+acl2-par version of an error quadruple,
; printing an error message if one is called for.

; Keep in sync with cmp-and-value-to-error-quadruple.

  `(mv-let (ctx msg-or-val extra-value)
           ,form
           (cond
            (ctx (cond (msg-or-val
                        (assert$ (not (eq ctx t))
                                 (mv-let (erp val)
                                         (er@par soft ctx "~@0" msg-or-val)
                                         (declare (ignore erp val))
                                         (mv t nil extra-value))))
                       (t (mv t nil extra-value))))
            (t (mv nil msg-or-val extra-value)))))

(defun er-cmp-fn (ctx msg)

; Warning: Keep in sync with trans-er.  For an explanation, see the
; corresponding warning in trans-er.

  (declare (xargs :guard t))
  (mv ctx msg))

(defmacro er-cmp (ctx str &rest args)

; Warning: Keep in sync with trans-er.  For an explanation, see the
; corresponding warning in trans-er.

  `(er-cmp-fn ,ctx (msg ,str ,@args)))

(defmacro value-cmp (x)
  `(mv nil ,x))

(defun er-progn-fn-cmp (lst)

; Warning: Keep this in sync with er-progn-fn.

  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((endp (cdr lst)) (car lst))
        (t (list 'mv-let
                 '(er-progn-not-to-be-used-elsewhere-ctx
                   er-progn-not-to-be-used-elsewhere-msg)
                 (car lst)
; Avoid possible warning after optimized compilation:
                 '(declare (ignorable er-progn-not-to-be-used-elsewhere-msg))
                 (list 'if
                       'er-progn-not-to-be-used-elsewhere-ctx
                       '(mv er-progn-not-to-be-used-elsewhere-ctx
                            er-progn-not-to-be-used-elsewhere-msg)
                       (list 'check-vars-not-free
                             '(er-progn-not-to-be-used-elsewhere-ctx
                               er-progn-not-to-be-used-elsewhere-msg)
                             (er-progn-fn-cmp (cdr lst))))))))

(defmacro er-progn-cmp (&rest lst)
  (declare (xargs :guard (and (true-listp lst)
                              lst)))
  (er-progn-fn-cmp lst))

(defmacro er-let*-cmp (alist body)

; Warning: Keep this in sync with er-let*.

; This macro introduces the variable er-let-star-use-nowhere-else.
; The user who uses that variable in his forms is likely to be
; disappointed by the fact that we rebind it.

  (declare (xargs :guard (and (doublet-listp alist)
                              (symbol-alistp alist))))
  (cond ((null alist)
         (list 'check-vars-not-free
               '(er-let-star-use-nowhere-else)
               body))
        (t (list 'mv-let
                 (list 'er-let-star-use-nowhere-else
                       (caar alist))
                 (cadar alist)
                 (list 'cond
                       (list 'er-let-star-use-nowhere-else
                             (list 'mv
                                   'er-let-star-use-nowhere-else
                                   (caar alist)))
                       (list t (list 'er-let*-cmp (cdr alist) body)))))))

(defun warning1-cw (ctx summary str alist wrld state-vars)

; This function has the same effect as warning1, except that printing is in a
; wormhole and hence doesn't modify state.

  (declare (xargs :guard (and (or (null summary)
                                  (and (stringp summary)
                                       (standard-string-p summary)))
                              (alistp alist)
                              (plist-worldp wrld)
                              (standard-string-alistp
                               (table-alist 'inhibit-warnings-table wrld))
                              (weak-state-vars-p state-vars))))
  (warning1-form t))

(defmacro warning$-cw1 (ctx summary str+ &rest fmt-args)

; Warning: Keep this in sync with warning$.

; This macro assumes that wrld and state-vars are bound to a world and
; state-vars record, respectively.

  (list 'warning1-cw
        ctx

; We seem to have seen a GCL 2.6.7 compiler bug, laying down bogus calls of
; load-time-value, when replacing (consp (cadr args)) with (and (consp (cadr
; args)) (stringp (car (cadr args)))).  But it seems fine to have the semantics
; of warning$ be that conses are quoted in the second argument position.

        (if (consp summary)
            (kwote summary)
          summary)
        str+
        (make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                             #\5 #\6 #\7 #\8 #\9)
                           fmt-args)
        'wrld
        'state-vars))

(defmacro warning$-cw (ctx &rest args)

; This differs from warning$-cw1 in that state-vars and wrld are bound here for
; the user, warnings are not suppressed based on the value of state global
; 'ld-skip-proofsp, and there is no summary string.  A typical use of this
; macro might be as follows.

; (warning$-cw ctx "The :REWRITE rule ~x0 loops forever." name)

  `(let ((state-vars (default-state-vars nil))
         (wrld nil))
     (warning$-cw1 ,ctx nil ,@args)))

(defun chk-length-and-keys (actuals form wrld)
  (declare (xargs :guard (and (true-listp actuals)
                              (true-listp form)
                              (symbolp (car form))
                              (plist-worldp wrld))
                  :measure (acl2-count actuals)))
  (cond ((endp actuals)
         (value-cmp nil))
        ((null (cdr actuals))
         (er-cmp *macro-expansion-ctx*
                 "A non-even key/value arglist was encountered while macro ~
                  expanding ~x0.  The argument list for ~x1 is ~%~F2."
                 form
                 (car form)
                 (macro-args (car form) wrld)))
        ((keywordp (car actuals))
         (chk-length-and-keys (cddr actuals) form wrld))
        (t (er-cmp *macro-expansion-ctx*
                   "A non-keyword was encountered while macro expanding ~x0 ~
                    where a keyword was expected.  The formal parameters list ~
                    for ~x1 is ~%~F2."
                   form
                   (car form)
                   (macro-args (car form) wrld)))))

(table duplicate-keys-action-table nil nil
       :guard
       (and (symbolp key)
            (member val '(:error :warning nil))))

(defmacro set-duplicate-keys-action! (key action)
  `(with-output
     :off (event summary)
     (progn (table duplicate-keys-action-table ',key ',action)
            (value-triple ',action))))

(defmacro set-duplicate-keys-action (key action)
  `(local (set-duplicate-keys-action! ,key ,action)))

(defun duplicate-keys-action (key wrld)
  (declare (xargs :guard
                  (and (plist-worldp wrld)
                       (symbol-alistp (table-alist 'duplicate-keys-action-table
                                                   wrld)))))
  (let ((pair (assoc-eq key (table-alist 'duplicate-keys-action-table wrld))))
    (cond (pair (cdr pair))
          (t ; default

; We make :error the default in order to help users to identify quickly
; potential dumb bugs involving a duplicated keyword in a macro call.

           :error))))

;  We permit macros under the following constraints on the args.

;  1.  No destructuring.  (Maybe some day.)
;  2.  No &aux.           (LET* is better.)
;  3.  Initforms must be quotes.  (Too hard for us to do evaluation right.)
;  4.  No &environment.   (Just not clearly enough specified in CLTL.)
;  5.  No nonstandard lambda-keywords.  (Of course.)
;  6.  No multiple uses of :allow-other-keys.  (Implementations differ.)

;  There are three nests of functions that have the same view of
;  the subset of macro args that we support:  macro-vars...,
;  chk-macro-arglist..., and bind-macro-args...  Of course, it is
;  necessary to keep them all with the same view of the subset.

; The following code is a ``pseudo'' translation of the functions between
; chk-legal-init-msg and chk-macro-arglist.  Those checkers cause errors when
; their requirements are violated and these functions are just predicates.
; However, they are ``pseudo'' translations because they do not check, for
; example, that alleged variable symbols really are legal variable symbols.
; They are used in the guards for the functions leading up to and including
; macro-vars, which recovers all the variable symbols used in the formals list
; of an acceptable defmacro.

(defun legal-initp (x)
  (and (consp x)
       (true-listp x)
       (equal 2 (length x))
       (eq (car x) 'quote)))

(defun macro-arglist-keysp (args keys-passed)
  (declare (xargs :guard (and (true-listp args)
                              (true-listp keys-passed))))
  (cond ((endp args) t)
        ((eq (car args) '&allow-other-keys)
         (null (cdr args)))
        ((atom (car args))
         (cond ((symbolp (car args))
                (let ((new (intern (symbol-name (car args)) "KEYWORD")))
                  (and (not (member new keys-passed))
                       (macro-arglist-keysp (cdr args)
                                            (cons new keys-passed)))))
               (t nil)))
        ((or (not (true-listp (car args)))
             (> (length (car args)) 3))
         nil)
        (t (and (or (symbolp (caar args))
                    (and (true-listp (caar args))
                         (equal (length (caar args)) 2)
                         (keywordp (car (caar args)))
                         (symbolp (cadr (caar args)))))
                (implies (> (length (car args)) 1)
                         (legal-initp (cadr (car args))))
                (implies (> (length (car args)) 2)
                         (symbolp (caddr (car args))))
                (let ((new (cond ((symbolp (caar args))
                                  (intern (symbol-name (caar args))
                                          "KEYWORD"))
                                 (t (car (caar args))))))
                  (and (not (member new keys-passed))
                       (macro-arglist-keysp (cdr args)
                                            (cons new keys-passed))))))))

(defun macro-arglist-after-restp (args)
  (declare (xargs :guard (true-listp args)))
  (cond ((endp args) t)
        ((eq (car args) '&key)
         (macro-arglist-keysp (cdr args) nil))
        (t nil)))

(defun macro-arglist-optionalp (args)
  (declare (xargs :guard (true-listp args)))
  (cond ((endp args) t)
        ((member (car args) '(&rest &body))
         (cond ((and (cdr args)
                     (symbolp (cadr args))
                     (not (lambda-keywordp (cadr args))))
                (macro-arglist-after-restp (cddr args)))
               (t nil)))
        ((eq (car args) '&key)
         (macro-arglist-keysp (cdr args) nil))
        ((symbolp (car args))
         (macro-arglist-optionalp (cdr args)))
        ((or (atom (car args))
             (not (true-listp (car args)))
             (not (< (length (car args)) 4)))
         nil)
        ((not (symbolp (car (car args))))
         nil)
        ((and (> (length (car args)) 1)
              (not (legal-initp (cadr (car args)))))
         nil)
        ((and (equal (length (car args)) 3)
              (not (symbolp (caddr (car args)))))
         nil)
        (t (macro-arglist-optionalp (cdr args)))))

(defun macro-arglist1p (args)
  (declare (xargs :guard (true-listp args)))
  (cond ((endp args) t)
        ((not (symbolp (car args)))
         nil)
        ((member (car args) '(&rest &body))
         (cond ((and (cdr args)
                     (symbolp (cadr args))
                     (not (lambda-keywordp (cadr args))))
                (macro-arglist-after-restp (cddr args)))
               (t nil)))
        ((eq (car args) '&optional)
         (macro-arglist-optionalp (cdr args)))
        ((eq (car args) '&key)
         (macro-arglist-keysp (cdr args) nil))
        (t (macro-arglist1p (cdr args)))))

(defun subsequencep (lst1 lst2)

  (declare (xargs :guard (and (eqlable-listp lst1)
                              (true-listp lst2))))

; We return t iff lst1 is a subsequence of lst2, in the sense that
; '(a c e) is a subsequence of '(a b c d e f) but '(a c b) is not.

  (cond ((endp lst1) t)
        (t (let ((tl (member (car lst1) lst2)))
             (cond ((endp tl) nil)
                   (t (subsequencep (cdr lst1) (cdr tl))))))))

(defun collect-lambda-keywordps (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((lambda-keywordp (car lst))
         (cons (car lst) (collect-lambda-keywordps (cdr lst))))
        (t (collect-lambda-keywordps (cdr lst)))))

(defun macro-args-structurep (args)
  (declare (xargs :guard t))
  (and (true-listp args)
       (let ((lambda-keywords (collect-lambda-keywordps args)))
         (and
          (or (subsequencep lambda-keywords
                            '(&whole &optional &rest &key &allow-other-keys))
              (subsequencep lambda-keywords
                            '(&whole &optional &body &key &allow-other-keys)))
          (and (not (member-eq '&whole (cdr args)))
               (implies (member-eq '&allow-other-keys args)
                        (member-eq '&allow-other-keys
                                   (member-eq '&key args)))
               (implies (eq (car args) '&whole)
                        (and (consp (cdr args))
                             (symbolp (cadr args))
                             (not (lambda-keywordp (cadr args)))
                             (macro-arglist1p (cddr args))))
               (macro-arglist1p args))))))

(defun bind-macro-args-keys1 (args actuals allow-flg alist form wrld
                                   state-vars)

; We need parameter state-vars because of the call of warning$-cw1 below.

  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-keysp args nil)
                              (keyword-value-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (symbolp (car form))
                              (plist-worldp wrld)
                              (symbol-alistp
                               (table-alist 'duplicate-keys-action-table
                                            wrld))
                              (weak-state-vars-p state-vars))))
  (cond ((endp args)
         (cond ((or (null actuals) allow-flg)
                (value-cmp alist))
               (t (er-cmp *macro-expansion-ctx*
                          "Illegal key/value args ~x0 in macro expansion of ~
                           ~x1.  The argument list for ~x2 is ~%~F3."
                          actuals form
                          (car form)
                          (macro-args (car form) wrld)))))
        ((eq (car args) '&allow-other-keys)
         (value-cmp alist))
        (t (let* ((formal (cond ((atom (car args))
                                 (car args))
                                ((atom (caar args))
                                 (caar args))
                                (t (cadr (caar args)))))
                  (key (cond ((atom (car args))
                              (intern (symbol-name (car args))
                                      "KEYWORD"))
                             ((atom (car (car args)))
                              (intern (symbol-name (caar args))
                                      "KEYWORD"))
                             (t (caaar args))))
                  (tl (assoc-keyword key actuals))
                  (alist (cond ((and (consp (car args))
                                     (= 3 (length (car args))))
                                (cons (cons (caddr (car args))
                                            (not (null tl)))
                                      alist))
                               (t alist)))
                  (name (car form))
                  (duplicate-keys-action
                   (and (assoc-keyword key (cddr tl))
                        (duplicate-keys-action name wrld)))
                  (er-or-warn-string
                   "The keyword argument ~x0 occurs twice in ~x1.  This ~
                    situation is explicitly allowed in Common Lisp (see ~
                    CLTL2, page 80) but it often suggests a mistake was ~
                    made.~@2  See :DOC set-duplicate-keys-action."))
             (prog2$
              (and (eq duplicate-keys-action :warning)
                   (warning$-cw1 *macro-expansion-ctx* "Duplicate-Keys"
                                 er-or-warn-string
                                 key
                                 form
                                 "  The leftmost value for ~x0 is used."))
              (cond
               ((eq duplicate-keys-action :error)
                (er-cmp *macro-expansion-ctx*
                        er-or-warn-string
                        key form ""))
               (t
                (bind-macro-args-keys1
                 (cdr args)
                 (remove-keyword key actuals)
                 allow-flg
                 (cons (cons formal
                             (cond (tl (cadr tl))
                                   ((atom (car args))
                                    nil)
                                   ((> (length (car args)) 1)
                                    (cadr (cadr (car args))))
                                   (t nil)))
                       alist)
                 form wrld state-vars))))))))

(defun bind-macro-args-keys (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-keysp args nil)
                              (true-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (er-progn-cmp
   (chk-length-and-keys actuals form wrld)
   (cond ((assoc-keyword :allow-other-keys
                         (cdr (assoc-keyword :allow-other-keys
                                             actuals)))
          (er-cmp *macro-expansion-ctx*
                  "ACL2 prohibits multiple :allow-other-keys because ~
                   implementations differ significantly concerning which ~
                   value to take."))
         (t (value-cmp nil)))
   (bind-macro-args-keys1
    args actuals
    (let ((tl
           (assoc-keyword :allow-other-keys actuals)))
      (and tl (cadr tl)))
    alist form wrld state-vars)))

(defun bind-macro-args-after-rest (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-after-restp args)
                              (true-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (cond
   ((endp args) (value-cmp alist))
   ((eq (car args) '&key)
    (bind-macro-args-keys (cdr args) actuals alist form wrld state-vars))
   (t (er-cmp *macro-expansion-ctx*
              "Only keywords and values may follow &rest or &body; error in ~
               macro expansion of ~x0."
              form))))

(defun bind-macro-args-optional (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist-optionalp args)
                              (true-listp actuals)
                              (symbol-alistp alist)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (cond ((endp args)
         (cond ((null actuals)
                (value-cmp alist))
               (t (er-cmp *macro-expansion-ctx*
                          "Wrong number of args in macro expansion of ~x0."
                          form))))
        ((eq (car args) '&key)
         (bind-macro-args-keys (cdr args) actuals alist form wrld state-vars))
        ((member (car args) '(&rest &body))
         (bind-macro-args-after-rest
          (cddr args) actuals
          (cons (cons (cadr args) actuals) alist)
          form wrld state-vars))
        ((symbolp (car args))
         (bind-macro-args-optional
          (cdr args) (cdr actuals)
          (cons (cons (car args) (car actuals))
                alist)
          form wrld state-vars))
        (t (let ((alist (cond ((equal (length (car args)) 3)
                               (cons (cons (caddr (car args))
                                           (not (null actuals)))
                                     alist))
                              (t alist))))
             (bind-macro-args-optional
              (cdr args) (cdr actuals)
              (cons (cons (car (car args))
                          (cond (actuals (car actuals))
                                ((>= (length (car args)) 2)
                                 (cadr (cadr (car args))))
                                (t nil)))
                    alist)
              form wrld state-vars)))))

(defun bind-macro-args1 (args actuals alist form wrld state-vars)
  (declare (xargs :guard (and (true-listp args)
                              (macro-arglist1p args)
                              (true-listp form)
                              (symbol-alistp alist)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (cond ((endp args)
         (cond ((null actuals)
                (value-cmp alist))
               (t (er-cmp *macro-expansion-ctx*
                      "Wrong number of args in macro expansion of ~x0."
                      form))))
        ((member-eq (car args) '(&rest &body))
         (bind-macro-args-after-rest
          (cddr args) actuals
          (cons (cons (cadr args) actuals) alist)
          form wrld state-vars))
        ((eq (car args) '&optional)
         (bind-macro-args-optional (cdr args) actuals alist form wrld
                                   state-vars))
        ((eq (car args) '&key)
         (bind-macro-args-keys (cdr args) actuals alist form wrld state-vars))
        ((null actuals)
         (er-cmp *macro-expansion-ctx*
             "Wrong number of args in macro expansion of ~x0."
             form))
        (t (bind-macro-args1 (cdr args) (cdr actuals)
                             (cons (cons (car args) (car actuals))
                                   alist)
                             form wrld state-vars))))

(defun bind-macro-args (args form wrld state-vars)
  (declare (xargs :guard (and (macro-args-structurep args)
                              (true-listp form)
                              (plist-worldp wrld)
                              (weak-state-vars-p state-vars))))
  (cond ((and (consp args)
              (eq (car args) '&whole))
         (bind-macro-args1 (cddr args) (cdr form)
                           (list (cons (cadr args) form))
                           form wrld state-vars))
        (t (bind-macro-args1 args (cdr form) nil form wrld state-vars))))

(defun macro-guard-er-msg (x ctx wrld)
  (let* ((name (car x))
         (args (cdr x))
         (form (cdr (assoc-eq name (table-alist 'guard-msg-table wrld)))))
    (mv-let
     (erp msg)
     (cond (form (ev-w form
                       (list (cons 'world wrld)
                             (cons 'args args)
                             (cons 'coda
                                   (msg "(Note: The custom guard message for ~
                                         ~x0 references the variable ~x1, ~
                                         which is essentially ignored for ~
                                         macros.  Consider modifying the ~
                                         entry for ~x0 in ~x2.)"
                                        name 'coda 'guard-msg-table)))
                       wrld
                       nil ; user-stobj-alist
                       nil ; safe-mode
                       t   ; gc-off
                       t   ; hard-error-returns-nilp
                       t   ; aok
                       ))
           (t (mv nil nil)))
     (cond
      (erp
       (er-cmp ctx
               "~|~%Note: Evaluation has resulted in an error for the form ~
                associated with ~x0 in the table, ~x1, to obtain a custom ~
                guard error message.  Consider modifying that table entry; ~
                see :doc set-guard-msg."
               name
               'guard-msg-table))
      (msg (er-cmp ctx "~@0" msg))
      (t (er-cmp ctx
                 "In the attempt to macroexpand the form ~x0 the guard, ~x1, ~
                  for ~x2 failed."
                 x
                 (guard name nil wrld)
                 name))))))

(defun macroexpand1-cmp (x ctx wrld state-vars)
  (let ((gc-off (gc-off1 (access state-vars state-vars :guard-checking-on))))
    (er-let*-cmp
     ((alist (bind-macro-args
              (macro-args (car x) wrld)
              x wrld state-vars)))
     (mv-let (erp guard-val)
             (ev-w (guard (car x) nil wrld) alist wrld
                   nil ; user-stobj-alist
                   t
                   gc-off
                   nil

; It is probably critical to use nil for the aok argument of this call.
; Otherwise, one can imagine a book with sequence of events
;   (local EVENT0)
;   (defattach ...)
;   EVENT0
; such that a change in macroexpansion, due to the defattach, causes a
; different event to be exported from the book, for EVENT0, than the local one
; originally admitted.

                   nil)
             (cond
              (erp (er-cmp ctx
                           "In the attempt to macroexpand the form ~x0 ~
                            evaluation of the guard for ~x2 caused the ~
                            error below.~|~%~@1"
                           x
                           guard-val
                           (car x)))
              ((null guard-val)
               (macro-guard-er-msg x ctx wrld))
              (t (mv-let (erp expansion)
                         (ev-w
                          (getpropc (car x) 'macro-body
                                    '(:error "Apparently macroexpand1 was ~
                                              called where there was no ~
                                              macro-body.")
                                    wrld)
                          alist wrld
                          nil ; user-stobj-alist
                          (not (access state-vars state-vars

; Note that if state-vars comes from (default-state-vars nil), then this flag
; is nil so safe-mode is t, which is acceptable, merely being needlessly
; conservative when the actual state global 'boot-strap-flg is t and hence
; safe-mode could have been nil here.

                                       :boot-strap-flg)) ; safe-mode
                          gc-off nil nil)
                         (cond (erp
                                (er-cmp ctx
                                        "In the attempt to macroexpand the ~
                                         form ~x0, evaluation of the macro ~
                                         body caused the error below.~|~%~@1"
                                        x
                                        expansion))
                               (t (value-cmp expansion))))))))))

(defun macroexpand1 (x ctx state)
  (cmp-to-error-triple (macroexpand1-cmp x ctx (w state)
                                         (default-state-vars t))))

(defun chk-declare (form ctx)
  (let ((msg
         "An expression has occurred where we expect a form whose car is ~
          DECLARE; yet, that expression is ~x0.  This problem generally is ~
          caused by (a) a parenthesis mistake, (b) the use of an ``implicit ~
          PROGN'' so that a term that you intended to be part of the body was ~
          taken as a declaration, or (c) the incorrect belief that ~
          macroexpansion is applied to declarations.  See :DOC declare."))
    (cond ((or (not (consp form))
               (not (symbolp (car form))))
           (er-cmp ctx msg form))
          ((eq (car form) 'declare)
           (cond ((not (true-listp form))
                  (er-cmp ctx
                          "A declaration must be a true-list but ~x0 is not.  ~
                           See :DOC declare."
                          form))
                 (t (value-cmp form))))
          (t (er-cmp ctx msg form)))))

(defun collect-dcls (l ctx)
  (cond ((null l) (value-cmp nil))
        (t (er-let*-cmp
            ((expansion
              (chk-declare (car l) ctx))
             (rst (collect-dcls (cdr l) ctx)))
            (value-cmp (append (cdr expansion) rst))))))

; The following alist maps "binders" to the permitted types of
; declarations at the top-level of the binding environment.

(defconst *acceptable-dcls-alist*

; Warning: Keep this in sync with :DOC declare.

; The declarations dynamic-extent, inline, and notinline were found useful by
; Bob Boyer in early development of hons-enabled ACL2, but we do not see a way
; to support such declarations soundly, so we do not support them.  Note that
; inline and notinline declarations are supported adequately (though
; indirectly) by defun-inline and defun-notinline.

  `((let ignore ignorable type)
    (mv-let ignore ignorable type)
    (flet ignore ignorable type) ; for each individual definition in the flet
    (defmacro ignore ignorable type xargs)
    (defuns ignore ignorable irrelevant type optimize xargs)))

; The following list gives the names of binders that permit at most
; one documentation string among their declarations.  If this list is
; changed, visit all calls of collect-declarations because its answer
; is known NOT to have a doc string in it if the binder on which it
; was called is not in this list.

(defconst *documentation-strings-permitted*
  '(defmacro defuns))

; For each type of declaration the following alist offers an explanatory
; string.

(defconst *dcl-explanation-alist*
  '((ignore "(IGNORE v1 ... vn) and (IGNORABLE v1 ... vn), where the vi are ~
             introduced in the immediately superior lexical environment")
    (irrelevant "(IRRELEVANT v1 ... vn)")
    (type "(TYPE type v1 ... vn), as described on pg 158 of CLTL")
    (xargs "(XARGS :key1 :val1 ... :keyn :valn), where each :keyi is a ~
            keyword (e.g., :GUARD or :HINTS)")))

; The following two functions are used to create an appropriate error
; message explaining what kinds of declarations are permitted by a binder.

(defun tilde-*-conjunction-phrase1 (syms alist)
  (cond ((null syms) nil)
        (t (let ((temp (assoc-eq (car syms) alist)))
             (cons
              (cond (temp (cdr temp))
                    (t (coerce (cons #\(
                                     (append (explode-atom (car syms) 10)
                                             (coerce " ...)" 'list)))
                               'string)))
              (tilde-*-conjunction-phrase1 (cdr syms) alist))))))

(defun tilde-*-conjunction-phrase (syms alist)

; Syms is a list of symbols.  Alist maps symbols to strings, called
; the "explanation" of each symbol.  We create an object that when
; given to the tilde-* fmt directive will print out the conjunction of
; the explanations for each of the symbols.

  (let ((syms ; accommodate a single phrase for ignore and ignorable
         (cond ((member-eq 'ignorable syms)
                (let ((syms (remove1-eq 'ignorable syms)))
                  (if (member-eq 'ignore syms)
                      syms
                    (cons 'ignore syms))))
               (t syms))))
    (list "" "~@*" "~@* and " "~@*, "
          (tilde-*-conjunction-phrase1 syms alist))))

(defun collect-non-legal-variableps (lst)
  (cond ((null lst) nil)
        ((legal-variablep (car lst))
         (collect-non-legal-variableps (cdr lst)))
        (t (cons (car lst) (collect-non-legal-variableps (cdr lst))))))

(defun optimize-alistp (lst)
  (cond ((atom lst) (null lst))
        ((consp (car lst))
         (and (consp (cdar lst))
              (null (cddar lst))
              (symbolp (caar lst))
              (integerp (cadar lst))
              (<= 0 (cadar lst))
              (<= (cadar lst) 3)
              (optimize-alistp (cdr lst))))
        (t (and (symbolp (car lst))
                (optimize-alistp (cdr lst))))))

(defun chk-dcl-lst (l vars binder ctx wrld)

; L is the list of expanded declares.  Vars is a list of variables
; bound in the immediately superior lexical environment.  Binder is
; a binder, as listed in *acceptable-dcls-alist*.

  (cond
   ((null l) (value-cmp nil))
   (t (er-progn-cmp
       (let ((entry (car l)))
         (cond
          ((not (consp entry))
           (er-cmp ctx
                   "Each element of a declaration must be a cons, but ~x0 is ~
                    not.  See :DOC declare."
                   entry))
          (t (let ((dcl (car entry))
                   (temp (cdr (assoc-eq binder *acceptable-dcls-alist*))))
               (cond
                ((not (member-eq dcl temp))
                 (er-cmp ctx
                         "The only acceptable declaration~#0~[~/s~] at the ~
                          top-level of ~#1~[an FLET binding~/a ~x2 form~] ~
                          ~#0~[is~/are~] ~*3.  The declaration ~x4 is thus ~
                          unacceptable here.  See :DOC declare."
                         temp
                         (if (eq binder 'flet) 0 1)
                         binder
                         (tilde-*-conjunction-phrase temp
                                                     *dcl-explanation-alist*)
                         entry))
                ((not (true-listp entry))
                 (er-cmp ctx
                         "Each element of a declaration must end in NIL but ~
                          ~x0 does not.  See :DOC declare." entry))
                (t
                 (case
                  dcl
                  (optimize
                   (cond ((optimize-alistp (cdr entry)) (value-cmp nil))
                         (t (er-cmp ctx
                                    "Each element in the list following an ~
                                     OPTIMIZE declaration must be either a ~
                                     symbol or a pair of the form (quality ~
                                     value), where quality is a symbol and ~
                                     value is an integer between 0 and 3.  ~
                                     Your OPTIMIZE declaration, ~x0, does not ~
                                     meet this requirement."
                                    entry))))
                  ((ignore ignorable irrelevant)
                   (cond ((subsetp (cdr entry) vars)
                          (value-cmp nil))
                         (t (er-cmp ctx
                                    "The variables of an ~x0 declaration must ~
                                     be introduced in the ~#1~[immediately ~
                                     superior lexical ~
                                     environment~/surrounding DEFUN form~]; ~
                                     but ~&2, which ~#2~[is~/are~] said to be ~
                                     ~#3~[ignored~/ignorable~/irrelevant~] in ~
                                     ~x4, ~#2~[is~/are~] not.  See :DOC ~
                                     declare."
                                    dcl
                                    (if (eq dcl 'irrelevant) 1 0)
                                    (set-difference-equal (cdr entry) vars)
                                    (if (eq dcl 'ignore) 0
                                      (if (eq dcl 'ignorable) 1 2))
                                    entry))))
                  (type
                   (cond
                    ((not (>= (length entry) 3))
                     (er-cmp ctx
                             "The length of a type declaration must be at ~
                              least 3, but ~x0 does not satisfy this ~
                              condition.  See :DOC declare."
                             entry))
                    ((collect-non-legal-variableps (cddr entry))
                     (er-cmp ctx
                             "Only the types of variables can be declared by ~
                              TYPE declarations such as ~x0.  But ~&1 ~#1~[is ~
                              not a legal ACL2 variable symbol~/are not legal ~
                              ACL2 variable symbols~].  See :DOC declare."
                             entry
                             (collect-non-legal-variableps (cddr entry))))
                    ((not (subsetp (cddr entry) vars))
                     (er-cmp ctx
                             "The variables declared in a type declaration, ~
                              such as ~x0, must be bound immediately above, ~
                              but ~&1 ~#1~[is~/are~] not bound.  See :DOC ~
                              declare."
                             entry
                             (set-difference-equal (cddr entry) vars)))
                    ((not (translate-declaration-to-guard (cadr entry)
                                                          'var
                                                          wrld))

; We use the variable var because we are not interested in the
; particular value returned, only whether (cadr entry) stands for some
; type.

                     (cond
                      ((and (true-listp (cadr entry))
                            (int= (length (cadr entry)) 3)
                            (eq (car (cadr entry)) 'or)
                            (eq (cadr (cadr entry)) t))

; The type-spec is (or t x).  There is an excellent chance that this comes from
; (the type-spec ...); see the-fn.  So we change the error message a bit for
; this case.  Note that the error message is accurate, since (or t x) is
; illegal as a type-spec iff x is illegal.  And the message is reasonable
; because it is not misleading and it is likely to be only for THE, where the
; user did not use an explicit declaration (which was generated by us).

                       (er-cmp ctx
                               "~x0 fails to be a legal type-spec.  See :DOC ~
                                type-spec."
                               (caddr (cadr entry))))
                      ((weak-satisfies-type-spec-p (cadr entry))
                       (er-cmp ctx
                               "In the declaration ~x0, ~x1 fails to be a ~
                                legal type-spec because the symbol ~x2 is not ~
                                a known function symbol~@3.  See :DOC ~
                                type-spec."
                               entry (cadr entry) (cadr (cadr entry))
                               (if (eq (getpropc (cadr (cadr entry))
                                                 'macro-args t wrld)
                                       t)
                                   ""
                                 "; rather, it is the name of a macro")))
                      (t
                       (er-cmp ctx
                               "In the declaration ~x0, ~x1 fails to be a ~
                                legal type-spec.  See :DOC type-spec."
                               entry (cadr entry)))))
                    (t (value-cmp nil))))
                  (xargs
                   (cond
                    ((not (keyword-value-listp (cdr entry)))
                     (er-cmp ctx
                             "The proper form of the ACL2 declaration is ~
                              (XARGS :key1 val1 ... :keyn valn), where each ~
                              :keyi is a keyword and no key occurs twice.  ~
                              Your ACL2 declaration, ~x0, is not of this ~
                              form.  See :DOC xargs."
                             entry))
                    ((not (no-duplicatesp-equal (evens (cdr entry))))
                     (er-cmp ctx
                             "Even though Common Lisp permits duplicate ~
                              occurrences of keywords in keyword/actual ~
                              lists, all but the left-most occurrence are ~
                              ignored.  You have duplicate occurrences of the ~
                              keyword~#0~[~/s~] ~&0 in your declaration ~x1.  ~
                              This suggests a mistake has been made."
                             (duplicates (evens (cdr entry)))
                             entry))
                    ((and (eq binder 'defmacro)
                          (assoc-keyword :stobjs (cdr entry)))
                     (er-cmp ctx
                             "The use of the :stobjs keyword is prohibited ~
                              for an xargs declaration in a call of defmacro."))
                    (t (value-cmp nil))))
                  (otherwise
                   (mv t
                       (er hard! 'chk-dcl-lst
                           "Implementation error: A declaration, ~x0, is ~
                            mentioned in *acceptable-dcls-alist* but not in ~
                            chk-dcl-lst."
                           dcl))))))))))
       (chk-dcl-lst (cdr l) vars binder ctx wrld)))))

(defun number-of-strings (l)
  (cond ((null l) 0)
        ((stringp (car l))
         (1+ (number-of-strings (cdr l))))
        (t (number-of-strings (cdr l)))))

(defun get-string (l)
  (cond ((null l) nil)
        ((stringp (car l)) (list (car l)))
        (t (get-string (cdr l)))))

(defun collect-declarations-cmp (lst vars binder ctx wrld)

; Lst is a list of (DECLARE ...) forms, and/or documentation strings.
; We check that the elements are declarations of the types appropriate
; for binder, which is one of the names bound in
; *acceptable-dcls-alist*.  For IGNORE and TYPE declarations, which
; are seen as part of term translation (e.g., in LETs), we check that
; the variables mentioned are bound in the immediately superior
; lexical scope (i.e., are among the vars (as supplied) bound by
; binder).  But for all other declarations, e.g., GUARD, we merely
; check the most routine syntactic conditions.  WE DO NOT TRANSLATE
; the XARGS.  We return a list of the checked declarations.  I.e., if
; given ((DECLARE a b)(DECLARE c d)) we return (a b c d), or else
; cause an error.  If given ((DECLARE a b) "Doc string" (DECLARE c d))
; (and binder is among those in *documentation-strings-permitted*),
; we return ("Doc string" a b c d).

; If binder is among those in *documentation-strings-permitted* we permit
; at most one documentation string in lst.  Otherwise, we cause an error.

  (cond ((> (number-of-strings lst)
            (if (member-eq binder *documentation-strings-permitted*)
                1
              0))
         (cond ((member-eq binder *documentation-strings-permitted*)
                (er-cmp ctx
                        "At most one documentation string is permitted at the ~
                         top-level of ~x0 but you have provided ~n1."
                        binder
                        (number-of-strings lst)))
               (t
                (er-cmp ctx
                        "Documentation strings are not permitted in ~x0 forms."
                        binder))))
        (t
         (er-let*-cmp
          ((dcls (collect-dcls (remove-strings lst) ctx)))
          (er-progn-cmp (chk-dcl-lst dcls vars binder ctx wrld)
                        (value-cmp (append (get-string lst) dcls)))))))

(defun collect-declarations (lst vars binder state ctx)
  (cmp-to-error-triple (collect-declarations-cmp lst vars binder ctx
                                                 (w state))))

(defun listify (l)
  (cond ((null l) *nil*)
        (t (list 'cons (car l) (listify (cdr l))))))

(defun translate-dcl-lst (edcls wrld)

; Given a bunch of expanded dcls we find all the (TYPE x v1 ... vn)
; dcls among them and make a list of untranslated terms expressing the
; type restriction x for each vi.

  (cond ((null edcls) nil)
        ((eq (caar edcls) 'type)
         (append (translate-declaration-to-guard-var-lst (cadr (car edcls))
                                                         (cddr (car edcls))
                                                         wrld)
                 (translate-dcl-lst (cdr edcls) wrld)))
        (t (translate-dcl-lst (cdr edcls) wrld))))

(defconst *oneify-primitives*

;;;; Some day we should perhaps remove consp and other such functions from this
;;;; list because of the "generalized Boolean" problem.

; Add to this list whenever we find a guardless function in #+acl2-loop-only.

  '(if equal cons not consp atom acl2-numberp characterp integerp rationalp
       stringp symbolp

; We want fmt-to-comment-window (which will arise upon macroexpanding calls of
; cw and cw-print-base-radix) to be executed always in raw Lisp, so we add it
; to this list in order to bypass its *1* function.

       fmt-to-comment-window
       fmt-to-comment-window!

; When we oneify, we sometimes do so on code that was laid down for constrained
; functions.  Therefore, we put throw on the list.

       throw-raw-ev-fncall

; The next group may be important for the use of safe-mode.

       makunbound-global
       trans-eval ev ev-lst ev-fncall
;      fmt-to-comment-window ; already included above
;      fmt-to-comment-window! ; already included above
       sys-call-status
;      pstack-fn
       untranslate
       untranslate-lst
       trace$-fn-general untrace$-fn-general untrace$-fn1 maybe-untrace$-fn
       set-w acl2-unwind-protect

; We know that calls of mv-list in function bodies are checked syntactically to
; satisfy arity and syntactic requirements, so it is safe to call it in raw
; Lisp rather than somehow considering its *1* function.  We considered adding
; return-last as well, but not only does return-last have a guard other than T,
; but indeed (return-last 'mbe1-raw exec logic) macroexpands in raw Lisp to
; exec, which isn't what we want in oneified code.  We considered adding
; functions in *defun-overrides*, but there is no need, since defun-overrides
; makes suitable definitions for *1* functions.

       mv-list
       ))

(defconst *ec-call-bad-ops*

; We are conservative here, avoiding (ec-call (fn ...)) when we are the least
; bit nervous about that.  Reasons to be nervous are special treatment of a
; function symbol by guard-clauses (if) or special treatment in oneify
; (return-last and anything in *oneify-primitives*).

  (union-equal '(if wormhole-eval return-last)
               *oneify-primitives*))

(defmacro return-last-call (fn &rest args)
  `(fcons-term* 'return-last ',fn ,@args))

(defmacro prog2$-call (x y)
  `(fcons-term* 'return-last ''progn ,x ,y))

(defun dcl-guardian (term-lst)

; Suppose term-lst is a list of terms, e.g., '((INTEGERP X) (SYMBOLP V)).
; We produce an expression that evaluates to t if the conjunction of the
; terms is true and returns a call of illegal otherwise.

  (cond ((or (null term-lst)

; A special case is when term-list comes from (the (type type-dcl) x).  The
; expansion of this call of THE results in a declaration of the form (declare
; (type (or t type-dcl) var)).  We have seen examples where generating the
; resulting if-term, to be used in a call of prog2$, throws off a proof that
; succeeded before the addition of this declaration (which was added in order
; to handle (the (satisfies pred) term)); specifically, len-pushus in
; symbolic/tiny-fib/tiny.lisp (and probably in every other tiny.lisp).  Here we
; simplify the resulting term (if t t (type-pred x)) to t.  And when we use
; dcl-guardian to create (prog2$ type-test u), we instead simply create u if
; type-test is t.

             (let ((term (car term-lst)))
               (and (ffn-symb-p term 'if)
                    (equal (fargn term 1) *t*)
                    (equal (fargn term 2) *t*))))
         *t*)
        ((null (cdr term-lst))
         (fcons-term* 'check-dcl-guardian
                      (car term-lst)
                      (kwote (car term-lst))))
        (t (prog2$-call (fcons-term* 'check-dcl-guardian
                                     (car term-lst)
                                     (kwote (car term-lst)))
                        (dcl-guardian (cdr term-lst))))))

(defun ignore-vars (dcls)
  (cond ((null dcls) nil)
        ((eq (caar dcls) 'ignore)
         (append (cdar dcls) (ignore-vars (cdr dcls))))
        (t  (ignore-vars (cdr dcls)))))

(defun ignorable-vars (dcls)
  (cond ((null dcls) nil)
        ((eq (caar dcls) 'ignorable)
         (append (cdar dcls) (ignorable-vars (cdr dcls))))
        (t  (ignorable-vars (cdr dcls)))))

(defun mv-nth-list (var i maximum)
  (cond ((= i maximum) nil)
        (t (cons (fcons-term* 'mv-nth (list 'quote i) var)
                 (mv-nth-list var (1+ i) maximum)))))

(defmacro translate-bind (x val bindings)

; Used only in translation.  Binds x to val on bindings.

  `(cons (cons ,x ,val) ,bindings))

(defun translate-deref (x bindings)

; X is t, a consp value or the name of some function.  If the last, we
; chase down its ``ultimate binding'' in bindings.  Bindings may
; contain many indirections, but may not be circular except when x is
; bound to x itself.  We return nil if x is not bound in bindings.

  (cond ((eq x t) t)
        ((consp x) x)
        (t
         (let ((p (assoc-eq x bindings)))
           (cond (p
                  (cond ((eq x (cdr p)) x)
                        (t (translate-deref (cdr p) bindings))))
                 (t nil))))))

(defun translate-unbound (x bindings)

; X is considered unbound if it is a function name whose ultimate
; binding is a function name.

  (and (not (eq x t))
       (atom (translate-deref x bindings))))

(defun listlis (l1 l2)

;  Like pairlis$, but LISTs instead of CONSes.

  (cond ((null l1) nil)
        (t (cons (list (car l1) (car l2))
                 (listlis (cdr l1) (cdr l2))))))

(mutual-recursion

(defun find-first-var (term)
  (cond ((variablep term) term)
        ((fquotep term) nil)
        ((find-first-var-lst (fargs term)))
        ((flambdap (ffn-symb term))
         (car (lambda-formals (ffn-symb term))))
        (t nil)))

(defun find-first-var-lst (lst)
  (cond ((null lst) nil)
        (t (or (find-first-var (car lst))
               (find-first-var-lst (cdr lst))))))
)

(mutual-recursion

(defun find-first-fnsymb (term)
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambdap (ffn-symb term))
         (or (find-first-fnsymb-lst (fargs term))
             (find-first-fnsymb (lambda-body (ffn-symb term)))))
        (t (ffn-symb term))))

(defun find-first-fnsymb-lst (lst)
  (cond ((null lst) nil)
        (t (or (find-first-fnsymb (car lst))
               (find-first-fnsymb-lst (cdr lst))))))
)

(defun find-pkg-witness (term)

; This function must return a symbol.  Imagine that term is to be replaced by
; some variable symbol.  In which package do we intern that symbol?  This
; function finds a symbol which is used with intern-in-package-of-symbol.
; Thus, the package of the returned symbol is important to human readability.
; We return the first variable we see in term, if there is one.  Otherwise, we
; return the first function symbol we see, if there is one.  Otherwise, we
; return the symbol 'find-pkg-witness.

  (or (find-first-var term)
      (find-first-fnsymb term)
      'find-pkg-witness))


;                          TRANSLATE

; For comments on translate, look after the following nest.

(defmacro trans-er (&rest args)

; Warning: Keep in sync with er-cmp (see commented-out call below) and
; er-cmp-fn.  We avoid using er-cmp because we don't want break-on-error to
; break on translate errors, since we know that sometimes translate errors are
; benign -- for example, in translate11 we backtrack if there is an error in
; translating the term tbr in (IF tst tbr fbr), to translate fbr first.

; Like er-cmp but returns 3 values, the additional one being the current value
; of bindings.  See also trans-er+ and trans-er+?.

  `(mv-let (ctx msg-or-val)
;          (er-cmp ,@args) ; See "keep in sync" comment above.
           (mv ,(car args) (msg ,(cadr args) ,@(cddr args)))
           (mv ctx msg-or-val bindings)))

(defmacro trans-er+ (form ctx str &rest args)

; Warning: Keep in sync with er-cmp (see commented-out call below) and
; er-cmp-fn.  For an explanation, see the corresponding warning in trans-er.

; This macro is like trans-er, but it also prints the offending context, form,
; which could be the untranslated term or a surrounding term, etc.

  `(mv-let (ctx msg-or-val)
;          (er-cmp ,ctx ; See "keep in sync" comment above.
;                  "~@0  Note:  this error occurred in the context ~x1."
;                  (msg ,str ,@args)
;                  ,form)
           (mv ,ctx
               (msg "~@0  Note:  this error occurred in the context ~x1."
                    (msg ,str ,@args)
                    ,form))
           (mv ctx msg-or-val bindings)))

(defmacro trans-er+? (cform x ctx str &rest args)

; This macro behaves as trans-er+ using cform, if x and cform are distinct (in
; which case cform can provide context beyond x); else it behaves as trans-er.

; The guard is for efficiency, to guarantee that we don't evaluate x or cform
; twice.  (Actually x is only evaluated once by the expansion of this macro,
; but it is likely evaluated in another place by the calling code.)

  (declare (xargs :guard (and (symbolp cform)
                              (symbolp x))))
  `(cond ((equal ,x ,cform)
          (trans-er ,ctx ,str ,@args))
         (t
          (trans-er+ ,cform ,ctx ,str ,@args))))

(defmacro trans-value (x &optional (bindings 'bindings))

; Like value-cmp but returns 3 values, erp, x, and bindings.

  `(mv nil ,x ,bindings))

(defmacro trans-er-let* (alist body)

; Like er-let*-cmp but deals in trans-er's 3-tuples and binds and returns
; bindings.

  (declare (xargs :guard (alistp alist)))
  (cond ((null alist)
         (list 'check-vars-not-free
               '(er-let-star-use-nowhere-else)
               body))
        (t (list 'mv-let
                 (list 'er-let-star-use-nowhere-else
                       (caar alist)
                       'bindings)
                 (cadar alist)
                 (list 'cond
                       (list 'er-let-star-use-nowhere-else
                             (list 'mv
                                   'er-let-star-use-nowhere-else
                                   (caar alist)
                                   'bindings))
                       (list t (list 'trans-er-let* (cdr alist) body)))))))

(defun hide-ignored-actuals (ignore-vars bound-vars value-forms)
  (cond

; Most of the time there won't be any ignore-vars, so we don't mind
; paying the price of checking the following condition on each
; recursive call (even though the answer remains the same).

   ((null ignore-vars)
    value-forms)
   ((null bound-vars)
    nil)
   ((and (member-eq (car bound-vars) ignore-vars)
         (let ((form (car value-forms)))
           (and (or (variablep form)
                    (fquotep form)
                    (not (eq (ffn-symb form) 'hide)))
                (cons (fcons-term* 'hide form)
                      (hide-ignored-actuals ignore-vars
                                            (cdr bound-vars)
                                            (cdr value-forms)))))))
   (t
    (cons (car value-forms)
          (hide-ignored-actuals ignore-vars
                                (cdr bound-vars)
                                (cdr value-forms))))))

(defun augment-ignore-vars (bound-vars value-forms acc)

; Note added shortly before releasing ACL2 Version_6.1.  This function seems to
; have been added in Version_2.9.4.  It's not clear that we need this function,
; since it doesn't seem that translate11 is passed a form with HIDE calls
; already added in the manner described below.  For now we'll continue to calls
; this function, as it seems harmless enough.  We might want to try a
; regression sometime with it redefined simply to return acc, and if that
; succeeds, we could consider deleting it.  (But that seems dangerous to do
; just before a release!)

; Bound-vars and value-forms are lists of the same length.  Return the result
; of extending the list acc by each member of bound-vars for which the
; corresponding element of value-forms (i.e., in the same position) is a call
; of hide.  Since translate11 inserts a call of hide for each bound var, this
; function returns a list that contains every variable declared ignored in the
; original let form binding bound-vars to value-forms (or the corresponding
; untranslations of the terms in value-forms).

  (cond ((endp bound-vars)
         acc)
        ((let ((form (car value-forms)))
           (or (variablep form)
               (fquotep form)
               (not (eq (ffn-symb form) 'hide))))
         (augment-ignore-vars (cdr bound-vars) (cdr value-forms) acc))
        (t (augment-ignore-vars (cdr bound-vars)
                                (cdr value-forms)
                                (cons (car bound-vars) acc)))))

; Essay on STOBJS-IN and STOBJS-OUT

; Once upon a time, before user-defined single-threaded objects came along,
; every function symbol had four aspects to its syntactic character:
; * its arity
; * which of its inputs was STATE
; * its multiplicity (how many results it returns)
; * which of its outputs was STATE
; These were coded on the property list in a somewhat optimized way involving
; the four properties FORMALS, STATE-IN, MULTIPLICITY, and STATE-OUT.  If
; STATE-IN was absent or NIL, then STATE was not a formal.  Otherwise, STATE-IN
; indicated the position (1-based) of STATE in the FORMALS.  If MULTIPLICITY
; was absent, it was implicitly 1.  If STATE-OUT was T then multiplicity was 1
; and STATE was the single result.  We review these old characteristics because
; they were generalized when we introduced single-threaded objects, or
; ``stobjs''.

; Since the introduction of stobjs, every function has four aspects to its
; syntactic character:

; * its arity
; * which of its inputs are stobjs
; * its multiplicity
; * which of its outputs are stobjs

; This is coded on the property list as follows.  First, a ``STOBJ flag'' is
; either NIL or the name of a stobj (including STATE).  A list of n STOBJ flags
; can thus indicate which elements of another list of length n are stobjs and
; which stobjs they are.

; FORMALS gives the list of formals.

; STOBJS-IN is a list of STOBJ flags that is interpreted in 1:1 correspondence
; with the formals.  Every function symbol must have a STOBJS-IN property.  We
; do not support space-efficient coding of any special cases.  Each formal must
; be the corresponding stobj.

; STOBJS-OUT is a list of stobj flags indicating both the multiplicity and
; which outputs are stobjs, and the correspondence between output stobjs and
; input stobjs.  For example, if the STOBJS-IN property is (nil $s1 $s2 nil)
; and the STOBJS-OUT property is (nil $s2), then two values are returned, where
; the second value returned is the same stobj as the third input (labeled $s2
; above).  Every function must have a STOBJS-OUT property, with the effective
; exception of return-last: an error is caused if the function stobjs-out is
; applied to return-last, which always returns its last argument (possibly a
; multiple value) and should generally be considered as not having STOBJS-OUT.

; We now consider translation performed on behalf of evaluation (as opposed to
; translating only for the logic, as when translating proposed theorems).
; During translation of each argument of a function call, we generally have a
; stobj flag associated with the term we are translating, indicating the
; expected stobj, if any, produced by the term.  Consider a stobj flag, $s,
; that is non-nil, i.e., is a stobj name.  Then the term occupying the
; corresponding slot MUST be the stobj name $s, except in the case that
; congruent stobjs are involved (see below).  We think of the stobj flags as
; meaning that the indicated stobj name is the only term that can be passed
; into that slot.

; We mentioned a relaxation above for the case of congruent stobjs.  (See :DOC
; defstobj for an introduction to congruent stobjs.)  Consider again a function
; call.  Each argument corresponding to a non-nil stobj flag should be
; a stobj that is congruent to that flag (a stobj).  Moreover, no two such
; arguments may be the same.

; We turn now from translation to evaluation in the logic (i.e., with *1*
; functions that might or might not pass control to raw Lisp functions).

; Our stobj primitives are all capable of computing on the logical objects that
; represent stobjs.  But they give special treatment to the live ones.  There
; are two issues.  First, we do not want a live one ever to get into a
; non-stobj slot because the rest of the functions do not know how to handle
; it.  So if the actual is a live stobj, the formal must be a stobj.  Second,
; if the ith element of STOBJS-IN is a stobj, $s, and the jth element of
; STOBJS-OUT is also $s, and the ith actual of a call is a live stobj, then the
; jth return value from that call is that same live stobj.  This is the only
; way that a live stobj can be found in the output (unless there is a call of a
; creator function, which is untouchable).

(defun compute-stobj-flags (lst known-stobjs w)

; Lst is a list of possibly UNTRANSLATED terms!  This function
; computes the stobj flags for the elements of the list, assigning nil
; unless the element is a symbol with a 'STOBJ property in w.

  (cond ((endp lst) nil)
        ((stobjp (car lst) known-stobjs w)
         (cons (car lst)
               (compute-stobj-flags (cdr lst) known-stobjs w)))
        (t (cons nil
                 (compute-stobj-flags (cdr lst) known-stobjs w)))))

(defun prettyify-stobj-flags (lst)

; Note: The use of * to denote NIL here is arbitrary.  But if another
; symbol is used, make sure it could never be defined as a stobj by
; the user!

  (cond ((endp lst) nil)
        (t (cons (or (car lst) '*) (prettyify-stobj-flags (cdr lst))))))

(defun unprettyify-stobj-flags (lst)
  (cond ((endp lst) nil)
        (t (cons (if (eq (car lst) '*) nil (car lst))
                 (unprettyify-stobj-flags (cdr lst))))))

(defun prettyify-stobjs-out (stobjs-out)

; This function uses prettyify-stobj-flags in the singleton case just
; to localize the choice of external form to that function.

  (if (cdr stobjs-out)
      (cons 'mv (prettyify-stobj-flags stobjs-out))
    (car (prettyify-stobj-flags stobjs-out))))

(defun defstobj-supporterp (name wrld)

; If name is supportive of a single-threaded object implementation, we return
; the name of the stobj.  Otherwise, we return nil.  By "supportive" we mean
; name is the object name, the live var, a recognizer, accessor, updater,
; helper, resizer, or length function, or a constant introduced by the
; defstobj, or in the case of defabsstobj, a recognizer, accessor, or (other)
; exported function.

  (cond
   ((getpropc name 'stobj nil wrld)
    name)
   ((getpropc name 'stobj-function nil wrld))
   ((getpropc name 'stobj-constant nil wrld))
   (t (getpropc name 'stobj-live-var nil wrld))))

(defun stobj-creatorp (name wrld)

; Returns the name of the stobj that name creates, if name is a stobj creator;
; else returns nil.

; Keep the null test below in sync with the null test (and stobj-flag (null
; (cadr def))) near the top of oneify-cltl-code.

  (and (symbolp name)
       (null (getpropc name 'formals t wrld))
       (getpropc name 'stobj-function nil wrld)))

(mutual-recursion

(defun ffnnamep (fn term)

; We determine whether the function fn (possibly a lambda-expression)
; is used as a function in term.

  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (equal fn (ffn-symb term))
             (ffnnamep fn (lambda-body (ffn-symb term)))
             (ffnnamep-lst fn (fargs term))))
        ((eq (ffn-symb term) fn) t)
        (t (ffnnamep-lst fn (fargs term)))))

(defun ffnnamep-lst (fn l)
  (declare (xargs :guard (pseudo-term-listp l)))
  (if (endp l)
      nil
    (or (ffnnamep fn (car l))
        (ffnnamep-lst fn (cdr l)))))

)

(defconst *synp-trans-err-string*
  "A synp term must take three quoted arguments, unlike ~x0.  Normally, a call ~
   to synp is the result of the macroexpansion of a call to syntaxp or ~
   bind-free, but this does not seem to be the case here.  If you believe this ~
   error message is itself in error please contact the maintainers of ACL2.")

(defun unknown-binding-msg (stobjs-bound str1 str2 str3)
  (msg
   "The single-threaded object~#0~[ ~&0 has~/s ~&0 have~] been bound in ~@1.  ~
    It is a requirement that ~#0~[this object~/these objects~] be among the ~
    outputs of ~@2.  But, at the time at which we process ~@2, we are unable ~
    to determine what the outputs are and so cannot allow it.  This situation ~
    arises when the output of ~@2 is a recursive call of the function being ~
    admitted and the call is encountered before we have encountered the first ~
    base case of the function (which would tell us what single-threaded ~
    objects are being returned).  In the case of the admission of a clique of ~
    mutually-recursive functions, the situation can additionally arise when ~
    the output of ~@2 is a call of a function in the clique and that function ~
    appears in the clique after the definition in question.  This situation ~
    can be eliminated by rearranging the order of the branches of an IF ~
    and/or rearranging the order of the presentation of a clique of mutually ~
    recursive functions."
   stobjs-bound str1 str2 str3))

(defconst *macros-for-nonexpansion-in-raw-lisp*

; If a symbol, sym, is on this list then the form (sym a1 ... ak) is oneified
; to (sym a1' ... ak') where ai' is the oneification of ai.  Thus, conditions
; for sym being put on this list include that it is defined as a function or
; macro in raw lisp and that it is "applied" to a list of terms.  Another
; condition is that it not have a guard, because if a guard is present it is
; likely that Common Lisp will cause an error when we run the oneified version
; on inappropriate inputs.

; The value of this list should be a subset of
; (loop for x in (w state) when (eq (cadr x) 'macro-body) collect (car x))
; Below we exhibit the value of the sloop above and comment out the macros we
; do not want on it.  The macros commented out will be translated away in
; oneified code.

; When in doubt, comment it out!

  '(f-decrement-big-clock  ; we leave these two in oneified code because they
    f-big-clock-negative-p ; are handled by our raw lisp
;   make-list
;   ; Must omit f-put-global, f-get-global, and f-boundp-global, in order to
;   ; avoid calling global-table in raw Lisp.
;   mv-let                 ; not of the right shape so special-cased in oneify
    mv

; The following are not in primitive-event-macros (which is handled directly
; in oneify-cltl-code).

; Note that safe-mode for make-event will require addition of the following four:
;   certify-book make-event defpkg in-package

;   acl2-unwind-protect
;   pprogn
;   the
    list*

;   rest tenth ninth eighth seventh sixth fifth fourth third second first cddddr
;   cdddar cddadr cddaar cdaddr cdadar cdaadr cdaaar cadddr caddar cadadr cadaar
;   caaddr caadar caaadr caaaar cdddr cddar cdadr cdaar caddr cadar caadr caaar
;   cddr cdar cadr caar

;   case progn mutual-recursion

;   / * >= > <=   ; guarded
;   let* cond
;   + -           ; guarded
    or and list
;   local
    with-live-state
    ))

; Historical Note: The following material -- chk-no-duplicate-defuns,
; chk-state-ok, chk-arglist, and chk-defuns-tuples -- used to be in the file
; defuns.lisp.  It is mainly concerned with translating hints.  But we had to
; move it to before prove.lisp when we added hint functions, and then we had to
; move it before translate11 when we introduced flet.

(defun chk-no-duplicate-defuns-cmp (lst ctx)
  (declare (xargs :guard (true-listp lst)))
  (cond ((no-duplicatesp lst)
         (value-cmp nil))
        (t (er-cmp ctx
                   "We do not permit duplications among the list of symbols ~
                    being defined.  However, the symbol~#0~[ ~&0 is~/s ~&0 ~
                    are each~] defined more than once."
                   (duplicates lst)))))

(defun chk-no-duplicate-defuns (lst ctx state)
  (cmp-to-error-triple (chk-no-duplicate-defuns-cmp lst ctx)))

(defun chk-state-ok-msg (wrld)

; We are in a context where 'state is a member of a list of formals.  Is this
; OK?

  (cond ((not (cdr (assoc-eq :state-ok
                             (table-alist 'acl2-defaults-table
                                          wrld))))
         (msg "The variable symbol STATE should not be used as a formal ~
               parameter of a defined function unless you are aware of its ~
               unusual status and the restrictions enforced on its use.  See ~
               :DOC set-state-ok."))
        (t nil)))

(defun chk-state-ok (ctx wrld state)
  (let ((msg (chk-state-ok-msg wrld)))
    (cond (msg (er soft ctx "~@0" msg))
          (t (value nil)))))

(defun chk-arglist-msg (args chk-state wrld)
  (cond ((arglistp args)
         (if (and chk-state (member-eq 'state args))
             (chk-state-ok-msg wrld)
           nil))
        ((not (true-listp args))
         (msg "The argument list to a function or macro must be a true list ~
               but ~x0 is not."
              args))
        (t (mv-let (culprit explan)
                   (find-first-bad-arg args)
                   (msg "The argument list to a function or macro must be a ~
                         true list of distinct, legal variable names.  ~x0 is ~
                         not such a list.  The element ~x1 violates the rules ~
                         because it ~@2."
                        args culprit explan)))))

(defun msg-to-cmp (ctx msg)

; Convert a given context and message to a corresponding context-message pair
; (see the Essay on Context-message Pairs).

  (assert$ ctx
           (cond (msg (mv ctx msg))
                 (t (mv nil nil)))))

(defun chk-arglist-cmp (args chk-state ctx wrld)
  (msg-to-cmp ctx (chk-arglist-msg args chk-state wrld)))

(defun@par chk-arglist (args chk-state ctx wrld state)
  (let ((msg (chk-arglist-msg args chk-state wrld)))
    (cond (msg (er@par soft ctx "~@0" msg))
          (t (value@par nil)))))

(defun logical-name-type (name wrld quietp)

; Given a logical-namep we determine what sort of logical object it is.

  (cond ((stringp name) 'package)
        ((function-symbolp name wrld) 'function)
        ((getpropc name 'macro-body nil wrld) 'macro)
        ((getpropc name 'const nil wrld) 'const)
        ((getpropc name 'theorem nil wrld) 'theorem)
        ((not (eq (getpropc name 'theory t wrld) t))
         'theory)
        ((getpropc name 'label nil wrld) 'label)
        ((getpropc name 'stobj nil wrld)

; Warning: Non-stobjs can have the stobj property, so do not move this cond
; clause upward!

         'stobj)
        ((getpropc name 'stobj-live-var nil wrld)
         'stobj-live-var)
        (quietp nil)
        (t (er hard 'logical-name-type
               "~x0 is evidently a logical name but of undetermined type."
               name))))

(defun chk-all-but-new-name-cmp (name ctx new-type w)

; We allow new-type to be NIL.  Currently, its only uses are to allow
; redefinition of functions, macros, and consts residing in the main Lisp
; package, and to allow events to use the main Lisp package when they
; do not introduce functions, macros, or constants.

  (cond ((not (symbolp name))
         (er-cmp ctx
                 "Names must be symbols and ~x0 is not."
                 name))
        ((keywordp name)
         (er-cmp ctx
                 "Keywords, such as ~x0, may not be defined or constrained."
                 name))
        ((and (member-eq new-type '(function const stobj macro
                                             constrained-function))
              (equal *main-lisp-package-name* (symbol-package-name name))
              (or

; Only definitions can be redefined from :program mode to :logic mode.

               (not (eq new-type 'function))
               (not (eq (logical-name-type name w t) 'function)))
              (not (global-val 'boot-strap-flg w)))
         (er-cmp ctx
                 "Symbols in the main Lisp package, such as ~x0, may not be ~
                  defined or constrained."
                 name))
        (t (value-cmp nil))))

(defun chk-all-but-new-name (name ctx new-type w state)
  (cmp-to-error-triple (chk-all-but-new-name-cmp name ctx new-type w)))

(defun chk-defuns-tuples-cmp (lst local-p ctx wrld)
  (cond ((atom lst)

; This error message can never arise because we know terms are true
; lists.

         (cond ((eq lst nil) (value-cmp nil))
               (t (er-cmp ctx
                          "A list of definitions must be a true list."))))
        ((not (true-listp (car lst)))
         (er-cmp ctx
                 "Each~#0~[ local~/~] definition must be a true list and ~x1 ~
                  is not."
                 (if local-p 0 1)
                 (if local-p (car lst) (cons 'DEFUN (car lst)))))
        ((not (>= (length (car lst))
                  3))
         (er-cmp ctx
                 "A definition must be given three or more arguments, but ~x0 ~
                  has length only ~x1."
                 (car lst)
                 (length (car lst))))
        (t (er-progn-cmp
            (chk-all-but-new-name-cmp (caar lst) ctx 'function wrld)
            (chk-arglist-cmp (cadar lst) nil ctx wrld)
            (er-let*-cmp
             ((edcls (collect-declarations-cmp
                      (butlast (cddar lst) 1)
                      (cadar lst)
                      (if local-p 'flet 'defuns)
                      ctx wrld))
              (rst (chk-defuns-tuples-cmp (cdr lst) local-p ctx wrld)))
             (value-cmp (cons (list* (caar lst)
                                     (cadar lst)
                                     (if (stringp (car edcls))
                                         (car edcls)
                                       nil)
                                     (if (stringp (car edcls))
                                         (cdr edcls)
                                       edcls)
                                     (last (car lst)))
                              rst)))))))

(defun chk-defuns-tuples (lst local-p ctx wrld state)
  (cmp-to-error-triple (chk-defuns-tuples-cmp lst local-p ctx wrld)))

(defun non-trivial-encapsulate-ee-entries (embedded-event-lst)
  (cond ((endp embedded-event-lst)
         nil)
        ((and (eq (caar embedded-event-lst) 'encapsulate)
              (cadar embedded-event-lst))
         (cons (car embedded-event-lst)
               (non-trivial-encapsulate-ee-entries (cdr embedded-event-lst))))
        (t (non-trivial-encapsulate-ee-entries (cdr embedded-event-lst)))))

(defun name-dropper (lst)

; This function builds a term that mentions each element of lst.  Provided the
; elements of list are translated terms, the output is a translated term.
; Provided every element of lst has a guard of t, the output has a guard of t.
; The intention here is that lst is a list of distinct variable names and
; name-dropper builds a translated term whose free-vars are those variables;
; furthermore, it is cheap to evaluate and always has a guard of T.
; The general form is either 'NIL, a single var, or a PROG2$ nest around
; the vars.

  (cond ((endp lst) *nil*)
        ((endp (cdr lst)) (car lst))
        (t (prog2$-call (car lst)
                        (name-dropper (cdr lst))))))

(defun first-assoc-eq (keys alist)
  (declare (xargs :guard (and (alistp alist)
                              (symbol-listp keys))))
  (cond ((endp keys)
         nil)
        (t (or (assoc-eq (car keys) alist)
               (first-assoc-eq (cdr keys) alist)))))

(defun context-for-encapsulate-pass-2 (wrld in-local-flg)

; Return 'illegal if we are in pass 2 of a non-trivial encapsulate, or if known
; to be non-local (as per in-local-flg) in pass 1 of a non-trivial encapsulate.
; We include the latter because presumably it is courteous to the user to
; signal an issue during pass 1, rather than waiting till the inevitable
; problem in pass 2.

; If we are in pass 1 of a non-trivial encapsulate but in a local context, then
; we might or might not be in an illegal context for the corresponding pass 2,
; depending on whether the local wrapper is close enough to make the context
; disappear in pass 2.  So we return 'maybe in this case.  Otherwise, we return
; nil.

  (let ((ee-entries (non-trivial-encapsulate-ee-entries
                     (global-val 'embedded-event-lst wrld))))
    (and ee-entries ; we are in at least one non-trivial encapsulate
         (cond ((or

; The term (cddr (car ee-entries)) is true exactly when we are in pass 2 of the
; immediately superior non-trivial encapsulate, hence holds if we are in pass 2
; of some superior encapsulate (since then we would be skipping pass 1 of its
; inferior encapsulates).  So (cddr (car ee-entries)) is non-nil if and only if
; we are in pass 2 of some encapsulate.

                 (cddr (car ee-entries))
                 (null in-local-flg))
                'illegal)
               (t 'maybe)))))

(defconst *brr-globals*
  '(brr-monitored-runes
    brr-stack
    brr-gstack
    brr-alist))

(defun unknown-binding-msg-er (x ctx stobjs-bound str1 str2 str3)
  (mv-let
   (erp msg bindings)
   (let ((bindings nil)) ; don't-care
     (trans-er+
      x ctx
      "~@0"
      (msg "The single-threaded object~#0~[ ~&0 has~/s ~&0 have~] been bound ~
            in ~@1.  It is a requirement that ~#0~[this object~/these ~
            objects~] be among the outputs of ~@2.  But, at the time at which ~
            we process ~@2, we are unable to determine what the outputs are ~
            and so cannot allow it.  In the case of the admission of a clique ~
            of mutually-recursive functions, this situation can arise when ~
            the output of ~@2 is a call of a function defined in the clique ~
            after the definition containing ~@2, in which case the problem ~
            might be eliminated by rearranging the order of the definitions."
            stobjs-bound str1 str2 str3)))
   (declare (ignore bindings))
   (mv erp msg :UNKNOWN-BINDINGS)))

(defun congruent-stobjsp (st1 st2 wrld)
  (eq (congruent-stobj-rep st1 wrld)
      (congruent-stobj-rep st2 wrld)))

(defun stobjs-in-out1 (stobjs-in args known-stobjs wrld alist new-stobjs-in)

; We are translating an application of a function to args. where args satisfies
; the stobjs discipline of passing a stobj name to a stobjs-in position; see
; the comment about this in translate11-call.

  (cond ((endp stobjs-in)
         (if (null args)
             (mv alist (reverse new-stobjs-in))
           (mv :failed nil)))
        ((endp args) (mv :failed nil))
        ((null (car stobjs-in))
         (stobjs-in-out1 (cdr stobjs-in) (cdr args) known-stobjs wrld alist
                         (cons nil new-stobjs-in)))
        ((and (car stobjs-in)
              (stobjp (car args) known-stobjs wrld)
              (not (rassoc-eq (car args)
                              alist)) ; equiv. to not member of new-stobjs-in
              (or (eq (car stobjs-in) (car args))
                  (congruent-stobjsp (car stobjs-in) (car args) wrld)))
         (stobjs-in-out1 (cdr stobjs-in) (cdr args) known-stobjs wrld
                         (acons (car stobjs-in) (car args) alist)
                         (cons (car args) new-stobjs-in)))
        (t (mv :failed nil))))

(defun stobjs-in-matchp (stobjs-in args)
  (cond ((endp stobjs-in) (null args))
        ((endp args) nil)
        ((or (null (car stobjs-in))
             (eq (car stobjs-in) (car args)))
         (stobjs-in-matchp (cdr stobjs-in) (cdr args)))
        (t nil)))

(defun stobjs-in-out (fn args stobjs-out known-stobjs wrld)

; We are translating an application of fn to args, where fn has the indicated
; stobjs-out and args satisfies the stobjs discipline of passing a stobj name
; to a stobjs-in position.  See the comment about this discipline in
; translate11-call.

; In general we return (mv flg new-stobjs-in new-stobjs-out), according to one
; of the following cases.

; - If flg is :failed, then we return (mv :failed stobjs-in stobjs-out), where
;   stobjs-in is the stobjs-in of fn and stobjs-out is returned unchanged.

; - Otherwise flg is an alist, and either stobjs-out is a symbol (representing
;   a function symbol or :stobjs-out bound in an implicit bindings in
;   translate11), or else fn can be viewed as mapping new-stobjs-in to
;   new-stobjs-out.  Alist maps the original stobjs-in to new-stobjs-in; in
;   particular, if alist is nil then new-stobjs-in is equal to the original
;   stobjs-in.

  (let ((stobjs-in (cond ((consp fn)
                          (compute-stobj-flags (lambda-formals fn)
                                               known-stobjs
                                               wrld))
                         (t (stobjs-in fn wrld)))))
    (cond ((stobjs-in-matchp stobjs-in args)
           (mv nil stobjs-in stobjs-out))
          (t (mv-let
              (alist new-stobjs-in)
              (stobjs-in-out1 stobjs-in args known-stobjs wrld nil nil)
              (cond ((eq alist :failed)
                     (mv :failed stobjs-in stobjs-out))
                    ((symbolp stobjs-out)
                     (mv alist new-stobjs-in stobjs-out))
                    (t (mv alist
                           new-stobjs-in
                           (apply-symbol-alist alist stobjs-out nil)))))))))

(defun non-trivial-stobj-binding (stobj-flags bindings)
  (declare (xargs :guard (and (symbol-listp stobj-flags)
                              (symbol-doublet-listp bindings)
                              (eql (length stobj-flags)
                                   (length bindings)))))
  (cond ((endp stobj-flags) nil)
        ((or (null (car stobj-flags))
             (assert$ (eq (car stobj-flags) (caar bindings))
                      (eq (car stobj-flags) (cadar bindings))))
         (non-trivial-stobj-binding (cdr stobj-flags) (cdr bindings)))
        (t (car stobj-flags))))

(defun formalized-varlistp (varlist formal-lst)
  (declare (xargs :guard (and (symbol-listp varlist)
                              (pseudo-termp formal-lst))))
  (cond ((endp varlist)
         (equal formal-lst *nil*))
        ((variablep formal-lst)
         nil)
        (t (and ; (not (fquotep formal-lst))
            (eq (ffn-symb formal-lst) 'cons)
            (eq (car varlist) (fargn formal-lst 1))
            (formalized-varlistp (cdr varlist) (fargn formal-lst 2))))))

(defun throw-nonexec-error-p1 (targ1 targ2 name formals)

; Consider a term (return-last targ1 targ2 ...).  We recognize when this term
; is of the form (return-last 'progn (throw-non-exec-error x ...) ...), with
; some additional requirements as explained in a comment in
; throw-nonexec-error-p.

  (declare (xargs :guard (and (pseudo-termp targ1)
                              (pseudo-termp targ2)
                              (symbolp name)
                              (symbol-listp formals))))
  (and (quotep targ1)
       (eq (unquote targ1) 'progn)
       (ffn-symb-p targ2 'throw-nonexec-error)
       (or (null name)
           (let ((qname (fargn targ2 1)))
             (and (quotep qname)
                  (if (eq name :non-exec)
                      (eq (unquote qname) :non-exec)
                    (and (eq (unquote qname) name)
                         (formalized-varlistp formals (fargn targ2 2)))))))))

(defun throw-nonexec-error-p (body name formals)

; We recognize terms that could result from translating (prog2$
; (throw-nonexec-error x ...) ...), i.e., terms of the form (return-last 'progn
; (throw-non-exec-error x ...) ...).  If name is nil, then there are no further
; requirements.  If name is :non-exec, then we require that x be (quote
; :non-exec).  Otherwise, we require that x be (quote name) and that the second
; argument of throw-non-exec-error be (cons v1 (cons v2 ... (cons vk nil)
; ...)), where formals is (v1 v2 ... vk).

  (declare (xargs :guard (and (pseudo-termp body)
                              (symbolp name)
                              (symbol-listp formals))))
  (and (ffn-symb-p body 'return-last)
       (throw-nonexec-error-p1 (fargn body 1) (fargn body 2) name formals)))

(defun chk-flet-declarations (names decls declare-form ctx)
  (cond ((null decls)
         (value-cmp nil))
        ((atom decls)
         (er-cmp ctx
                 "The DECLARE form for an FLET expression must be a ~
                  true-list.  The form ~x0 is thus illegal.  See :DOC flet."
                 declare-form))
        (t (let ((decl (car decls)))
             (cond ((and (consp decl)
                         (member-eq (car decl)
                                    '(inline notinline))
                         (true-listp (cdr decl))
                         (subsetp-eq (cdr decl) names))
                    (chk-flet-declarations names (cdr decls) declare-form ctx))
                   (t (er-cmp ctx
                              "Each declaration in a DECLARE form of an flet ~
                               expression must be of the form (INLINE . fns) ~
                               or (NOTINLINE . fns), where fns is a true-list ~
                               of names that are all defined by the FLET ~
                               expression.  The declare form ~x0 is thus ~
                               illegal because of its declaration, ~x1.  See ~
                               :DOC flet."
                              declare-form
                              decl)))))))

(defun chk-flet-declare-form (names declare-form ctx)
  (cond
   ((null declare-form)
    (value-cmp nil))
   (t (case-match declare-form
        (('declare . decls)
         (chk-flet-declarations names decls declare-form ctx))
        (&
         (er-cmp ctx
                 "The optional DECLARE forms for an flet expression must each ~
                  be of the form (DECLARE DCL1 DCL2 ... DCLk), where each ~
                  DCLi is an INLINE or NOTINLINE declaration.  The form ~x0 ~
                  is thus not a legal DECLARE form.  See :DOC flet."
                 declare-form))))))

(defun chk-flet-declare-form-list (names declare-form-list ctx)
  (cond ((endp declare-form-list)
         (value-cmp nil))
        (t (er-progn-cmp
            (chk-flet-declare-form names (car declare-form-list) ctx)
            (chk-flet-declare-form-list names (cdr declare-form-list) ctx)))))

(defun stobj-updater-guess-from-accessor (accessor)

; Warning: Keep the following in sync with defstobj-fnname.

; This function guesses a stobj updater name for a field from the accessor name
; for that field.  We use it to supply a reasonable default when a stobj-let
; binding does not specify an updater, but ultimately we check it just as we
; would check a supplied updater name.

; The following example shows why this is only a guess.

; (defpkg "MY-PKG" '(fldi))
; (defstobj st (my-pkg::fld :type (array t (8))))

; Then the accessor is ACL2::FLDI and the updater is MY-PKG::UPDATE-FLDI.  But
; the call of pack-pos below, with acc bound to ACL2::FLDI, yields
; ACL2::UPDATE-FLDI.

  (packn-pos (list "UPDATE-" accessor)
             accessor))

(defun parse-stobj-let1 (bindings producer-vars bound-vars actuals stobj
                                  updaters corresp-accessor-fns)

; Either return (mv binding nil nil ... nil) for some unsuitable binding in
; bindings, or else return the result of accumulating from bindings into the
; other arguments.  See parse-stobj-let.  Note that stobj is initially nil, but
; is bound by the first recursive call and must be the same at every ensuing
; recursive call.

  (declare (xargs :guard (and (true-listp bindings)
                              (true-listp producer-vars)
                              (true-listp bound-vars)
                              (true-listp actuals)
                              (true-listp updaters))))
  (cond
   ((endp bindings)
    (mv nil
        (reverse bound-vars)
        (reverse actuals)
        stobj
        (reverse updaters)
        (reverse corresp-accessor-fns)))
   (t (let ((binding (car bindings)))
        (case-match binding
          ((s act . rest) ; e.g. (st1 (fld1 st+) update-fld1)
           (cond
            ((not (or (null rest)
                      (and (consp rest)
                           (null (cdr rest))
                           (symbolp (car rest)))))
             (mv binding nil nil nil nil nil))
            ((not (and (true-listp act)
                       (member (length act) '(2 3))
                       (symbolp (car act))
                       (symbolp (car (last act)))))
             (mv binding nil nil nil nil nil))
            (t (let ((arrayp (eql (length act) 3))) ; e.g. (fld3i 4 st+)
                 (cond
                  ((and arrayp
                        (let ((index (cadr act)))

; As discussed in the Essay on Nested Stobjs, the index must be a natural
; number or else a symbol that is not among the producer variables.  We relax
; the former condition to allow a quoted natural.

                          (not (or (and (symbolp index)
                                        (not (member-eq index
                                                        producer-vars)))
                                   (natp index)
                                   (and (consp index)
                                        (consp (cdr index))
                                        (null (cddr index))
                                        (eq (car index) 'quote)
                                        (natp (cadr index)))))))
                   (mv binding nil nil nil nil nil))
                  (t
                   (let ((accessor (car act))
                         (stobj0 (car (last act)))
                         (update-fn (car rest)))
                     (cond
                      ((or (null stobj0)
                           (and stobj
                                (not (eq stobj0 stobj))))
                       (mv binding nil nil nil nil nil))
                      ((member-eq s producer-vars)
                       (parse-stobj-let1
                        (cdr bindings)
                        producer-vars
                        (cons s bound-vars)
                        (cons act actuals)
                        stobj0
                        (cons (cons (or update-fn
                                        (stobj-updater-guess-from-accessor
                                         accessor))
                                    (if arrayp
                                        (list* (cadr act) ; index
                                               s
                                               (cddr act))
                                      (cons s (cdr act))))
                              updaters)
                        (cons accessor corresp-accessor-fns)))
                      (t
                       (parse-stobj-let1
                        (cdr bindings)
                        producer-vars
                        (cons s bound-vars)
                        (cons act actuals)
                        stobj0
                        updaters
                        corresp-accessor-fns))))))))))
          (& (mv binding nil nil nil nil nil)))))))

(defun illegal-stobj-let-msg (msg form)
  (msg "~@0  The form ~x1 is thus illegal.  See :DOC stobj-let."
       msg form))

(defun parse-stobj-let (x)

; This function is used both in the definition of the stobj-let macro and, in
; translate11, to translate stobj-let forms.  This function is not responsible
; for all error checking, as some checks take place in translate11, which must
; ensure that x and its oneification will execute correctly.  Nevertheless, the
; error checking done in this function is useful for giving feedback on misuses
; of stobj-let in contexts such as theorems in which translate11 will not
; insist on correctness for execution, such as single-threadedness.  Of course,
; users who have a specific reason for "misusing" stobj-let in such contexts
; are welcome to avoid stobj-let and write let-expressions instead.

; X is a stobj-let form.  We return (mv erp bound-vars actuals stobj
; producer-vars producer updaters corresponding-accessor-fns consumer), where
; erp is either a msg or nil, and when erp is nil:
; - bound-vars is a list of symbols, without duplicates;
; - actuals is a corresponding list of untranslated field accessors;
; - stobj is the stobj accessed by those field accessors;
; - producer-vars is the true-list of producer variables
; - producer is an untranslated expression that returns values corresponding to
;   producer-vars;
; - updaters is a list of stobj updaters, obtained from producer-vars, actuals,
;   and any updaters specified explicitly in the first argument of the
;   stobj-let;
; - corresponding-accessor-fns is a list of accessor functions that corresponds
;   positionally to updaters; and
; - consumer is an expression that provides the return value(s).

; For example, if x is

;   (stobj-let
;    ((st1 (fld1 st+))
;     (st2 (fld2 st+) update-fld2)
;     (st3 (fld3i 4 st+)))
;    (x st1 y st3)
;    (producer st1 u st2 v st3)
;    (consumer st+ u x y v w))

; then we return:

;   (mv nil                                    ; erp
;       (st1 st2 st3)                          ; bound-vars
;       ((fld1 st+) (fld2 st+) (fld3i 4 st+))  ; untranslated actuals
;       st+                                    ; stobj accessed above
;       (x st1 y st3)                          ; producer-vars
;       (producer st1 u st2 v st3)             ; producer (untranslated)
;       ((update-fld1 st+)                     ; stobj updaters
;        (update-fld3i 4 st3 st+))
;       (fld1 fld3)                            ; accessors for the updaters
;       (consumer st+ u x y v w)               ; consumer (untranslated)
;       )

  (declare (xargs :guard t))
  (case-match x
    (('stobj-let bindings
                 producer-vars
                 producer
                 consumer)
     (cond
      ((not (and bindings

; We could check true-list-listp here, but we prefer to leave such a check to
; parse-stobj-let1 so that the error message can refer to the particular
; ill-formed binding.

                 (true-listp bindings)))
       (mv (illegal-stobj-let-msg
            "The bindings of a STOBJ-LET form must be a non-empty true-list."
            x)
           nil nil nil nil nil nil nil nil))
      ((not (and producer-vars
                 (arglistp producer-vars)))
       (mv (illegal-stobj-let-msg
            "The producer-variables of a STOBJ-LET form must be a non-empty ~
             list of legal variable names."
            x)
           nil nil nil nil nil nil nil nil))
      (t (mv-let
          (bad bound-vars actuals stobj updaters corresp-accessor-fns)
          (parse-stobj-let1 bindings producer-vars nil nil nil nil nil)
          (cond
           (bad (mv (illegal-stobj-let-msg
                     (msg "Illegal binding for stobj-let, ~x0."
                          bad)
                     x)
                    nil nil nil nil nil nil nil nil))
           (t (mv nil bound-vars actuals stobj producer-vars producer
                  updaters corresp-accessor-fns consumer)))))))
    (& (mv (illegal-stobj-let-msg
            "The proper form of a stobj-let is (STOBJ-LET <bindings> ~
             <producer-variables> <producer> <consumer>)."
            x)
           nil nil nil nil nil nil nil nil))))

(defun pairlis-x1 (x1 lst)

; Cons x1 onto the front of each element of lst.

  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (cons x1 (car lst))
                 (pairlis-x1 x1 (cdr lst))))))

(defun pairlis-x2 (lst x2)

; Make an alist pairing each element of lst with x2.

  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        (t (cons (cons (car lst) x2)
                 (pairlis-x2 (cdr lst) x2)))))

(defun no-duplicatesp-checks-for-stobj-let-actuals/alist (alist)
  (cond ((endp alist) nil)
        (t (let ((indices (cdar alist)))
             (cond ((or (null (cdr indices))
                        (and (nat-listp indices)
                             (no-duplicatesp indices)))
                    (no-duplicatesp-checks-for-stobj-let-actuals/alist
                     (cdr alist)))
                   (t (cons `(with-guard-checking
                              t

; This use of with-guard-checking guarantees that the guard will be checked by
; running chk-no-duplicatesp inside *1* code for stobj-let.  (See a comment
; near the end of stobj-let-fn for how handling of invariant-risk guarantees
; that such *1* code is run under program-mode wrappers.)

                              (chk-no-duplicatesp

; The use of reverse is just aesthetic, to preserve the original order.

                               (list ,@(reverse indices))))
                            (no-duplicatesp-checks-for-stobj-let-actuals/alist
                             (cdr alist)))))))))

(defun no-duplicatesp-checks-for-stobj-let-actuals (exprs alist)

; Alist associates array field accessor names with lists of index terms.

  (cond ((endp exprs)
         (no-duplicatesp-checks-for-stobj-let-actuals/alist alist))
        (t (let ((expr (car exprs)))
             (no-duplicatesp-checks-for-stobj-let-actuals
              (cdr exprs)
              (cond
               ((eql (length expr) 3) ; array case, (fldi index st)
                (let* ((key (car expr))
                       (index (cadr expr))
                       (index (if (consp index)
                                  (assert$ (and (eq (car index) 'quote)
                                                (natp (cadr index)))
                                           (cadr index))
                                index))
                       (entry (assoc-eq key alist)))
                  (put-assoc-eq key
                                (cons index (cdr entry))
                                alist)))
               (t alist)))))))

(defun stobj-let-fn (x)

; Warning: Keep this in sync with stobj-let-fn-raw, with the handling of
; stobj-let in translate11, and with the handling of stobj-let in oneify.

; See the Essay on Nested Stobjs.

  (mv-let
   (msg bound-vars actuals stobj producer-vars producer updaters
        corresp-accessor-fns consumer)
   (parse-stobj-let x)
   (declare (ignore corresp-accessor-fns))
   (cond (msg (er hard 'stobj-let "~@0" msg))
         (t (let* ((guarded-producer
                    `(check-vars-not-free (,stobj) ,producer))
                   (guarded-consumer
                    `(check-vars-not-free ,bound-vars ,consumer))
                   (updated-guarded-consumer
                    `(let* ,(pairlis-x1 stobj (pairlis$ updaters nil))
                       ,guarded-consumer))
                   (form
                    `(let ,(pairlis$ bound-vars (pairlis$ actuals nil))
                       (declare (ignorable ,@bound-vars))
                       ,(cond
                         ((cdr producer-vars)
                          `(mv-let ,producer-vars
                                   ,guarded-producer
                                   ,updated-guarded-consumer))
                         (t `(let ((,(car producer-vars) ,guarded-producer))
                               ,updated-guarded-consumer)))))
                   (no-dups-exprs
                    (no-duplicatesp-checks-for-stobj-let-actuals actuals nil)))
              `(progn$ ,@no-dups-exprs

; Warning: Think carefully before modifying how the no-dups-exprs test (just
; above) is worked into this logical code.  A concern is whether a program-mode
; wrapper will be able to circumvent this check.  Fortunately, the check only
; needs to be done if there are updater calls in form, in which case there is
; invariant-risk that will cause execution of this code as *1* code.  A concern
; is that if the no-dups-exprs check is buried in a function call, perhaps that
; call would somehow avoid that check by being executed in raw Lisp.

                       ,form))))))

(defun the-live-var-bindings (stobj-names)
  (cond ((endp stobj-names) nil)
        (t (cons (let ((stobj (car stobj-names)))
                   `(,(the-live-var stobj) ,stobj))
                 (the-live-var-bindings (cdr stobj-names))))))

(defun the-maybe-live-var-bindings (stobj-names)
  (cond ((endp stobj-names) nil)
        (t (cons (let* ((stobj (car stobj-names))
                        (live-var (the-live-var stobj)))
                   `(,live-var
                     (if (live-stobjp ,stobj)
                         ,stobj
                       ,live-var)))
                 (the-maybe-live-var-bindings (cdr stobj-names))))))

#-acl2-loop-only
(defun non-memoizable-stobj-raw (name)
  (assert name)
  (let* ((d (get (the-live-var name)
                 'redundant-raw-lisp-discriminator))
         (ans (cdr (cddddr d))))
    ans))

#-acl2-loop-only
(defun stobj-let-fn-raw (x)

; Warning: Keep this in sync with stobj-let-fn and with the
; handling of stobj-let in translate11.

; This function could be admitted into the logic were it not for the calls of
; congruent-stobj-rep-raw and non-memoizable-stobj-raw below.

; See the Essay on Nested Stobjs.

  (mv-let
   (msg bound-vars actuals stobj producer-vars producer updaters
        corresp-accessor-fns consumer)
   (parse-stobj-let x)
   (declare (ignore updaters corresp-accessor-fns
                    #-hons stobj))
   (cond (msg (er hard 'stobj-let "~@0" msg))
         (t

; Should we allow trans-eval under a stobj-let?  We decided not to, for two
; reasons: first, potential user confusion over the meaning of a stobj
; reference (which in the trans-eval case is to the value in the
; *user-stobj-alist*, not to the value bound by a superior stobj-let); and
; second, difficulty in getting the implementation right!  The following
; example illustrates how trans-eval would operate, were we to allow it in such
; a circumstance.  Note that the trans-eval call below updates the global
; stobj, sub1, not the locally bound sub1 that is a field of top1.

;   (defstobj sub1 sub1-fld1)
;   (defstobj top1 (top1-fld :type sub1))
;
;   (defun f (x top1 state)
;     (declare (xargs :stobjs (top1 state) :mode :program))
;     (stobj-let
;      ((sub1 (top1-fld top1)))
;      (sub1 state)
;      (mv-let (erp val state)
;
;   ; NOTE: The reference to sub1 inside the following trans-eval call is
;   ; actually a reference to the global sub1 from the *user-stobj-alist*, not
;   ; to the sub1 bound by stobj-let above.
;
;              (trans-eval `(update-sub1-fld1 ',x sub1) 'my-top state t)
;              (declare (ignore erp val))
;              (mv sub1 state))
;      top1))
;
;   (f 7 top1 state)
;   (assert-event (equal (sub1-fld1 sub1) 7))
;   (f 8 top1 state)
;   (assert-event (equal (sub1-fld1 sub1) 8))
;
;   (defun f2 (top1)
;     (declare (xargs :stobjs top1 :mode :program))
;     (stobj-let
;      ((sub1 (top1-fld top1)))
;      (val)
;      (sub1-fld1 sub1)
;      val))
;
;   (assert-event (equal (f2 top1) nil))

; Thus, in the code below, we bind the live var for each bound stobj so that we
; will get the error "It is illegal to run ACL2 evaluators...." when attempting
; to call trans-eval (as trans-eval calls ev-for-trans-eval, which calls
; user-stobj-alist-safe, which calls chk-user-stobj-alist, which checks the
; global *user-stobj-alist* against the live stobj values).

; Another reason to bind the-live-stobj is in case we need to print the stobj
; during guard violations or tracing, in which case we can distinguish it from
; the global stobj with the same name.  See for example stobj-print-symbol,
; which is used during tracing.

          `(let* (,@(pairlis$ bound-vars (pairlis$ actuals nil))
                  ,@(the-live-var-bindings bound-vars))
             (declare (ignorable ,@bound-vars))
             ,(let* ((modified-bound-vars (intersection-eq producer-vars
                                                           bound-vars))
                     (flush-form
                      #-hons nil
                      #+hons
                      (and modified-bound-vars
                           (not (non-memoizable-stobj-raw stobj))
                           `(memoize-flush ,(congruent-stobj-rep-raw stobj)))))
                (cond
                 ((cdr producer-vars)
                  `(mv-let ,producer-vars
                           ,producer
                           ,@(and modified-bound-vars
                                  `((declare (ignore ,@modified-bound-vars))))
                           ,(if flush-form
                                `(progn ,flush-form ,consumer)
                              consumer)))
                 (t `(let ((,(car producer-vars) ,producer))
                       ,@(and modified-bound-vars
                              `((declare (ignore ,@modified-bound-vars))))

; Here is a proof of nil in ACL2(h)  6.4 that exploits an unfortunate
; "interaction of stobj-let and memoize", discussed in :doc note-6-5.  This
; example let us to add the call of memoize-flush in flush-form, below.  A
; comment in chk-stobj-field-descriptor explains how this flushing is important
; for allowing memoization of functions that take a stobj argument even when
; that stobj has a child stobj that is :non-memoizable.

;   (in-package "ACL2")
;
;   (defstobj kid1 fld1)
;
;   (defstobj kid2 fld2)
;
;   (defstobj mom
;     (kid1-field :type kid1)
;     (kid2-field :type kid2))
;
;   (defun mom.update-fld1 (val mom)
;     (declare (xargs :stobjs mom))
;     (stobj-let
;      ((kid1 (kid1-field mom)))
;      (kid1)
;      (update-fld1 val kid1)
;      mom))
;
;   (defun mom.fld1 (mom)
;     (declare (xargs :stobjs mom))
;     (stobj-let
;      ((kid1 (kid1-field mom)))
;      (val)
;      (fld1 kid1)
;      val))
;
;   (defun test ()
;     (with-local-stobj
;      mom
;      (mv-let (val mom)
;              (let* ((mom (mom.update-fld1 3 mom))
;                     (val1 (mom.fld1 mom))
;                     (mom (mom.update-fld1 4 mom))
;                     (val2 (mom.fld1 mom)))
;                (mv (equal val1 val2) mom))
;              val)))
;
;   (defthm true-prop
;     (not (test))
;     :rule-classes nil)
;
;   (memoize 'mom.fld1)
;
;   (defthm false-prop
;     (test)
;     :rule-classes nil)
;
;   (defthm contradiction
;     nil
;     :hints (("Goal" :in-theory nil
;              :use (true-prop false-prop)))
;     :rule-classes nil)

                       ,@(and flush-form (list flush-form))
                       ,consumer)))))))))

(defun stobj-field-accessor-p (fn stobj wrld)
  (and

; We believe that the first check is subsumed by the others, but we leave it
; here for the sake of robustness.

   (eq (getpropc fn 'stobj-function nil wrld)
       stobj)

; The 'stobj property of stobj is (*the-live-var* recognizer creator ...).

   (member-eq fn (cdddr (getpropc stobj 'stobj nil wrld)))

; At this point, fn could still be a constant.

   (function-symbolp fn wrld)

; Now distinguish accessors from updaters.

   (not (eq (car (stobjs-out fn wrld))
            stobj))))

(defun chk-stobj-let/bindings (stobj acc-stobj first-acc bound-vars actuals
                                     wrld)

; The bound-vars and actuals have been returned by parse-stobj-let, so we know
; that some basic syntactic requirements have been met and that the two lists
; have the same length.  See also chk-stobj-let.

; Stobj is the variable being accessed/updated.  Acc-stobj is the stobj
; associated with the first accessor; we have already checked in chk-stobj-let
; that this is congruent to stobj.  First-acc is the first accessor, which is
; just used in the error message when another accessor's stobj doesn't match.

  (cond ((endp bound-vars) nil)
        (t (let* ((var (car bound-vars))
                  (actual (car actuals))
                  (accessor (car actual))
                  (st (car (last actual))))
             (assert$
              (eq st stobj) ; guaranteed by parse-stobj-let
              (cond ((not (stobj-field-accessor-p accessor acc-stobj wrld))
                     (msg "The name ~x0 is not the name of a field accessor ~
                           for the stobj ~x1.~@2"
                          accessor acc-stobj
                          (if (eq acc-stobj stobj)
                              ""
                            (msg "  (The first accessor used in a stobj-let, ~
                                  in this case ~x0, determines the stobj with ~
                                  which all other accessors must be ~
                                  associated, namely ~x1.)"
                                 first-acc acc-stobj))))
                    ((not (stobjp var t wrld))
                     (msg "The stobj-let bound variable ~x0 is not the name ~
                           of a known single-threaded object in the current ~
                           ACL2 world."
                          var))
                    ((not (eq (congruent-stobj-rep var wrld)
                              (congruent-stobj-rep
                               (car (stobjs-out accessor wrld))
                               wrld)))
                     (msg "The stobj-let bound variable ~x0 is not the same ~
                           as, or even congruent to, the output ~x1 of accessor ~
                           ~x2 (of stobj ~x3)."
                          var
                          (car (stobjs-out (caar actuals) wrld))
                          (caar actuals)
                          stobj))
                    ((member-equal actual (cdr actuals))

; This case fixes a soundness bug for duplicated actuals (see :DOC note-8-0).
; It effectively checks no-duplicatesp-equal of the actuals, but doing it here
; one-by-one has the advantage that we can easily say which actual is
; duplicated.  Alternatively, we could check only that scalar accessor
; functions are not used more than once.  This is a bit stronger since it also
; disallows duplicate array accesses (though they would be disallowed by guards
; anyway).  If we ever relax the strict syntactic restrictions on actuals --
; e.g., allow accessors from multiple congruent stobjs -- this check will need
; to become smarter.

                     (msg "The bindings of a stobj-let must contain no ~
                           duplicated actuals, but in the following form, the ~
                           actual ~x0 is bound more than once."
                          actual))
                    (t (chk-stobj-let/bindings stobj acc-stobj first-acc
                                               (cdr bound-vars)
                                               (cdr actuals)
                                               wrld))))))))

(defun chk-stobj-let/updaters1 (updaters accessors lst)

; Lst is the cdddr of the 'stobj property of a stobj in an implicit world,
; accessors is a list of field accessors for that stobj, and updaters is a list
; of the same length as accessors.  We check for each i < (length accessors),
; the ith updater is indeed the stobj field updater corresponding to the ith
; accessor.  Recall that the 'stobj property is a list of the form
; (*the-live-var* recognizer creator ...), and that each field updater
; immediately follows the corresponding field accessor in that list.

  (cond ((endp updaters) nil)
        (t (let* ((updater-expr (car updaters))
                  (updater (car updater-expr))
                  (accessor (car accessors))
                  (accessor-tail (member-eq (car accessors) lst))
                  (actual-updater (cadr accessor-tail)))
             (assert$

; This assertion should be true because of the check done by a call of
; stobj-field-accessor-p in chk-stobj-let/bindings.

              accessor-tail
              (cond
               ((eq updater actual-updater)
                (chk-stobj-let/updaters1 (cdr updaters) (cdr accessors) lst))
               (t (msg "The stobj-let bindings have specified that the stobj ~
                        field updater corresponding to accessor ~x0 is ~x1, ~
                        but the actual corresponding updater is ~x2."
                       accessor updater actual-updater))))))))

(defun chk-stobj-let/updaters (updaters corresp-accessor-fns stobj wrld)
  (chk-stobj-let/updaters1
   updaters
   corresp-accessor-fns
   (cdddr ; optimization: pop live-var, recognizer, and creator
    (getpropc stobj 'stobj nil wrld))))

(defun chk-stobj-let (bound-vars actuals stobj updaters corresp-accessor-fns
                                 known-stobjs wrld)

; The inputs (other than wrld) have been returned by parse-stobj-let, so we
; know that some basic syntactic requirements have been met.  Others are to be
; checked directly by translate11 after the present check passes.  Here, we
; do the checks necessary after parse-stobj-let but before translate11.

  (cond
   ((not (stobjp stobj known-stobjs wrld))
    (msg
     "The name ~x0 is being used as a single-threaded object.  But in the ~
      current context, ~x0 is not a declared stobj name."
     stobj))
   ((getpropc stobj 'absstobj-info nil wrld)
    (msg
     "The name ~x0 is the name of an abstract stobj."
     stobj))
   (t (let* ((first-actual (car actuals))
             (first-accessor (car first-actual))
             (acc-stobj (getpropc first-accessor 'stobj-function nil wrld)))
        (cond
         ((not (eq (congruent-stobj-rep acc-stobj wrld)
                   (congruent-stobj-rep stobj wrld)))
          (msg "The name ~x0 is not the name of a field accessor for the ~
                stobj ~x1, or even one congruent to it."
               first-accessor stobj))
         ((chk-stobj-let/bindings
           stobj acc-stobj first-accessor bound-vars actuals wrld))
         ((chk-stobj-let/updaters
           updaters corresp-accessor-fns acc-stobj wrld))
         (t nil))))))

(defun all-nils-or-x (x lst)
  (declare (xargs :guard (and (symbolp x)
                              (true-listp lst))))
  (cond ((endp lst) t)
        ((or (eq (car lst) x)
             (null (car lst)))
         (all-nils-or-x x (cdr lst)))
        (t nil)))

(defun stobj-field-fn-of-stobj-type-p (fn wrld)

; Return true if for some concrete stobj st, fn is the accessor or updater for
; a field fld of st of stobj type.  For fn the accessor or updater for fld,
; this is equivalent to taking or returning that stobj type, respectively,
; which is equivalent to taking or returning some stobj other than st.
; Abstract stobjs are not a concern here; they don't have "fields".

  (let ((st (getpropc fn 'stobj-function nil wrld)))
    (and st
         (not (getpropc st 'absstobj-info nil wrld))
         (or (not (all-nils-or-x st (stobjs-in fn wrld)))
             (not (all-nils-or-x st (stobjs-out fn wrld)))))))

(defun stobj-recognizer-p (fn wrld)

; Fn is a function symbol of wrld.  We return true when fn is a stobj
; recognizer in wrld.

  (let ((stobj (getpropc fn 'stobj-function nil wrld)))
    (and stobj
         (eq fn (get-stobj-recognizer stobj wrld)))))

(defmacro trans-or (form1 condition form2 extra-msg)

; Like trans-er-let*, this function deals in trans-er's 3-tuples (mv erp val
; bindings).  The 3-tuple produced by form1 is returned except in one case:
; that 3-tuple has non-nil first value (erp), condition is true, and form2
; produces a 3-tuple of the form (mv nil val bindings), in which case that
; 3-tuple is returned.

  `(let ((trans-or-extra-msg ,extra-msg))
     (mv-let (trans-or-erp trans-or-val trans-or-bindings)
             ,form1
             (cond
              ((and trans-or-erp
                    (check-vars-not-free
                     (trans-or-er trans-or-val trans-or-bindings
                                  trans-or-extra-msg)
                     ,condition))
               (mv-let (erp val bindings)
                       (check-vars-not-free
                        (trans-or-er trans-or-val trans-or-bindings
                                     trans-or-extra-msg)
                        ,form2)
                       (cond
                        (erp (mv trans-or-erp
                                 (msg "~@0~@1" trans-or-val trans-or-extra-msg)
                                 trans-or-bindings))
                        (t (mv nil val bindings)))))
              (t (mv trans-or-erp trans-or-val trans-or-bindings))))))

(defun inside-defabsstobj (wrld)

; We use this function to allow certain violations of normal checks in
; translate11 while executing events on behalf of defabsstobj.  In particular,
; we avoid the normal translation checks in the :exec components of mbe calls
; that are laid down for defabsstobj; see defabsstobj-axiomatic-defs.

  (eq (caar (global-val 'embedded-event-lst wrld))

; It seems reasonable to expect 'defabsstobj below instead of 'defstobj, but
; 'defstobj is what we actually get.

      'defstobj))

(defun missing-known-stobjs (stobjs-out stobjs-out2 known-stobjs acc)

; See translate11-call for a discussion of the arguments of this function,
; which is intended to return a list of stobj names that are unexpectedly
; returned because they are not known to be stobjs in the current context.

; It is always legal to return nil.  But if the result is non-nil, then the
; members of stobjs-out and stobjs-out2 are positionally equal (where the
; shorter one is extended by nils if necessary) except that in some positions,
; stobjs-out may contain nil while stobjs-out2 contains a value missing from
; known-stobjs.  In that case the value returned can be the result of pushing
; all such values onto acc.

  (cond ((and (endp stobjs-out) (endp stobjs-out2))
         (reverse acc))
        ((eq (car stobjs-out) (car stobjs-out2))
         (missing-known-stobjs (cdr stobjs-out) (cdr stobjs-out2) known-stobjs
                               acc))
        ((and (null (car stobjs-out))
              (not (or (eq known-stobjs t)
                       (member-eq (car stobjs-out2) known-stobjs))))
         (missing-known-stobjs (cdr stobjs-out) (cdr stobjs-out2) known-stobjs
                               (cons (car stobjs-out2) acc)))
        (t nil)))

(defun deref-macro-name (macro-name macro-aliases)
  (declare (xargs :guard (if (symbolp macro-name)
                             (alistp macro-aliases)
                           (symbol-alistp macro-aliases))))
  (let ((entry (assoc-eq macro-name macro-aliases)))
    (if entry
        (cdr entry)
      macro-name)))

(defun corresponding-inline-fn (fn wrld)
  (let ((macro-body (getpropc fn 'macro-body t wrld)))
    (and (not (eq macro-body t))
         (let* ((fn$inline (add-suffix fn *inline-suffix*))
                (formals (getpropc fn$inline 'formals t wrld)))
           (and (not (eq formals t))
                (equal (macro-args fn wrld) formals)
                (equal macro-body
                       (fcons-term*
                        'cons
                        (kwote fn$inline)
                        (if formals
                            (xxxjoin 'cons
                                     (append formals
                                             (list
                                              *nil*)))
                          (list *nil*))))
                fn$inline)))))

(defmacro untouchable-fn-p (sym wrld temp-touchable-fns)

; Warning: Keep this in sync with ev-fncall-w-guard (see the comment about
; untouchable-fn-p in that definition).

  `(let ((sym ,sym)
         (untouchable-fns ; avoid global-val; wrld can be nil during boot-strap
          (getpropc 'untouchable-fns 'global-value nil ,wrld)))
     (and (member-eq sym untouchable-fns)
          (let ((temp-touchable-fns
                 (check-vars-not-free (sym untouchable-fns)
                                      ,temp-touchable-fns)))
            (and (not (eq temp-touchable-fns t))
                 (not (member-eq sym temp-touchable-fns)))))))

(defun macroexpand1*-cmp (x ctx wrld state-vars)

; We expand x repeatedly as long as it is a macro call, though we may stop
; whenever we like.  We rely on a version of translate with to finish the job;
; indeed, it should be the case that when translate11 is called on x with the
; following arguments, it returns the same result regardless of whether
; macroexpand1*-cmp is first called to do some expansion.

; stobjs-out   - :stobjs-out
; bindings     - ((:stobjs-out . :stobjs-out))
; known-stobjs - t
; flet-alist   - nil

; Warning: Keep this in sync with translate11 -- especially the first cond
; branch's test below.

  (cond ((or (or (atom x) (eq (car x) 'quote))
             (not (true-listp (cdr x)))
             (not (symbolp (car x)))
             (member-eq (car x) '(mv
                                  mv-let
                                  pargs
                                  translate-and-test
                                  with-local-stobj
                                  stobj-let))
             (assoc-eq (car x) *ttag-fns-and-macros*))
         (value-cmp x))
        ((and (getpropc (car x) 'macro-body nil wrld)
              (not (and (member-eq (car x) '(pand por pargs plet))
                        (eq (access state-vars state-vars :parallel-execution-enabled)
                            t)))
              (not (untouchable-fn-p (car x)
                                     wrld
                                     (access state-vars state-vars
                                             :temp-touchable-fns))))
         (mv-let
          (erp expansion)
          (macroexpand1-cmp x ctx wrld state-vars)
          (cond
           (erp (mv erp expansion))
           (t (macroexpand1*-cmp expansion ctx wrld state-vars)))))
        (t (value-cmp x))))

(defun find-stobj-out-and-call (lst known-stobjs ctx wrld state-vars)

; Lst is a list of possibly UNTRANSLATED terms!

  (cond
   ((endp lst) nil)
   (t
    (or (mv-let (erp val)
          (macroexpand1*-cmp (car lst) ctx wrld state-vars)
          (and (not erp)
               (consp val)
               (symbolp (car val))
               (not (member-eq (car val) *stobjs-out-invalid*))
               (let ((stobjs-out (stobjs-out (car val) wrld)))
                 (and (consp stobjs-out)
                      (null (cdr stobjs-out))
                      (stobjp (car stobjs-out) known-stobjs wrld)
                      (cons (car stobjs-out) (car lst))))))
        (find-stobj-out-and-call (cdr lst) known-stobjs ctx wrld
                                 state-vars)))))

(defconst *initial-return-last-table*
  '((time$1-raw . time$1)
    (with-prover-time-limit1-raw . with-prover-time-limit1)
    (with-fast-alist-raw . with-fast-alist)
    (with-stolen-alist-raw . with-stolen-alist)
    (fast-alist-free-on-exit-raw . fast-alist-free-on-exit)

; Keep the following comment in sync with return-last-table and with
; chk-return-last-entry.

; The following could be omitted since return-last gives them each special
; handling: prog2$ and mbe1 are used during the boot-strap before tables are
; supported, and ec-call1 and (in ev-rec-return-last) with-guard-checking gets
; special handling.  It is harmless though to include them explicitly, in
; particular at the end so that they do not add time in the expected case of
; finding one of the other entries in the table.  If we decide to avoid special
; handling (which we have a right to do, by the way, since users who modify
; return-last-table are supposed to know what they are doing, as a trust tag is
; needed), then we should probably move these entries to the top where they'll
; be seen more quickly.

    (progn . prog2$)
    (mbe1-raw . mbe1)
    (ec-call1-raw . ec-call1)
    (with-guard-checking1-raw . with-guard-checking1)))

(defun defined-symbols (sym-name pkg-name known-package-alist wrld acc)
  (cond
   ((endp known-package-alist) acc)
   (t (let* ((entry (car known-package-alist))
             (pkg-entry-name (package-entry-name entry)))
        (cond
         ((or (equal pkg-name pkg-entry-name)
              (package-entry-hidden-p entry))
          (defined-symbols sym-name pkg-name (cdr known-package-alist) wrld
            acc))
         (t (let ((sym (intern$ sym-name pkg-entry-name)))
              (defined-symbols sym-name pkg-name
                (cdr known-package-alist)
                wrld
                (if (and (not (member-eq sym acc))
                         (or (function-symbolp sym wrld)
                             (getpropc sym 'macro-body nil wrld)))
                    (cons sym acc)
                  acc)))))))))

(defun macros-and-functions-in-other-packages (sym wrld)
  (let ((kpa (global-val 'known-package-alist wrld)))
    (defined-symbols (symbol-name sym) (symbol-package-name sym) kpa wrld
      nil)))

(defun match-stobjs (lst1 lst2 acc)

; Lst1 and lst2 are proposed stobjs-out values.  So they are lists of symbols,
; presumably each with nil as the only possible duplicate.

  (cond ((endp lst1) (mv (null lst2) acc))
        ((endp lst2) (mv nil nil))
        ((not (eq (null (car lst1))
                  (null (car lst2))))
         (mv nil nil))
        ((null (car lst1))
         (match-stobjs (cdr lst1) (cdr lst2) acc))
        (t (let ((pair (assoc-eq (car lst1) acc)))
             (cond ((null pair)
                    (match-stobjs (cdr lst1)
                                  (cdr lst2)
                                  (if (eq (car lst1) (car lst2))
                                      acc
                                    (acons (car lst1) (car lst2) acc))))
                   (t (mv (er hard! 'match-stobjs
                              "Implementation error: expected no duplicates ~
                               in stobjs-out list!")
                          nil)))))))

(defun make-lambda-term (formals actuals body)

; Warning: If you consider making a call of this function, ask yourself whether
; make-lambda-application would be more appropriate; the answer depends on why
; you are calling this function.  For example, make-lambda-application function
; requires that every free variable in body is a member of formals, but the
; present function does not.  Make-lambda-application will drop an unused
; formal, but the present function does not (though its caller could choose to
; "hide" such a formal; see translate11-let).

; Formals is a true list of distinct variables, actuals is a true list of terms
; of the same length as formals, and body is a term.  We want to create
; something like ((lambda formals body) . actuals).  However, body may have
; free variables that do not belong to formals, and lambdas must be closed in
; ACL2.  We add the necessary extra variables to the end of formals and
; actuals.  See translate11-let for how this function may be called to "hide"
; unused formals.

  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (pseudo-termp body))))
  (let* ((body-vars (all-vars body))
         (extra-body-vars (set-difference-eq body-vars formals)))
    (fcons-term (make-lambda (append formals extra-body-vars)
                             body)
                (append actuals extra-body-vars))))

(mutual-recursion

(defun translate11-flet-alist (form fives stobjs-out bindings known-stobjs
                                    flet-alist ctx wrld state-vars)
  (cond ((endp fives)
         (trans-value flet-alist))
        (t
         (trans-er-let*
          ((flet-entry
            (translate11-flet-alist1 form (car fives) stobjs-out bindings
                                     known-stobjs flet-alist ctx wrld state-vars))
           (flet-entries
            (translate11-flet-alist  form (cdr fives) stobjs-out bindings
                                     known-stobjs flet-alist ctx wrld state-vars)))
          (trans-value (cons flet-entry flet-entries))))))

(defun translate11-flet-alist1 (form five stobjs-out bindings known-stobjs
                                     flet-alist ctx wrld state-vars)
  (let* ((name (car five))
         (bound-vars (cadr five))
         (edcls (fourth five))
         (body (fifth five))
         (new-stobjs-out
          (if (eq stobjs-out t)
              t
            (genvar name (symbol-name name) nil (strip-cars bindings)))))
    (cond
     ((member-eq name '(flet with-local-stobj throw-raw-ev-fncall
                         untrace$-fn-general))

; This check may not be necessary, because of our other checks.  But the
; symbols above are not covered by our check for the 'predefined property.

      (trans-er+ form ctx
                 "An FLET form has attempted to bind ~x0.  However, this ~
                  symbol must not be FLET-bound."
                 name))
     ((getpropc name 'predefined nil wrld)
      (trans-er+ form ctx
                 "An FLET form has attempted to bind ~x0, which is predefined ~
                  in ACL2 hence may not be FLET-bound."
                 name))
     #-acl2-loop-only
     ((or (special-form-or-op-p name)
          (and (or (macro-function name)
                   (fboundp name))
               (not (getpropc name 'macro-body nil wrld))
               (eq (getpropc name 'formals t wrld) t)))
      (prog2$ (er hard ctx
                  "It is illegal to FLET-bind ~x0, because it is defined as a ~
                   ~s1 in raw Lisp~#2~[~/ but not in the ACL2 loop~]."
                  name
                  (cond ((special-form-or-op-p name) "special operator")
                        ((macro-function name) "macro")
                        (t "function"))
                  (if (special-form-or-op-p name) 0 1))
              (mv t
                  nil ; empty "message": see the Essay on Context-message Pairs
                  nil)))
     (t
      (trans-er-let*
       ((tdcls (translate11-lst (translate-dcl-lst edcls wrld)
                                nil           ;;; '(nil ... nil)
                                bindings
                                known-stobjs
                                "in a DECLARE form in an FLET binding"
                                flet-alist form ctx wrld state-vars))
        (tbody (translate11 body new-stobjs-out
                            (if (eq stobjs-out t)
                                bindings
                              (translate-bind new-stobjs-out new-stobjs-out
                                              bindings))
                            known-stobjs
                            flet-alist form ctx wrld state-vars)))
       (let ((used-vars (union-eq (all-vars tbody)
                                  (all-vars1-lst tdcls nil)))
             (ignore-vars (ignore-vars edcls))
             (ignorable-vars (ignorable-vars edcls))
             (stobjs-out (translate-deref new-stobjs-out bindings)))
         (cond

; We skip the following case, where stobjs-out is not yet bound to a consp and
; some formal is a stobj, in favor of the next, which removes the stobjs-bound
; criterion.  But we leave this case here as a comment in case we ultimately
; find a way to eliminate the more sweeping case after it.  Note:
; unknown-binding-msg has been replaced by unknown-binding-msg-er, so a bit of
; rework will be needed if this case is to be reinstalled.  Also note that we
; will need to bind stobjs-bound to

;         ((and (not (eq stobjs-out t))
;               (collect-non-x ; stobjs-bound
;                nil
;                (compute-stobj-flags bound-vars
;                                     known-stobjs
;                                     wrld))
;               (not (consp stobjs-out)))
;          (trans-er ctx
;                    "~@0"
;                    (unknown-binding-msg
;                     (collect-non-x ; stobjs-bound
;                      nil
;                      (compute-stobj-flags bound-vars
;                                           known-stobjs
;                                           wrld))
;                     (msg "the formals of an FLET binding for function ~x0"
;                          name)
;                     "the body of this FLET binding"
;                     "that body")))

          ((and (not (eq stobjs-out t))
                (not (consp stobjs-out)))

; Warning: Before changing this case, see the comment above about the
; commented-out preceding case.

; We might be able to fix this case by using the :UNKNOWN-BINDINGS trick
; employed by unknown-binding-msg-er; see that function and search for
; :UNKNOWN-BINDINGS, to see how that works.

           (trans-er+ form ctx
                      "We are unable to determine the output signature for an ~
                       FLET-binding of ~x0.  You may be able to remedy the ~
                       situation by rearranging the order of the branches of ~
                       an IF and/or rearranging the order of the presentation ~
                       of a clique of mutually recursive functions.  If you ~
                       believe you have found an example on which you believe ~
                       ACL2 should be able to complete this translation, ~
                       please send such an example to the ACL2 implementors."
                     name))
          ((intersectp-eq used-vars ignore-vars)
           (trans-er+ form ctx
                      "Contrary to the declaration that ~#0~[it is~/they ~
                       are~] IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 are~] ~
                       used in the body of an FLET-binding of ~x1, whose ~
                       formal parameter list includes ~&2."
                     (intersection-eq used-vars ignore-vars)
                     name
                     bound-vars))
          (t
           (let* ((diff (set-difference-eq
                         bound-vars
                         (union-eq used-vars
                                   (union-eq ignorable-vars
                                             ignore-vars))))
                  (ignore-ok
                   (if (null diff)
                       t
                     (cdr (assoc-eq
                           :ignore-ok
                           (table-alist 'acl2-defaults-table wrld))))))
             (cond
              ((null ignore-ok)
               (trans-er+ form ctx
                          "The variable~#0~[ ~&0 is~/s ~&0 are~] not used in ~
                           the body of the LET expression that binds ~&1.  ~
                           But ~&0 ~#0~[is~/are~] not declared IGNOREd or ~
                           IGNORABLE.  See :DOC set-ignore-ok."
                         diff
                         bound-vars))
              (t
               (prog2$
                (cond
                 ((eq ignore-ok :warn)
                  (warning$-cw1 ctx "Ignored-variables"
                                "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                 used in the body of an FLET-binding of ~x1 ~
                                 that binds ~&2.  But ~&0 ~#0~[is~/are~] not ~
                                 declared IGNOREd or IGNORABLE.  See :DOC ~
                                 set-ignore-ok."
                                diff
                                name
                                bound-vars))
                 (t nil))
                (let* ((tbody
                        (cond
                         (tdcls
                          (let ((guardian (dcl-guardian tdcls)))
                            (cond ((equal guardian *t*)

; See the comment about THE in dcl-guardian.

                                   tbody)
                                  (t
                                   (prog2$-call guardian tbody)))))
                         (t tbody)))
                       (body-vars (all-vars tbody))
                       (extra-body-vars (set-difference-eq
                                         body-vars
                                         bound-vars)))
                  (cond
                   (extra-body-vars

; Warning: Do not eliminate this error without thinking about the possible role
; of variables that are declared special in Common Lisp.  There might not be
; such an issue, but we haven't thought about it.

                    (trans-er+ form ctx
                               "The variable~#0~[ ~&0 is~/s ~&0 are~] used in ~
                                the body of an FLET-binding of ~x1 that only ~
                                binds ~&2.  In ACL2, every variable occurring ~
                                in the body of an FLET-binding, (fn vars ~
                                body), must be in vars, i.e., a formal ~
                                parameter of that binding.  The ACL2 ~
                                implementors may be able to remove this ~
                                restriction, with some effort, if you ask."
                              extra-body-vars
                              name
                              bound-vars))
                   (t
                    (trans-value
                     (list* name
                            (make-lambda bound-vars tbody)
                            stobjs-out)
                     (if (eq new-stobjs-out t)
                         bindings
                       (delete-assoc-eq-all new-stobjs-out
                                            bindings))))))))))))))))))

(defun translate11-flet (x stobjs-out bindings known-stobjs flet-alist
                           ctx wrld state-vars)
  (cond
   ((< (length x) 3)
    (trans-er ctx
              "An FLET form must have the form (flet bindings body) or (flet ~
               bindings declare-form1 ... declare-formk body), but ~x0 does ~
               not have this form.  See :DOC flet."
              x))
   (t
    (let ((defs (cadr x))
          (declare-form-list (butlast (cddr x) 1))
          (body (car (last x))))
      (mv-let
       (erp fives)
       (chk-defuns-tuples-cmp defs t ctx wrld)
       (let ((names (and (not erp)
                         (strip-cars fives))))
         (mv-let
          (erp msg)
          (if erp ; erp is a ctx and fives is a msg
              (mv erp fives)

; Note that we do not need to call chk-xargs-keywords, since
; *acceptable-dcls-alist* guarantees that xargs is illegal.

            (er-progn-cmp
             (chk-no-duplicate-defuns-cmp names ctx)
             (chk-flet-declare-form-list names declare-form-list ctx)))
          (cond
           (erp

; Erp is a context that we are ignoring in the message below.  Probably it is
; ctx anyhow, but if not, there isn't an obvious problem with ignoring it.

            (trans-er ctx
                      "~@0~|~%The above error indicates a problem with the ~
                       form ~p1."
                      msg x))
           ((first-assoc-eq names (table-alist 'return-last-table wrld))

; What horrors may lie ahead, for example, with
; (flet ((ec-call1-raw ....)) (ec-call ...))?  The problem is that ec-call
; expands to a call of ec-call1-raw, but only through several steps that the
; user might not notice, and only in raw Lisp.  Of course it's doubtful that
; someone would flet-bound ec-call1-raw; but it isn't hard to imagine a binding
; whose error isn't so obvious.  Of course, someday a serious system hacker
; might want to flet ec-call1-raw; in that case, with a trust tag that person
; can also edit the code here!

            (trans-er ctx
                      "It is illegal for FLET to bind a symbol that is given ~
                       special handling by ~x0.  The FLET-binding~#1~[ is~/s ~
                       are~] thus illegal for ~&1.  See :DOC ~
                       return-last-table."
                      'return-last
                      (intersection-eq
                       names
                       (strip-cars (table-alist 'return-last-table wrld)))))
           (t
            (trans-er-let*
             ((flet-alist (translate11-flet-alist x fives stobjs-out bindings
                                                  known-stobjs flet-alist ctx wrld
                                                  state-vars)))
             (translate11 body
                          stobjs-out bindings known-stobjs flet-alist x
                          ctx wrld state-vars)))))))))))

(defun translate-stobj-calls (calls len bindings known-stobjs flet-alist
                                    cform ctx wrld state-vars)

; Calls is a list of applications of stobj accessor or updater calls, as
; returned by parse-stobj-let1 and vetted by chk-stobj-let.  We translate those
; applications without going through translate11, because in the case of
; updater calls, the calls update stobj fields, which is illegal except in
; proper support of a stobj-let form.

; We return a usual context-message triple: either (mv ctx erp bindings) or (mv
; nil translated-calls bindings).  The only syntax changed by translation is
; in the case of an index for an array update, where len is the length of a
; call for such a case (3 for accessor calls, 4 for updater calls).

  (cond ((endp calls) (trans-value nil))
        (t (trans-er-let*
            ((rest (translate-stobj-calls (cdr calls) len bindings
                                          known-stobjs flet-alist
                                          cform ctx wrld state-vars)))
            (let ((call (car calls)))
              (cond
               ((eql (length call) len) ; e.g. (fldi index parent-st)
                (trans-er-let*
                 ((index

; We know from parse-stobj-let1 that the index is either a symbol, a natural
; number, or the quotation of a natural number.  But in case we relax that
; restriction someday, and because a symbol can be a variable or a constant, we
; do not rely on that fact here.

                   (translate11 (cadr call) '(nil) bindings known-stobjs
                                flet-alist cform ctx wrld state-vars)))
                 (trans-value (cons (list* (car call) index (cddr call))
                                    rest))))
               (t (trans-value (cons call rest)))))))))

(defun translate11-let (x tbody0 targs stobjs-out bindings known-stobjs
                          flet-alist ctx wrld state-vars)

; Warning:  If the final form of a translated let is changed,
; be sure to reconsider translated-acl2-unwind-protectp.

; X is a cons whose car is 'LET.  If tbody0 is nil, as is the case for a
; user-supplied LET expression, then this function is nothing more than the
; restriction of function translate11 to that case.  Otherwise, the LET
; expression arises from a STOBJ-LET expression, and we make the following
; exceptions: the bindings are allowed to bind more than one stobj; we suppress
; the check that a stobj bound in the LET bindings must be returned by the LET;
; tbody0 is used as the translation of the body of the LET; and targs, if
; non-nil, is used as the translation of the strip-cadrs of the bindings of the
; let, as these are assumed already to be translated.

; In translating LET and MV-LET we generate "open lambdas" as function
; symbols.  The main reason we did this was to prevent translate from
; exploding in our faces when presented with typical DEFUNs (e.g., our
; own code).  Note that such LAMBDAs can be expanded away.  However,
; expansion affects the guards.  Consider (let ((x (car 3))) t), which
; expands to ((lambda (x) t) (car 3)).

  (cond
   ((not (and (>= (length x) 3)
              (doublet-listp (cadr x))))
    (trans-er ctx
              "The proper form of a let is (let bindings dcl ... dcl body), ~
               where bindings has the form ((v1 term) ... (vn term)) and the ~
               vi are distinct variables, not constants, and do not begin ~
               with an asterisk, but ~x0 does not have this form."
              x))
   ((not (arglistp (strip-cars (cadr x))))
    (mv-let (culprit explan)
      (find-first-bad-arg (strip-cars (cadr x)))
      (trans-er ctx
                "The form ~x0 is an improper let expression because it ~
                       attempts to bind ~x1, which ~@2."
                x culprit explan)))
   (t
    (let* ((bound-vars (strip-cars (cadr x)))
           (multiple-bindings-p (consp (cdr bound-vars)))
           (stobj-flags
            (and (not (eq stobjs-out t))
                 (compute-stobj-flags bound-vars known-stobjs wrld)))
           (stobjs-bound (and stobj-flags ; optimization
                              (collect-non-x nil stobj-flags))))
      (cond
       ((and stobj-flags ; optimization (often false)
             multiple-bindings-p
             (null tbody0)
             (non-trivial-stobj-binding stobj-flags (cadr x)))
        (trans-er ctx
                  "A single-threaded object name, such as ~x0, may be ~
                   LET-bound to other than itself only when it is the only ~
                   binding in the LET, but ~x1 binds more than one variable."
                  (non-trivial-stobj-binding stobj-flags (cadr x))
                  x))
       (t (mv-let
            (erp edcls)
            (collect-declarations-cmp (butlast (cddr x) 1)
                                      bound-vars 'let ctx wrld)
            (cond
             (erp (mv erp edcls bindings))
             (t
              (trans-er-let*
               ((value-forms
                 (cond (targs (trans-value targs))
                       ((and stobjs-bound ; hence (not (eq stobjs-out t))
                             (not multiple-bindings-p))

; In this case, we know that the only variable of the LET is a stobj name.
; Note that (list (car bound-vars)) is thus a stobjs-out specifying
; a single result consisting of that stobj.

                        (trans-er-let*
                         ((val (translate11 (cadr (car (cadr x)))
                                            (list (car bound-vars))
                                            bindings known-stobjs flet-alist
                                            x ctx wrld state-vars)))
                         (trans-value (list val))))
                       (t (translate11-lst (strip-cadrs (cadr x))
                                           (if (eq stobjs-out t)
                                               t
                                             stobj-flags)
                                           bindings known-stobjs
                                           "in a LET binding (or LAMBDA ~
                                           application)"
                                           flet-alist x ctx wrld
                                           state-vars))))
                (tbody
                 (if tbody0
                     (trans-value tbody0)
                   (translate11 (car (last x)) stobjs-out bindings known-stobjs
                                flet-alist x ctx wrld state-vars)))
                (tdcls (translate11-lst
                        (translate-dcl-lst edcls wrld)
                        (if (eq stobjs-out t)
                            t
                          nil) ;;; '(nil ... nil)
                        bindings known-stobjs
                        "in a DECLARE form in a LET (or LAMBDA)"
                        flet-alist x ctx wrld state-vars)))
               (let ((used-vars (union-eq (all-vars tbody)
                                          (all-vars1-lst tdcls nil)))
                     (ignore-vars (ignore-vars edcls))
                     (ignorable-vars (ignorable-vars edcls))
                     (stobjs-out (translate-deref stobjs-out bindings)))
                 (cond
                  ((and stobjs-bound ; hence (not (eq stobjs-out t))
                        (not (consp stobjs-out)))
                   (unknown-binding-msg-er x ctx stobjs-bound
                                           "a LET" "the LET" "the LET"))
                  ((and
                    (null tbody0)            ; else skip this check
                    stobjs-bound             ; hence (not (eq stobjs-out t))
                    (not multiple-bindings-p) ; possible stobj mod in bindings
                    (not (eq (caar (cadr x))
                             (cadar (cadr x)))) ; stobj mod in bindings
                    (assert$ (null (cdr stobjs-bound))
                             (not (member-eq (car stobjs-bound) stobjs-out))))
                   (let ((stobjs-returned (collect-non-x nil stobjs-out)))
                     (trans-er+ x ctx
                                "The single-threaded object ~x0 has been bound ~
                                in a LET.  It is a requirement that this ~
                                object be among the outputs of the LET, but ~
                                it is not.  The LET returns ~#1~[no ~
                                single-threaded objects~/the single-threaded ~
                                object ~&2~/the single-threaded objects ~&2~]."
                                (car stobjs-bound)
                                (zero-one-or-more stobjs-returned)
                                stobjs-returned)))
                  ((intersectp-eq used-vars ignore-vars)
                   (trans-er+ x ctx
                              "Contrary to the declaration that ~#0~[it ~
                              is~/they are~] IGNOREd, the variable~#0~[ ~&0 ~
                              is~/s ~&0 are~] used in the body of the LET ~
                              expression that binds ~&1."
                              (intersection-eq used-vars ignore-vars)
                              bound-vars))
                  (t
                   (let* ((ignore-vars (augment-ignore-vars bound-vars
                                                            value-forms
                                                            ignore-vars))
                          (diff (set-difference-eq
                                 bound-vars
                                 (union-eq used-vars
                                           (union-eq ignorable-vars
                                                     ignore-vars))))
                          (ignore-ok
                           (if (null diff)
                               t
                             (cdr (assoc-eq
                                   :ignore-ok
                                   (table-alist 'acl2-defaults-table wrld))))))
                     (cond
                      ((null ignore-ok)
                       (trans-er+ x ctx
                                  "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                  used in the body of the LET expression that ~
                                  binds ~&1.  But ~&0 ~#0~[is~/are~] not ~
                                  declared IGNOREd or IGNORABLE.  See :DOC ~
                                  set-ignore-ok."
                                  diff
                                  bound-vars))
                      (t
                       (prog2$
                        (cond
                         ((eq ignore-ok :warn)
                          (warning$-cw1 ctx "Ignored-variables"
                                        "The variable~#0~[ ~&0 is~/s ~&0 are~] ~
                                        not used in the body of the LET ~
                                        expression that binds ~&1.  But ~&0 ~
                                        ~#0~[is~/are~] not declared IGNOREd ~
                                        or IGNORABLE.  See :DOC set-ignore-ok."
                                        diff
                                        bound-vars))
                         (t nil))
                        (let* ((tbody
                                (cond
                                 (tdcls
                                  (let ((guardian (dcl-guardian tdcls)))
                                    (cond ((equal guardian *t*)

; See the comment about THE in dcl-guardian.

                                           tbody)
                                          (t (prog2$-call guardian tbody)))))
                                 (t tbody))))
                          (trans-value
                           (make-lambda-term bound-vars
                                             (hide-ignored-actuals
                                              ignore-vars
                                              bound-vars
                                              value-forms)
                                             tbody))))))))))))))))))))

(defun translate11-let* (x tbody targs stobjs-out bindings known-stobjs
                           flet-alist ctx wrld state-vars)

; This function is analogous to translate11-let, but it is for let* instead of
; let and here we assume no declarations.  Thus, x is (let* ((var1 arg1) (vark
; ... argk)) body), where targs is the list of translations of arg1, ..., argk
; and tbody is the translation of body.  Note that unlike translate11-let, here
; tbody and targs are not optional.

  (cond ((endp targs) (trans-value tbody))
        (t (case-match x
             (('let* (pair . pairs) y)
              (let ((body0 `(let* ,pairs ,y)))
                (trans-er-let*
                 ((tbody0 (translate11-let*
                           body0 tbody (cdr targs) stobjs-out bindings
                           known-stobjs flet-alist ctx wrld state-vars)))
                 (translate11-let
                  `(let (,pair) ,body0)
                  tbody0 (list (car targs)) stobjs-out bindings known-stobjs
                  flet-alist ctx wrld state-vars))))
             (& (trans-er+ x ctx
                           "Implementation error: Unexpected form for ~x0."
                           'translate11-let*))))))

(defun translate11-mv-let (x tbody0 stobjs-out bindings known-stobjs
                             local-stobj local-stobj-creator flet-alist
                             ctx wrld state-vars)

; X is a cons whose car is 'MV-LET.  This function is nothing more than the
; restriction of function translate11 to that case, with two exceptional cases:
; if tbody0 is not nil, then it is to be used as the translation of the body of
; the MV-LET, and we suppress the check that a stobj bound by MV-LET must be
; returned by the MV-LET; and if local-stobj is not nil, then we are in the
; process of translating (with-local-stobj local-stobj x local-stobj-creator),
; where we know that local-stobj-creator is the creator function for the stobj
; local-stobj.

; Warning: If the final form of a translated mv-let is changed, be sure to
; reconsider translated-acl2-unwind-protectp and the creation of mv-let
; expressions in untranslate1.

  (cond
   ((not (and (true-listp (cadr x))
              (> (length (cadr x)) 1)))
    (trans-er ctx
              "The first form in an MV-LET expression must be a true list of ~
               length 2 or more.  ~x0 does not meet these conditions."
              (cadr x)))
   ((not (arglistp (cadr x)))
    (mv-let (culprit explan)
            (find-first-bad-arg (cadr x))
            (trans-er ctx
                      "The first form in an MV-LET expression must be a list ~
                       of distinct variables of length 2 or more, but ~x0 ~
                       does not meet these conditions.  The element ~x1 ~@2."
                      x culprit explan)))
   ((not (>= (length x) 4))
    (trans-er ctx
              "An MV-LET expression has the form (mv-let (var var var*) form ~
               dcl* form) but ~x0 does not have sufficient length to meet ~
               this condition."
              x))
   (t
    (let* ((bound-vars (cadr x))
           (producer-known-stobjs (if (and local-stobj
                                           (not (eq known-stobjs t)))
                                      (add-to-set-eq local-stobj known-stobjs)
                                    known-stobjs))
           (bound-stobjs-out (if (and (eq stobjs-out t)

; If local-stobj is true (hence we are being called by translate in the case of
; a with-local-stobj term), then we want to do syntax-checking that we wouldn't
; normally do with stobjs-out = t, because we don't have a spec for
; with-local-stobj in the case that this syntax-checking is turned off.

                                      (not local-stobj))
                                 t
                               (compute-stobj-flags bound-vars
                                                    producer-known-stobjs
                                                    wrld)))
           (stobjs-bound0 (if (eq bound-stobjs-out t)
                              nil
                            (collect-non-x nil bound-stobjs-out)))
           (stobjs-bound

; Stobjs-bound is perhaps an odd name for this variable, since if there is a
; local stobj, then literally speaking it is bound -- though we do not consider
; it so here.  Really, stobjs-bound is the list of stobj names that we require
; to come out of the mv-let.

            (if local-stobj
                (remove1-eq local-stobj stobjs-bound0)
              stobjs-bound0)))
      (mv-let
       (erp edcls)
       (collect-declarations-cmp (butlast (cdddr x) 1)
                                 (cadr x) 'mv-let ctx wrld)
       (cond
        (erp ; erp is a ctx and edcls is a msg
         (trans-er erp "~@0" edcls))
        (t
         (trans-er-let*
          ((tcall (translate11 (caddr x)
                               bound-stobjs-out
                               bindings
                               producer-known-stobjs
                               flet-alist x ctx wrld state-vars))
           (tdcls (translate11-lst (translate-dcl-lst edcls wrld)
                                   (if (eq stobjs-out t)
                                       t
                                     nil) ;;; '(nil ... nil)
                                   bindings known-stobjs
                                   "in a DECLARE form in an MV-LET"
                                   flet-alist x ctx wrld state-vars))
           (tbody (if tbody0
                      (trans-value tbody0)
                    (translate11 (car (last x))
                                 stobjs-out bindings known-stobjs flet-alist x
                                 ctx wrld state-vars))))
          (let ((used-vars (union-eq (all-vars tbody)
                                     (all-vars1-lst tdcls nil)))
                (ignore-vars (if local-stobj
                                 (cons local-stobj (ignore-vars edcls))
                               (ignore-vars edcls)))
                (ignorable-vars (ignorable-vars edcls))
                (stobjs-out (translate-deref stobjs-out bindings)))
            (cond
             ((and local-stobj
                   (not (member-eq local-stobj ignore-vars)))
              (trans-er+ x ctx
                         "A local-stobj must be declared ignored, but ~x0 is ~
                          not.  See :DOC with-local-stobj."
                         local-stobj))
             ((and stobjs-bound
                   (not (consp stobjs-out)))
              (unknown-binding-msg-er x ctx stobjs-bound
                                      "an MV-LET" "the MV-LET" "the MV-LET"))
             ((and stobjs-bound
                   (null tbody0) ; else skip this check
                   (not (subsetp stobjs-bound
                                 (collect-non-x nil stobjs-out))))
              (let ((stobjs-returned (collect-non-x nil stobjs-out)))
                (trans-er+ x ctx
                           "The single-threaded object~#0~[ ~&0 has~/s ~&0 ~
                            have~] been bound in an MV-LET.  It is a ~
                            requirement that ~#0~[this object~/these ~
                            objects~] be among the outputs of the MV-LET, but ~
                            ~#0~[it is~/they are~] not.  The MV-LET returns ~
                            ~#1~[no single-threaded objects~/the ~
                            single-threaded object ~&2~/the single-threaded ~
                            objects ~&2~]."
                           (set-difference-eq stobjs-bound stobjs-returned)
                           (zero-one-or-more stobjs-returned)
                           stobjs-returned)))
             ((intersectp-eq used-vars ignore-vars)
              (trans-er+ x ctx
                         "Contrary to the declaration that ~#0~[it is~/they ~
                          are~] IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 ~
                          are~] used in the MV-LET expression that binds ~&1."
                         (intersection-eq used-vars ignore-vars)
                         bound-vars))
             (t
              (let* ((diff (set-difference-eq
                            bound-vars
                            (union-eq used-vars
                                      (union-eq ignorable-vars
                                                ignore-vars))))
                     (ignore-ok
                      (if (null diff)
                          t
                        (cdr (assoc-eq
                              :ignore-ok
                              (table-alist 'acl2-defaults-table wrld))))))
                (cond
                 ((null ignore-ok)
                  (trans-er+ x ctx
                             "The variable~#0~[ ~&0 is~/s ~&0 are~] not used ~
                              in the body of the MV-LET expression that binds ~
                              ~&1.  But ~&0 ~#0~[is~/are~] not declared ~
                              IGNOREd or IGNORABLE.  See :DOC set-ignore-ok."
                             diff
                             bound-vars))
                 (t
                  (prog2$
                   (cond
                    ((eq ignore-ok :warn)
                     (warning$-cw1 ctx "Ignored-variables"
                                   "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                    used in the body of the MV-LET expression ~
                                    that binds ~&1. But ~&0 ~#0~[is~/are~] ~
                                    not declared IGNOREd or IGNORABLE.  See ~
                                    :DOC set-ignore-ok."
                                   diff
                                   bound-vars))
                    (t nil))
                   (let* ((tbody
                           (cond
                            (tdcls
                             (let ((guardian (dcl-guardian tdcls)))
                               (cond ((equal guardian *t*)

; See the comment about THE in dcl-guardian.

                                      tbody)
                                     (t (prog2$-call guardian tbody)))))
                            (t tbody)))
                          (body-vars (all-vars tbody))
                          (extra-body-vars
                           (set-difference-eq body-vars (cadr x)))
                          (vars (all-vars1 tcall extra-body-vars))
                          (mv-var (genvar 'genvar "MV" nil vars)))
                     (trans-value
                      (list* (make-lambda
                              (cons mv-var extra-body-vars)
                              (cons (make-lambda
                                     (append (cadr x)
                                             extra-body-vars)
                                     tbody)

; When the rewriter encounters ((lambda (... xi ...) body) ... actuali
; ...), where xi is ignored and actuali is in the corresponding
; position, we'd like to tell the rewriter not to bother rewriting
; actuali.  We do this by wrapping a hide around it.  This typically
; only happens with MV-LET expressions, though we do it for LET
; expressions as well.

                                    (append (hide-ignored-actuals
                                             ignore-vars
                                             (cadr x)
                                             (mv-nth-list
                                              mv-var 0
                                              (length (cadr x))))
                                            extra-body-vars)))
                             (if local-stobj
                                 (let ((tcall-vars
                                        (remove1-eq local-stobj
                                                    (all-vars tcall))))
                                   (cons (make-lambda
                                          (cons local-stobj tcall-vars)
                                          tcall)
                                         (cons (list local-stobj-creator)
                                               tcall-vars)))
                               tcall)
                             extra-body-vars))))))))))))))))))

(defun translate11-wormhole-eval (x y z bindings flet-alist ctx wrld
                                    state-vars)

; The three arguments of wormhole-eval are x y and z.  Here, z has been
; translated but x and y have not been.  We want to insure that x and y are
; well-formed quoted forms of a certain shape.  We don't actually care about z
; and ignore it!  We translated it just for sanity's sake: no point in allowing
; the user ever to write an ill-formed term in a well-formed term.

  (declare (ignore z))
  (cond
   ((not (and (true-listp x)
              (equal (length x) 2)
              (equal (car x) 'quote)))
    (trans-er ctx
              "The first argument to wormhole-eval must be a QUOTE expression ~
               containing the name of the wormhole in question and ~x0 is not ~
               quoted."
              x))
   ((not (and (true-listp y)
              (equal (length y) 2)
              (equal (car y) 'quote)))
    (trans-er ctx
              "The second argument to wormhole-eval must be a QUOTE ~
               expression containing a LAMBDA expression and ~x0 is not ~
               quoted."
              y))
   ((not (and (true-listp (cadr y))
              (equal (length (cadr y)) 3)
              (equal (car (cadr y)) 'lambda)
              (true-listp (cadr (cadr y)))
              (<= (length (cadr (cadr y))) 1)))
    (trans-er ctx
              "The second argument to wormhole-eval must be a QUOTE ~
               expression containing a LAMBDA expression with at most one ~
               formal, e.g., the second argument must be either of the form ~
               '(LAMBDA () body) or of the form (LAMBDA (v) body).  But ~x0 ~
               is of neither form."
              y))
   (t (let ((lambda-formals (cadr (cadr y)))
            (lambda-body (caddr (cadr y))))
        (cond
         ((not (arglistp lambda-formals))
          (mv-let (culprit explan)
                  (find-first-bad-arg lambda-formals)
                  (trans-er ctx
                            "The quoted lambda expression, ~x0, supplied to ~
                             wormhole-eval is improper because it binds ~x1, ~
                             which ~@2."
                            y culprit explan)))
         (t
          (let ((whs (car lambda-formals)))

; Whs is either nil or the legal variable name bound by the lambda.

            (mv-let
               (body-erp tlambda-body body-bindings)
               (translate11 lambda-body
                            '(nil)           ; stobjs-out
                            nil
                            '(state) ; known-stobjs
                            flet-alist
                            x ctx wrld state-vars)
               (declare (ignore body-bindings))
               (cond
                (body-erp (mv body-erp tlambda-body bindings))
                ((and whs
                      (not (member-eq whs (all-vars tlambda-body))))
                 (trans-er ctx
                           "The form ~x0 is an improper quoted lambda ~
                            expression for wormhole-eval because it binds but ~
                            does not use ~x1, which is understood to be the ~
                            name you're giving to the current value of the ~
                            wormhole status for the wormhole in question."
                           y whs))
                (t

; We replace the second argument of wormhole-eval by a possibly different
; quoted object.  But that is ok because wormhole-eval returns nil no matter
; what objects we pass it.  We also compute a form with the same free vars as
; the lambda expression and stuff it in as the third argument, throwing away
; whatever the user supplied.

                 (trans-value
                  (fcons-term* 'wormhole-eval
                               x
                               (list 'quote
                                     (if whs
                                         `(lambda (,whs) ,tlambda-body)
                                         `(lambda () ,tlambda-body)))
                               (name-dropper
                                (if whs
                                    (remove1-eq whs (all-vars tlambda-body))
                                    (all-vars tlambda-body)))))))))))))))

(defun translate11-call-1 (form fn args bindings
                                known-stobjs msg flet-alist ctx wrld state-vars
                                stobjs-in-call flg)

; Here we carve out some code from translate11-call (for the case that both
; stobjs-out and stobjs-out2 are conses), so that we can invoke it twice
; without writing the code twice.  Msg is as described in translate11-lst.

  (trans-er-let*

; We handle the special translation of wormhole-eval both here, when stobjs-out
; is known, and below, where it is not.  Of course, stobjs-out2 (for
; wormhole-eval) is fixed: (nil).  Keep this code in sync with that below.

; The odd treatment of wormhole-eval's first two arguments below is due to the
; fact that we actually don't want to translate them.  We will insist that they
; actually be quoted forms, not macro calls that expand to quoted forms.  So we
; put bogus nils in here and then swap back the untranslated args below.

   ((targs (trans-or
            (translate11-lst (if (eq fn 'wormhole-eval)
                                 (list *nil* *nil* (nth 2 args))
                               args)
                             stobjs-in-call
                             bindings
                             known-stobjs
                             msg flet-alist form ctx wrld
                             state-vars)

; Just below, we allow a stobj recognizer to be applied to an ordinary object,
; even when translating for execution (function bodies or top-level loop).
; This is an exception to the the usual rule, which requires stobj functions to
; respect their stobjs-in arguments when translating for execution.  We take
; advantage of this exception in our support for stobj fields of stobjs.  For
; example, consider the following two events.

;   (defstobj sub1 sub1-fld1)
;   (defstobj top1 (top1-fld :type sub1))

; The axiomatic definition generated in the second defstobj for function
; top1-fldp is as follows.

;   (defun top1-fldp (x)
;     (declare (xargs :guard t :verify-guards t)
;              (ignorable x))
;     (sub1p x))

; At this point, x is an ordinary object; only at the conclusion of a defstobj
; event do we put stobjs-in and stobjs-out properties for the new functions.
; By allowing sub1p to be applied to an ordinary object, we allow the
; definition to be accepted without any (other) special treatment.

            (and (eq flg :failed)
                 (stobj-recognizer-p fn wrld))
            (translate11-lst args
                             '(nil)
                             bindings
                             known-stobjs
                             msg flet-alist form ctx wrld
                             state-vars)
            (msg "  Observe that while it is permitted to apply ~x0 to an ~
                  ordinary object, this stobj recognizer must not be applied ~
                  to the wrong stobj."
                 fn))))
   (cond ((eq fn 'wormhole-eval)
          (translate11-wormhole-eval (car args)
                                     (cadr args)
                                     (caddr targs)
                                     bindings flet-alist ctx wrld
                                     state-vars))
         (t (trans-value (fcons-term fn targs))))))

(defun translate11-call (form fn args stobjs-out stobjs-out2 bindings
                              known-stobjs msg flet-alist ctx wrld state-vars)

; We are translating (for execution, not merely theorems) a call of fn on args.
; Stobjs-out and stobjs-out2 are respectively the expected stobjs-out from the
; present context and the stobjs-out from fn, already dereferenced.  Note that
; each of these is either a legitimate (true-list) stobjs-out or else a symbol
; representing an unknown stobjs-out.

; Msg is as described in translate11-lst.

; Note that for this call to be suitable, args has to satisfy the stobjs
; discipline of passing a stobj name to a stobjs-in position.  We take
; advantage of this requirement: stobjs-in-out (called below) invokes
; stobjs-in-out1, which checks stobjp of each arg in args.  For that reason, it
; is important that we do not call translate11-call on arbitrary lambdas, where
; an arg might not be a stobj name, e.g., ((LAMBDA (ST) ST) (UPDATE-FLD '2
; ST)).

; We are tempted to enforce the call-arguments-limit imposed by Common Lisp.
; According to the HyperSpec, this constant has an implementation-dependent
; value that is "An integer not smaller than 50", and is "The upper exclusive
; bound on the number of arguments that may be passed to a function."
; The limits vary considerably, and are as follows in increasing order.

;   GCL Version 2.6.12
;                    64
;   LispWorks Version 7.0.0
;                  2047
;   Allegro CL Enterprise Edition 8.0
;                 16384
;   Clozure Common Lisp Version 1.12-dev-r16695M-trunk
;                 65536
;   CMU Common Lisp snapshot-2016-01 (21A Unicode)
;             536870911
;   SBCL 1.3.0
;   4611686018427387903

; We have decided not to impose this limit ourselves, because for example, it
; would be sad if a large existing proof development done using, say, CCL, were
; to start failing because we impose a limit of 50 or 64.  Instead, we view
; this limit as a resource limitation that is implementation-dependent, in the
; same spirit as how one could get a stack overflow or memory exhaustion on one
; platform but not another.

  (mv-let
    (flg stobjs-in-call stobjs-out-call)
    (stobjs-in-out fn args stobjs-out2 known-stobjs wrld)

; Fn can be viewed as mapping stobjs-in-call to stobjs-out-call; see
; stobjs-in-out.

; If flg is :failed, then stobjs-in-call and stobjs-out-call are just the
; stobjs-in and (dereferenced) stobjs-out of fn.  In that case we proceed
; happily without any mapping of input stobjs, expecting the usual
; input-mismatch error from a failed call of translate11-lst.

    (cond
     ((consp stobjs-out)
      (cond
       ((consp stobjs-out-call) ; equivalently: (consp stobjs-out2)
        (cond
         ((equal stobjs-out stobjs-out-call)

; Then we translate where we view fn as mapping stobjs-in-call to
; stobjs-out-call; see stobjs-in-out.

          (translate11-call-1 form fn args bindings
                              known-stobjs msg flet-alist ctx wrld state-vars
                              stobjs-in-call flg))
         (t

; We are definitely in an error case: stobjs-in-out adjusted the stobjs-in of
; fn to match args, and then adjusted stobjs-out accordingly to yield
; stobjs-out-call, which disagrees with the expected stobjs-out.  But in order
; to produce a helpful error message, we want to determine whether the problem
; is with input stobjs or output stobjs.  Consider the following example.

;   (defstobj st1 fld1)
;   (defstobj st2 fld2 :congruent-to st1)
;   (defun f (st2)
;     (declare (xargs :stobjs st2))
;     (let ((st2 (update-fld1 st2 3)))
;       st2))

; The definition of f is ill-formed because the arguments to update-fld1 are in
; the wrong order.  We can catch this and other input problems simply by
; attempting to translate the arguments, using the modified stobjs-in,
; stobjs-in-call.  But consider the normal case, where no congruent stobjs are
; involved, and suppose that there are errors both in the arguments and in the
; stobjs-out.  Traditionally we prefer to blame the stobjs-out in that case.
; Our solution is to check the stobjs-out and only report a stobjs-in problem
; when the stobjs-out match up when viewed through the lens of congruent
; stobjs.

          (mv-let (flg2 alist2)
            (match-stobjs stobjs-out stobjs-out2 nil)
            (cond
             ((and flg2 alist2)

; Note that if congruent stobjs aren't involved, alist2 will be nil.  So this
; case only applies when congruent stobjs are involved.  Otherwise we report
; (in the error further below) that the function call returns a result of the
; wrong shape (as we probably always did before congruent stobjs were
; introduced).

; To see why we insist on alist2 being non-nil in the test just above even when
; congruent stobjs are involved, consider another example (thanks to Sol
; Swords), which assumes the same two defstobj events as above:

;   (defun foo (st1 st2)
;     (declare (xargs :stobjs (st1 st2)))
;     (let ((st1 (update-fld1 0 st2)))
;       (mv st1 st2)))

; In this case alist2 is nil, so the call below of translate11-call-1 completes
; without error.  Rather than come up with a custom error message for that
; case, we prefer simply to report (in the error further below): "This function
; call returns a result of shape ST2 (after accounting for the replacement of
; some input stobjs by congruent stobjs) where a result of shape ST1 is
; required."

              (trans-er-let*
               ((tform (translate11-call-1 form fn args bindings
                                           known-stobjs msg flet-alist
                                           ctx wrld state-vars
                                           (apply-symbol-alist
                                            alist2
                                            stobjs-in-call
                                            nil)
                                           flg)))

; We fully expect an error from the call above of translate11-call-1, since the
; application of alist2 to the expected stobjs-in-call should cause a stobj
; mismatch.  Perhaps the following error should suggest contacting the
; implementors.  But since the only issue here is how to report an error -- we
; definitely are in an error case -- we don't bother with that suggestion.

               (trans-er+ form ctx
                          "It is illegal to invoke ~@0 here because of a ~
                           signature mismatch involving congruent stobjs.  ~
                           ACL2 was unable to determine the exact nature of ~
                           the mismatch."
                          (if (consp fn) msg (msg "~x0" fn)))))
             (t
              (trans-er+ form ctx
                         "It is illegal to invoke ~@0 here because of a ~
                          signature mismatch.  This function call returns a ~
                          result of shape ~x1~@2 where a result of shape ~x3 ~
                          is required.~@4"
                         (if (consp fn) msg (msg "~x0" fn))
                         (prettyify-stobjs-out stobjs-out-call)
                         (if (and flg (not (eq flg :failed)))
                             " (after accounting for the replacement of some ~
                              input stobjs by congruent stobjs)"
                           "")
                         (prettyify-stobjs-out stobjs-out)
                         (let* ((missing (missing-known-stobjs stobjs-out
                                                               stobjs-out2
                                                               known-stobjs
                                                               nil))
                                (missing-user-stobjs (set-difference-eq missing
                                                                        '(nil state)))
                                (state-string
                                 "  This error may occur when the ACL2 state ~
                                  is not available in the current context, ~
                                  for example as a formal parameter of a ~
                                  defun.")
                                (user-stobj-string
                                 "  This error may~@0 occur when ~&1 ~
                                  ~#1~[is~/are~] not declared to be ~#1~[a ~
                                  stobj~/stobjs~] in the current context."))
                           (cond
                            ((and missing-user-stobjs
                                  (member-eq 'state missing))
                             (msg "~@0~@1"
                                  state-string
                                  (msg user-stobj-string
                                       " also"
                                       missing-user-stobjs)))
                            (missing-user-stobjs
                             (msg user-stobj-string
                                  ""
                                  missing-user-stobjs))
                            (missing state-string)
                            (t ""))))))))))
       (t ; (symbolp stobjs-out2); equivalently, (symbolp stobjs-out-call)

; If flg is a non-empty alist, then the expected stobjs-out is not the
; stobjs-out to be returned by fn on arguments satisfying its declared
; signature.  For example, suppose that st1 and st2 are congruent stobjs;
; stobjs-out is (st2); fn is f; f has input signature (st1); and args is (st2),
; i.e., we are considering the call (f st2).  Then flg is ((st1 . st2)).  We
; apply the mapping, flg, in reverse to stobjs-out = (st2), to deduce that the
; stobjs-out of fn is (st1) -- the point is that if we apply flg to (st1), then
; we get the expected stobjs-out of (st2).

        (let ((bindings
               (translate-bind stobjs-out2
                               (if (consp flg)
                                   (apply-inverse-symbol-alist flg stobjs-out
                                                               nil)
                                 stobjs-out)
                               bindings)))
          (trans-er-let*
           ((args (translate11-lst args
                                   stobjs-in-call
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)))
           (trans-value (fcons-term fn args)))))))
     ((consp stobjs-out-call) ; equivalently: (consp stobjs-out2)
      (let ((bindings
             (translate-bind stobjs-out stobjs-out-call bindings)))
        (trans-er-let*
         ((targs (trans-or
                  (translate11-lst (if (eq fn 'wormhole-eval)
                                       (list *nil* *nil* (nth 2 args))
                                     args)
                                   stobjs-in-call
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)

; See the comment above about applying a stobj recognizer to be applied to an
; ordinary object.

                  (and (eq flg :failed)
                       (stobj-recognizer-p fn wrld))
                  (translate11-lst args
                                   '(nil)
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)
                  (msg "  Observe that while it is permitted to apply ~x0 to ~
                        an ordinary object, this stobj recognizer must not be ~
                        applied to the wrong stobj."
                       fn))))
         (cond ((eq fn 'wormhole-eval)
                (translate11-wormhole-eval (car args)
                                           (cadr args)
                                           (caddr targs)
                                           bindings flet-alist ctx wrld
                                           state-vars))
               (t (trans-value (fcons-term fn targs)))))))
     (t (let ((bindings

; If the stobjs-in of fn are compatible with args, but only when mapping at
; least one input stobj to a congruent stobj (i.e., flg is a non-empty alist),
; then we cannot simply bind stobjs-out2 to stobjs-out.  For example, suppose
; st1 and st2 are congruent stobjs and we are defining a function (f st1 st2)
; in a context where we do not know the expected result signature, i.e.,
; stobjs-out is a symbol, nor do we know the stobjs-out of f, which could for
; example be (st1 st2) or (st2 st1).  (Is this example even possible?  Not
; sure, so let's continue....)  If we are looking at a call (f st2 st1), then
; we can actually be certain that the call does _not_ return the output
; signature of f!

               (if (consp flg)
                   bindings
                 (translate-bind stobjs-out2 stobjs-out bindings))))
          (trans-er-let*
           ((args (translate11-lst args
                                   stobjs-in-call
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)))
           (trans-value (fcons-term fn args))))))))

(defun translate11 (x stobjs-out bindings known-stobjs flet-alist
                      cform ctx wrld state-vars)

; Warning: Keep this in sync with macroexpand1*-cmp.  Also, for any new special
; operators (e.g., let and translate-and-test), consider extending
; *special-ops* in community book books/misc/check-acl2-exports.lisp.

; Bindings is an alist binding symbols either to their corresponding STOBJS-OUT
; or to symbols.  The only symbols used are (about-to-be introduced) function
; symbols or the keyword :STOBJS-OUT.  When fn is bound to gn it means we have
; determined that the STOBJS-OUT of fn is that of gn.  We allow fn to be bound
; to itself -- indeed, it is required initially!  (This allows bindings to
; double as a recording of all the names currently being introduced.)  A
; special case is when :STOBJS-OUT is bound in bindings: initially it is bound
; to itself, but in the returned bindings it will be bound to the stobjs-out of
; the expression being translated.

; Stobjs-out is one of:

; t              - meaning we do not care about multiple-value or stobj
;                  restrictions (as when translating proposed theorems).
; (s1 s2 ... sk) - a list of 1 or more stobj flags indicating where stobjs
;                  are returned in the translation of x
; fn             - a function name, indicating that we are trying to deduce
;                  the stobjs-out setting for fn from some output branch, x,
;                  of its body, as we translate.  We also enforce prohibitions
;                  against the use of DEFUN, IN-PACKAGE, etc inside bodies.
; :stobjs-out    - like a function name, except we know we are NOT in a defun
;                  body and allow DEFUN, IN-PACKAGE, etc., but restrict certain
;                  calls of return-last.

; See the essay on STOBJS-IN and STOBJS-OUT, above.

; When stobjs-out is a symbol, it must be dereferenced through bindings
; before using it.  [One might think that we follow the convention of keeping
; it dereferenced, e.g., by using the new value whenever we bind it.
; But that is hard since the binding may come deep in some recursive
; call of translate.]

; T always dereferences to t and nothing else dereferences to t.  So you
; can check (eq stobjs-out t) without dereferencing to know whether we
; care about the stobjs-out conditions.

; Known-stobjs is a subset of the list of all stobjs known in world wrld (but
; may contain some NIL elements, to be ignored; see "slight abuse" comment in
; chk-acceptable-defuns1) or else known-stobjs is T and denotes all the stobjs
; in wrld.  A name is considered a stobj iff it is in known-stobjs.  This
; allows us to implement the :STOBJS declaration in defuns, by which the user
; can declare the stobjs in a function.

; The cform argument is a form that provides context -- it is the one to be
; printed by trans-er+ when there isn't another obvious contextual form to
; print.  (Often x carries enough context.)

; Keep this in sync with oneify.

  (cond
   ((or (atom x) (eq (car x) 'quote))

; We handle both the (quote x) and atom case together because both
; have the same effects on calculating the stobjs-out.

    (let* ((stobjs-out (translate-deref stobjs-out bindings))
           (vc (legal-variable-or-constant-namep x))
           (const (and (eq vc 'constant)
                       (defined-constant x wrld))))
      (cond
       ((and (symbolp x)
             (not (keywordp x))
             (not vc))
        (trans-er+? cform x
                    ctx
                    "The symbol ~x0 is being used as a variable or constant ~
                     symbol but does not have the proper syntax.  Such names ~
                     must ~@1.  See :DOC name."
                    x
                    (tilde-@-illegal-variable-or-constant-name-phrase x)))
       ((and (eq vc 'constant)
             (not const))
        (trans-er+? cform x
                    ctx
                    "The symbol ~x0 (in package ~x1) has the syntax of a ~
                     constant, but has not been defined."
                    x
                    (symbol-package-name x)))

       ((and (not (atom x)) (not (termp x wrld)))
        (trans-er+? cform x
                    ctx
                    "The proper form of a quoted constant is (quote x), but ~
                     ~x0 is not of this form."
                    x))

; We now know that x denotes a term.  Let transx be that term.

       (t (let ((transx (cond ((keywordp x) (kwote x))
                              ((symbolp x)
                               (cond ((eq vc 'constant) const)
                                     (t x)))
                              ((atom x) (kwote x))
                              (t x))))

; Now consider the specified stobjs-out.  It is fully dereferenced.
; So there are three cases: (1) we don't care about stobjs-out, (2)
; stobjs-out tells us exactly what kind of output is legal here and we
; must check, or (3) stobjs-out is an unknown but we now know its
; value and can bind it.

            (cond
             ((eq stobjs-out t) ;;; (1)
              (trans-value transx))
             ((consp stobjs-out) ;;; (2)
              (cond
               ((cdr stobjs-out)
                (trans-er+? cform x
                            ctx
                            "One value, ~x0, is being returned where ~x1 ~
                             values were expected."
                            x (length stobjs-out)))
               ((and (null (car stobjs-out))
                     (stobjp transx known-stobjs wrld))
                (trans-er+? cform x
                            ctx
                            "A single-threaded object, namely ~x0, is being ~
                             used where an ordinary object is expected."
                            transx))
               ((and (car stobjs-out)
                     (not (eq (car stobjs-out) transx)))
                (cond
                 ((stobjp transx known-stobjs wrld)
                  (trans-er+? cform x
                              ctx
                              "The single-threaded object ~x0 is being used ~
                               where the single-threaded object ~x1 was ~
                               expected."
                              transx (car stobjs-out)))
                 (t
                  (trans-er+? cform x
                              ctx
                              "The ordinary object ~x0 is being used where ~
                               the single-threaded object ~x1 was expected."
                              transx (car stobjs-out)))))
               (t (trans-value transx))))
             (t ;;; (3)
              (trans-value transx
                           (translate-bind
                            stobjs-out
                            (list (if (stobjp transx known-stobjs wrld)
                                      transx
                                    nil))
                            bindings)))))))))
   ((not (true-listp (cdr x)))
    (trans-er ctx
              "Function (and macro) applications in ACL2 must end in NIL.  ~
               ~x0 is not of this form."
              x))
   ((not (symbolp (car x)))
    (cond ((or (not (consp (car x)))
               (not (eq (caar x) 'lambda)))
           (trans-er ctx
                     "Function (and macro) applications in ACL2 must begin ~
                      with a symbol or LAMBDA expression.  ~x0 is not of this ~
                      form."
                     x))
          ((or (not (true-listp (car x)))
               (not (>= (length (car x)) 3))
               (not (true-listp (cadr (car x)))))
           (trans-er ctx
                     "Illegal LAMBDA expression: ~x0."
                     x))
          ((not (= (length (cadr (car x))) (length (cdr x))))
           (trans-er+ x ctx
                      "The LAMBDA expression ~x0 takes ~#1~[no arguments~/1 ~
                       argument~/~x2 arguments~] and is being passed ~#3~[no ~
                       arguments~/1 argument~/~x4 arguments~]."
                      (car x)
                      (zero-one-or-more (length (cadr (car x))))
                      (length (cadr (car x)))
                      (zero-one-or-more (length (cdr x)))
                      (length (cdr x))))
          (t (translate11
              (list* 'let
                     (listlis (cadr (car x)) (cdr x))
                     (cddr (car x)))
              stobjs-out bindings known-stobjs flet-alist x ctx wrld
              state-vars))))
   ((and (not (eq stobjs-out t)) (eq (car x) 'mv))

; If stobjs-out is t we let normal macroexpansion handle mv.

    (let ((stobjs-out (translate-deref stobjs-out bindings)))
      (cond
       ((let ((len (length (cdr x))))
          (or (< len 2)
              (> len

; Keep the number below (which also occurs in the string) equal to the value of
; raw Lisp constant *number-of-return-values*.

                 32)))
        (cond ((< (length (cdr x)) 2)
               (trans-er ctx
                         "MV must be given at least two arguments, but ~x0 has ~
                          fewer than two arguments."
                         x))
              (t
               (trans-er ctx
                         "MV must be given no more than 32 arguments; thus ~x0 ~
                          has too many arguments."
                         x))))
       ((consp stobjs-out)
        (cond
         ((not (int= (length stobjs-out) (length (cdr x))))
          (trans-er+? cform x
                      ctx
                      "The expected number of return values for ~x0 is ~x1 ~
                       but the actual number of return values is ~x2."
                      x
                      (length stobjs-out)
                      (length (cdr x))))
         (t
          (trans-er-let*
           ((args (translate11-lst (cdr x) stobjs-out bindings known-stobjs 'mv
                                   flet-alist x ctx wrld state-vars)))
           (trans-value (listify args))))))
       (t (let* ((new-stobjs-out (compute-stobj-flags (cdr x)
                                                      known-stobjs
                                                      wrld))
                 (bindings
                  (translate-bind stobjs-out new-stobjs-out bindings)))

; When we compute new-stobjs-out, above, we do with untranslated
; terms.  The stobj slots of an mv must be occupied by stobj variable
; names!  If a slot is occupied by anything else, the occupant must be
; a single non-stobj.

            (cond
             ((not (no-duplicatesp (collect-non-x nil new-stobjs-out)))
              (trans-er ctx
                        "It is illegal to return more than one reference to a ~
                         given single-threaded object in an MV form.  The ~
                         form ~x0 is thus illegal."
                        x))
             (t
              (mv-let
                (erp args bindings)
                (translate11-lst (cdr x) new-stobjs-out
                                 bindings known-stobjs
                                 'mv flet-alist x ctx wrld state-vars)
                (cond
                 (erp
                  (let ((st/call (find-stobj-out-and-call (cdr x) known-stobjs
                                                          ctx wrld state-vars)))
                    (cond
                     (st/call
                      (trans-er+ cform ctx
                                 "The form ~x0 is being used as an argument ~
                                  to a call of ~x1.  This form evaluates to a ~
                                  single-threaded object, ~x2; but for an ~
                                  argument of ~x1, the stobj variable itself ~
                                  (here, ~x2) is required, not merely a term ~
                                  that returns such a single-threaded object. ~
                                  ~ So you may need to bind ~x2 with LET; see ~
                                  :DOC stobj."
                                 (cdr st/call)
                                 'mv
                                 (car st/call)))
                     (t (mv erp args bindings)))))
                 (t (trans-value (listify args))))))))))))
   ((eq (car x) 'mv-let)
    (translate11-mv-let x nil stobjs-out bindings known-stobjs
                        nil nil ; stobj info
                        flet-alist ctx wrld state-vars))
   ((assoc-eq (car x) flet-alist)

; The lambda-bodies in flet-alist are already translated.  Our approach is to
; consider a call of an flet-bound function symbol to be a call of the lambda
; to which it is bound in flet-alist.

    (let* ((entry (assoc-eq (car x) flet-alist))
           (lambda-fn (cadr entry))
           (formals (lambda-formals lambda-fn))
           (stobjs-out (translate-deref stobjs-out bindings))
           (stobjs-out2 (translate-deref (cddr entry) bindings)))
      (cond ((not (eql (length formals) (length (cdr x))))
             (trans-er ctx
                       "FLET-bound local function ~x0 takes ~#1~[no ~
                        arguments~/1 argument~/~x2 arguments~] but in the ~
                        call ~x3 it is given ~#4~[no arguments~/1 ~
                        argument~/~x5 arguments~].   The formal parameters ~
                        list for the applicable FLET-binding of ~x0 is ~X67."
                       (car x)
                       (zero-one-or-more (length formals))
                       (length formals)
                       x
                       (zero-one-or-more (length (cdr x)))
                       (length (cdr x))
                       formals
                       nil))
            ((eq stobjs-out t)
             (trans-er-let*
              ((args (translate11-lst (cdr x) t bindings known-stobjs
                                      nil flet-alist x ctx wrld state-vars)))
              (trans-value (fcons-term lambda-fn args))))
            (t
             (translate11-call x lambda-fn (cdr x) stobjs-out stobjs-out2
                               bindings known-stobjs
                               (msg "a call of FLET-bound function ~x0"
                                    (car x))
                               flet-alist ctx wrld state-vars)))))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member-eq (car x) '(defun defmacro in-package progn defpkg
                               with-guard-checking-event)))
    (trans-er+ x ctx
               "We do not permit the use of ~x0 inside of code to be executed ~
                by Common Lisp because its Common Lisp meaning differs from ~
                its ACL2 meaning.~@1"
               (car x)
               (cond ((eq (car x) 'with-guard-checking-event)
                      (msg "  Consider using ~x0 instead."
                           'with-guard-checking-error-triple))
                     (t ""))))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member-eq (car x)

; The following list should contain every symbol listed in
; primitive-event-macros for which the error message below applies.  We keep
; both lists alphabetical to make it convenient to compare them.  For
; efficiency, we may omit those that will ultimately expand to calls of table
; (or any other symbol in the list below).  We also omit those handled in the
; previous case, above, such as defun.

                    '(
                      #+:non-standard-analysis defthm-std
                      #+:non-standard-analysis defun-std
                      add-custom-keyword-hint
                      add-include-book-dir ; definition explains inclusion
                      add-include-book-dir! ; definition explains inclusion
                      add-match-free-override
                      certify-book
                      comp
                      defattach
                      defaxiom
                      defchoose
                      defconst
                      deflabel
                      defstobj defabsstobj
                      deftheory
                      defthm
                      defuns
                      delete-include-book-dir ; definition explains inclusion
                      delete-include-book-dir! ; definition explains inclusion
                      encapsulate
                      in-arithmetic-theory
                      in-theory
                      include-book
                      local ; note: not in (primitive-event-macros)
                      make-event ; note: not in (primitive-event-macros)
                      mutual-recursion
                      progn!
                      push-untouchable
                      regenerate-tau-database
                      remove-untouchable
                      reset-prehistory
                      set-body
                      set-override-hints-macro
                      table
                      theory-invariant
                      value-triple
                      verify-guards
                      with-output ; note: not in (primitive-event-macros)
                      with-prover-step-limit ; not in (primitive-event-macros)
                      verify-termination-boot-strap
                      )))
    (trans-er+ x ctx
               "We do not permit the use of ~x0 inside of code to be executed ~
                by Common Lisp because its Common Lisp runtime value and ~
                effect differs from its ACL2 meaning.~@1"
               (car x)
               (cond ((eq (car x) 'with-output)
                      (msg "  Consider using ~x0 instead."
                           'with-output!))
                     (t ""))))
   ((and (eq (car x) 'pargs)
         (true-listp x)
         (member (length x) '(2 3))

; Notice that we are restricting this error case to a pargs that is
; syntactically well-formed, in the sense that if this pargs has one or two
; arguments, then the form argument is a function call.  The rest of the
; well-formedness checking will be done during macro expansion of pargs; by
; making the above restriction, we avoid the possibility that the error message
; below is confusing.

         (let ((form (car (last x)))) ; should be a function call
           (or flet-alist
               (not (and (consp form)
                         (symbolp (car form))
                         (function-symbolp (car form) wrld))))))
    (cond
     (flet-alist

; It may be fine to have flet-bound functions as in:

; (defun g ()
;   (flet ((foo (x) (+ x x)))
;     (pargs (h (foo 3)))))

; But we haven't thought through whether closures really respect superior FLET
; bindings, so for now we simply punt.

      (trans-er+ x ctx
                 "~x0 may not be called in the scope of ~x1.  If you want ~
                  support for that capability, please contact the ACL2 ~
                  implementors."
                 'pargs
                 'flet))
     (t
      (let ((form (car (last x))))
        (trans-er+ x ctx
                   "~x0 may only be used when its form argument is a function ~
                    call, unlike the argument ~x1.~@2  See :DOC pargs."
                   'pargs
                   form
                   (if (and (consp form)
                            (symbolp (car form))
                            (getpropc (car form) 'macro-body nil wrld))
                       (list "  Note that ~x0 is a macro, not a function ~
                              symbol."
                             (cons #\0 (car form)))
                     ""))))))
   ((eq (car x) 'check-vars-not-free) ; optimization; see check-vars-not-free

; Warning: Keep this in sync with the code for check-vars-not-free.

    (cond ((not (equal (length x) 3))
           (trans-er+ x ctx
                      "CHECK-VARS-NOT-FREE requires exactly two arguments."))
          ((null (cadr x)) ; optimization for perhaps a common case
           (translate11 (caddr x) stobjs-out bindings
                        known-stobjs flet-alist x ctx wrld
                        state-vars))
          ((not (symbol-listp (cadr x)))
           (trans-er+ x ctx
                      "CHECK-VARS-NOT-FREE requires its first argument to be ~
                       a true-list of symbols."))
          (t
           (trans-er-let*
            ((ans (translate11 (caddr x) stobjs-out bindings
                               known-stobjs flet-alist x ctx wrld
                               state-vars)))
            (let ((msg (check-vars-not-free-test (cadr x) ans)))
              (cond
               ((not (eq msg t))
                (trans-er+ x ctx
                           "CHECK-VARS-NOT-FREE failed:~|~@0"
                           msg))
               (t (trans-value ans))))))))
   ((eq (car x) 'translate-and-test)
    (cond ((not (equal (length x) 3))
           (trans-er+ x ctx
                      "TRANSLATE-AND-TEST requires exactly two arguments."))
          (t (trans-er-let*
              ((ans (translate11 (caddr x) stobjs-out bindings
                                 known-stobjs flet-alist x ctx wrld
                                 state-vars)))

; The next mv-let is spiritually just a continuation of the trans-er-let*
; above, as though to say "and let test-term be (translate11 (list ...)...)"
; except that we do not want to touch the current setting of bindings nor
; do we wish to permit the current bindings to play a role in the translation
; of the test.

              (mv-let
               (test-erp test-term test-bindings)
               (translate11 (list (cadr x) 'form)
                            '(nil) nil known-stobjs flet-alist x ctx wrld
                            state-vars)
               (declare (ignore test-bindings))
               (cond
                (test-erp (mv test-erp test-term bindings))
                (t
                 (mv-let (erp msg)
                         (ev-w test-term
                               (list (cons 'form ans)
                                     (cons 'world wrld))
                               wrld
                               nil ; user-stobj-alist
                               (access state-vars state-vars :safe-mode)
                               (gc-off1 (access state-vars state-vars
                                                :guard-checking-on))
                               nil

; We are conservative here, using nil for the following AOK argument in case
; the intended test-term is to be considered in the current theory, without
; attachments.

                               nil)
                         (cond
                          (erp
                           (trans-er+ x ctx
                                      "The attempt to evaluate the ~
                                       TRANSLATE-AND-TEST test, ~x0, when ~
                                       FORM is ~x1, failed with the ~
                                       evaluation error:~%~%``~@2''"
                                      (cadr x) ans msg))
                          ((or (consp msg)
                               (stringp msg))
                           (trans-er ctx "~@0" msg))
                          (t (trans-value ans)))))))))))
   ((eq (car x) 'with-local-stobj)

; Even if stobjs-out is t, we do not let normal macroexpansion handle
; with-local-stobj, because we want to make sure that we are dealing with a
; stobj.  Otherwise, the raw lisp code will bind a bogus live stobj variable;
; although not particularly harmful, that will give rise to an inappropriate
; compiler warning about not declaring the variable unused.

    (mv-let (erp st mv-let-form creator)
            (parse-with-local-stobj (cdr x))
            (cond
             (erp
              (trans-er ctx
                        "Ill-formed with-local-stobj form, ~x0.  ~
                         See :DOC with-local-stobj."
                        x))
             ((assoc-eq :stobjs-out bindings)

; We need to disallow the use of ev etc. for with-local-stobj, because the
; latching mechanism assumes that all stobjs are global, i.e., in the
; user-stobj-alist.

              (trans-er ctx
                        "Calls of with-local-stobj, such as ~x0, cannot be ~
                         evaluated directly, as in the top-level loop.  ~
                         See :DOC with-local-stobj and see :DOC top-level."
                        x))
             ((untouchable-fn-p creator
                                wrld
                                (access state-vars state-vars
                                        :temp-touchable-fns))
              (trans-er ctx
                        "Illegal with-local-stobj form~@0~|~%  ~y1:~%the stobj ~
                         creator function ~x2 is untouchable.  See :DOC ~
                         remove-untouchable.~@3"
                        (if (eq creator 'create-state)
                            " (perhaps expanded from a corresponding ~
                             with-local-state form),"
                          ",")
                        x
                        creator
                        (if (eq creator 'create-state)
                            "  Also see :DOC with-local-state, which ~
                             describes how to get around this restriction and ~
                             when it may be appropriate to do so."
                          "")))
             ((and st
                   (if (eq st 'state)
                       (eq creator 'create-state)
                     (eq st (stobj-creatorp creator wrld))))
              (translate11-mv-let mv-let-form nil stobjs-out bindings
                                  known-stobjs st creator flet-alist ctx wrld
                                  state-vars))
             (t
              (let ((actual-creator (get-stobj-creator st wrld)))
                (cond
                 (actual-creator ; then st is a stobj
                  (trans-er ctx
                            "Illegal with-local-stobj form, ~x0.  The creator ~
                             function for stobj ~x1 is ~x2, but ~@3.  See ~
                             :DOC with-local-stobj."
                            x st actual-creator
                            (cond ((cdddr x) ; wrong creator was supplied
                                   (msg "the function ~x0 was supplied instead"
                                        creator))
                                  (t
                                   (msg "the creator was computed to be ~x0, ~
                                         so you will need to supply the ~
                                         creator explicitly for your call of ~
                                         ~x1"
                                        creator
                                        'with-local-stobj)))))
                 (t ; st is not a stobj
                  (trans-er ctx
                            "Illegal with-local-stobj form, ~x0.  The first ~
                             argument must be the name of a stobj, but ~x1 is ~
                             not.  See :DOC with-local-stobj."
                            x st))))))))
   ((and (assoc-eq (car x) *ttag-fns-and-macros*)
         (not (ttag wrld))
         (not (global-val 'boot-strap-flg wrld)))
    (trans-er+ x ctx
               "The ~x0 ~s1 cannot be called unless a trust tag is in effect. ~
                ~ See :DOC defttag.~@2"
               (car x)
               (if (getpropc (car x) 'macro-body nil wrld)
                   "macro"
                 "function")
               (or (cdr (assoc-eq (car x) *ttag-fns-and-macros*))
                   "")))
   ((and (eq (car x) 'stobj-let)
         (not (eq stobjs-out t))) ; else let stobj-let simply macroexpand

; Keep this in sync with the definition of the stobj-let macro.  We use the
; following running example:

; (stobj-let
;  ((st1 (fld1 st+))
;   (st2 (fld2 st+) update-fld2)
;   (st3 (fld3i 4 st+)))
;  (st1)                      ; PRODUCER-VARS, below
;  (producer st1 u st2 v st3) ; PRODUCER, below
;  (consumer st+ u x y v w)   ; CONSUMER, below
;  )
; ==>
; (let ((st1 (fld1 st+))                     ; sti are BOUND-VARS, below
;       (st2 (fld2 st+) update-fld2)         ; cadrs are ACTUALS, below
;       (st3 (fld3i 4 st+)))                 ; st+ is STOBJ, below
;   (let ((st1 (producer st1 u st2 v st3)))  ; BODY2
;     (declare (ignorable st1))
;     (let ((st+ (update-fld1 st1 st+)))     ; BODY1
;       (consumer st+ u x y v w))))

    (mv-let
     (msg bound-vars actuals stobj producer-vars producer updaters
          corresp-accessor-fns consumer)
     (parse-stobj-let x)
     (cond
      (msg (trans-er ctx "~@0" msg))
      ((assoc-eq :stobjs-out bindings)

; We need to disallow the use of ev etc. for stobj-let, because the latching
; mechanism assumes that all stobjs are global, i.e., in the user-stobj-alist.

       (trans-er ctx
                 "Calls of stobj-let, such as ~x0, cannot be evaluated ~
                  directly, as in the top-level loop."
                 x))
      (t
       (let ((msg (chk-stobj-let bound-vars actuals stobj updaters
                                 corresp-accessor-fns known-stobjs wrld)))
         (cond
          (msg (trans-er ctx
                         "~@0"
                         (illegal-stobj-let-msg msg x)))
          (t
           (let* ((new-known-stobjs (if (eq known-stobjs t)
                                        t
                                      (union-eq bound-vars known-stobjs)))
                  (guarded-producer
                   `(check-vars-not-free (,stobj) ,producer))
                  (guarded-consumer
                   `(check-vars-not-free ,bound-vars ,consumer))
                  (letp (null (cdr producer-vars)))
                  (updater-bindings (pairlis-x1 stobj
                                                (pairlis-x2 updaters nil)))
                  (body1 `(let* ,updater-bindings
                            ,guarded-consumer))
                  (body2 (cond (letp `(let ((,(car producer-vars)
                                             ,guarded-producer))
                                        (declare (ignorable ,@producer-vars))
                                        ,body1))
                               (t `(mv-let ,producer-vars
                                           ,guarded-producer
                                           (declare (ignorable ,@producer-vars))
                                           ,body1)))))
             (trans-er-let*
              ((tactuals
                (translate-stobj-calls actuals 3 bindings new-known-stobjs
                                       flet-alist x ctx wrld state-vars))
               (tupdaters
                (translate-stobj-calls updaters 4 bindings new-known-stobjs
                                       flet-alist x ctx wrld state-vars))
               (tconsumer
                (translate11 guarded-consumer stobjs-out bindings known-stobjs
                             flet-alist x ctx wrld state-vars))
               (tbody1 (translate11-let* body1 tconsumer tupdaters stobjs-out
                                         bindings known-stobjs flet-alist ctx
                                         wrld state-vars))
               (tbody2 (cond (letp (translate11-let body2 tbody1 nil
                                                    stobjs-out
                                                    bindings new-known-stobjs
                                                    flet-alist ctx wrld
                                                    state-vars))
                             (t (translate11-mv-let body2 tbody1 stobjs-out
                                                    bindings new-known-stobjs
                                                    nil nil ; local-stobj args
                                                    flet-alist ctx wrld
                                                    state-vars)))))
              (let ((actual-stobjs-out
                     (translate-deref stobjs-out bindings))
                    (no-dups-exprs
                     (no-duplicatesp-checks-for-stobj-let-actuals actuals
                                                                  nil))
                    (producer-stobjs
                     (collect-non-x
                      nil
                      (compute-stobj-flags producer-vars known-stobjs wrld))))
                (cond
                 ((and updaters

; It may be impossible for actual-stobjs-out to be an atom here (presumably
; :stobjs-out or a function symbol).  But we cover that case, albeit with a
; potentially mysterious error message.

                       (or (not (consp actual-stobjs-out))
                           (not (member-eq stobj actual-stobjs-out))))
                  (let ((stobjs-returned
                         (and (consp actual-stobjs-out)
                              (collect-non-x nil actual-stobjs-out))))
                    (trans-er+ x ctx
                               "A STOBJ-LET form has been encountered that ~
                                specifies (with its list of producer ~
                                variables) ~#1~[a call~/calls~] of stobj ~
                                updater~#2~[~/s~] ~&2 of ~x0.  It is ~
                                therefore a requirement that ~x0 be among the ~
                                outputs of the STOBJ-LET, but it is not.  The ~
                                STOBJ-LET returns ~#3~[no single-threaded ~
                                objects~/the single-threaded object ~&4~/the ~
                                single-threaded objects ~&4~/an undetermined ~
                                output signature in this context~].  See :DOC ~
                                stobj-let."
                               stobj
                               updaters
                               (remove-duplicates-eq (strip-cars updaters))
                               (if (consp actual-stobjs-out)
                                   (zero-one-or-more stobjs-returned)
                                 3)
                               stobjs-returned)))
                 ((and (atom actual-stobjs-out) ; impossible?
                       (set-difference-eq producer-stobjs bound-vars))
                  (trans-er+ x ctx
                             "A STOBJ-LET form has been encountered that ~
                              specifies stobj producer variable~#0~[~/s~] ~&0 ~
                              that cannot be determined to be returned by ~
                              that STOBJ-LET form, that is, by its consumer ~
                              form.  See :DOC stobj-let."
                             (set-difference-eq producer-stobjs bound-vars)))
                 ((set-difference-eq
                   (set-difference-eq producer-stobjs bound-vars)
                   actual-stobjs-out)
                  (trans-er+ x ctx
                             "A STOBJ-LET form has been encountered that ~
                              specifies stobj producer variable~#0~[ ~&0 that ~
                              is~/s ~&0~ that are~] not returned by that ~
                              STOBJ-LET form, that is, not returned by its ~
                              consumer form.  See :DOC stobj-let."
                             (set-difference-eq
                              (set-difference-eq producer-stobjs bound-vars)
                              actual-stobjs-out)))
                 (t
                  (trans-er-let*
                   ((val
                     (translate11-let `(let ,(pairlis$ bound-vars
                                                       (pairlis$ actuals nil))
                                         (declare (ignorable ,@bound-vars))
                                         ,body2)
                                      tbody2 tactuals stobjs-out bindings
                                      known-stobjs flet-alist ctx wrld
                                      state-vars)))
                   (cond (no-dups-exprs
                          (trans-er-let*
                           ((chk (translate11 (cons 'and no-dups-exprs)
                                              '(nil) bindings known-stobjs
                                              flet-alist cform ctx wrld
                                              state-vars)))
                           (trans-value (prog2$-call chk val))))
                         (t (trans-value val))))))))))))))))
   ((getpropc (car x) 'macro-body nil wrld)
    (cond
     ((and (eq stobjs-out :stobjs-out)
           (member-eq (car x) '(pand por pargs plet))
           (eq (access state-vars state-vars :parallel-execution-enabled)
               t))
      (trans-er ctx
                "Parallel evaluation is enabled, but is not implemented for ~
                 calls of parallelism primitives (~&0) made directly in the ~
                 ACL2 top-level loop, as opposed to being made inside a ~
                 function definition.  The call ~x1 is thus illegal.  To ~
                 allow such calls to be evaluated (but without parallelism), ~
                 either evaluate ~x2 or use the macro top-level.  See :DOC ~
                 parallelism-at-the-top-level and :DOC ~
                 set-parallel-execution."
                '(pand por pargs plet)
                x
                '(set-parallel-execution :bogus-parallelism-ok)))
     ((untouchable-fn-p (car x)
                        wrld
                        (access state-vars state-vars
                                :temp-touchable-fns))

; If this error burns you during system maintenance, you can subvert our
; security by setting untouchables to nil in raw Lisp:

; (setf (cadr (assoc 'global-value
;                    (get 'untouchable-fns *current-acl2-world-key*)))
;       nil)

      (trans-er+ x ctx
                 "It is illegal to call ~x0 because it has been placed on ~
                  untouchable-fns."
                 (car x)))
     ((and (eq (car x) 'ld) ; next check if we're in a definition body
           (not (or (eq stobjs-out t)
                    (assoc-eq :stobjs-out bindings)))

; Here we enforce the requirement that a call of LD in a user definition body
; must specify :ld-user-stobjs-modified-warning.  This requirement forces the
; tool writer who calls LD to confront the question of whether or not
; "user-stobjs-modified" warnings are appropriate.

           (not (global-val 'boot-strap-flg wrld))
           (true-listp x) ; else macroexpansion will disallow this anyhow
           (not (member-eq :ld-user-stobjs-modified-warning (cdr x))))
      (trans-er+ x ctx
                 "It is illegal to call ~x0 in a function body without ~
                  specifying a value for :ld-user-stobjs-modified-warning.  ~
                  See :DOC user-stobjs-modified-warnings."
                 (car x)))
     (t
      (mv-let
       (erp expansion)
       (macroexpand1-cmp x ctx wrld state-vars)
       (cond
        (erp (mv erp expansion bindings))
        (t (translate11 expansion stobjs-out bindings known-stobjs flet-alist x
                        ctx wrld state-vars)))))))
   ((eq (car x) 'let)
    (translate11-let x nil nil stobjs-out bindings known-stobjs
                     flet-alist ctx wrld state-vars))
   ((eq (car x) 'flet) ; (flet bindings form)
    (translate11-flet x stobjs-out bindings known-stobjs flet-alist ctx
                      wrld state-vars))
   ((and (not (eq stobjs-out t))
         (null (cdr x)) ; optimization
         (stobj-creatorp (car x) wrld))
    (trans-er+ x ctx
               "It is illegal to call ~x0 in this context because it is a ~
                stobj creator.  Stobj creators cannot be called directly ~
                except in theorems.  If you did not explicitly call a stobj ~
                creator, then this error is probably due to an attempt to ~
                evaluate a with-local-stobj form directly in the top-level ~
                loop.  Such forms are only allowed in the bodies of functions ~
                and in theorems.  Also see :DOC with-local-stobj."
               (car x)))
   ((equal (arity (car x) wrld) (length (cdr x)))
    (cond ((untouchable-fn-p (car x)
                             wrld
                             (access state-vars state-vars
                                     :temp-touchable-fns))
           (trans-er+ x ctx
                      "It is illegal to call ~x0 because it has been placed ~
                       on untouchable-fns."
                      (car x)))
          ((eq (car x) 'if)
           (cond
            ((stobjp (cadr x) known-stobjs wrld)
             (trans-er+ x ctx
                        "It is illegal to test on a single-threaded object ~
                         such as ~x0."
                        (cadr x)))

; Because (cadr x) has not yet been translated, we do not really know it is not
; a stobj!  It could be a macro call that expands to a stobj.'  The error
; message above is just to be helpful.  An accurate check is made below.

            (t
             (trans-er-let*
              ((arg1 (translate11 (cadr x)
                                  (if (eq stobjs-out t)
                                      t
                                    '(nil))
                                  bindings known-stobjs
                                  flet-alist x ctx wrld state-vars)))
              (mv-let
               (erp2 arg2 bindings2)
               (trans-er-let*
                ((arg2 (translate11 (caddr x)
                                    stobjs-out bindings known-stobjs
                                    flet-alist x ctx wrld state-vars)))
                (trans-value arg2))
               (cond
                (erp2
                 (cond
                  ((eq bindings2 :UNKNOWN-BINDINGS)
                   (mv-let
                    (erp3 arg3 bindings)
                    (translate11 (cadddr x)
                                 stobjs-out bindings known-stobjs
                                 flet-alist x ctx wrld state-vars)
                    (cond
                     (erp3 (mv erp2 arg2 bindings2))
                     (t (trans-er-let*
                         ((arg2 (translate11 (caddr x)
                                             stobjs-out bindings known-stobjs
                                             flet-alist x ctx wrld state-vars)))
                         (trans-value (fcons-term* 'if arg1 arg2 arg3)))))))
                  (t (mv erp2 arg2 bindings2))))
                (t
                 (let ((bindings bindings2))
                   (trans-er-let*
                    ((arg3 (translate11 (cadddr x)
                                        stobjs-out bindings known-stobjs
                                        flet-alist x ctx wrld state-vars)))
                    (trans-value (fcons-term* 'if arg1 arg2 arg3)))))))))))
          ((eq (car x) 'synp)

; Synp is a bit odd.  We store the quotation of the term to be evaluated in the
; third arg of the synp form.  We store the quotation so that ACL2 will not see
; the term as a potential induction candidate.  (Eric Smith first pointed out
; this issue.)  This, however forces us to treat synp specially here in order
; to translate the term to be evaluated and thereby get a proper ACL2 term.
; Without this special treatment (cadr x), for instance, would be left alone
; whereas it needs to be translated into (car (cdr x)).

; This mangling of the third arg of synp is sound because synp always returns
; t.

; Robert Krug has mentioned the possibility that the known-stobjs below could
; perhaps be t.  This would allow a function called by synp to use, although
; not change, stobjs.  If this is changed, change the references to stobjs in
; the documentation for syntaxp and bind-free as appropriate.  But before
; making such a change, consider this: no live user-defined stobj will ever
; appear in the unifying substitution that binds variables in the evg of
; (cadddr x).  So it seems that such a relaxation would not be of much value.

           (cond ((not (eq stobjs-out t))
                  (trans-er ctx
                            "A call to synp is not allowed here.  This ~
                             call may have come from the use of syntaxp ~
                             or bind-free within a function definition ~
                             since these two macros expand into calls to ~
                             synp.  The form we were translating when we ~
                             encountered this problem is ~x0.  If you ~
                             believe this error message is itself in error ~
                             or that we have been too restrictive, please ~
                             contact the maintainers of ACL2."
                            x))
                 ((eql (length x) 4)
                  (mv-let
                   (erp val bindings)
                   (trans-er-let*
                    ((quoted-vars (translate11 (cadr x)
                                               '(nil) ; stobjs-out
                                               bindings
                                               '(state) ; known-stobjs
                                               flet-alist x ctx wrld state-vars))
                     (quoted-user-form (translate11 (caddr x)
                                                    '(nil) ; stobjs-out
                                                    bindings
                                                    '(state) ; known-stobjs
                                                    flet-alist x ctx wrld
                                                    state-vars))
                     (quoted-term (translate11 (cadddr x)
                                               '(nil) ; stobjs-out
                                               bindings
                                               '(state) ; known-stobjs
                                               flet-alist x ctx wrld state-vars)))
                    (let ((quoted-term (if (quotep quoted-term)
                                           quoted-term
                                         (sublis-var nil quoted-term))))
                      (cond ((quotep quoted-term)
                             (trans-er-let*
                              ((term-to-be-evaluated
                                (translate11 (cadr quoted-term)
                                             '(nil) ; stobjs-out
                                             bindings
                                             '(state) ; known-stobjs
                                             flet-alist x ctx wrld state-vars)))
                              (let ((quoted-vars (if (quotep quoted-vars)
                                                     quoted-vars
                                                   (sublis-var nil quoted-vars)))
                                    (quoted-user-form (if (quotep quoted-user-form)
                                                          quoted-user-form
                                                        (sublis-var nil
                                                                    quoted-user-form))))
                                (cond ((and (quotep quoted-vars)
                                            (quotep quoted-user-form))
                                       (trans-value
                                        (fcons-term* 'synp quoted-vars
                                                     quoted-user-form
                                                     (kwote
                                                      term-to-be-evaluated))))
                                      (t (trans-er ctx
                                                   *synp-trans-err-string*
                                                   x))))))
                            (t
                             (trans-er ctx
                                       *synp-trans-err-string*
                                       x)))))
                   (cond (erp
                          (let ((quoted-user-form (caddr x)))
                            (case-match quoted-user-form
                              (('QUOTE ('SYNTAXP form))
                               (mv erp
                                   (msg "The form ~x0, from a ~x1 hypothesis, ~
                                         is not suitable for evaluation in an ~
                                         environment where its variables are ~
                                         bound to terms.  See :DOC ~x1.  Here ~
                                         is further explanation:~|~t2~@3"
                                        form 'syntaxp 5 val)
                                   bindings))
                              (& (mv erp val bindings)))))
                         (t (mv erp val bindings)))))
                 (t
                  (trans-er ctx
                            *synp-trans-err-string*
                            x))))
          ((eq stobjs-out t)
           (trans-er-let*
            ((args (translate11-lst (cdr x) t bindings known-stobjs
                                    nil flet-alist x ctx wrld state-vars)))
            (trans-value (fcons-term (car x) args))))
          ((eq (car x) 'mv-list) ; and stobjs-out is not t
           (trans-er-let*
            ((arg1 (translate11 (cadr x)
                                stobjs-out bindings known-stobjs
                                flet-alist x ctx wrld state-vars)))
            (cond ((not (and (quotep arg1)
                             (integerp (unquote arg1))
                             (<= 2 (unquote arg1))))
                   (trans-er ctx
                             "A call of ~x0 can only be made when the first ~
                              argument is explicitly an integer that is at ~
                              least 2.  The call ~x1 is thus illegal."
                             'mv-list x))
                  (t
                   (trans-er-let*
                    ((arg2 (translate11 (caddr x)
                                        (make-list (unquote arg1)
                                                   :initial-element nil)
                                        bindings known-stobjs
                                        flet-alist x ctx wrld state-vars)))
                    (trans-value (fcons-term* 'mv-list arg1 arg2)))))))
          ((stobj-field-fn-of-stobj-type-p
            (car x) wrld) ; and stobjs-out is not t
           (trans-er+ x ctx
                      "It is illegal to call ~x0 because it is a stobj ~
                       updater or accessor for a field of stobj type.  For a ~
                       way to generate such a call, see :DOC stobj-let."
                      (car x)))
          ((eq (car x) 'return-last) ; and stobjs-out is not t
           (let* ((arg1 (nth 1 x))
                  (arg2 (nth 2 x))
                  (arg3 (nth 3 x))
                  (key (and (consp arg1)
                            (eq (car arg1) 'quote)
                            (consp (cdr arg1))
                            (cadr arg1)))
                  (keyp (and (symbolp key) key)))
             (trans-er-let*
              ((targ1 (translate11 arg1
                                   '(nil) bindings known-stobjs
                                   flet-alist x ctx wrld state-vars)))
              (cond
               ((and keyp (not (equal targ1 arg1))) ; an optional extra check
                (trans-er ctx
                          "Implementation error: We have thought that a ~
                           quotep must translate to itself, but ~x0 did not!"
                          arg1))
               ((eq key 'mbe1-raw)

; We need to know that the two arguments of mbe1 have the same signature.  If
; for example we have (mv-let (x y) (mbe1 <exec-form> <logic-form>)), but
; <exec-form> has signature *, then Common Lisp will get confused during
; evaluation.  This signature requirement is enforced by the trans-er-let*
; bindings below.

; At one time we disallowed the use of mbe inside a non-trivial encapsulate
; when translating for execution (stobjs-out not equal to t).  To see why, see
; the example in the comment near the top of :DOC note-3-4.  However, we
; subsequently disallowed guard verification for functions defined non-locally
; inside an encapsulate (see :DOC note-4-0), which is the proper fix for this
; issue.  What then is this issue?  The issue is that we need to be able to
; trust guard verification; evaluating the :exec branch of an mbe is just a
; special case.

                (trans-er-let*
                 ((targ2 (translate11 arg2
                                      (if (inside-defabsstobj wrld)
                                          t
                                        stobjs-out)
                                      bindings known-stobjs
                                      flet-alist x ctx wrld state-vars))
                  (targ3 (translate11 arg3 stobjs-out bindings known-stobjs
                                      flet-alist x ctx wrld state-vars)))
                 (trans-value
                  (fcons-term* 'return-last targ1 targ2 targ3))))
               ((and
                 (eq key 'ec-call1-raw)
                 (not
                  (and
                   (consp arg3)
                   (true-listp arg3)
                   (and
                    (symbolp (car arg3))
                    (let ((fn (if (function-symbolp (car arg3) wrld)
                                  (car arg3)
                                (corresponding-inline-fn (car arg3) wrld))))
                      (and fn
                           (not (member-eq fn *ec-call-bad-ops*))))))))
                (trans-er ctx
                          "The argument ~x0 is illegal for ~x2, because ~@1.  ~
                           A call of ~x2 must only be made on an argument of ~
                           the form (FN ...), where FN is a known function ~
                           symbol of the current ACL2 world not belonging to ~
                           the list that is the value of the constant ~x3, or ~
                           is a macro expanding in a certain direct way (as ~
                           with defun-inline) to a call of FN$INLINE (i.e., ~
                           the result of adding suffix \"$INLINE\" to the ~
                           symbol-name of FN).  See :DOC ec-call."
                          (car (last x))
                          (let* ((fn0 (and (consp arg3)
                                           (car arg3)))
                                 (fn (and fn0
                                          (symbolp fn0)
                                          (if (function-symbolp fn0 wrld)
                                              fn0
                                            (corresponding-inline-fn fn0
                                                                     wrld)))))
                            (cond ((not (and fn0
                                             (true-listp arg3)))
                                   (msg "~x0 does not have the form of a ~
                                         function call"
                                        arg3))
                                  ((not (symbolp fn0))
                                   (msg "~x0 is not a symbol" fn0))
                                  ((member-eq fn *ec-call-bad-ops*)
                                   (msg "~x0 belongs to ~x1"
                                        fn
                                        '*ec-call-bad-ops*))
                                  ((eq (getpropc fn0 'macro-args t wrld)
                                       t)

; At this point we know that fn is nil and fn0 is not nil.  So
; (corresponding-inline-fn fn0 wrld) is nil.  So fn0 is not a function symbol.
; From the test just above we also know that fn0 is not a macro.

                                   (msg "~x0 is not defined"
                                        fn0))
                                  (t (msg "~x0 is a macro, not a function ~
                                           symbol~@1"
                                          fn0
                                          (let ((sym (deref-macro-name
                                                      fn0
                                                      (macro-aliases wrld))))
                                            (cond
                                             ((eq sym fn0) "")
                                             (t
                                              (msg ".  Note that ~x0 is a ~
                                                    macro-alias for ~x1 (see ~
                                                    :DOC ~
                                                    macro-aliases-table), so ~
                                                    a solution might be to ~
                                                    replace ~x0 by ~x1"
                                                   fn0 sym))))))))
                          'ec-call '*ec-call-bad-ops*))
               ((and
                 (eq key 'with-guard-checking1-raw)
                 (or (not (case-match arg2
                            (('chk-with-guard-checking-arg &) t)
                            (& nil)))
                     (not (case-match arg3
                            (('translate-and-test gate form)
                             (equal gate (with-guard-checking-gate form)))
                            (& nil))))
                 (not (global-val 'boot-strap-flg
                                  wrld)) ; see ev-rec-return-last
                 (not (ttag wrld)))
                (trans-er+? cform x ctx
                            "The form ~x0 is essentially a call of ~x1, but ~
                             without certain checks performed.  This is ~
                             illegal unless there is an active trust tag; see ~
                             :DOC defttag.  To avoid this error without use ~
                             of a trust tag, call ~x1 directly."
                            x 'with-guard-checking))
               ((and keyp
                     (let ((val
                            (or (return-last-lookup key wrld)
                                (and (global-val 'boot-strap-flg wrld)
                                     (cdr (assoc-eq
                                           key
                                           *initial-return-last-table*))))))
                       (or (null val)
                           (and (consp val) ; see chk-return-last-entry
                                (eq stobjs-out :stobjs-out)))))

; In an early implementation of return-last, we insisted that keyp be true.  But
; when we attempted to update the "GL" work of Sol Swords to use return-last,
; we encountered the creation of symbolic terms (presumably for some sort of
; meta reasoning) for which the first argument was not quoted.  Rather than try
; to understand whether this was necessary, we decided that others might also
; want to write meta-level functions that cons up return-last terms without a
; quoted first argument; and since it is easy to support that, we do so.

                (cond
                 ((not (or (return-last-lookup key wrld)
                           (and (global-val 'boot-strap-flg wrld)
                                (cdr (assoc-eq key
                                               *initial-return-last-table*)))))
                  (trans-er ctx
                            "The symbol ~x0 is specified in the first ~
                             argument of the form ~x1.  But ~x0 is not ~
                             associated in the table ~x2 with a non-nil ~
                             value.  See :DOC return-last."
                            key x 'return-last-table))
                 (t
                  (trans-er ctx
                            "Illegal call, ~x0: the association of ~x1 with ~
                             the symbol ~x2 has been restricted to avoid ~
                             top-level evaluation of such calls of ~x3.  See ~
                             :DOC return-last.  Also consider placing the ~
                             offending call inside a call of ~x4; see :DOC ~
                             ~x4."
                            x key
                            (car (return-last-lookup key wrld))
                            'return-last 'top-level))))
               (t
                (mv-let
                 (erp targ2 targ2-bindings)
                 (translate11 arg2 '(nil) bindings known-stobjs flet-alist x
                              ctx wrld state-vars)
                 (declare (ignore targ2-bindings))
                 (cond
                  (erp (mv erp targ2 bindings))
                  ((throw-nonexec-error-p1 targ1 targ2 :non-exec nil)
                   (mv-let
                    (erp targ3 targ3-bindings)
                    (translate11
                     arg3
                     t ; stobjs-out
                     bindings
                     nil ; known-stobjs is irrelevant
                     flet-alist x ctx wrld state-vars)
                    (declare (ignore targ3-bindings))
                    (cond
                     (erp (mv erp targ3 bindings))
                     (t (trans-value
                         (fcons-term* 'return-last
                                      targ1 targ2 targ3))))))
                  (t
                   (trans-er-let*
                    ((targ3 (translate11 arg3 stobjs-out bindings known-stobjs
                                         flet-alist x ctx wrld state-vars)))
                    (trans-value
                     (fcons-term* 'return-last
                                  targ1 targ2 targ3)))))))))))
          ((eq (getpropc (car x) 'non-executablep nil wrld)
               t)
           (let ((computed-stobjs-out (compute-stobj-flags (cdr x)
                                                           known-stobjs
                                                           wrld)))
             (trans-er-let*
              ((args (translate11-lst (cdr x) computed-stobjs-out bindings
                                      known-stobjs nil flet-alist x ctx wrld
                                      state-vars)))
              (trans-value (fcons-term (car x) args)))))
          ((and (member-eq (car x) '(makunbound-global put-global))
                (not (eq (access state-vars state-vars :temp-touchable-vars)
                         t))
                (or ; Keep this case in sync with the cond cases below
                 (not (and (consp (cadr x))
                           (eq (car (cadr x)) 'quote)
                           (null (cddr (cadr x)))
                           (symbolp (cadr (cadr x)))))
                 (and (member-eq (cadr (cadr x))
                                 (global-val 'untouchable-vars wrld))
                      (not (member-eq (cadr (cadr x))
                                      (access state-vars state-vars
                                              :temp-touchable-vars))))
                 (and (eq (car x) 'makunbound-global)
                      (or (always-boundp-global (cadr (cadr x)))
                          (member-eq (cadr (cadr x)) *brr-globals*)))

; It is tempting to get the following value of boot-strap from state-vars.  But
; some calls of translate11 supply state-vars using (default-state-vars nil),
; which sets field :boot-strap-flg to nil.  So we pay the price of checking the
; boot-strap-flg directly in wrld.  This seems a relatively minor deal, since
; presumably makunbound-global and put-global are not called by users all that
; often.  If performance becomes an issue, we can try deal with the issue at
; that point.

                 (and (global-val 'boot-strap-flg wrld)
                      (not (or (always-boundp-global (cadr (cadr x)))
                               (member-eq (cadr (cadr x)) *brr-globals*))))))
           (cond ( ; Keep this case the same as its twin above
                  (not (and (consp (cadr x))
                            (eq (car (cadr x)) 'quote)
                            (null (cddr (cadr x)))
                            (symbolp (cadr (cadr x)))))
                  (trans-er+ x ctx
                             "The first arg of ~x0 must be a quoted symbol, ~
                              unlike ~x1.  We make this requirement in ~
                              support of untouchable-vars."
                             (car x) (cadr x)))
                 ( ; Keep this case the same as its twin above
                  (and (member-eq (cadr (cadr x))
                                  (global-val 'untouchable-vars wrld))
                       (not (member-eq (cadr (cadr x))
                                       (access state-vars state-vars
                                               :temp-touchable-vars))))
                  (trans-er ctx
                            "State global variable ~x0 has been rendered ~
                             untouchable and thus may not be directly ~
                             altered, as in ~x1.~@2"
                            (cadr (cadr x))
                            x
                            (let ((set-fn (intern-in-package-of-symbol
                                           (concatenate 'string
                                                        "SET-"
                                                        (symbol-name
                                                         (cadr (cadr x))))
                                           (cadr (cadr x)))))
                              (cond ((function-symbolp set-fn wrld)
                                     (msg "~|There is a function ~x0, which ~
                                           (from the name) may provide the ~
                                           functionality you desire."
                                          set-fn))
                                    (t "")))))
                 ((always-boundp-global (cadr (cadr x)))
                  (trans-er ctx
                            "Built-in state global variables may not be made ~
                             unbound, as in ~x0."
                            x))
                 (t ; (global-val 'boot-strap-flg wrld)
                  (trans-er ctx
                            "State global ~x0 needs to be declared for the ~
                             build by adding it to *initial-global-table*, ~
                             *initial-ld-special-bindings*, or *brr-globals*."
                            (cadr (cadr x))))))
          (t
           (let ((stobjs-out (translate-deref stobjs-out bindings))
                 (stobjs-out2 (let ((temp (translate-deref (car x) bindings)))
                                (cond (temp temp)
                                      (t (stobjs-out (car x) wrld))))))
             (translate11-call x (car x) (cdr x) stobjs-out stobjs-out2
                               bindings known-stobjs (car x) flet-alist
                               ctx wrld state-vars)))))
   ((arity (car x) wrld)
    (trans-er ctx
              "~x0 takes ~#1~[no arguments~/1 argument~/~x2 arguments~] but ~
               in the call ~x3 it is given ~#4~[no arguments~/1 argument~/~x5 ~
               arguments~].  The formal parameters list for ~x0 is ~X67."
              (car x)
              (zero-one-or-more (arity (car x) wrld))
              (arity (car x) wrld)
              x
              (zero-one-or-more (length (cdr x)))
              (length (cdr x))
              (formals (car x) wrld)
              nil))
   ((eq (car x) 'declare)
    (trans-er ctx
              "It is illegal to use DECLARE as a function symbol, as in ~x0.  ~
               DECLARE forms are permitted only in very special places, e.g., ~
               before the bodies of function definitions, LETs, and MV-LETs.  ~
               DECLARE forms are never permitted in places in which their ~
               ``values'' are relevant.  If you already knew this, it is ~
               likely you have made a typographical mistake, e.g., including ~
               the body in the DECLARE form or closing the superior form ~
               before typing the body."
              x))
   (t (let ((syms (macros-and-functions-in-other-packages
                   (car x)
                   wrld)))
        (trans-er+ x ctx
                   "The symbol ~x0 (in package ~x1) has neither a function ~
                    nor macro definition in ACL2.  ~#2~[Please define ~
                    it~@3~/Moreover, this symbol is in the main Lisp package; ~
                    hence, you cannot define it in ACL2.~]  See :DOC ~
                    near-misses."
                   (car x)
                   (symbol-package-name (car x))
                   (if (equal (symbol-package-name (car x))
                              *main-lisp-package-name*)
                       1
                     0)
                   (cond
                    ((null syms) ".")
                    ((null (cdr syms))
                     (msg "; or perhaps you meant ~x0, which has the same ~
                           name but is in a different package."
                          (car syms)))
                    (t
                     (msg "; or perhaps you meant one of the following, each ~
                           with the same name but in a different package: ~v0."
                          syms))))))))

(defun translate11-lst (lst stobjs-out bindings known-stobjs
                            msg flet-alist cform ctx wrld state-vars)

; WARNING: This function's treatment of stobjs-out is unusual:
; (1) stobjs-out must be either t, nil, or list of stobj flags.
;     It CANNOT be a function name (``an unknown'').
; (2) If stobjs-out is nil, it is treated as though it were a list of
;     nils as long as lst.

; If stobjs-out is t, we translate each element of lst (with stobjs-out t)
; and return the resulting list.

; If stobjs-out is not t, it is a list of stobj flags as long as lst.
; We consider each element, x, of list in correspondence with each
; flag, flg.  If flg is nil, we insist that the translation of x
; return one non-stobj result.  If flg is a stobj, we insist that x BE
; flg -- except that x ``is'' a stobj, flg, only if x is flg and x is
; among known-stobjs (with proper treatment of known-stobjs = t).

; Msg is used to describe the form that contains the list, lst, of
; forms being translated.  It is only used if an error is caused when
; some element of lst violates the stobj restrictions of stobjs-out.
; If msg is nil, no allusion to the containing form is made.  If msg
; is a symbol, we describe the containing form as though it were a
; call of that function symbol.  Otherwise, we print msg with ~@ in
; ``the form x is being used, @msg, where a stobj...''.

; The cform argument is a form that provides context -- it is the one to be
; printed by trans-er+ when there isn't another obvious contextual form to
; print.  (Often x carries enough context.)

  (cond ((atom lst) (trans-value nil))
        ((eq stobjs-out t)
         (trans-er-let*
          ((x (translate11 (car lst) t bindings known-stobjs flet-alist
                           (car lst) ctx wrld state-vars))
           (y (translate11-lst (cdr lst) t bindings known-stobjs msg flet-alist
                               cform ctx wrld state-vars)))
          (trans-value (cons x y))))
        ((car stobjs-out)
         (trans-er-let*
          ((x (cond
               ((eq (if (or (eq known-stobjs t)
                            (member-eq (car lst) known-stobjs))
                        (car lst)
                      nil)
                    (car stobjs-out))
                (trans-value (car lst)))

; The following case is checked to allow our use of big-clock-entry to control
; recursion, a violation of our normal rule that state-producing forms are not
; allowed where STATE is expected (except when binding STATE).  We have to look
; for the unexpanded form of the macro f-decrement-big-clock as well.

               ((and (eq (car stobjs-out) 'state)
                     (or (equal (car lst)
                                '(decrement-big-clock state))
                         (equal (car lst)
                                '(f-decrement-big-clock state))))
                (trans-value '(decrement-big-clock state)))
               ((eq (car lst) (car stobjs-out))

; In this case, we failed because (car lst) is not considered a stobj even
; though it has the right name.

                (let ((known-stobjs (collect-non-x nil known-stobjs)))
                  (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object of that name is ~
                              required.  But in the current context, ~
                              ~#3~[there are no declared stobj names~/the ~
                              only declared stobj name is ~&4~/the only ~
                              declared stobj names are ~&4~]."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (cond ((null known-stobjs) 0)
                                   ((null (cdr known-stobjs)) 1)
                                   (t 2))
                             known-stobjs)))
               ((and (symbolp (car lst))
                     (congruent-stobjsp (car lst)
                                        (car stobjs-out)
                                        wrld))
                (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object ~x3 was expected, even ~
                              though these are congruent stobjs.  See :DOC ~
                              defstobj, in particular the discussion of ~
                              congruent stobjs."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (car stobjs-out)))
               (t (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object ~x3 is required.  Note ~
                              that the variable ~x3 is required, not merely a ~
                              term that returns such a single-threaded ~
                              object, so you may need to bind ~x3 with LET; ~
                              see :DOC stobj."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (car stobjs-out)))))
           (y (translate11-lst (cdr lst) (cdr stobjs-out)
                               bindings known-stobjs msg flet-alist cform ctx
                               wrld state-vars)))
          (trans-value (cons x y))))
        (t (trans-er-let*
            ((x (translate11 (car lst) '(nil) bindings known-stobjs flet-alist

; At one time we passed in (car lst) here for cform (to represent the
; surrounding context).  But it makes more sense to preserve cform.  To see
; why, first note that translate11-call passes the call down to
; translate11-lst.  Now suppose we have an error, for example from the
; following where st is a stobj and the call should be (foo x st), not (foo st
; x).
;   (defun bar (x st) (declare (xargs :stobjs st)) (foo st x))
; We want to see the call of foo when told that st is being used where an
; ordinary object is expected.

                             cform ctx wrld state-vars))
             (y (translate11-lst (cdr lst) (cdr stobjs-out)
                                 bindings known-stobjs msg flet-alist cform ctx
                                 wrld state-vars)))
            (trans-value (cons x y))))))

)

(defun translate1-cmp (x stobjs-out bindings known-stobjs ctx w state-vars)

; See also translate1 for a corresponding version that also returns state.

; Stobjs-out should be t, a proper STOBJS-OUT setting, a function symbol, or
; the symbol :stobjs-out.

; Stobjs-out t means we do not enforce mv-let or stobjs restrictions.  A proper
; STOBJS-OUT setting (a list of stobj flags) enforces the given restrictions.
; A function symbol means we enforce the rules and determine the stobjs-out,
; binding the symbol in the returned bindings alist.  In addition, a function
; symbol tells us we are in a definition body and enforce certain rules
; prohibiting calls of functions like DEFUN and IN-PACKAGE.  The symbol
; :stobjs-out -- which is not a function symbol -- has the same meaning as a
; function symbol except that it tells us we are NOT processing a definition
; body.  As is noted below, if the initial stobjs-out is :stobjs-out, bindings
; MUST be '((:stobjs-out . :stobjs-out)) and we use (eq (caar bindings)
; :stobjs-out) to determine that we are not in a definition.

; CAUTION: If you call this function with stobjs-out being a symbol, say fn,
; make sure that

; (a) fn is bound to itself in bindings, e.g., bindings = ((fn . fn)), and
; (b) fn is not an existing function name in w, in particular, it must not have
;     a STOBJS-OUT setting, since that is what we use fn to compute.

; In general, bindings is a list of pairs, one for each fn in the clique being
; introduced, and each is initially bound to itself.  If a function symbol is
; not bound in bindings, its STOBJS-OUT is obtained from w.

; Known-stobjs is either a list of stobj names (but may contain some NIL
; elements, to be ignored; see "slight abuse" comment in
; chk-acceptable-defuns1) or T (meaning, all stobj names in world w).  A name
; is considered a stobj only if it is in this list.

; State-vars is a state-vars record, typically (default-state-vars t) unless
; one does not have state available, and then (default-state-vars nil).

; We return (mv erp transx bindings), where transx is the translation and
; bindings has been modified to bind every fn (ultimately) to a proper
; stobjs-out setting.  A special case is when the initial stobjs-out is
; :stobjs-out; in that case, :stobjs-out is bound in the returned bindings to
; the stobjs-out of the expression being translated.  Use translate-deref to
; recover the bindings.

  (trans-er-let*
   ((result
     (translate11 x stobjs-out bindings known-stobjs nil x ctx w state-vars)))
   (cond ((and bindings
               (null (cdr bindings))
               (symbolp (caar bindings))
               (eq (caar bindings) (cdar bindings)))

; This case can happen because x is the call of a non-executable function.  We
; return a proper stobjs-out value, for example as passed by trans-eval to
; ev-for-trans-eval.  This treatment is necessary for the following example, to
; avoid being unable to determine the output signature of g.

; (defun-nx f (x) x)
; (defun g (x) (f x))

; This treatment is consistent with our use of stobjs-out = (nil) for
; non-executable functions.

          (trans-value result
                       (translate-bind (caar bindings) '(nil) bindings)))
         (t (trans-value result)))))

(defun@par translate1 (x stobjs-out bindings known-stobjs ctx w state)
  (cmp-and-value-to-error-quadruple@par
   (translate1-cmp x stobjs-out bindings known-stobjs ctx w
                   (default-state-vars t))))

(defun collect-programs (names wrld)

; Names is a list of function symbols.  Collect the :program ones.

  (cond ((null names) nil)
        ((programp (car names) wrld)
         (cons (car names) (collect-programs (cdr names) wrld)))
        (t (collect-programs (cdr names) wrld))))

; The following is made more efficient below by eliminating the mutual
; recursion.  This cut the time of a proof using bdds by nearly a factor of 4;
; it was of the form (implies (pred n) (prop n)) where pred has about 1800
; conjuncts.  The culprit was the call(s) of all-fnnames in bdd-rules-alist1, I
; think.

; (mutual-recursion
;
; (defun all-fnnames (term)
;   (cond ((variablep term) nil)
;         ((fquotep term) nil)
;         ((flambda-applicationp term)
;          (union-eq (all-fnnames (lambda-body (ffn-symb term)))
;                    (all-fnnames-lst (fargs term))))
;         (t
;          (add-to-set-eq (ffn-symb term)
;                         (all-fnnames-lst (fargs term))))))
;
; (defun all-fnnames-lst (lst)
;   (cond ((null lst) nil)
;         (t (union-eq (all-fnnames (car lst))
;                      (all-fnnames-lst (cdr lst))))))
; )

(defun all-fnnames1 (flg x acc)

; Flg is nil for all-fnnames, t for all-fnnames-lst.  Note that this includes
; function names occurring in the :exec part of an mbe.  Keep this in sync with
; all-fnnames1-exec.

  (declare (xargs :guard (and (true-listp acc)
                              (cond (flg (pseudo-term-listp x))
                                    (t (pseudo-termp x))))))
  (cond (flg ; x is a list of terms
         (cond ((endp x) acc)
               (t (all-fnnames1 nil (car x)
                                (all-fnnames1 t (cdr x) acc)))))
        ((variablep x) acc)
        ((fquotep x) acc)
        ((flambda-applicationp x)
         (all-fnnames1 nil (lambda-body (ffn-symb x))
                       (all-fnnames1 t (fargs x) acc)))
        (t
         (all-fnnames1 t (fargs x)
                       (add-to-set-eq (ffn-symb x) acc)))))

(defmacro all-fnnames (term)
  `(all-fnnames1 nil ,term nil))

(defmacro all-fnnames-lst (lst)
  `(all-fnnames1 t ,lst nil))

(mutual-recursion

(defun logic-fnsp (term wrld)

; We check for the absence of calls (f ...) in term for which the symbol-class
; of f is :program.  If f is a term (not merely a pseudo-term), that's
; equivalent to saying that every function symbol called in term is in :logic
; mode, i.e., has a 'symbol-class property of :ideal or :common-lisp-compliant.

  (declare (xargs :guard (and (plist-worldp wrld)
                              (pseudo-termp term))))
  (cond ((mbe :logic (atom term)
              :exec (variablep term))
         t)
        ((fquotep term) t)
        ((flambdap (ffn-symb term))
         (and (logic-fnsp (lambda-body (ffn-symb term)) wrld)
              (logic-fns-listp (fargs term) wrld)))
        ((programp (ffn-symb term) wrld) nil)
        (t (logic-fns-listp (fargs term) wrld))))

(defun logic-fns-listp (lst wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (pseudo-term-listp lst))))
  (cond ((endp lst) t)
        (t (and (logic-fnsp (car lst) wrld)
                (logic-fns-listp (cdr lst) wrld)))))
)

(defun logic-termp (x wrld)

; Warning: Checks in rewrite-with-lemma, eval-clause-processor, and
; eval-clause-processor@par check logical-termp by separately checking termp
; and (not (program-termp ...)).  If you change logical-termp, consider whether
; it's also necessary to modify those checks.

  (declare (xargs :guard (plist-worldp-with-formals wrld)))
  (and (termp x wrld)
       (logic-fnsp x wrld)))

(defun logic-term-listp (x w)

; We could define this recursively, but proofs about logical-termp can involve
; program-termp and hence its mutual-recursion nest-mate, program-term-listp.
; So we here we avoid introducing a second recursion.

  (declare (xargs :guard (plist-worldp-with-formals w)))
  (and (term-listp x w)
       (logic-fns-listp x w)))

(defun logic-fns-list-listp (x wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (pseudo-term-list-listp x))))
  (cond ((endp x) t)
        (t (and (logic-fns-listp (car x) wrld)
                (logic-fns-list-listp (cdr x) wrld)))))

(defun logic-term-list-listp (x w)
  (declare (xargs :guard (plist-worldp-with-formals w)))
  (and (term-list-listp x w)
       (logic-fns-list-listp x w)))

(defun translate-cmp (x stobjs-out logic-modep known-stobjs ctx w state-vars)

; See translate.  Here we return a context-message pair; see the Essay on
; Context-message Pairs.  State-vars is a state-vars record, typically
; (default-state-vars t) unless one does not have state available, and then
; (default-state-vars nil).

  (mv-let (erp val bindings)
          (translate1-cmp x stobjs-out nil known-stobjs ctx w state-vars)
          (declare (ignore bindings))
          (cond (erp ; erp is a ctx and val is a msg
                 (mv erp val))
                ((and logic-modep
                      (not (logic-fnsp val w)))
                 (er-cmp ctx
                         "Function symbols of mode :program are not allowed ~
                          in the present context.  Yet, the function ~
                          symbol~#0~[ ~&0 occurs~/s ~&0 occur~] in the ~
                          translation of the form~|~%  ~x1,~%~%which is~|~%  ~
                          ~x2."
                         (collect-programs (all-fnnames val) w)
                         x
                         val))
                (t (value-cmp val)))))

(defun@par translate (x stobjs-out logic-modep known-stobjs ctx w state)

; This is the toplevel entry into translation throughout ACL2,
; excepting translate-bodies, which translates the bodies of
; definitions.  The output of translate is (mv erp transx state).

; Stobjs-out should be
; * t           - to indicate that we are translating only for logical use, as
;                 in theorems etc.  Do NOT use t for defuns, defmacros,
;                 defconst, or other events involving Common Lisp execution.

; * (s1 ... sn) - where each si is either nil or a stobj name (possibly
;                 STATE) to indicate that the mv-let and stobj
;                 restrictions should be enforced AND that x is to have
;                 the indicated stobj signature.  See the Essay on
;                 STOBJS-IN and STOBJS-OUT.

; Logic-modep should be set when we want to ensure that the resulting
; term does not mention any function symbols of defun-mode :program.
; This check is NOT made on-the-fly (in translate1) but as an
; after-the-fact convenience here.

; Known-stobjs is either a list of stobj names (but may contain some NIL
; elements, to be ignored; see "slight abuse" comment in
; chk-acceptable-defuns1) or T (meaning, all stobj names in world w).  A name
; is considered a stobj only if it is in this list.

  (cmp-to-error-triple@par
   (translate-cmp x stobjs-out logic-modep known-stobjs ctx w
                  (default-state-vars t))))

(defun translatable-p (form stobjs-out bindings known-stobjs ctx wrld)
  (mv-let (erp val bindings)
          (translate1-cmp form stobjs-out bindings known-stobjs ctx wrld
                          (default-state-vars nil))
          (declare (ignore val bindings))
          (null erp)))

(defmacro chk-translatable (form shape)
  `(translate-and-test
    (lambda (qform)
      (cond ((translatable-p (cadr qform)
                             ',(cond ((eq shape 'state)
                                      '(state))
                                     (t (cdr shape)))
                             nil t 'chk-translatable
                             world)
             t)
            (t (msg "IO? was given the following body, which fails to ~
                     translate for the expected shape, STATE:~|~  ~y0"
                    ',form))))
    ',form))

; We now move on to the definition of the function trans-eval, which
; evaluates a form containing references to the free variable STATE,
; and possibly to other stobj names, by binding 'STATE to the given
; state and the other stobj names to their current values in that
; state.  Consing STATE and other stobjs into a list is a gross
; violation of our rules on the use of stobjs.  We believe it is
; legitimate in the special case that a stobj variable name is used in
; the appropriate places in the form, a check that we can make by
; translating the form and inspecting the STOBJS-IN and STOBJS-OUT.
; We arrange to admit trans-eval to the logic by special dispensation.

(defun replaced-stobj (name)
  (if (eq name 'STATE)
; This is just an optimization because it is so common.
      'REPLACED-STATE
    (packn (list 'replaced- name))))

(defun replace-stobjs1 (stobjs-out val)
  (cond ((endp val) val)
        ((car stobjs-out)
         (cons (replaced-stobj (car stobjs-out))
               (replace-stobjs1 (cdr stobjs-out) (cdr val))))
        (t (cons (car val)
                 (replace-stobjs1 (cdr stobjs-out) (cdr val))))))

(defun replace-stobjs (stobjs-out val)

; Replace the stobj objects indicated by the stobj flags in stobjs-out
; by an ordinary symbol derived from the stobj name.  In the case that
; the stobj objects are the live ones, this is crucial to do before
; returning out of trans-eval.  Val is either a single value or a list
; of 2 or more values, as indicated by stobjs-out.  If stobjs-out is
; nil it is treated as a list of as many nils as necessary and no
; change is made to val.

  (cond ((null stobjs-out) val)
        ((null (cdr stobjs-out))
         (cond ((car stobjs-out)
                (replaced-stobj (car stobjs-out)))
               (t val)))
        (t (replace-stobjs1 stobjs-out val))))

; The following is from an old attempt to make the read-eval-print loop handle
; free variables as references to globals.  We abandoned this attempt because
; the LAMBDA abstraction handling introduced by mv-let was forcing globals to
; be evaluated before they had been set, making it confusing which value of a
; global was to be used.  We have left in trans-eval the code that used this,
; within comments.  Note that such an attempt now would need to change
; 'untouchables to 'untouchable-vars.

; (defun build-alist (vars state)
;   (declare (xargs :guard (true-listp vars)))
;   (cond ((null vars) (value nil))
;         ((eq (car vars) 'state)
;          (build-alist (cdr vars) state))
;         ((member (car vars) (global-val 'untouchables (w state)))
;          (er soft 'trans-eval
;              "The global variable ~x0 is on untouchables."
;              (car vars)))
;         (t (er-let* ((alist (build-alist (cdr vars) state)))
;                     (value (cons (cons (car vars)
;                                        (list 'get-global
;                                              (list 'quote (car vars)) 'state))
;                                  alist))))))
;

(defun non-stobjps (vars known-stobjs w)
  (cond ((endp vars) nil)
        ((stobjp (car vars) known-stobjs w)
         (non-stobjps (cdr vars) known-stobjs w))
        (t (cons (car vars)
                 (non-stobjps (cdr vars) known-stobjs w)))))

(defun user-stobjsp (stobjs-out)
  (cond ((endp stobjs-out) nil)
        ((or (null (car stobjs-out))
             (eq (car stobjs-out) 'state))
         (user-stobjsp (cdr stobjs-out)))
        (t t)))

(defun put-assoc-eq-alist (alist1 alist2)

; Setting: A form has been evaluated, producing a state with alist1 as its
; user-stobj-alist.  The evaluation also produced some latches, which are
; alist2.  We wish to merge the latches into the user-stobj-alist of the state
; and this is the workhorse.  We know that the form returns at least one user
; stobj (and so, we know the form is not a DEFSTOBJ or DEFABSSTOBJ or its undo
; or redo).  Given this knowledge, we wish to store the new stobjs in latches
; back into the user-stobj-alist.

; Spec for this function: Both arguments are duplicate-free symbol alists.  For
; every (key . val) in alist2 we a put-assoc-eq of key and val into alist1.

  (cond ((endp alist2) alist1)

; The following clause is an optimization.  If alist1 and alist2 are equal and
; we continued as though this clause weren't here, then we would store each
; (key . val) pair of alist2 into an already identical pair of alist1,
; affecting no change of alist1.  So we can stop and return alist1 now.  (Note
; that if the two alists contained duplicate keys, this would not be an
; optimization: alist1 = alist2 = '((a . 1) (a . 2)) would yeild '((a . 1) (a
; . 2)) with this optimization in place but would yeild '((a . 2) (a . 2))
; without this optimization.)  This optimization increases the efficiency of
; trans-eval's handling of latches.  See the Essay on the Handling of
; User-Stobj-Alist in Trans-Eval.

        ((equal alist2 alist1) alist1)
        (t
         (put-assoc-eq-alist (put-assoc-eq (caar alist2)
                                           (cdar alist2)
                                           alist1)
                             (cdr alist2)))))

#-acl2-loop-only
(defun-one-output chk-user-stobj-alist (stobjs alist acc ctx)
  (if (endp alist)
      (if acc

; We use interface-er rather than (er hard ...) because we do not expect to be
; in the context of a (catch 'raw-ev-fncall ...).

          (interface-er
           "It is illegal to run ACL2 evaluators trans-eval and ~
            simple-translate-and-eval on any term that mentions a stobj that ~
            has been bound by with-local-stobj or stobj-let.  The reason is ~
            that those evaluators expect each stobj to match perfectly the ~
            corresponding global stobj that is stored in the ACL2 state.  The ~
            offending stobj name~#0~[ is~/s are~]:  ~&0."
           acc)
        t)
    (if (and (member-eq (caar alist) stobjs)
             (not (eq (symbol-value (the-live-var (caar alist)))
                      (cdar alist))))
        (chk-user-stobj-alist stobjs
                              (cdr alist)
                              (cons (caar alist) acc)
                              ctx)
      (chk-user-stobj-alist stobjs (cdr alist) acc ctx))))

(defun user-stobj-alist-safe (ctx stobjs state)
  #-acl2-loop-only
  (if stobjs ; optimization
      (chk-user-stobj-alist stobjs (user-stobj-alist state) nil ctx)
    (user-stobj-alist state))
  #+acl2-loop-only
  (declare (ignore ctx stobjs))
  (user-stobj-alist state))

(defun collect-user-stobjs (stobjs-out)
  (cond ((endp stobjs-out) nil)
        ((or (null (car stobjs-out))
             (eq (car stobjs-out) 'state))
         (collect-user-stobjs (cdr stobjs-out)))
        (t (cons (car stobjs-out)
                 (collect-user-stobjs (cdr stobjs-out))))))

(defun ev-for-trans-eval (trans vars stobjs-out ctx state aok
                                user-stobjs-modified-warning)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately,
; it depends hereditarily on the function ev, which has raw Lisp code and is
; thus (as of this writing) prevented from being promoted to :logic mode.

; Warning: Keep in sync with ev-w-for-trans-eval.

; Trans is a translated term with the indicated stobjs-out, and vars is
; (all-vars term).  We return the result of evaluating trans, but formulated as
; an error triple with possibly updated state as described in trans-eval.

; This function is called by trans-eval, and is a suitable alternative to
; trans-eval when the term to be evaluated has already been translated by
; translate1 with stobjs-out = :stobjs-out.

  (let ((alist (cons (cons 'state
                           (coerce-state-to-object state))
                     (user-stobj-alist-safe 'trans-eval vars state)))
        (user-stobjs (collect-user-stobjs stobjs-out)))
    (mv-let
      (erp val latches)
      (ev trans alist state alist

; The next argument is hard-error-returns-nilp.  Think hard before changing it!
; For example, ev-for-trans-eval is called by eval-clause-processor; hence if a
; clause-processor invokes sys-call, the call (er hard ...) under sys-call will
; be guaranteed to cause an error that the user can see (and react to).

          nil aok)

; The first state binding below is the state produced by the evaluation of the
; form.  The second state is the first, but with the user-stobj-alist of that
; state (possibly) updated to contain the modified latches.  Note that we don't
; bother to modify the user-stobj-alist if the form's output signature does not
; involve a user-defined stobj.  The particular forms we have in mind for this
; case are DEFSTOBJ and DEFABSSTOBJ forms and their ``undoers'' and
; ``re-doers''.  They compute the state they mean and we shouldn't mess with
; the user-stobj-alist of their results, else we risk overturning carefully
; computed answers by restoring old stobjs.

      (pprogn
       (coerce-object-to-state (cdr (car latches)))
       (cond (user-stobjs
              (pprogn
               (update-user-stobj-alist
                (put-assoc-eq-alist (user-stobj-alist state)
                                    (cdr latches))
                state)
               (cond
                (user-stobjs-modified-warning
                 (warning$ ctx "User-stobjs-modified"
                           "A call of the ACL2 evaluator on the term ~x0 has ~
                            modified the user stobj~#1~[~/s~] ~&1.  See :DOC ~
                            user-stobjs-modified-warning."
                           trans
                           user-stobjs))
                (t state))))
             (t state))
       (cond
        (erp

; If ev caused an error, then val is a pair (str . alist) explaining the error.
; We will process it here (as we have already processed the translate errors
; that might have arisen) so that all the errors that might be caused by this
; translation and evaluation are handled within this function.

         (error1 ctx (car val) (cdr val) state))
        (t (mv nil
               (cons stobjs-out
                     (replace-stobjs stobjs-out val))
               state)))))))

#+acl2-par
(defun ev-w-for-trans-eval (trans vars stobjs-out ctx state aok
                                  user-stobjs-modified-warning)

; Warning: Keep in sync with ev-for-trans-eval.

; Parallelism wart: add an assertion that stobjs-out does not contain state (or
; any other stobj).  Perhaps the assertion should be that stobjs-out equals the
; representation for an ordinary value.

  (let ((alist (cons (cons 'state
                           (coerce-state-to-object state))
                     (user-stobj-alist-safe 'trans-eval vars state)))
        (user-stobjs (collect-user-stobjs stobjs-out)))
    (mv-let
      (erp val)
      (ev-w trans alist
            (w state)
            (user-stobj-alist state)
            (f-get-global 'safe-mode state) (gc-off state)
            nil aok)
      (prog2$
       (and user-stobjs-modified-warning
            (warning$@par ctx "User-stobjs-modified"
              "A call of the ACL2 evaluator on the term ~x0 has modified the ~
               user stobj~#1~[~/s~] ~&1.  See :DOC ~
               user-stobjs-modified-warning."
              trans
              user-stobjs))
       (cond
        (erp

; If ev caused an error, then val is a pair (str . alist) explaining
; the error.  We will process it here (as we have already processed the
; translate errors that might have arisen) so that all the errors that
; might be caused by this translation and evaluation are handled within
; this function.

; Parallelism wart: check that the above comment is true and applicable in this
; function, even though we call ev-w instead of ev.

         (error1@par ctx (car val) (cdr val) state))
        (t (mv nil
               (cons stobjs-out
                     (replace-stobjs stobjs-out val)))))))))

(defun macroexpand1* (x ctx wrld state)

; See macroexpand1*-cmp, including the Warning there to keep in sync with
; translate11.

  (cmp-to-error-triple
   (macroexpand1*-cmp x ctx wrld (default-state-vars t))))

(defun trans-eval1 (term stobjs-out ctx wrld state aok
                         user-stobjs-modified-warning)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately,
; it depends hereditarily on the function ev, which has raw Lisp code and is
; thus (as of this writing) prevented from being promoted to :logic mode.

  (let ((vars (all-vars term)))
    (cond
     ((non-stobjps vars t wrld) ;;; known-stobjs = t
      (er soft ctx
          "Global variables, such as ~&0, are not allowed. See :DOC ASSIGN ~
           and :DOC @."
          (reverse (non-stobjps vars t wrld)))) ;;; known-stobjs = t
     (t (ev-for-trans-eval term vars stobjs-out ctx state aok
                           user-stobjs-modified-warning)))))

(defun trans-eval0 (form ctx state aok user-stobjs-modified-warning)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately,
; it depends hereditarily on the function ev, which has raw Lisp code and is
; thus (as of this writing) prevented from being promoted to :logic mode.

  (let ((wrld (w state)))
    (er-let* ((form (macroexpand1* form ctx wrld state)))
      (cond
       ((and (consp form)
             (eq (car form) 'if)
             (true-listp form)
             (equal (length form) 4))

; Do some lazy evaluation, in order to avoid translating the unnecessary
; branch.

        (let ((simple-stobjs-out '(nil)))
          (er-let* ((arg0 (translate (cadr form) simple-stobjs-out nil t ctx wrld
                                     state))
                    (val0 (trans-eval1 arg0 simple-stobjs-out ctx wrld state
                                       aok user-stobjs-modified-warning)))
            (if (cdr val0) ; the actual value
                (trans-eval0 (caddr form) ctx state aok
                             user-stobjs-modified-warning)
              (trans-eval0 (cadddr form) ctx state aok
                           user-stobjs-modified-warning)))))
       (t
        (mv-let
         (erp trans bindings state)
         (translate1 form
                     :stobjs-out '((:stobjs-out . :stobjs-out))
                     t
                     ctx wrld state)

; Known-stobjs = t.  We expect trans-eval to be used only when the
; user is granted full access to the stobjs in state.  Of course, some
; applications of trans-eval, e.g., in eval-event-lst, first check
; that the form doesn't access stobjs or state.

         (cond
          (erp (mv t nil state))
          (t (trans-eval1 trans (translate-deref :stobjs-out bindings) ctx wrld
                          state aok user-stobjs-modified-warning)))))))))

(defun trans-eval (form ctx state aok)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately,
; it depends hereditarily on the function ev, which has raw Lisp code and is
; thus (as of this writing) prevented from being promoted to :logic mode.

; Advice:  See if simple-translate-and-eval will do the job.

; This function translates form and then evaluates it, with 'state
; bound to state and the user's stobj names bound to their current
; values in (user-stobj-alist state).

; We return an error triple:  (mv erp val state').  If erp is t, then
; an error occurred (which has been printed into state').  State' will
; reflect changes caused to single-threaded objects prior to the
; error.

; If erp is nil, val is (stobjs-out . replaced-val), where stobjs-out
; is the stobjs out of the translated form and replaced-val is the
; value of the evaluation of form, with any output stobjs replaced by
; symbols as per replace-stobjs.  The final values of the stobjs may
; be found in (user-stobj-alist state').  Note that this change to
; state -- the storage of the final stobjs -- is done at the
; conclusion of the computation and is not directed by form.

  (trans-eval0 form ctx state aok t))

(defun trans-eval-no-warning (form ctx state aok)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately,
; it depends hereditarily on the function ev, which has raw Lisp code and is
; thus (as of this writing) prevented from being promoted to :logic mode.

; See :doc user-stobjs-modified-warning.

  (trans-eval0 form ctx state aok nil))

(defun trans-eval-default-warning (form ctx state aok)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately,
; it depends hereditarily on the function ev, which has raw Lisp code and is
; thus (as of this writing) prevented from being promoted to :logic mode.

; This version of trans-eval is appropriate when the relevant LD special is to
; be consulted for when to invoke the user-stobjs-modified-warning.  See :doc
; user-stobjs-modified-warning.

  (trans-eval0 form ctx state aok
               (f-get-global 'ld-user-stobjs-modified-warning state)))

(defun simple-translate-and-eval (x alist ok-stobj-names msg ctx wrld state
                                    aok)

; A Note on the Reason this Function Exists:

; This function is a cousin of trans-eval that is much easier to use
; in simple cases.  Trans-eval can handle any well-formed term.  Thus,
; it must have a way to communicate to the caller how many results are
; being returned and what they are.  The obvious thing for trans-eval
; to do is to list the results.  But if one of them is STATE or some
; other stobj, it cannot.  So trans-eval has a rather complicated
; interface that permits the caller to determine the multiplicity of
; the result and whether and where the stobjs appear (or, more precisely,
; are supposed to appear) in the output vector.  See the documentation
; of trans-eval for its specification.

; This function, simple-translate-and-eval, is designed to handle more
; simply the most common case, namely, when x is supposed to be a term
; that returns one result and that result is not state or any other
; stobj.  In that case, we can return the result directly.

; While trans-eval may be used whenever translation and evaluation are
; needed, we recommend using simple-translate-and-eval if the given
; term returns a single, non-stobj result, simply because the
; interface is simpler.

; The Spec of SIMPLE-TRANSLATE-AND-EVAL: We translate x, requiring
; that it be a term that returns one non-stobj result.  We verify that
; the translation mentions no variables other than those bound in
; alist and the stobj names listed in ok-stobj-names.  We then
; evaluate the translation of x under alist', where alist' is obtained
; from alist by appending the bindings of 'state to state and
; (user-stobj-alist state).  (The extra bindings can't hurt.  The
; bindings of alist have priority.)  If no errors arise, we return a
; pair, (term .  val), where term is the translation of x and val is
; its value under alist'.

; Msg is a ~@ message that should describe x and begin with a capital
; letter.  For example, msg might be the string "The second argument
; to foo".

; Note that we call translate with logic-modep nil.  Thus, :program
; mode functions may appear in x.

; Keep in sync with simple-translate-and-eval@par.

  (er-let* ((term (translate x '(nil) nil t ctx wrld state)))

; known-stobjs = t.  We expect simple-translate-and-eval to be used
; only when the user is granted full access to the stobjs in state
; (without modification rights, of course).

           (let ((vars (all-vars term))
                 (legal-vars (append (strip-cars alist)
                                     ok-stobj-names)))
             (cond ((not (subsetp-eq vars legal-vars))
                    (er soft ctx
                        "~@0 may contain ~#1~[no variables~/only the ~
                         variable ~&2~/only the variables ~&2~], but ~
                         ~x3 contains ~&4."
                        msg
                        (cond ((null legal-vars) 0)
                              ((null (cdr legal-vars)) 1)
                              (t 2))
                        legal-vars
                        x
                        (reverse vars)))
                   (t (mv-let (erp val latches)
                              (ev term
                                  (append alist
                                          (cons (cons 'state
                                                      (coerce-state-to-object
                                                       state))
                                                (user-stobj-alist-safe
                                                 'simple-translate-and-eval
                                                 (intersection-eq
                                                  ok-stobj-names
                                                  vars)
                                                 state)))
                                  state nil nil aok)
                              (declare (ignore latches))

; Parallelism wart: since we ignore latches, we should be able to create a
; version of simple-translate-and-eval that returns cmp's.

                              (cond
                               (erp (pprogn
                                     (error-fms nil ctx (car val) (cdr val)
                                                state)
                                     (er soft ctx
                                         "~@0 could not be evaluated."
                                         msg)))
                               (t (value (cons term val))))))))))

(defun error-fms-cw (hardp ctx str alist)
  (wormhole 'comment-window-io
            '(lambda (whs)
               (set-wormhole-entry-code whs :ENTER))
            (list hardp ctx str alist)
            `(let ((hardp (nth 0 (@ wormhole-input)))
                   (ctx (nth 1 (@ wormhole-input)))
                   (str (nth 2 (@ wormhole-input)))
                   (alist (nth 3 (@ wormhole-input))))
               (pprogn (error-fms hardp ctx str alist state)
                       (value :q)))
            :ld-error-action :error ; for robustness; no error is expected
            :ld-verbose nil
            :ld-pre-eval-print nil
            :ld-prompt nil))

#+acl2-par
(defmacro error-fms@par (&rest args)
  `(error-fms-cw ,@args))

(defun simple-translate-and-eval-cmp (x alist ok-stobj-names msg ctx wrld state
                                        aok safe-mode gc-off)

; Warning: Errors printed by this function are not inhibited by
; set-inhibit-output-lst.

; This version of simple-translate-and-eval returns a context-message pair; see
; the Essay on Context-message Pairs.  See simple-translate-and-eval for
; documentation, for example that translation is done under the assumption that
; the user is granted full access to the stobjs in state.

; Notice that we pass in safe-mode and gc-off explicitly, rather than reading
; them from state, because there are occasions (e.g., eval-theory-expr@par)
; where at least one of these parameters could differ from its corresponding
; state value.  But couldn't we have simply state-global-let*-bound the
; relevant state globals?  Well, no, not in contexts like eval-theory-expr@par
; that do not allow modification of state.

  (er-let*-cmp
   ((term (translate-cmp x '(nil) nil t ctx wrld (default-state-vars t))))
   (let ((vars (all-vars term))
         (legal-vars (append (strip-cars alist)
                             ok-stobj-names)))
     (cond ((not (subsetp-eq vars legal-vars))
            (er-cmp ctx
                    "~@0 may contain ~#1~[no variables~/only the variable ~
                     ~&2~/only the variables ~&2~], but ~x3 contains ~&4."
                    msg
                    (cond ((null legal-vars) 0)
                          ((null (cdr legal-vars)) 1)
                          (t 2))
                    legal-vars
                    x
                    (reverse vars)))
           (t (mv-let (erp val)

; Note that because translate-cmp is called above with parameter stobjs-out =
; '(nil), we have met the requirement on ev-w; specifically, evaluation of the
; given form cannot modify any stobj.

                      (ev-w term
                            (append alist
                                    (cons (cons 'state
                                                (coerce-state-to-object
                                                 state))
                                          (user-stobj-alist-safe
                                           'simple-translate-and-eval
                                           (intersection-eq
                                            ok-stobj-names
                                            vars)
                                           state)))
                            (w state)
                            (user-stobj-alist state)
                            safe-mode gc-off nil aok)
                      (cond
                       (erp (prog2$
                             (error-fms-cw nil ctx (car val) (cdr val))
                             (er-cmp ctx
                                     "~@0 could not be evaluated."
                                     msg)))
                       (t (value-cmp (cons term val))))))))))

(defun simple-translate-and-eval-error-double (x alist ok-stobj-names msg ctx
                                                 wrld state aok safe-mode
                                                 gc-off)

; Warning: Errors printed by this function are not inhibited by
; set-inhibit-output-lst.

; This version of simple-translate-and-eval returns an error double (mv erp
; val).  See simple-translate-and-eval for documentation, for example that
; translation is done under the assumption that the user is granted full access
; to the stobjs in state.

; This function was requested by David Rager so that he could make the
; community book books/cutil/wizard.lisp thread-safe for ACL2(p).  We return an
; error double (mv erp val).

; Our plan is to introduce simple-translate-and-eval-cmp first, because we have
; nice idioms for context-message pairs.  Then we trivially define
; simple-translate-and-eval-error-double in terms of
; simple-translate-and-eval-cmp.

; See a comment in simple-translate-and-eval-cmp for why we pass in safe-mode
; and gc-off explicitly, rather than reading them from state.

  (cmp-to-error-double
   (simple-translate-and-eval-cmp x alist ok-stobj-names msg ctx wrld state
                                  aok safe-mode gc-off)))

#+acl2-par
(defun simple-translate-and-eval@par (x alist ok-stobj-names msg ctx wrld state
                                        aok safe-mode gc-off)

; This function is just an ACL2(p) wrapper for
; simple-translate-and-eval-error-double.  The history is that this function
; was defined first, but David Rager needed a version that worked in
; non-parallel ACL2 as well; see simple-translate-and-eval-error-double.

; We keep the function simple-translate-and-eval@par because of its handling in
; bodies of functions defined using defun@par according to the table
; *@par-mappings*.  See for example the call of simple-translate-and-eval@par
; in (defun@par translate-do-not-hint ...).

  (simple-translate-and-eval-error-double x alist ok-stobj-names msg ctx wrld
                                          state aok safe-mode gc-off))

(defun tilde-*-alist-phrase1 (alist evisc-tuple level)
  (cond ((null alist) nil)
        (t (cons (msg "~t0~s1 : ~Y23~|" level (caar alist) (cdar alist)
                      evisc-tuple)
                 (tilde-*-alist-phrase1 (cdr alist) evisc-tuple level )))))

(defun tilde-*-alist-phrase (alist evisc-tuple level)

; This prints out a substitution alist, e.g., ((x . a) (y . b) (z . c))
; in the form
;  x : a
;  y : b
;  z : c
; when the output is printed with ~*.

  (list "" "~@*" "~@*" "~@*"
        (tilde-*-alist-phrase1 alist evisc-tuple level)))

(defun set-temp-touchable-fns (x state)

; Keep this in sync with set-temp-touchable-vars.

; Why make the indicated check below, rather than using a guard?  Because we
; want that check to be made even when this function is called underneath
; :program mode functions, hence even when guards aren't checked.

  (cond ((or (eq x t) (symbol-listp x))
         (f-put-global 'temp-touchable-fns x state))
        (t (prog2$ (er hard 'set-temp-touchable-fns
                       "The first argument to ~x0 may must be either ~x0 or a ~
                        true list of symbols, unlike:~| ~x1"
                       'temp-touchable-fns
                       x)
                   state))))

(defun set-temp-touchable-vars (x state)

; Keep this in sync with set-temp-touchable-fns.

; Why make the indicated check below, rather than using a guard?  Because we
; want that check to be made even when this function is called underneath
; :program mode functions, hence even when guards aren't checked.

  (cond ((or (eq x t) (symbol-listp x))
         (f-put-global 'temp-touchable-vars x state))
        (t (prog2$ (er hard 'set-temp-touchable-vars
                       "The first argument to ~x0 may must be either ~x0 or a ~
                        true list of symbols, unlike:~| ~x1"
                       'temp-touchable-vars
                       x)
                   state))))

(defun clear-temp-touchable-fns (state)
  (f-put-global 'temp-touchable-fns nil state))

(defun clear-temp-touchable-vars (state)
  (f-put-global 'temp-touchable-vars nil state))

;  Note on functional programming.

; Lest anyone think that ACL2 fails to have a functional programming
; component, we here illustrate how to code some of the traditional
; function manipulating operations of Lisp in ACL2.  All these
; operations depend upon the function trans-eval.  These functions are
; at the moment not very efficient because they involve a runtime call
; to translate.  Furthermore, proving interesting theorems about these
; functions would not be easy because they are tied up with the
; ``big-clock'' story which makes our evaluator primitive recursive.
; But nevertheless it is worth pointing out that this capability at
; least exists in ACL2.

(defun mapcar$ (fn l state)

; A version of the traditional lisp mapper, e.g.
; (mapcar$ 'reverse '((1 2 3) (4 5)) state) =>
; ((3 2 1) (5 4))

  (cond ((null l) (value nil))
        (t (er-let* ((ans (trans-eval (list fn (list 'quote (car l)))
                                      'mapcar$ state t))
                     (rst (mapcar$ fn (cdr l) state)))

; Ans is (stobjs-out . replaced-val), where stobjs-out indicates where
; stobjs are located in replaced-val.  However, those stobjs have been
; replaced by simple symbols.  The final value of state produced by fn
; is state, which may be among the stobjs-out.  We just cons the
; replaced-val into our answer, which is a little peculiar since it
; may contain 'replaced-state, but it's sufficient to indicate what is
; happening and the final state has been side-effected in the proper
; sequence.

             (value (cons (cdr ans) rst))))))

(defun mapdo (fn l state)

; A mapper that simply applies the fn for side effect (on the
; free variable state), e.g.
; (mapdo '(lambda (x) (princ$ x *standard-co* state)) '(1 2 3) state)
; prints 123  and returns nil.

  (cond ((null l) (value nil))
        (t (er-let* ((ans (trans-eval (list fn (list 'quote (car l)))
                                      'mapdo state t))
                     (rst (mapdo fn (cdr l) state)))
             (value nil)))))

(defun always (fn l state)

; A universal quantifier, e.g.  (always 'rationalp '(1 2 3) state) =>
; t

  (cond ((null l) (value t))
        (t (er-let* ((ans
                      (trans-eval
                       (list fn (list 'quote (car l)))
                       'always
                       state t)))
             (cond ((null (cdr ans)) (value nil))
                   (t (always fn (cdr l) state)))))))

(defun thereis (fn l state)

; An existential quantifier, e.g.
; (thereis 'rationalp '(a 2 b) state) => '(2 B)

  (cond ((null l) (value nil))
        (t (er-let* ((ans
                      (trans-eval
                       (list fn (list 'quote (car l)))
                       'thereis
                       state t)))
             (cond ((cdr ans) (value l))
                   (t (thereis fn (cdr l) state)))))))

; Now that ev-w, translate, untranslate, and so on are all defined, let us
; populate guard-msg-table.

(table guard-msg-table nil nil
       :guard
       (and (symbolp key)
            (or (null val)
                (termp val world))))

(defmacro set-guard-msg (fn form)
  (declare (xargs :guard (symbolp fn)))
  `(table guard-msg-table
          ',fn
          (mv-let
           (erp term bindings)
           (translate1-cmp ',form
                           '(nil)        ; stobjs-out
                           nil           ; bindings
                           t             ; known-stobjs
                           'set-guard-msg ; ctx
                           world
                           (default-state-vars nil))
           (declare (ignore bindings))
           (prog2$ (and erp ; erp is ctx, term is msg
                        (er hard! erp "~@0" term))
                   term))))

(set-guard-msg the-check
               (msg "The object ~x0 does not satisfy the type declaration ~
                     ~x1.~@2"
                    (nth 2 args)
                    (nth 1 args)
                    coda))

(set-guard-msg the-check-for-*1*
               (msg "The object ~x0 does not satisfy the type declaration ~x1 ~
                     for bound variable ~x2.~@3"
                    (nth 2 args)
                    (nth 1 args)
                    (nth 3 args)
                    coda))

(set-guard-msg check-dcl-guardian
               (msg "The guard condition ~x0, which was generated from a type ~
                     declaration, has failed.~@1"
                    (untranslate (cadr args) t world)
                    coda))

(set-guard-msg fmx-cw-fn
               (msg "Guard violation for ~x0:~|~@1"
                    'fmx-cw-fn
                    (let ((str (nth 0 args))
                          (alist (nth 1 args)))
                      (fmx-cw-msg str alist))))

(set-guard-msg fmx!-cw-fn
               (msg "Guard violation for ~x0:~|~@1"
                    'fmx!-cw-fn
                    (let ((str (nth 0 args))
                          (alist (nth 1 args)))
                      (fmx-cw-msg str alist))))
