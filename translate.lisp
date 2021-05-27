; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2020, Regents of the University of Texas

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
; upon the constrained functions in the apply$ development.  In particular, if
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

(defun ev-fncall-null-body-erp (fn)

; Warning: Keep this in sync with hide-with-comment.

  `(ev-fncall-null-body-er . ,fn))

(defun ev-fncall-null-body-er (ignored-attachment fn args latches)
  (mv (ev-fncall-null-body-erp fn)
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
            ((eq (cdr temp) (car vals))

; Two live stobjs are the same iff they are eq.  This is kind of a cheat; see
; the comment about the use of rassoc-eq in actual-stobjs-out1.

             (latch-stobjs1 (cdr stobjs-out)
                            (cdr vals)
                            latches))
            (t
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

(defun actual-stobjs-out1 (stobjs-in arg-exprs)
  (declare (xargs :guard (and (symbol-listp stobjs-in)
                              (true-listp arg-exprs)
                              (= (length stobjs-in)
                                 (length arg-exprs)))))
  (cond ((endp stobjs-in)
         (assert$ (null arg-exprs) nil))
        (t (cond ((or (null (car stobjs-in))
                      (eq (car stobjs-in) 'state)
                      (eq (car stobjs-in) (car arg-exprs)))
                  (actual-stobjs-out1 (cdr stobjs-in) (cdr arg-exprs)))
                 (t (acons (car stobjs-in)
                           (car arg-exprs)
                           (actual-stobjs-out1 (cdr stobjs-in)
                                               (cdr arg-exprs))))))))

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

(defun actual-stobjs-out (fn arg-exprs wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (not (member-eq fn *stobjs-out-invalid*))
                              (true-listp arg-exprs)
                              (plist-worldp wrld))))
  (let ((stobjs-out (stobjs-out fn wrld)))
    (cond ((all-nils stobjs-out) ; optimization for common case
           stobjs-out)
          (t (let ((stobjs-in (stobjs-in fn wrld)))
               (let ((alist (actual-stobjs-out1 stobjs-in arg-exprs)))
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
; than the live state: Ev a call of ev.  Here is what to execute inside the
; loop.

; (defttag t)
; (remove-untouchable ev t)
; (let ((st (build-state)))
;      (ev `(ev 'a '((a . 1)) ',st 'nil 'nil 't) nil state nil nil t))

; The outermost state above is indeed the live one, but the inner ev is
; executed on a dummy state.  The computation above produces the result
; (NIL (NIL 1 NIL) NIL).

; The inner state object has to pass the state-p predicate if guard checking is
; enabled in the outer state.  If guard checking is turned off in the live
; state, the following example shows the inner ev running on something that is
; not even a state-p.  At one time we could make this example work by first
; evaluating the remove-untouchable form above and then :set-guard-checking
; nil; but now we get a hard ACL2 error about program-only functions.

; (ev '(ev 'a '((a . 1)) '(nil nil nil nil nil 0) 'nil 'nil 't)
;     nil state nil nil t)

; The 0, above, is the big-clock-entry and must be a non-negative integer.  The
; result, when we could compute a result, was (NIL (NIL 1 NIL) NIL).

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

; The output of the ev above was (NIL (NIL (DUMMY-FOO . 1) NIL) NIL).

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

(defun save-ev-fncall-guard-er (fn guard stobjs-in args w)

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
                     (list fn guard stobjs-in args w)))
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

; This function returns all attachment pairs except for attachments to warrants
; and possibly attachments made with non-nil :skip-checks.

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
  (defvar *return-last-fn-aok*)
)

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

; Warning: The use of rassoc-eq below is essentially ill-guarded, and moreover,
; it gives different behavior when live stobjs are replaced by their Lisp
; representations.  The reason is that Common Lisp eq returns nil on two stobjs
; st1 and st2 with the same logical (list-based) representation, even when
; those two list are equal and thus logically eq.  (This issue is not solved if
; we replace rassoc-eq by rassoc-equal, which isn't a viable solution anyhow
; because of bit arrays, as explained below.)  Therefore, do not remove this
; function from *initial-untouchable-fns*.  We considered solving this problem
; by passing in actual argument expressions, for example as we do in
; raw-ev-fncall; but that would not suffice for discerning when a stobj is
; anonymous (from a local stobj or a nested stobj binding).

; The following example shows why we use rassoc-eq instead of rassoc-equal
; below (as we did through Version_8.2).  The fundamental problem is that
; distinct (non-eq) bit-arrays can be satisfy Common Lisp's equal.

;   (defstobj st1 (fld1 :type (array bit (8)) :initially 0))
;   (defstobj st2 (fld2 :type (array bit (8)) :initially 0) :congruent-to st1)
;   (defun my-update-fld1i (val st1)
;     (declare (xargs :stobjs st1 :guard (bitp val)))
;     (update-fld1i 0 val st1))
;   (my-update-fld1i '(a) st1)
;   (print-gv) ; erroneously mentions st2 if rassoc-eq replaces rassoc-equal

  (cond ((endp lst) (reverse acc))
        (t (apply-user-stobj-alist-or-kwote
            user-stobj-alist
            (cdr lst)
            (cons (cond ((live-state-symbolp (car lst))
                         'state)
                        ((bad-atom (car lst))
                         (let ((pair (rassoc-eq (car lst)
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
        (t (er-let* ((v (get-unambiguous-xargs-flg1 key (cdr lst) event-msg ctx
                                                    state))
                     (ans (get-unambiguous-xargs-flg1/edcls
                           key v (fourth (car lst)) event-msg ctx state)))
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

(defun translate-declaration-to-guard-gen-var-lst (x var-lst tflg wrld)

; It is assumed that (translate-declaration-to-guard-gen x 'var tflg wrld) is
; non-nil.  This function translates the declaration x for each of the vars in
; var-lst and returns the list of translations.  Use of the word
; ``translation'' in this comment and the name of this function is a bit
; misleading since the result is a list of UNtranslated terms if tflg is nil.

  (declare (xargs :guard (and (true-listp var-lst)
                              (plist-worldp wrld))))
  (cond
   ((null var-lst) nil)
   (t (cons (translate-declaration-to-guard-gen x (car var-lst) tflg wrld)
            (translate-declaration-to-guard-gen-var-lst x
                                                        (cdr var-lst)
                                                        tflg
                                                        wrld)))))

(defun translate-declaration-to-guard-var-lst (x var-lst wrld)
  (declare (xargs :guard (and (true-listp var-lst)
                              (plist-worldp wrld))))

; This is just the special case of translate-declaration-to-guard-gen-var-lst
; for tflg = nil for backwards compatibility.  See get-guards2 for a discussion
; of tflg.

  (translate-declaration-to-guard-gen-var-lst x var-lst nil wrld))

(defun get-guards2 (edcls targets tflg wrld stobjs-acc guards-acc)

; Targets is a subset of (GUARDS TYPES), where we pick up expressions from
; :GUARD and :STOBJS XARGS declarations if GUARDS is in the list and we pick up
; expressions corresponding to TYPE declarations if TYPES is in the list.

; Tflg specifies whether we want translated or user-level terms when we
; construct the type expressions.  Note that tflg does not affect how we treat
; the :GUARD term!  The :GUARD term is either already translated in edcls or is
; not and whatever it is is how we treat it.  But we have to assemble type
; expressions from TYPE specs and tflg affects that assembly.  For example
; (TYPE (INTEGER 1 5) X) can either produce (AND (INTEGERP X) (<= 1 X) (<= X
; 5)) or its translation into IFs, NOT, <, and quoted constants.

; Historical Note on tflg: This function originally did not have tflg and
; always returned untranslated type expressions.  We need the type expressions
; to be in translated form in translate11-lambda-object and
; well-formed-lambda-objectp because we must confirm that the (translated) type
; expressions are among the conjuncts of the (translated) :GUARD.  We could
; have avoided adding tflg and just always returned fully translated terms but
; that might have changed behavior assumed by user books that called various
; system translation functions.  So we introduced tflg in versions of those
; functions that needed it and added ``-gen'' (for ``-generalized'') to their
; names and then defined the old functions as instances, for backwards
; compatibility.

; See get-guards for an example of what edcls looks like.  We require that
; edcls contains only valid type declarations, as explained in the comment
; below about translate-declaration-to-guard-gen-var-lst.

; We are careful to preserve the order, except that we consider :STOBJS as
; going before :GUARD.  (An example is (defun load-qs ...) in community book
; books/defexec/other-apps/qsort/programs.lisp.)  Before Version_3.5, Jared
; Davis sent us the following example, for which guard verification failed on
; the guard of the guard, because the :GUARD conjuncts were unioned into the
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

; NOTE: A special case is when wrld is nil.  In that case, :STOBJS declarations
; in edcls are ignored and checks are skipped for SATISFIES declarations.
; Therefore, if you call this with wrld = nil, then other code should deal
; suitably with :STOBJS declarations and check SATISFIES declarations.

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
; The following (list t) avoids ignoring :GUARD (and).
                             (list t))
                         (list (cadr temp1)))
                     nil))
                (temp2 (and (consp wrld) ; see comment above about stobjs
                            (assoc-keyword :STOBJS (cdar edcls))))
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
                        tflg
                        wrld
                        (rev-union-equal stobj-conjuncts
                                         stobjs-acc)
                        (rev-union-equal guard-conjuncts
                                         guards-acc))))
        ((and (eq (caar edcls) 'type)
              (member-eq 'types targets))
         (get-guards2 (cdr edcls)
                      targets
                      tflg
                      wrld

; The call of translate-declaration-to-guard-gen-var-lst below assumes that
; (translate-declaration-to-guard-gen (cadr (car edcls)) 'var tflg wrld) is
; non-nil.  This is indeed the case, because edcls is as created by
; chk-defuns-tuples, which leads to a call of chk-dcl-lst to check that the
; type declarations are legal.

                      stobjs-acc
                      (rev-union-equal (translate-declaration-to-guard-gen-var-lst
                                        (cadr (car edcls))
                                        (cddr (car edcls))
                                        tflg
                                        wrld)
                                       guards-acc)))
        (t (get-guards2 (cdr edcls)
                        targets tflg wrld stobjs-acc guards-acc))))

(defun get-guards1 (edcls targets args name wrld)

; We compute the guards but add (state-p name) when necessary:

; When a function definition has a state argument but does not explicitly
; include state among its :stobjs declarations (presumably because
; (set-state-ok t) has been executed), the conjuncts returned by get-guards2 do
; not include (state-p state).  Thus, we add this conjunct when (1) targets
; includes the symbol, guards; (2) the formal arguments, args, include state;
; (3) (state-p state) is not already in the result of get-guards2; and (4) the
; function symbol in question, name, is not state-p itself, whose guard is
; truly t -- but see the exception for wrld = nil below.  If the (state-p
; state) conjunct is added, it is added in front of the other conjuncts,
; consistently with the order described in :DOC guard-miscellany.

; Note that we may pass in args = nil to avoid adding a state-p call, for
; example when defining a macro.  In that case name is ignored, so it is safe
; to pass in name = nil.

; NOTE: A special case is when wrld is nil.  In that case, :STOBJS declarations
; in edcls are ignored and checks are skipped for SATISFIES declarations;
; moreover, a state-p conjunct (as described above) is not added.  Therefore,
; if you call this with wrld = nil, then other code should deal suitably with
; :STOBJS declarations and check SATISFIES declarations.

  (let ((conjuncts (get-guards2 edcls targets nil wrld nil nil)))
    (cond ((and (consp wrld) ; see NOTE just above
                (member-eq 'guards targets) ; (1)
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

; Def is the cdr of a defun (or defun-nx, defund, etc.) event; thus, (car def)
; is the name being introduced.  Wrld is an ACL2 logical world, possibly nil
; (see note below).  We return (mv dcls guard), where dcls is the strip-cdrs of
; the declarations of def and guard is the untranslated guard extracted from
; def, comprehending not only :GUARD xargs but also TYPE declarations,
; :SPLIT-TYPES xargs, and if wrld is non-nil, :STOBJS xargs.

; NOTE: A special case is when wrld is nil.  In that case, :STOBJS declarations
; in edcls are ignored and checks are skipped for SATISFIES declarations.
; Therefore, if you call this with wrld = nil, then other code should deal
; suitably with :STOBJS declarations and check SATISFIES declarations.

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

; Warning: Do not use '(nil) here!  That will cause CMUCL builds to fail, and
; it will also cause SBCL builds to fail if we compile ACL2 source files with
; compile-file before loading them during the build.

  (list nil))

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

; At one time we considered a change here in the world global,
; attachment-records.  However, warrants do not change that global (at least,
; as of this writing), so we use this safer (more inclusive) check.

                               (eq (cadr trip) 'attachment))
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

(defun raw-ev-fncall (fn arg-values arg-exprs latches w user-stobj-alist
                         hard-error-returns-nilp aok)

; Warning: Keep this in sync with raw-ev-fncall-simple.

; Here we assume that w is "close to" (w *the-live-state*), as implemented by
; chk-raw-ev-fncall.  If latches is nil, then arg-exprs is irrelevant
; (typically nil); otherwise, we are evaluating (fn . arg-exprs) where
; arg-values is the list of values of arg-exprs.  We use that information to
; compute the expected stobjs-out, especially in the case that some stobj input
; is not the stobj specified by the signature of fn, but rather is congruent to
; it.

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
                     (latches (actual-stobjs-out fn arg-exprs w))
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
                           (apply applied-fn arg-values)
                           #+acl2-mv-as-values
                           (cond ((null (cdr stobjs-out))
                                  (apply applied-fn arg-values))
                                 (t (multiple-value-list
                                     (apply applied-fn arg-values)))))
                       (setq throw-raw-ev-fncall-flg nil))))

; It is important to rebind w here, since we may have updated state since the
; last binding of w.

              (w (if pair

; We use the live state now if and only if we used it above, in which case (cdr
; pair) = *the-live-state*.

                     (w (cdr pair))
                   w)))

; Observe that if a throw to 'raw-ev-fncall occurred during the
; (apply fn arg-values) then the local variable throw-raw-ev-fncall-flg
; is t and otherwise it is nil.  If a throw did occur, val is the
; value thrown.

         (cond
          (throw-raw-ev-fncall-flg
           (mv (if (and (consp val)
                        (eq (car val) 'ev-fncall-null-body-er))
                   (ev-fncall-null-body-erp (caddr val))
                 t)
               (ev-fncall-msg val w user-stobj-alist)
               latches))
          (t #-acl2-mv-as-values ; adjust val for the multiple value case
             (let ((val
                    (cond
                     ((null (cdr stobjs-out)) val)
                     (t (cons val
                              (mv-refs (1- (length stobjs-out))))))))
               (mv nil
                   val
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

; This function also returns the logical defun form submitted to ACL2 for fn,
; if any, provided fn does not have property 'non-executablep.  (We use this
; fact in the definition of logical-defun.)  To understand that restriction,
; note that install-event-defuns stores the original defun event in the
; function symbol's cltl-command except in the case that the function is
; non-executable; and, cltl-def-from-name2 looks up the defun form in the
; cltl-command.

  (cltl-def-from-name1 fn
                       (getpropc fn 'stobj-function nil wrld)
                       nil
                       wrld))

(defun unmake-true-list-cons-nest (formal-args)

; Formal-args is a term.  We return a list of term t1, ..., tn such that
; formal-args is the translation of (list t1 ... tn), unless that is impossible
; in which case we return :fail.

  (declare (xargs :guard (pseudo-termp formal-args)))
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

(defun all-quoteps (lst)
  (cond ((null lst) t)
        (t (and (quotep (car lst))
                (all-quoteps (cdr lst))))))

; We introduce some functions for manipulating LAMBDA objects now because we
; need them when we define untranslate, and we use untranslate in error
; messages in translate.  For a discussion of LAMBDA objects and lambda$ see
; the Essay on Lambda Objects and Lambda$.

; The next few functions develop the notion of a well-formed lambda object.

; Here is one of the most basic functions in the theorem prover.

; (Students of our code should study this elementary function just to see how
; we recur through terms.  The function instantiates a variable, i.e.,
; (subst-var new old form) substitutes the term new for the variable old in the
; term form.  For example, (subst-var '(car a) 'x '(foo x y)) = '(foo (car a)
; y).)

(mutual-recursion

(defun subst-var (new old form)
  (declare (xargs :guard (and (pseudo-termp new)
                              (variablep old)
                              (pseudo-termp form))))
  (cond ((variablep form)
         (cond ((eq form old) new)
               (t form)))
        ((fquotep form) form)
        (t (cons-term (ffn-symb form)
                      (subst-var-lst new old (fargs form))))))

(defun subst-var-lst (new old l)
  (declare (xargs :guard (and (pseudo-termp new)
                              (variablep old)
                              (pseudo-term-listp l))))
  (cond ((endp l) nil)
        (t (cons (subst-var new old (car l))
                 (subst-var-lst new old (cdr l))))))

)

(defun subst-each-for-var (new-lst old term)

; Successively substitute each element of new-lst for the variable old in term
; and collect the results.

  (cond
   ((endp new-lst) nil)
   (t (cons (subst-var (car new-lst) old term)
            (subst-each-for-var (cdr new-lst) old term)))))

; We now formalize the notion of a well-formed lambda object as the function
; well-formed-lambda-objectp. That function is not actually used in
; translation; translate11 guarantees it for lambda objects and lambda$
; results, but translate11 checks the various well-formedness conditions
; individually and reports violation-specific error messages.  The
; well-formedness function is used elsewhere in our system code when we
; encounter a lambda object to be guard verified or compiled.

; There are aspects of well-formedness that are independent of the world.  For
; example, (lambda (x) (declare (type integer y)) (body x y)) is ill-formed in
; all worlds (e.g., whether body is a tame :logic-mode function in the world or
; not).  So we divide the well-formedness predicate into two parts, one
; independent of world, called ``syntactically plausible,'' and one dependent
; on it.  This partitioning becomes important when we develop the cl-cache in
; which we store lambda objects for evaluation purposes.

(defun type-expressions-from-type-spec (spec vars wrld)

; Given an alleged type spec, like INTEGER, (SATISFIES EVENP), or (OR STRING
; CONS), and a list of variables, var, we generate the non-empty list of
; equivalent type expressions (one for each variable) or nil if x is not a
; legal type spec.  There must be at least one variable in vars or else (TYPE
; spec . vars) is illegal, so the nil answer is unambiguous.

; This function is akin to translate-declaration-to-guard-gen-var-lst except
; that function assumes x is legal and this one doesn't.  Thus, this can be
; used as either a predicate, ``is (TYPE x . vars) legal?,'' or as a function
; that returns the corresponding list of type expressions.  We use this
; function both ways when checking that the DECLARE in a lambda object is
; legal: we have to check each TYPE declaration and we have to check that each
; type expression is a conjunct of the :GUARD.

; Efficiency: Rather than translate every declaration to its guard expression
; for each var in vars we just translate the first one and then use
; substitution to get the rest of the expressions.  The legality of a type spec
; is independent of the var constrained.

  (cond ((null vars) nil)
        (t (let ((expr (translate-declaration-to-guard-gen
                        spec (car vars) t wrld)))
             (cond
              ((null expr) nil)
              (t (cons expr (subst-each-for-var (cdr vars) (car vars) expr))))))))

(defun syntactically-plausible-lambda-objectp1
  (edcls formals ignores ignorables type-exprs satisfies-exprs guard)

; Edcls is supposed to be a list as might be used in (DECLARE . edcls) in a
; lambda object.  We construct the lists of all ignored and ignorable vars, the
; type expressions implied by any TYPE declarations in edcls, an instance of
; each (TYPE (SATISFIES p) ...) expression, and we recover the :guard.  We also
; check all the purely syntactic stuff.  If we find syntactic errors we return
; (mv nil ...).  If the syntax is ok we return (mv t ignores ignorables
; type-exprs satisfies-exprs guard).  Note that to be truly well-formed the
; TYPE expressions in a lambda DECLARE have to be conjuncts of the guard, the
; guard has to be a logic-mode term closed on the formals, etc.  We can't check
; those properties without the world, so we're just returning the parts whose
; complete well-formedness depends on a world.

; BTW: We need the full list of type-exprs to check that the guard contains
; them all as conjuncts.  We need the satisfies-exprs separated out so we can
; check, once we have a world in mind, that each satisfies expression is a
; term.

; Initially guard is NIL, meaning we have not yet seen a guard.  There can be
; be only one (XARGS :GUARD ...) form and this flag is used to confirm that we
; haven't seen a guard yet.  If the user writes (XARGS :GUARD NIL ...) we will
; act like he or she wrote (XARGS :GUARD 'NIL ...) to avoid confusion (though a
; case could be made that a lambda expression with a nil guard is pretty
; useless).

  (cond
   ((atom edcls)

; The edcls must be a true list.  In addition, every TYPE expr must be a
; conjunct of the guard.  But we don't know the guard is a term yet so we can't
; explore it for conjuncts.  However, we know that the lambda is ill-formed if
; no guard has been seen but there are TYPE declarations.  Furthermore, we know
; it's ill-formed if the guard is 'NIL and there are TYPE declarations.

    (mv (and (eq edcls nil)
             (not (and (or (null guard)
                           (equal guard *nil*))
                       type-exprs)))
        ignores
        ignorables
        type-exprs
        satisfies-exprs
        (or guard *t*)))
   (t
    (let ((item (car edcls)))
      (case-match item
        (('TYPE spec . vars)
         (cond
          ((and (true-listp vars)
                (subsetp-eq vars formals))
           (let ((exprs (type-expressions-from-type-spec spec vars nil)))

; We use wrld=nil in type-expressions-from-type-spec, which short-cuts the
; check that each (SATISFIES p) always mentions a unary function symbol p.
; We'll have to come back and check that when we have a world.  But syntactic
; check will rule out (type (SATISFIES p var)), for example, where the user
; should have written (type (SATISFIES p) var).

             (cond (exprs
                    (syntactically-plausible-lambda-objectp1
                     (cdr edcls)
                     formals ignores ignorables

; When we use get-guards to collect type expressions in
; translate11-lambda-object we're collecting the expressions in a different
; order.  But we don't care about order.

                     (revappend exprs type-exprs)
                     (if (and (consp spec)
                              (eq (car spec) 'satisfies))
                         (add-to-set-equal (list (cadr spec) 'X) satisfies-exprs)
                         satisfies-exprs)
                     guard))
                   (t (mv nil nil nil nil nil nil)))))
          (t (mv nil nil nil nil nil nil))))
        (('IGNORE . vars)
         (cond
          ((and (true-listp vars)
                (subsetp-eq vars formals))
           (syntactically-plausible-lambda-objectp1
            (cdr edcls)
            formals

; Note: When we ignore-vars in translate11-lambda-object we're collecting the
; variables in a different order.  But we don't care about order.

            (revappend vars ignores)
            ignorables type-exprs satisfies-exprs guard))
          (t (mv nil nil nil nil nil nil))))
        (('IGNORABLE . vars)
         (cond
          ((and (true-listp vars)
                (subsetp-eq vars formals))
           (syntactically-plausible-lambda-objectp1
            (cdr edcls)
            formals ignores

; Note: When we ignorable-vars in translate11-lambda-object we're collecting
; the variables in a different order.  But we don't care about order.

            (revappend vars ignorables)
            type-exprs satisfies-exprs guard))
          (t (mv nil nil nil nil nil nil))))
        (('XARGS :GUARD g :SPLIT-TYPES 'T)
         (cond
          ((null guard) ; no guard seen yet

; If the symbol nil appears as an explicitly declared guard then the LAMBDA
; isn't syntactically plausible: The guard is always translated and the symbol
; nil would become 'NIL, which is a legal (but impossible to satisfy) guard.
; But a raw symbol nil makes no sense: it's not even a term.

           (if (null g)
               (mv nil nil nil nil nil nil)
               (syntactically-plausible-lambda-objectp1
                (cdr edcls)
                formals ignores ignorables
                type-exprs satisfies-exprs
                g)))
          (t (mv nil nil nil nil nil nil))))
        (& (mv nil nil nil nil nil nil)))))))

(defun flatten-ands-in-lit (term)
  (declare (xargs :guard (pseudo-termp term)))
  (case-match term
              (('if t1 t2 t3)
               (cond ((equal t2 *nil*)
                      (append (flatten-ands-in-lit (dumb-negate-lit t1))
                              (flatten-ands-in-lit t3)))
                     ((equal t3 *nil*)
                      (append (flatten-ands-in-lit t1)
                              (flatten-ands-in-lit t2)))
                     (t (list term))))
              (& (cond ((equal term *t*) nil)
                       (t (list term))))))

(defun flatten-ands-in-lit-lst (x)
  (if (endp x)
      nil
    (append (flatten-ands-in-lit (car x))
            (flatten-ands-in-lit-lst (cdr x)))))

; See the comment in Syntactically-Plausible-Lambda-Objectp (from which this
; record gets its name) for an explanation of the fields.

(defrec splo-extracts-tuple ((gflg . satisfies-exprs) . (guard . body)) t)

(mutual-recursion

(defun syntactically-plausible-lambda-objectp (gflg x)

; This function takes a purported lambda expression and determines if it is
; syntactically well-formed -- at least as far as that can be determined
; without access to the world.  The result is either nil or a list, called the
; ``extracts'' from the lambda object.  The extracts is a list of
; splo-extracts-tuples, where the gflg field indicates whether the tuple comes
; from a guard or not and the other fields, satisfies-exprs, guard, and body
; are the corresponding parts of the TYPE, :GUARD, and body of the lambda
; object.  (More on gflg below.)  Critically, the first splo-extracts-tuple in
; the extracts contains the gflg, satisfies-exprs, guard, and body of x itself;
; the remaining tuples are from lambda objects properly within x.  To confirm
; well-formedness all of the extracts must be checked for certain properties
; wrt the world.  The point of collecting these tuples is so that the lambda
; cache can determine whether the lambda object is well-formed in a subsequent
; world, without having to re-parse the object.  (It is possible a lambda
; object was added to the cache even before every ``function'' symbol in it was
; defined, or before they're all :logic mode, or before they're all guard
; verified, or was added when it was perfectly well-formed but the world has
; been undone since rendering it ill-formed.)  Roughly speaking, if a lambda
; object is syntactically plausible and all the components of the
; splo-extracts-tuples are terms in the world, the object is well-formed.

; We would like to believe that if x is syntactically plausible then there is
; some world in which it is well-formed.  But our plausibility check, which
; relies on pseudo-termp to check alleged terms (without access to world), is
; insufficient.  Here are some examples of syntactically plausible lambda
; objects that no world makes well-formed.  Each example suggests a
; strengthening of the test on body below.

; (lambda (x) (cons (undef x) (undef x x))) - symb with multiple arities
; (lambda (x) (cadr x)) - primitive macro assumed to be a function symbol

; It will turn out that even though these lambdas pass the syntactic
; plausibility test the cache will treat them as :UGLY (hopelessly doomed)
; because it uses the stronger potential-termp test (which needs a world to
; detect all primitives) instead of mere pseudo-termp.  But historically we
; relied initially on syntactic plausibility alone and the only :UGLY lambdas
; were the implausible ones.

; The consequence of that weakness of the simple pseudo-termp test was that
; make-new-cl-cache-line assigned the status :BAD to these lambda expressions
; when they should be assigned :UGLY.  Anthropomorphically speaking, the
; cl-cache was hoping it would eventually encounter a world that makes these
; :BAD lambdas well-formed and will check termp on them every time they're
; apply$'d in a different world.  If we assigned status :UGLY we would,
; correctly, never try to validate them.  See potential-term-listp and its use
; in managing the cl-cache in make-new-cl-cache-line.

; Because of the translate-time enforcement of well-formedness on explicitly
; quoted lambda objects and lambda$s, the only way to get an :ugly lambda into
; the cache is to sneak it past translate, e.g., write (cons 'lambda '((x)
; (cadr x))) or better yet `(lambda (x) (cadr x)).  If, for example, a lambda
; object was created by a lambda$ then there really is a world in which it's
; well-formed, i.e., the one translate used, even if in the current world the
; lambda is :BAD because of undos.

; Furthermore, we'd really like to check that the body and guard satisfy the
; syntactic rules on the use of formals vis-a-vis the free-vars and IGNORE and
; IGNORABLE declarations.  Those rules can't be checked unless we can sweep the
; body and guard to collect the vars, and we can do that if we know merely
; pseudo-termp.  The resultant vars are in fact the free vars in any world that
; makes body and guard terms.  Any lambda that fails the vars checks will be
; correctly classed as :UGLY.

; Now we discuss the gflg.  It was introduced for V8.4.  Prior to that,
; syntactically-plausible-lambda-objectp built 3-tuples.  But then we allowed
; :program mode functions to be badged.  This meant that well-formed lambda
; objects no longer had to be in :logic mode.  However, their bodies have to be
; badged.  Given that background, consider the (slightly cleaned-up)
; translation of the loop$ below, where gp and mog are :program mode functions
; and mog has been badged.

; (loop$ for e in lst collect :guard (gp e) (mog e))

; translates to

; (COLLECT$
;  '(LAMBDA (LOOP$-IVAR)
;           (DECLARE (XARGS :GUARD ((LAMBDA (E) (GP E)) LOOP$-IVAR)
;                           :SPLIT-TYPES T)
;                    (IGNORABLE LOOP$-IVAR))
;           ((LAMBDA (E) (MOG E)) LOOP$-IVAR))
;  LST)

; where we're removed the return-last cruft normally around the body.  Note
; there are two interior lambdas, one for the :guard and one for the body.  For
; the body, we will ultimately require that MOG be badged, though we can't
; check that syntactically (it may become badged).  You might think we need GP
; to be badged.  But you would be wrong!  In truth, these are two different
; kinds of lambdas.  The one in the guard is an ACL2 lambda expression, but the
; one in the body is interpreted by EV$ each time the outer lambda is applied
; to an element of LST.  So both (GP E) and (MOG E) need to be :logic terms if
; proofs are done with them, but MOG needs a badge and GP doesn't.  The role of
; the gflg is to mark the tuples that come from :guards.

  (case-match x
    (('LAMBDA formals body)
     (if (and (arglistp formals)
              (pseudo-termp body)
              (let ((used-vars (all-vars body)))

; In the general case below, where there's a DECLARE form with IGNORE and
; IGNORABLE, we check conformance with those declarations.  But here there are
; no such declarations.  This just means that there must be no free vars.  At
; one time we also checked that every var is used, but that is not actually an
; invariant of well-formed terms, even though it is enforced at translate-
; time.  In particular ((lambda (e x) (declare (ignorable e x)) x) a b)
; translates non-erroneously to ((LAMBDA (E X) X) A B), where E is unusued in
; the lambda.

                (subsetp-eq used-vars formals)))
         (let ((ans (syntactically-plausible-lambda-objectsp-within gflg body)))
           (cond
            ((null ans) nil)
            ((eq ans t) (list (make splo-extracts-tuple
                                    :gflg gflg
                                    :satisfies-exprs nil
                                    :guard *t*
                                    :body body)))
            (t (cons (make splo-extracts-tuple
                           :gflg gflg
                           :satisfies-exprs nil
                           :guard *t*
                           :body body)
                     ans))))
         nil))
    (('LAMBDA formals ('DECLARE . edcls) body)
     (if (arglistp formals)
         (mv-let (flg ignores ignorables type-exprs satisfies-exprs guard)
           (syntactically-plausible-lambda-objectp1 edcls formals
                                                    nil nil nil nil nil)
           (if (and flg
                    (pseudo-termp guard)
                    (subsetp-equal (flatten-ands-in-lit-lst type-exprs)
                                   (flatten-ands-in-lit guard))
                    (pseudo-termp body)
                    (subsetp-eq (all-vars guard) formals)
                    (let ((used-vars (all-vars body)))

; We check that (a) there are no free vars and (b) that no var declared IGNOREd
; is actually used, and (c) that all unused vars that aren't declared IGNOREd
; are declared IGNORABLE.

                      (and (subsetp-eq used-vars formals)          ; (a)
                           (not (intersectp-eq used-vars ignores)) ; (b)
                           (subsetp-eq (set-difference-eq          ; (c)
                                        (set-difference-eq formals used-vars)
                                        ignores)
                                       ignorables))))
               (let* ((ans1 (syntactically-plausible-lambda-objectsp-within
                             t
                             guard))
                      (ans2 (if ans1
                                (syntactically-plausible-lambda-objectsp-within
                                 gflg
                                 body)
                                nil)))
                 (cond
                  ((null ans2) nil)
                  ((eq ans1 t)
                   (if (eq ans2 t)
                       (list (make splo-extracts-tuple
                                   :gflg gflg
                                   :satisfies-exprs satisfies-exprs
                                   :guard guard
                                   :body body))
                       (cons (make splo-extracts-tuple
                                   :gflg gflg
                                   :satisfies-exprs satisfies-exprs
                                   :guard guard
                                   :body body)
                             ans2)))
                  ((eq ans2 t)
                   (cons (make splo-extracts-tuple
                               :gflg gflg
                               :satisfies-exprs satisfies-exprs
                               :guard guard
                               :body body)
                         ans1))
                  (t (cons (make splo-extracts-tuple
                                 :gflg gflg
                                 :satisfies-exprs satisfies-exprs
                                 :guard guard
                                 :body body)
                           (append ans1 ans2)))))
               nil))
         nil))
    (& nil)))

(defun syntactically-plausible-lambda-objectsp-within (gflg body)

; Body is a pseudo-termp and we call syntactically-plause-lambda-objectsp on
; every quoted lambda-like object in it and return one of nil (meaning we found
; a syntactically illegal quoted lambda-like object), t (meaning there were no
; quoted lambda-like objects found), or a list of all the splo-extracts-tuples
; that need further checking by well-formed-lambda-objectp1.

  (cond
   ((variablep body) t)
   ((fquotep body)
    (cond ((and (consp (unquote body))
                (eq (car (unquote body)) 'lambda))
           (syntactically-plausible-lambda-objectp gflg (unquote body)))
          (t t)))
   ((flambda-applicationp body)
    (let* ((ans1
            (syntactically-plausible-lambda-objectp
             gflg
             (ffn-symb body)))
           (ans2
            (if ans1
                (syntactically-plausible-lambda-objectsp-within-lst
                 gflg
                 (fargs body))
                nil)))
      (cond
       ((null ans2) nil) ; = (or (null ans1) (null ans2))
       ((eq ans1 t) ans2)
       ((eq ans2 t) ans1)
       (t (append ans1 ans2)))))
   (t (syntactically-plausible-lambda-objectsp-within-lst
       gflg
       (fargs body)))))

(defun syntactically-plausible-lambda-objectsp-within-lst (gflg args)
  (cond
   ((null args) t)
   (t (let* ((ans1
              (syntactically-plausible-lambda-objectsp-within
               gflg
               (car args)))
             (ans2
              (if ans1
                  (syntactically-plausible-lambda-objectsp-within-lst
                   gflg
                   (cdr args))
                  nil)))
        (cond
         ((null ans2) nil)
         ((eq ans1 t) ans2)
         ((eq ans2 t) ans1)
         (t (append ans1 ans2))))))))

(defun collect-programs (names wrld)

; Names is a list of function symbols.  Collect the :program ones.

  (cond ((null names) nil)
        ((programp (car names) wrld)
         (cons (car names) (collect-programs (cdr names) wrld)))
        (t (collect-programs (cdr names) wrld))))

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

; Essay on the Badge-Table

; The badge-table is a table.  It's :guard is badge-table-guard and the table
; is initialized in apply.lisp.  The table has only one entry, named
; :badge-userfn-structure.  (Once upon a time it had another entry but that
; that was eliminated and we never simplified its structure.)  The
; :badge-userfn-structure is an alist with entries of the form
; (fn warrantp badge), where fn is a function symbol, warrantp is t or nil
; indicating whether there is a warrant for fn, and badge is the apply$-badge
; record for fn.

; Note: As documented in apply-constraints.lisp, there are three categories of
; function symbols known to apply$: primitives like CONS and BINARY-+, boot
; functions like TAMEP and APPLY$ itself, and user-defined functions.
; (Functions in the last category were necessarily defined by the user -- the
; user might have taken a system function and converted it to :logic mode and
; then successfully called defwarrant on it -- but we call the last category
; ``user-defined'' because mostly they are!)  Badges for primitives and boot
; functions are built-in.  The badge-table's job is to tell us the badges of
; user-defined functions.

; As of Version 8.3, every badged user-defined function had a warrant.  See
; Badges versus Warrants in apply-constraints.lisp.  But this may change and
; should not be assumed in the source code.  For example, currently defwarrant
; insists that warrantable functions have a restricted form of measure,
; permitting us to show that a model of apply$ could be admitted.  But we see
; no reason why such a function couldn't be given a badge but no warrant.  Such
; a function couldn't be apply$d but could be used in a function that is
; apply$d.  (We once disallowed multi-valued functions to have warrants but
; permitted them to be used in functions that did; but now apply$ handles
; multi-valued functions.)  Or, perhaps we'll permit :program mode functions to
; have badges so they can be handled by apply$ in the evaluation theory; they
; would then have badges but not warrants (since warrants are necessarily
; logical).  To allow such eventual extensions the :badge-userfn-structure
; includes not just the badge but a flag indicating whether fn has been issued
; a warrant.  If the warrantp flag is set for fn then its warrant function is
; named APPLY$-WARRANT-fn.  See warrant-name.

; On Why Warrantp is not in the Badge:

; We decided not to put the warrantp flag into the badge because we didn't want
; to change the structure of badges because there are places where car/cdr
; nests are used instead of the record accessors in certain theorems.  Here is
; a comment from books/apply-model-2/apply-prim.lisp:

; ; Note: Unfortunately, record accessors translate into lambda applications.
; ; :Rewrite rules handle this appropriately by beta reducing the lambda
; ; applications in the conclusion.  But :linear rules do not.  So we've written
; ; all the rules in terms of car/cdr nests rather than access terms. FTR:

; ; (access apply$-badge x :arity) = (car (cdr x))
; ; (access apply$-badge x :out-arity) = (car (cdr (cdr x)))
; ; (access apply$-badge x :ilks) = (cdr (cdr (cdr x)))

; The same violation of the record abstraction is known to occur in
; books/projects/apply-model-2/ex1/doppelgangers.lisp
; books/projects/apply-model-2/ex2/doppelgangers.lisp

; In addition, there are numerous books where explicit badges are quoted,
; as in books/projects/apply-model-2/ex2/defattach-demo.lisp where we show

; (expected-to :succeed :evaluation
;              (badge 'expt-5)
;              '(APPLY$-BADGE 1 1 . T))

; And explicit badges are displayed about a dozen times in
; books/system/doc/acl2-doc.lisp.

; On a more principled level, the idea of :program mode functions having badges
; encourages the view that badges are a syntactic property having nothing to do
; with logical justification and just recording whether a function maintains
; the discipline that :FN arguments are treated exclusively as functions and
; not sometimes as data.  Warrants, on the other hand, connect such functions
; to the logic.

; In any case, we decided not to put the warrantp flag into the badge!

; The entries in the :badge-userfn-structure are tuples as built and accessed below.
; You can think of them as though we defined

; (defrec badge-userfn-structure-tuple (fn warrantp badge) t)

; so that the fn is in the car, allowing lists of these tuples to be an alist
; with function symbols as keys.  We define our own ``make'' and ``access''
; macros, mainly so that we can use those macros in rewrite rules.  The defrec
; access macros expand into let-forms which make them unsuitable for use in the
; lhs.

(defun make-badge-userfn-structure-tuple (fn warrantp badge)
; Keep this function in sync with badge-table-guard and the recognizer below.
; WARNING: keep fn in the car, as noted above.

  (list fn warrantp badge))

(defun put-badge-userfn-structure-tuple-in-alist (tuple alist)

; This is the way we put a new tuple into the badge-table -- or change the
; fields of an existing tuple for the fn.  However, if we know that fn is not
; already bound in the alist, we can just cons the tuple on instead of using
; this function.

  (if (assoc-eq (car tuple) alist)
      (put-assoc-eq (car tuple) (cdr tuple) alist)
      (cons tuple alist)))

(defun weak-badge-userfn-structure-tuplep (x)

; We check that x is of the form (& & & . &) so that we can access the fn,
; warrantp, and badge in guard-verified ways after checking this predicate.

  (declare (xargs :mode :logic :guard t))
  (and (consp x)
       (consp (cdr x))
       (consp (cddr x))))

(defmacro access-badge-userfn-structure-tuple-warrantp (x)
  `(cadr ,x))

(defmacro access-badge-userfn-structure-tuple-badge (x)
  `(caddr ,x))

; On some occasions we may want to know both if a function has a badge and
; whether it is warranted.  So we provide three accessors.

; WARNING: These macros only recover badges for user-defined functions!  To get
; the badge of any badged function, use executable-badge.  To get the warrant
; name of any warranted function, use find-warrant-function-name.

(defmacro get-warrantp (fn wrld)

; Warning: This macro expects fn to be a userfn.  It fais for apply$ primitives
; and boot functions!  To determine whether a given symbol has or needs a
; warrant, use find-warrant-function-name.

  `(access-badge-userfn-structure-tuple-warrantp
    (assoc-eq ,fn
              (cdr (assoc-eq :badge-userfn-structure
                             (table-alist 'badge-table ,wrld))))))

(defmacro get-badge (fn wrld)

; Warning: This macro expects fn to be a userfn.  It fails for apply$
; primitives and boot functions!  To find the badge, if any, of any symbol, use
; executable-badge.

  `(access-badge-userfn-structure-tuple-badge
    (assoc-eq ,fn
              (cdr (assoc-eq :badge-userfn-structure
                             (table-alist 'badge-table ,wrld))))))

(defmacro get-badge-and-warrantp (fn wrld)

; Warning: This macro expects fn to be a userfn.  It fails for apply$
; primitives and boot functions!

  `(let ((temp (assoc-eq ,fn
                         (cdr (assoc-eq :badge-userfn-structure
                                        (table-alist 'badge-table ,wrld))))))
     (mv (access-badge-userfn-structure-tuple-badge temp)
         (access-badge-userfn-structure-tuple-warrantp temp))))

(defun warrant-name (fn)

; Warning: Keep this in sync with warrant-name-inverse.  This function is
; purely syntactic.  There is no guarantee that the returned symbol is actually
; the defwarrant-created warrant function of fn!  Fn may have no warrant!

; From fn generate the name APPLY$-WARRANT-fn.

  (declare (xargs :mode :logic ; :program mode may suffice, but this is nice
                  :guard (symbolp fn)))
  (intern-in-package-of-symbol
   (concatenate 'string
                "APPLY$-WARRANT-"
                (symbol-name fn))
   fn))

(defun string-prefixp-1 (str1 i str2)
  (declare (type string str1 str2)
           (type (unsigned-byte 29) i)
           (xargs :guard (and (<= i (length str1))
                              (<= i (length str2)))))
  (cond ((zpf i) t)
        (t (let ((i (1-f i)))
             (declare (type (unsigned-byte 29) i))
             (cond ((eql (the character (char str1 i))
                         (the character (char str2 i)))
                    (string-prefixp-1 str1 i str2))
                   (t nil))))))

(defun string-prefixp (root string)

; We return a result propositionally equivalent to
;   (and (<= (length root) (length string))
;        (equal root (subseq string 0 (length root))))
; but, unlike subseq, without allocating memory.

; At one time this was a macro that checked `(eql 0 (search ,root ,string
; :start2 0)).  But it seems potentially inefficient to search for any match,
; only to insist at the end that the match is at 0.

  (declare (type string root string)
           (xargs :guard (<= (length root) (fixnum-bound))))
  (let ((len (length root)))
    (and (<= len (length string))
         (assert$ (<= len (fixnum-bound))
                  (string-prefixp-1 root len string)))))

(defun warrant-name-inverse (warrant-fn)

; Warning: Keep this in sync with warrant-name (q.v.).

  (declare (xargs :guard (symbolp warrant-fn)))
  (let ((warrant-fn-name (symbol-name warrant-fn)))
    (and (string-prefixp "APPLY$-WARRANT-" warrant-fn-name)
         (intern-in-package-of-symbol
          (subseq warrant-fn-name
                  15 ; (length "APPLY$-WARRANT-")
                  (length warrant-fn-name))
          warrant-fn))))

; Matt:  The following function used to be called warrantp.
(defun warrant-function-namep (warrant-fn wrld)

; We check whether warrant-fn is the warrant function of some function, fn.  If
; fn has a warrant, its name is APPLY$-WARRANT-fn.  But having a name of that
; shape is no guarantee that the function is the warrant function for fn.  (Fn
; may have no warrant function and apply$-warrant-fn might have been --
; maliciously! -- defined by the user.)  Thus, we answer this question by
; recovering fn from warrant-fn and then looking in the badge-userfn-structure
; to see whether fn has a warrant.

; Note: We allow the user to define functions named APPLY$-WARRANT-fn
; independently of warrants, but that would preclude the subsequent warranting
; of fn.  We considered allowing the user to supply the name of the warrant
; function for fn, instead of using the purely syntactic convention of
; APPLY$-WARRANT-fn.  However, it would then be impossible to provide the macro
; (warrant fn).  The table guard for badge-table, badge-table-guard, actually
; confirms that if the warrantp flag is set by the user, indicating that fn has
; a warrant, then the name of the warrant is indeed APPLY$-WARRANT-fn and that
; that symbol is properly constrained as by defwarrant.

  (declare (xargs :guard (and (symbolp warrant-fn)
                              (plist-worldp wrld))))
  (let ((fn (warrant-name-inverse warrant-fn)))
    (and fn
         (get-warrantp fn wrld))))

; We originally defined the apply$-badge and the commonly used generic badges in
; apply-prim.lisp but they're needed earlier now.

; We evaluate the defrec below in :logic mode so that the its accessors can be
; used in doppelganger-badge-userfn.
(encapsulate () (logic)
(defrec apply$-badge

; Warning: Keep this in sync with apply$-badge-arity, below.

  (arity out-arity . ilks)
  nil)
)

(defmacro apply$-badge-arity (x)

; Warning: Keep this in sync with apply$-badge, above.

; Essentially, this expands to (access apply$-badge x :arity).  However, that
; form may not be suitable for use in rules, because it further expands to a
; lambda application.

  `(cadr ,x))

(defun weak-apply$-badge-p (x)
  (declare (xargs :mode :logic :guard t))
  (and (consp x)
       (eq (car x) 'APPLY$-BADGE)
       (let ((x (cdr x)))
         (and (consp x)
              (let ((x (cdr x))) (consp x))))))

(defconst *generic-tame-badge-1*
  (MAKE APPLY$-BADGE :ARITY 1 :OUT-ARITY 1 :ILKS t))
(defconst *generic-tame-badge-2*
  (MAKE APPLY$-BADGE :ARITY 2 :OUT-ARITY 1 :ILKS t))
(defconst *generic-tame-badge-3*
  (MAKE APPLY$-BADGE :ARITY 3 :OUT-ARITY 1 :ILKS t))
(defconst *apply$-badge*
  (MAKE APPLY$-BADGE :ARITY 2 :OUT-ARITY 1 :ILKS '(:FN NIL)))
(defconst *ev$-badge*
  (MAKE APPLY$-BADGE :ARITY 2 :OUT-ARITY 1 :ILKS '(:EXPR NIL)))

; In order to infer badges of new functions as will be done in defwarrant we
; must be able to determine the badges of already-badged functions.  Similarly,
; we must be able to determine that certain quoted expressions are tame.  So we
; define executable versions of badge and tamep that look at data structures
; maintained by defwarrant.

(defun executable-badge (fn wrld)

; Find the badge, if any, for any fn in wrld; else return nil.  Aside from
; primitives and the apply$ boot functions, all badges are stored in the
; badge-table entry :badge-userfn-structure.

; Note: The word ``executable'' in the name means this function is executable,
; unlike its namesake, badge, which is just constrained.

; Aside: The apply$ primitives have badges stored in the *badge-prim-falist*.
; The apply$ boot functions have built-in badges as specified below.  All other
; badged functions are in the :badge-userfn-structure of the badge-table.  The
; apply$ primitives and boot functions do not have warrants and don't need
; them.  The functions in :badge-userfn-structure may or may not have warrants,
; depending on the warrantp flag of the entry for fn in the structure.  See the
; Essay on the Badge-Table.

; There's nothing wrong with putting this in logic mode but we don't need it in
; logic mode here.  This function is only used by defwarrant, to analyze and
; determine the badge, if any, of a newly submitted function, and in translate,
; to determine if a lambda body is legal.  (To be accurate, this function is
; called from several places, but all of them are in support of those two
; issues.)  Of course, the badge computed by a non-erroneous (defwarrant fn)
; is then built into the defun of APPLY$-WARRANT-fn and thus participates in
; logical reasoning; so the results computed by this function are used in
; proofs.

  (declare (xargs :mode :program))
  (cond
   ((and (global-val 'boot-strap-flg wrld)
         (or (not (getpropc '*badge-prim-falist* 'const nil wrld))
             (not (getpropc 'badge-table 'table-guard nil wrld))))
    (er hard 'executable-badge
        "It is illegal to call this function during boot strapping because ~
         primitives have not yet been identified and badges not yet computed!"))
   ((symbolp fn)
    (let ((temp
           (hons-get fn ; *badge-prim-falist* is not yet defined!
                     (unquote
                      (getpropc '*badge-prim-falist* 'const nil wrld)))))
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

(defun find-warrant-function-name (fn wrld)

; If fn has a warrant function, return the name of the warrant function.  If fn
; is known to apply$ and needs no warrant, e.g., fn is CONS or fn is APPLY$,
; etc., return t.  Else, return nil.  See executable-badge for further
; discussion.

  (declare (xargs :mode :program))
  (cond
   ((and (global-val 'boot-strap-flg wrld)
         (or (not (getpropc '*badge-prim-falist* 'const nil wrld))
             (not (getpropc 'badge-table 'table-guard nil wrld))))
    (er hard 'find-warrant-function-name
        "It is illegal to call this function during boot strapping because ~
         primitives have not yet been identified and warrants not yet ~
         computed!"))
   ((symbolp fn)
    (let ((temp
           (hons-get fn ; *badge-prim-falist* is not yet defined!
                     (unquote
                      (getpropc '*badge-prim-falist* 'const nil wrld)))))
      (cond
       (temp t)
       ((eq fn 'BADGE) t)
       ((eq fn 'TAMEP) t)
       ((eq fn 'TAMEP-FUNCTIONP) t)
       ((eq fn 'SUITABLY-TAMEP-LISTP) t)
       ((eq fn 'APPLY$) t)
       ((eq fn 'EV$) t)
       (t (let ((temp (get-warrantp fn wrld)))
            (cond
             (temp (warrant-name fn))
             (t nil)))))))
   (t nil)))

; Compare this to the TAMEP clique.

(defabbrev executable-tamep-lambdap (fn wrld)

; This function expects a consp fn (which is treated as a lambda expression by
; apply$) and checks whether fn is a tame lambda.  Compare to tamep-lambdap.
; It does not check full well-formedness.  It is possible for an ill-formed
; lambda expression to pass this test!

; Note: The word ``executable'' in the name means this ``function'' is
; executable, unlike its namesake tamep-lambdap which involves constrained
; functions.  The same clarification applies to the mutually recursive clique
; below.

; This function is one of the ways of recognizing a lambda object.  See the end
; of the Essay on Lambda Objects and Lambda$ for a discussion of the various
; recognizers and their purposes.

  (and (lambda-object-shapep fn)
       (symbol-listp (lambda-object-formals fn))
       (executable-tamep (lambda-object-body fn) wrld)))

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
            ((eq (access apply$-badge bdg :ilks) t)
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
; Given (tamep-lambdap fn), (cadr fn) = (lambda-object-formals fn).
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

(defun well-formed-lambda-objectp1 (extracts wrld)

; Extracts is a non-nil list splo-extracts-tuples, as returned by a successful
; syntactically-plausible-lambda-objectp.  We check that each tuple contains
; truly well-formed components wrt wrld.

  (cond
   ((endp extracts) t)
   (t (let ((gflg (access splo-extracts-tuple (car extracts) :gflg))
            (satisfies-exprs
             (access splo-extracts-tuple (car extracts) :satisfies-exprs))
            (guard (access splo-extracts-tuple (car extracts) :guard))
            (body (access splo-extracts-tuple (car extracts) :body)))
        (and (term-listp satisfies-exprs wrld)
             (termp guard wrld)
; Prior to V8.4 we included:
;                 (null (collect-programs (all-fnnames guard) wrld))
; but now we allow :program mode fns in the guard (and body).  But this will
; force the containing defun to be in :program mode too.
             (termp body wrld)
             (or gflg ; see syntactically-plausible-lambda-object
                 (executable-tamep body wrld))
             (well-formed-lambda-objectp1 (cdr extracts) wrld))))))

(defun well-formed-lambda-objectp (x wrld)

; We check that x is a well-formed lambda object.  This means it is either
; (lambda formals body) or (lambda formals dcl body) where the formals are
; distinct variables, the dcl is as expected in a lambda object, the :guard is
; a term closed under formals in wrld and the body is a tame term closed under
; formals in wrld.  See the Essay on Lambda Objects and Lambda$.

; We do not check that the :guard and/or body are composed of guard verified
; functions, nor do we prove the guard conjectures for x.

  (let ((extracts (syntactically-plausible-lambda-objectp nil x)))

; Extracts is either nil, indicating that the object x is not syntactically
; plausible or is a list of splo-extracts-tuples to be checked wrt the wrld.

    (and extracts
         (well-formed-lambda-objectp1 extracts wrld))))

(defun all-fnnames! (lst-flg where-flg collect-flg
                             term ilk wrld acc)

; Roughly speaking, we collect every function symbol in term -- including those
; occurring as quoted symbols in :FN slots and in well-formed quoted lambda
; constants in :FN slots.  This is coded as a flagged mutually recursive
; function with lst-flg = t meaning term is really a list of terms.

; Where-flg controls from where we collect.  It can be:

; :inside - only collect while inside a quoted well-formed object in an ilk :FN
;   or :EXPR slot

; :outside - only collect while outside those objects -- this is the same as
;   all-fnnames and is only implemented because it's easy and symmetric

; :both - collect both inside and outside.

; Collect-flg is t if we are in a context in which we're collecting.

; IMPORTANT NOTE: Think carefully about the initial values of where-flg and
; collect-flg!  Typically, if you're processing a term, you're outside of
; quoted functions and expressions, so if your where-flg = :INSIDE, your
; initial collect-flg should be nil.  But if your where-flg = :OUTSIDE or :BOTH
; your initial collect-flg should be t.

; Term is either a term or a list of terms, ilk is the corresponding ilk or
; list of ilks, and acc is our collection site.

; Purpose: Certain of these sets of function symbols collected must be in
; :logic mode and warranted for term to be considered :logic mode.  They are
; the fns that are encountered by the rewriter if we rewrite this term.  When
; this term is compiled, these are the fns that will be called directly.  We
; don't collect the fn in (apply$ 'fn ...) or in (ev$ '(fn ...) ...) because
; they are not called directly but only fed to apply$.

; Warning: This function must not be called during boot-strap, so check
; (global-val 'boot-strap-flg wrld) before calling this function.

  (cond
   (lst-flg ; term is a list of terms
    (cond ((endp term) acc)
          (t (all-fnnames! nil where-flg collect-flg
                           (car term)
                           (car ilk)
                           wrld
                           (all-fnnames! t where-flg collect-flg
                                         (cdr term)
                                         (cdr ilk)
                                         wrld
                                         acc)))))
   ((variablep term) acc)
   ((fquotep term)
    (cond ((eq where-flg :outside) acc)
          ((eq ilk :FN)
           (let ((evg (unquote term)))
             (cond
              ((symbolp evg)
               (add-to-set-eq evg acc))
              ((and (consp evg)
                    (eq (car evg) 'lambda)
                    (well-formed-lambda-objectp evg wrld))
               (all-fnnames! nil where-flg t
                             (lambda-object-body evg)
                             nil wrld acc))
              (t acc))))
          ((eq ilk :EXPR)
           (let ((evg (unquote term)))
             (cond
              ((termp evg wrld)
               (all-fnnames! nil where-flg t
                             evg nil wrld acc))
              (t acc))))
          (t acc)))
   ((lambda-applicationp term)
    (all-fnnames! t where-flg collect-flg
                  (fargs term)
                  nil
                  wrld
                  (all-fnnames! nil where-flg collect-flg
                                (lambda-body (ffn-symb term))
                                nil wrld acc)))
   (t (let ((bdg (executable-badge (ffn-symb term) wrld)))
        (all-fnnames!
         t where-flg collect-flg
         (fargs term)
         (if (or (null bdg)
                 (eq (access apply$-badge bdg :ilks) t))
             nil
             (access apply$-badge bdg :ilks))
         wrld
         (if collect-flg
             (add-to-set-eq (ffn-symb term) acc)
             acc))))))

; Essay on Cleaning Up Dirty Lambda Objects

; A dirty lambda object is one that contains arbitrary but irrelevant junk that
; makes it unnecessarily distinct from functionally equivalent lambda objects.
; There are three kinds of junk: DECLARE forms, guard holder forms like
; RETURN-LAST, and lambda expressions.  For clarity, an example of the last is

; '(lambda (x) ((lambda (y) (car y)) x))

; which arises in the translation of a lambda$ containing a LET form.
; In fact,

; ACL2 !>:translam (lambda$ (x) (let ((y x)) (car y)))
;  '(LAMBDA (X)
;           (DECLARE (IGNORABLE X))
;           (RETURN-LAST 'PROGN
;                        '(LAMBDA$ (X) (LET ((Y X)) (CAR Y)))
;                        ((LAMBDA (Y) (CAR Y)) X)))

; illustrates a dirty lambda suffering from all three afflictions!
; Functionally, the junk contributes nothing.  Furthermore, the user is often
; unaware of the junk because much is removed by
; untranslate1-lambda-objects-in-fn-slots when we print quoted lambda objects
; in :fn slots as lambda$ expressions.  Even when the junk survives that
; untranslation it is hard to notice because the Lisp programmer is accustomed
; to ignoring such declarations.  For example, who notices the difference
; between (declare (ignorable x y)) and (declare (ignorable y x)) or the
; absence of the declaration altogether?

; The cleaned up version of the triply dirty lambda above is

; '(lambda (x) (car x)).

; By cleaning up dirty lambdas in defun bodies and other rules, and in
; preprocess-clause, we can render trivial some problems that otherwise require
; induction.  For example, if lam1 and lam2 are two dirty lambdas that clean up
; to the same thing, then

; (equal (sum$ 'lam1 lst) (sum$ 'lam2 lst))

; must be proved by induction because the two lambda objects differ and their
; equivalence is only discovered upon their applications.  But after cleaning
; up that equality it is trivial.

; Cleaning up consists of deleting DECLAREs, lifting some subterms out of guard
; holders like RETURN-LAST, and beta reducing lambda explressions in dirty but
; well-formed lambda objects occurring in :FN slots.  The clean-up process uses
; remove-guard-holders on the body, but since it only runs on tame bodies the
; argument in remove-guard-holders1 establishes that we haven't changed the
; functionality of the transformed lambda object.

; Most of this essay focuses on beta reduction of all lambda expressions in
; well-formed lambda objects occurring in :FN slots, when the lambda object is
; in or will be injected into a formula being proved.  There are many
; questions: Under what circumstances is that sound -- or more accurately, can
; any of the conditions mentioned above be eased?  Why do we wish to do this?
; And where in our code should we do it?  These questions are sort of
; intertwined and we discuss them that way.

; At the time we decided to do this, Fall, 2019 while working on what may
; be become Version 8.3, we first considered adding this capability to
; remove-guard-holders (actually remove-guard-holders1).  It already removed
; guard holders from lambda objects.  And in fact, we extended it to
; additionally remove the optional DECLARE forms.  These optimizations can be
; done with fairly minimal checks about the well-formedness of the lambda
; objects.

; But further extending remove-guard-holders1 to do beta reduction in lambda
; objects requires more checks.  In particular, we need a full blown
; well-formed-lambda-objectp test, which checks that the body is truly a termp
; and is in fact tame and closed.

; But if we put a well-formed-lambda-objectp test in remove-guard-holders1 we
; have to be able run executable-tamep, which can't be run during the
; boot-strap.  (Furthermore, since we have to guard verify
; remove-guard-holders1 because of its use in supporting books/system/top, we
; need to guard verify a lot of executable tameness stuff, including
; executable-badge, which is how we realized we had this boot-strapping
; problem.)  But remove-guard-holders1 is run a lot during boot-strap, e.g., in
; defun processing and in producing rules from defthm.  So there's no way we
; want to make remove-guard-holders1 uncallable during boot-strap!

; So that leaves us with the idea of a separate little simplifier that cleans
; up well-formed lambda objects in :FN slots as part of preprocess-clause, not
; in remove-guard-holders1.  That is implemented in the function
; possibly-beta-reduce-lambda-objects defined further below.

; But why do we need a full well-formed-lambda-objectp test?  If a lambda
; object is not well-formed expanding the lambdas inside it can change its
; meaning under apply$.

; We give two examples.  The first shows what can happen if the body of the
; lambda object contains an un-closed lambda application.  Consider

; '(LAMBDA (X) ((LAMBDA (A) X) '123))

; But if you expand-all-lambdas on that object's (ill-formed) body you get

; '(LAMBDA (X) X)

; If you apply$ the first lambda to '(456) the answer is NIL, because when the
; inner X is evaluated by ev$ it is not in the alist which binds A to 123.  So
; that X has value NIL under ev$.  But clearly, if you apply$ the second lambda
; to '(456) you get 456.

; The second example illustrate why tameness is crucial.  Consider

; `(LAMBDA (FN) ((LAMBDA (A) '123) (APPLY$ FN '(1 2))))

; Note that the body of this object is not tame.  But expanding the lambda
; application in it eliminates the source of untameness and produces:

; '(LAMBDA (X) '123)

; That is, expand-all-lambdas can turn an untame lambda object into a tame one.
; The question is whether their applications are always equal, and the answer
; is no.

; This may be a bit surprising because intuitively the untame part of the
; expression is clearly irrelevant.  If ev$ would just proceed through the
; expression giving unspecified values to the innermost untame parts and
; carrying on, it would discover it didn't need the values of the untame parts.

; But that is not how ev$ is defined.  The first thing it does is check whether
; the expression is tame and if it is not it stops with an UNTAME-EV$ result.

; (thm
;  (equal (apply$
;          `(LAMBDA (FN) ((LAMBDA (A) '123) (APPLY$ FN '(1 2))))
;          '(cons))
;         (untame-ev$ '((LAMBDA (A) '123) (APPLY$ FN '(1 2)))
;                     '((FN . CONS))))

;  :hints (("Goal" :expand ((:free (x)(hide x))
;                           (EV$ '((LAMBDA (A) '123) (APPLY$ FN '(1 2)))
;                                '((FN . CONS))))))

; Of course, apply$ing the tame version of the object to '(cons) produces 123
; and that is not proveably equal to the call of untame-ev$.

; So we see that expanding lambdas in an untame expression changes the value.

; Our previous remarks about (sum$ 'lam1 lst) versus (sum$ 'lam2 lst) might
; suffice to explain our interest in this whole subject, but for posterity we
; here record how this issue arose.

; First, recall that the lambda$ generated by translate for loop$ bodies
; contains a LET that binds the free variables appearing in the body.  E.g.,
; the lambda$ produced for the loop$ body in

; (loop$ for e in lst always (occ v1 e))

; is

; (lambda$ (loop$-gvars loop$-ivars)
;          (let ((v1 (car loop$-gvars))
;                (e (car loop$-ivars)))
;            (occ v1 e)))

; which, when further translated is

; '(lambda (loop$-gvars loop$-ivars)
;           ((lambda (v1 e) (occ v1 e))
;            (car loop$-gvars)
;            (car loop$-ivars)))

; ignoring markers and declares.  Observe that this constant contains the
; symbols v1 and e.

; The lambda object produced for

; (loop$ for d in lst always (occ v2 d)).

; will contain the symbols v2 and d.

; Thus

; (thm (implies (equal v1 v2)
;               (equal (loop$ for e in lst always (occ v1 e))
;                      (loop$ for d in lst always (occ v2 d)))))

; requires induction to prove because the functional identity of the two
; lambdas (when v1 is v2) is not apparent until they are applied point-wise.
; However, with the expansion of all lambda expressions within well-formed
; lambda objects, the translation of the above theorem is

; (implies (equal v1 v2)
;          (equal (always$+ '(lambda (loop$-gvars loop$-ivars)
;                              (occ (car loop$-gvars)
;                                   (car loop$-ivars)))
;                           (list v1)
;                           (loop$-as (list lst)))
;                 (always$+ '(lambda (loop$-gvars loop$-ivars)
;                              (occ (car loop$-gvars)
;                                   (car loop$-ivars)))
;                           (list v2)
;                           (loop$-as (list lst)))))

; The two always$+ expressions have the same lambda expressions and the same
; targets.  The only difference is that v1 is passed as a ``global'' in one
; where v2 is passed in the other.  Note that the quoted constants v1, v2, e,
; and d no longer occur in the formula; the only occurrences of v1 and v2 are
; as logical variables.  The proof is immediate by substitution of equals for
; equals.

; All this motivates the desire for beta-reduction in well-formed lambda
; objects in :FN slots.  We start the development of the requisite beta reducer
; by first trying to determine rapidly whether a lambda-looking object might be
; dirty.  If so, it might be reducible if it is in a well-formed lambda object.
; Then we define the function to determine whether a term contains a lambda
; object that might have a lambda application or guard holder in it.  All this
; is done without checking well-formedness of lambda objects.  If the quick
; check indicates that we might find a dirty lambda object, we pay the price of
; copying the term and cleaning up all the well-formed lambda objects in :fn
; positions.

(defstub remove-guard-holders-blocked-by-hide-p () t)
(defattach remove-guard-holders-blocked-by-hide-p constant-t-function-arity-0)

(mutual-recursion

(defun possibly-dirty-lambda-objectp1 (x)
; Warning:  This function cannot expect x to be a term, only a pseudo-termp!
  (declare (xargs :guard (pseudo-termp x)))
  (cond ((variablep x) nil)
        ((fquotep x) nil)
        ((and (eq (ffn-symb x) 'HIDE)
              (remove-guard-holders-blocked-by-hide-p))
         nil)
        ((lambda-applicationp x) t)
        ((member-eq (ffn-symb x)
                    '(RETURN-LAST
                      MV-LIST
                      CONS-WITH-HINT
                      THE-CHECK))
         t)
        (t (possibly-dirty-lambda-objectp1-lst (fargs x)))))

(defun possibly-dirty-lambda-objectp1-lst (x)
; Warning: This function cannot expect x to be a list of terms, only a list of
; pseudo-termps!
  (declare (xargs :guard (pseudo-term-listp x)))
  (cond ((endp x) nil)
        (t (or (possibly-dirty-lambda-objectp1 (car x))
               (possibly-dirty-lambda-objectp1-lst (cdr x)))))))

(defun possibly-dirty-lambda-objectp (obj)
  (and (lambda-object-shapep obj)
       (or (lambda-object-dcl obj)
           (and (pseudo-termp (lambda-object-body obj))
                (possibly-dirty-lambda-objectp1
                 (lambda-object-body obj))))))

(mutual-recursion

(defun may-contain-dirty-lambda-objectsp (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond
   ((variablep term) nil)
   ((fquotep term)
    (possibly-dirty-lambda-objectp (unquote term)))
   ((and (eq (ffn-symb term) 'HIDE)
         (remove-guard-holders-blocked-by-hide-p))
    nil)
   ((lambda-applicationp term)
    (or (may-contain-dirty-lambda-objectsp
         (lambda-body (ffn-symb term)))
        (may-contain-dirty-lambda-objectsp-lst (fargs term))))
   (t (may-contain-dirty-lambda-objectsp-lst (fargs term)))))

(defun may-contain-dirty-lambda-objectsp-lst (terms)
  (cond
   ((endp terms) nil)
   (t (or (may-contain-dirty-lambda-objectsp (car terms))
          (may-contain-dirty-lambda-objectsp-lst (cdr terms)))))))

; Here is how we beta reduce all ACL2 lambda applications.  This is entirely
; unconcerned with quoted lambda objects and just beta reduces every lambda
; application in a fully translated term.

(mutual-recursion

(defun expand-all-lambdas (term)
  (declare (xargs :guard (pseudo-termp term)
                  :verify-guards nil))
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((flambdap (ffn-symb term))
; See note below.
    (subcor-var (lambda-formals (ffn-symb term))
                (expand-all-lambdas-lst (fargs term))
                (expand-all-lambdas (lambda-body (ffn-symb term)))))
   (t (fcons-term (ffn-symb term)
                  (expand-all-lambdas-lst (fargs term))))))

(defun expand-all-lambdas-lst (terms)
  (declare (xargs :guard (pseudo-term-listp terms)
                  :verify-guards nil))
  (cond
   ((endp terms) nil)
   (t (cons (expand-all-lambdas (car terms))
            (expand-all-lambdas-lst (cdr terms))))))
 )

; Note on the recursive scheme used in expand-all-lambdas.  At one time the
; flambdap case above was written this way, which we regard as more intuitively
; correct:

;    ((flambdap (ffn-symb term))
;     (expand-all-lambdas
;      (subcor-var (lambda-formals (ffn-symb term))
;                  (fargs term)
;                  (lambda-body (ffn-symb term)))))

; But it is hard to admit the definition with this handling of lambda
; applications because the subcor-var returns a larger term to recur into.
; Rather than invent an appropriate measure, we changed the definition.  By the
; way we don't actually need expand-all-lambdas to be in :logic mode, but at
; one point in the development of the code to beta reduce well-formed lambda
; objects we needed it to be in :logic mode: the beta-reduction was going to be
; implemented in remove-guard-holders1 which has to be a guard-verified :logic
; mode function to support books in books/system/top.

; In any case, we changed the code to make it easy to admit and now offer the
; following proof of the equivalence of the old and new versions.  In this
; proof, the ``old'' definition is the (expand-all-lambdas (subcor-var ...))
; version and the ``new'' definition is (subcor-var ... (expand-all-lambdas
; ...)) one.  The new definition is the current definition.

; Lemma.  Let s and s' be finite substitutions with the same domain such
; that for all v in the common domain, if t is s(v) and t' is s'(v) then
; |- t = t'.  Also let t1 and t2 be terms such that |- t1 = t2.  Then:

; |- t1/s = t2/s'

; Assuming the Lemma, it's easy to prove by computational induction that
; the new expand-all-lambdas always produces a term provably equal to
; its input.  For the flambdap case, first apply beta reduction to
; replace the lambda by the provably equal

; (subcor-var (lambda-formals (ffn-symb term))
;             (fargs term)
;             (lambda-body (ffn-symb term)))

; Now define:

; - s  is (pairlis$ (lambda-formals (ffn-symb term))
;                   (fargs term))
; - s' is (pairlis$ (lambda-formals (ffn-symb term))
;                   (expand-all-lambdas-lst (fargs term)))
; - t1 is (lambda-body (ffn-symb term))
; - t2 is (expand-all-lambdas-lst (lambda-body (ffn-symb term)))

; Then this lambda case of the induction follows immediately from the
; Lemma above, for the values above of s, s', t1, and t2.

; The Lemma, in turn, follows immediately from these two lemmas, as I
; show below.

; Lemma 1.  Let s and s' be finite substitutions with the same domain such
; that for all v in the common domain, if t is s(v) and t' is s'(v) then
; |- t = t'.  Also let t0 be a term.  Then:

; |- t0/s = t0/s'

; Lemma 2.  Let s be a finite substitution, and let t and t' be terms
; such that |- t = t'.  Then:

; |- t/s = t'/s

; Then the Lemma follows by observing that the following are all
; provably equal, using Lemma 1 and Lemma 2 as shown below and also
; using the computational inductive hypotheses.

; t1/s1
;   {applying Lemma 1 replacing t0 by t1, s by s1, and s' by s2}
; t1/s2
;   {applying Lemma 2 replacing s by s2}
; t2/s2

; It remains to prove Lemma 1 and Lemma 2.  But Lemma 1 follows by a
; trivial induction on terms, and Lemma 2 is just the usual
; instantiation rule of inference applied to the formula, t = t'.

; Q.E.D.

; Rockwell Addition:  A major change is the removal of THEs from
; many terms.

; Essay on the Removal of Guard Holders

; We now develop the code to remove certain trivial calls, such as those
; generated by THE, from a term.  Suppose for example that the user types (THE
; type expr); type is translated (using translate-declaration-to-guard) into a
; predicate in one variable.  The variable is always VAR.  Denote this
; predicate as (guard VAR).  Then the entire form (THE type expr) is translated
; into ((LAMBDA (VAR) (THE-CHECK (guard VAR) 'type VAR)) expr).  The-check is
; defined to have a guard that logically is its first argument, so when we
; generate guards for the translation above we generate the obligation to prove
; (guard expr).  Furthermore, the definition of the-check is such that unless
; the value of state global 'guard-checking-on is :none, executing it in the
; *1* function tests (guard expr) at runtime and signals an error.

; But logically speaking, the definition of (THE-check g x y) is y.  Hence,
;   (THE type expr)
; = ((LAMBDA (VAR) (THE-check (guard VAR) 'type VAR)) expr)
; = ((LAMBDA (VAR) VAR) expr)
; = expr.
; Observe that this is essentially just the expansion of certain non-rec
; functions (namely, THE-CHECK and the lambda application) and
; IF-normalization.

; We belabor this obvious point because until Version_2.5, we kept the THEs in
; bodies, which injected them into the theorem proving process.  We now remove
; them from the stored BODY property.  It is not obvious that this is a benign
; change; it might have had unintended side-effects on other processing, e.g.,
; guard generation.  But the BODY property has long been normalized with
; certain non-rec fns expanded, and so we argue that the removal of THE could
; have been accomplished by the processing we were already doing.

; But there is another place we wish to remove such ``guard holders.''  We want
; the guard clauses we generate not to have these function calls in them.  The
; terms we explore to generate the guards WILL have these calls in them.  But
; the output we produce will not, courtesy of the following code which is used
; to strip the guard holders out of a term.

; Starting with Version_2.8 the ``guard holders'' code appears elsewhere,
; because remove-guard-holders[-weak] needs to be defined before it is called
; by constraint-info.

; Aside from applications in the prover, remove-guard-holders is used
; extensively to process rules before they are stored, to eliminate cruft that
; might make a rule inapplicable.  It is also used to clean up termination and
; induction machines and contraints.

; Note that remove-guard-holders-weak does not take world.  It is called from
; some contexts in which world is not available or is inconvenient, i.e., in
; user books.  Furthermore, it supports books/system/top.lisp where it must be
; in :logic mode and guard verified.

; Remove-guard-holders-weak does not dive into lambda objects.  It cannot do so
; soundly without knowing that the body of the quoted lambda object is a
; well-formed tame term, which it cannot determine without world.  However,
; remove-guard-holders-weak is used by clean-up-dirty-lambda-objects, which is
; called to clean up rules before storage.  But because
; clean-up-dirty-lambda-objects cannot be called by badges are all in place for
; the primitives, it cannot be called in boot-strap.  But
; remove-guard-holders-weak can be and is!  Thus, the standard idiom for
; cleaning up a formula is (possibly-clean-up-dirty-lambda-objects
; (remove-guard-holders-weak term) wrld) where the inner expression cleans up
; the term outside any lambda objects and the outer one cleans up the
; well-formed lambdas.  For convenience we define (remove-guard-holders term
; wrld) to be exactly that composition.  Occasionally you will see just
; (remove-guard-holders-weak term) because we're nervous about messing with the
; lambdas.

(mutual-recursion

(defun remove-guard-holders1 (changedp0 term)

; Warning: If you change this function, consider changing :DOC guard-holders.

; We return (mv changedp new-term), where new-term is provably equal to term,
; and where if changedp is nil, then changedp0 is nil and new-term is identical
; to term.  The second part can be restated as follows: if changedp0 is true
; then changedp is true (a kind of monotonicity), and if the resulting term is
; distinct from the input term then changedp is true.  Intuitively, if changedp
; is true then new-term might be distinct from term but we don't know that
; (especially if changedp0 is true), but if changedp is nil then we know that
; new-term is just term.

; See the Essay on the Removal of Guard Holders.

; See the various WARNINGs below.

; The minimal requirement on this function is that it return a term that is
; provably equal to term.  But since this function is used to clean up the
; bodies of tame but dirty lambda objects in :FN slots (see
; clean-up-dirty-lambda-objects) it must also satisfy the ``ev$ property'': the
; ev$ of tame input must be provably equal to the ev$ of the output.  There is
; an easy way to ensure that remove-guard-holders-weak has the ev$ property:
; remove-guard-holders1 ``merely lifts'' ordinary subterms to ordinary slots.
; We call this the ``Merely Lifts'' principle and it is a sufficient but not
; necessary condition to guarantee the ev$ property.

; We will illustrate the ``Merely Lifts'' principle in a moment, but we first
; make two important observations about tameness: First, if any ordinary
; subterm of a term is untame then the term itself is untame, or
; contrapositively, if a term is tame, every ordinary subterm is tame.  Second,
; if a term, z, is tame, then (ev$ z s) = z/s, or colloquially, ``tame terms
; evaluate to themselves.''

; So now we illustrate the Merely Lifts principle and show how it insures the
; ev$ property.  Let term be (g u (f a b)) and assume the second slots of both
; g and f are ordinary (i.e., have ilk NIL).  We assume term is tame.  But if
; (g u (f a b)) is tame, then so is (f a b) and so is b.  Finally, assume that
; remove-guard-holders-weak merely lifts the b out of (f a b), producing (g u
; b) which we assume is provably equal to (g u (f a b)).  Then (g u b) is tame
; because the only difference between (g u (f a b)) and (g u b) is in an
; ordinary slot in which one tame term has been replaced by another.  Thus (ev$
; (remove-guard-holders-weak '(g u (f a b))) s) = (ev$ '(g u b) s) = (g u b)/s,
; but (ev$ '(g u (f a b)) s) = (g u (f a b))/s.  But since (g u b) is provably
; equal to (g u (f a b)), their mutual instantiations by s are provably equal.
; So if every transformation made by remove-guard-holders-weak is a lift of
; ordinary to ordinary, that is, if remove-guard-holders-weak merely lifts, it
; has the ev$ property.

; How could it do more than merely lift?  It could, for example, lift b out but
; then embed it in a non-tame expression, e.g., produce (g u (h b)) where h is
; an unwarranted identity function.  In that case, remove-guard-holders-weak
; would satisfy its minimal requirement of provable equality without having the
; ev$ property because the attempt to ev (g u (h b)) would produce an
; untame-ev$ term, which is not provably equal to anything besides itself.

; WARNING: The take home lesson from the discussion above is: Be careful if you
; change remove-guard-holders1 so as not to introduce any unbadged functions or
; untame expressions or the requirements for warrants that are not already
; implied by the subterms in term!  The simplest thing to do is to follow the
; Merely Lifts principle and always just lift out an ordinary subterm into an
; ordinary slot.

; WARNING: The resulting term is in quote normal form.  We take advantage of
; this fact in our implementation of :by hints, in function
; apply-top-hints-clause1, to increase the chances that the "easy-winp" case
; holds.  We also take advantage of this fact in
; interpret-term-as-rewrite-rule, as commented there.

; WARNING.  Remove-guard-holders-weak is used in induction-machine-for-fn1, and
; termination-machine, so (remove-guard-holders-weak term) needs to be provably
; equal to term, for every term and suitable ilk, in the ground-zero theory.
; In fact, because of the use in constraint-info, it needs to be the case that
; for any axiomatic event e, (remove-guard-holders-weak e) can be substituted
; for e without changing the logical power of the set of axioms.  Actually, we
; want to view the logical axiom added by e as though remove-guard-holders-weak
; had been applied to it, and hence RETURN-LAST, MV-LIST, and CONS-WITH-HINT
; appear in *non-instantiable-primitives*.

; Special functions recognized by this function are: RETURN-LAST, MV-LIST,
; CONS-WITH-HINT, and THE-CHECK.

  (declare (xargs :guard (pseudo-termp term)
                  :measure (acl2-count term)))
  (cond
   ((variablep term) (mv changedp0 term))
   ((fquotep term) (mv changedp0 term))
   ((and (eq (ffn-symb term) 'HIDE)
         (remove-guard-holders-blocked-by-hide-p))

; Without this case, the proof of
;   (thm (equal (car (cons x x)) (hide (prog2$ u x)))
;        :hints (("Goal" :expand ((hide (prog2$ u x))))))
; will fail.

    (mv changedp0 term))
   ((or (eq (ffn-symb term) 'RETURN-LAST)
        (eq (ffn-symb term) 'MV-LIST))

; Recall that PROG2$ (hence, RETURN-LAST) is used to attach the dcl-guardian of
; a LET to the body of the LET for guard generation purposes.  A typical call
; of PROG2$ is (PROG2$ dcl-guardian body), where dcl-guardian has a lot of IFs
; in it.  Rather than distribute them over PROG2$ and then when we finally get
; to the bottom with things like (prog2$ (illegal ...) body) and (prog2$ T
; body), we just open up the prog2$ early, throwing away the dcl-guardian.

    (remove-guard-holders1 t (car (last (fargs term)))))
   ((eq (ffn-symb term) 'CONS-WITH-HINT)
    (mv-let
      (changedp1 arg1)
      (remove-guard-holders1 nil (fargn term 1))
      (declare (ignore changedp1))
      (mv-let
        (changedp2 arg2)
        (remove-guard-holders1 nil (fargn term 2))
        (declare (ignore changedp2))
        (mv t (mcons-term* 'cons arg1 arg2)))))
   ((flambdap (ffn-symb term))
    (case-match
      term
      ((('LAMBDA ('VAR) ('THE-CHECK & & 'VAR))
        val)
       (remove-guard-holders1 t val))
      ((('LAMBDA formals ('RETURN-LAST ''MBE1-RAW & logic))
        . args)

; This case handles equality variants.  For example, the macroexpansion of
; (member x y) matches this pattern, and we return (member-equal x y).  The
; goal here is to deal with the uses of let-mbe in macro definitions of
; equality variants, as for member.

       (mv-let
         (changedp1 args1)
         (remove-guard-holders1-lst args)
         (declare (ignore changedp1))
         (mv-let
           (changedp2 logic2)
           (remove-guard-holders1 nil logic)
           (declare (ignore changedp2))
           (mv t (subcor-var formals args1 logic2)))))
      (&
       (mv-let
         (changedp1 lambda-body)
         (remove-guard-holders1 nil
                                (lambda-body (ffn-symb term)))
         (mv-let
           (changedp2 args)
           (remove-guard-holders1-lst (fargs term))
           (cond ((or changedp1 changedp2)
                  (mv t
                      (mcons-term
                       (if changedp1
                           (make-lambda (lambda-formals (ffn-symb term))
                                        lambda-body)
                         (ffn-symb term))
                       args)))
                 (t (mv changedp0 term))))))))
   (t (mv-let
        (changedp1 args)
        (remove-guard-holders1-lst (fargs term))
        (cond ((null changedp1)
               (cond ((quote-listp args)
                      (let ((new-term (mcons-term (ffn-symb term)
                                                  args)))
                        (cond ((equal term new-term) ; even if not eq
                               (mv changedp0 term))
                              (t (mv t new-term)))))
                     (t (mv changedp0 term))))
              (t (mv t (mcons-term (ffn-symb term) args))))))))

(defun remove-guard-holders1-lst (lst)
  (declare (xargs :guard (pseudo-term-listp lst)
                  :measure (acl2-count lst)))
  (cond ((endp lst) (mv nil nil))
        (t (mv-let (changedp1 a)
                   (remove-guard-holders1 nil (car lst))
                   (mv-let (changedp2 b)
                           (remove-guard-holders1-lst (cdr lst))
                           (cond ((or changedp1 changedp2)
                                  (mv t (cons a b)))
                                 (t (mv nil lst))))))))
)

(defun remove-guard-holders-weak (term)

; Return a term equal to term, but slightly simplified.  See also the warning
; in remove-guard-holders1.

  (declare (xargs :guard (pseudo-termp term)))
  (mv-let (changedp result)
          (remove-guard-holders1 nil term)
          (declare (ignore changedp))
          result))

(defun remove-guard-holders-weak-lst (lst)

; Return a list of terms element-wise equal to lst, but slightly simplified.

  (declare (xargs :guard (pseudo-term-listp lst)))
  (mv-let (changedp result)
          (remove-guard-holders1-lst lst)
          (declare (ignore changedp))
          result))

(defun remove-guard-holders1-lst-lst (lst)
  (declare (xargs :guard (pseudo-term-list-listp lst)))
  (cond ((null lst) (mv nil nil))
        (t (mv-let (changedp1 a)
                   (remove-guard-holders1-lst (car lst))
                   (mv-let (changedp2 b)
                           (remove-guard-holders1-lst-lst (cdr lst))
                           (cond ((or changedp1 changedp2)
                                  (mv t (cons a b)))
                                 (t (mv nil lst))))))))

(defun remove-guard-holders-weak-lst-lst (lst)

; Return a list of clauses element-wise equal to lst, but slightly simplified.

  (declare (xargs :guard (pseudo-term-list-listp lst)))
  (mv-let (changedp result)
          (remove-guard-holders1-lst-lst lst)
          (declare (ignore changedp))
          result))

(mutual-recursion

(defun clean-up-dirty-lambda-objects (term ilk wrld)

; Warning: This function must not be called during boot-strap, so check
; (global-val 'boot-strap-flg wrld) before calling this function.

; We advise that, in addition, you check (may-contain-dirty-lambda-objectsp
; term) since if term contains no dirty lambda objects this function needlessly
; copies term.

  (cond
   ((variablep term) term)
   ((fquotep term)
    (let ((evg (unquote term)))
      (cond ((eq ilk :FN)
             (cond
              ((and (consp evg)
                    (eq (car evg) 'lambda)
                    (well-formed-lambda-objectp evg wrld))

; We drop any DECLARE form, remove guard holders, expand all the lambdas (beta
; reduce) the body, and recursively clean up dirty lambdas that might be inside
; this one.  We actually clean up recursively before expanding lambdas to avoid
; having to clean up the same lambda repeatedly should expansion duplicate a
; dirty lambda.

               (kwote
                (list 'lambda
                      (lambda-object-formals evg)
                      (expand-all-lambdas
                       (clean-up-dirty-lambda-objects
                        (remove-guard-holders-weak
                         (lambda-object-body evg))
                        nil
                        wrld)))))
              (t term)))
            (t term))))
   ((and (eq (ffn-symb term) 'HIDE)
         (remove-guard-holders-blocked-by-hide-p))
    term)
   ((lambda-applicationp term)
    (fcons-term
     (list 'lambda
           (lambda-formals (ffn-symb term))
           (clean-up-dirty-lambda-objects
            (lambda-body (ffn-symb term))
            nil
            wrld))
     (clean-up-dirty-lambda-objects-lst (fargs term) nil wrld)))
   (t (let ((bdg (executable-badge (ffn-symb term) wrld)))
        (fcons-term (ffn-symb term)
                    (clean-up-dirty-lambda-objects-lst
                     (fargs term)
                     (if (or (null bdg)
                             (eq (access apply$-badge bdg :ilks) t))
                         nil
                         (access apply$-badge bdg :ilks))
                     wrld))))))

(defun clean-up-dirty-lambda-objects-lst (terms ilks wrld)
  (cond
   ((endp terms) nil)
   (t (cons (clean-up-dirty-lambda-objects (car terms) (car ilks) wrld)
            (clean-up-dirty-lambda-objects-lst (cdr terms) (cdr ilks) wrld))))))

(defun possibly-clean-up-dirty-lambda-objects (term wrld)

; We copy term and clean up every dirty well-formed lambda object occurring in
; a :FN slot.  We only do this if we're not in boot-strap and if we have reason
; to believe there is a dirty lambda object somewhere in term.  For a
; discussion of the reasons we do this and the necessary conditions to
; guarantee soundness, see the Essay on Cleaning Up Dirty Lambda Objects.

  (cond
   ((and (not (global-val 'boot-strap-flg wrld))
         (may-contain-dirty-lambda-objectsp term))
    (clean-up-dirty-lambda-objects term nil wrld))
   (t term)))

(defun possibly-clean-up-dirty-lambda-objects-lst (terms wrld)

; We copy each term in terms and clean up every dirty well-formed quoted lambda
; objects we find.  This funtion checks (not (global-val 'boot-strap-flg wrld))
; once for every element of terms.  This is less efficient than checking it
; once and then running the may-contain-dirty-lambda-objectsp check on each
; term, but that would require having a lot of nearly duplicate code.

  (cond
   ((endp terms) nil)
   (t (cons (possibly-clean-up-dirty-lambda-objects (car terms) wrld)
            (possibly-clean-up-dirty-lambda-objects-lst (cdr terms) wrld)))))

(defun possibly-clean-up-dirty-lambda-objects-lst-lst (terms-lst wrld)

; Again, we test the 'boot-strap-flg repeatedly when only one test would
; suffice.  So we're sacrificing a little efficiency for code simplicity.

  (cond
   ((endp terms-lst) nil)
   (t (cons (possibly-clean-up-dirty-lambda-objects-lst (car terms-lst) wrld)
            (possibly-clean-up-dirty-lambda-objects-lst-lst
             (cdr terms-lst)
             wrld)))))

(defun remove-guard-holders (term wrld)

; Return a term equal to term, but slightly simplified, even perhaps inside
; quoted lambda objects.  See remove-guard-holders-weak for a version that does
; not take a world argument and does not simplify quoted lambda objects.

; See the warning in remove-guard-holders1.

  (declare (xargs :guard (and (pseudo-termp term)
                              (plist-worldp wrld))))
  (cond (wrld (possibly-clean-up-dirty-lambda-objects
               (remove-guard-holders-weak term)
               wrld))
        (t (remove-guard-holders-weak term))))

(defun remove-guard-holders-lst (lst wrld)

; Return a list of terms element-wise equal to lst, but slightly simplified,
; even perhaps inside quoted lambda objects.  See remove-guard-holders-weak-lst
; for a version that does not take a world argument and does not simplify
; quoted lambda objects.

  (declare (xargs :guard (and (pseudo-term-listp lst)
                              (plist-worldp wrld))))
  (cond (wrld (possibly-clean-up-dirty-lambda-objects-lst
               (remove-guard-holders-weak-lst lst)
               wrld))
        (t (remove-guard-holders-weak-lst lst))))

(defun remove-guard-holders-lst-lst (lst wrld)

; Return a list of clauses element-wise equal to lst, but slightly simplified,
; even perhaps inside quoted lambda objects.  See
; remove-guard-holders-weak-lst-lst for a version that does not take a world
; argument and does not simplify quoted lambda objects.

  (declare (xargs :guard (and (pseudo-term-list-listp lst)
                              (plist-worldp wrld))))
  (cond (wrld (possibly-clean-up-dirty-lambda-objects-lst-lst
               (remove-guard-holders-weak-lst-lst lst)
               wrld))
        (t (remove-guard-holders-weak-lst-lst lst))))

(defun lambda-object-guard (x)

; X must be a well-formed lambda object.  We return the guard.  Note that if x
; is well-formed it is syntactically plausible, and if it is syntactically
; plausible the declared :guard cannot be the symbol nil.  So if the (cadr
; (assoc-keyword ...)) comes back nil it means there was no declared guard,
; which defaults to 'T.

; This function is not defined in axioms (where we define its namesakes
; lambda-object-formals, -dcl, and -body) because those are :logic mode
; functions with a guard of T and are guard verified.  This function is in
; :program mode and if it had a guard it would be
; (syntactically-plausible-lambda-objectp nil x).

  (or (cadr (assoc-keyword :guard
                           (cdr (assoc-eq 'xargs
                                          (cdr (lambda-object-dcl x))))))
      *t*))

(defun tag-translated-lambda$-body (lambda$-expr tbody)

; Keep this function in sync with lambda$-bodyp.

; This function takes a lambda$ expression whose body has been successfully
; translated to tbody and returns a term equivalent to tbody but marked in a
; way that allows us to (a) identify the resulting lambda-expression as having
; come from a lambda$ and (b) recover the original lambda$ expression that raw
; Lisp will see.  See the Essay on Lambda Objects and Lambda$.

  `(RETURN-LAST 'PROGN
                (QUOTE ,lambda$-expr)
                ,tbody))

(defun lambda$-bodyp (body)

; Keep this function in sync with tag-translated-lambda$-body.

; This function recognizes the special idiom used to tag translated
; lambda$ bodies.  See the Essay on Lambda Objects and Lambda$.

  (and (consp body)
       (eq (ffn-symb body) 'RETURN-LAST)
       (equal (fargn body 1) ''PROGN)
       (quotep (fargn body 2))
       (consp (unquote (fargn body 2)))
       (eq (car (unquote (fargn body 2))) 'LAMBDA$)))

(defun member-lambda-objectp (args)

; Think of args as having come from a term (fn . args), where fn is a function
; symbol.  We determine whether there is a quoted lambda-like object among
; args.  Motivation: If so, fn might have :FN slots which would make the quoted
; lambda-like objects possibly eligible for untranslation to lambda$
; expressions.  We think it is faster to check for presence of quoted
; lambda-like objects in args than to fetch the ilks of fn and look for :FN,
; though we will do that later if we find lambda-like objects now.

  (cond ((endp args) nil)
        ((and (quotep (car args))
              (consp (unquote (car args)))
              (eq (car (unquote (car args))) 'lambda))
         t)
        (t (member-lambda-objectp (cdr args)))))

(defun attachment-alist (fn wrld)
  (let ((prop (getpropc fn 'attachment nil wrld)))
    (and prop
         (cond ((symbolp prop)
                (getpropc prop 'attachment nil wrld))
               ((eq (car prop) :attachment-disallowed)
                prop) ; (cdr prop) follows "because", e.g., (msg "it is bad")
               (t prop)))))

(defun attachment-pair (fn wrld)
  (let ((attachment-alist (attachment-alist fn wrld)))
    (and attachment-alist
         (not (eq (car attachment-alist) :attachment-disallowed))
         (assoc-eq fn attachment-alist))))

(defun apply$-lambda-guard (fn args)

; This function provides the guard for a lambda application.  It implies
; (true-listp args), in support of guard verification for the apply$
; mutual-recursion.  It also guarantees that if we have a good lambda, then we
; can avoid checking in the raw Lisp definition of apply$-lambda that the arity
; of fn (the length of its formals) equals the length of args.

; We were a bit on the fence regarding whether to incorporate this change.  On
; the positive side: in one test involving trivial computation on a list of
; length 10,000,000, we found a 13% speedup.  But one thing that gave us pause
; is that the following test showed no speedup at all -- in fact it seemed to
; show a consistent slowdown, though probably well under 1%.  (In one trio of
; runs the average was 6.56 seconds for the old ACL2 and 6.58 for the new.)

;   cd books/system/tests/
;   acl2
;   (include-book "apply-timings")
;   ; Get a function with a guard of t:
;   (with-output
;     :off event
;     (encapsulate
;       ()
;       (local (in-theory (disable (:e ap4))))
;       (defun ap4-10M ()
;         (declare (xargs :guard t))
;         (ap4 *10m*
;              *good-lambda1* *good-lambda2* *good-lambda3* *good-lambda4*
;              0))))
;   (time$ (ap4-10M))

; But we decided that a stronger guard would be more appropriate, in part
; because that's really the idea of guards, in part because more user bugs
; could be caught, and in part because this would likely need to be part of the
; guards in support of a loop macro.

  (declare (xargs :guard t :mode :logic))
  (and (consp fn)
       (consp (cdr fn))
       (true-listp args)
       (equal (len (cadr fn)) ; (cadr fn) = (lambda-object-formals fn), here.
              (length args))))

(defun apply$-guard (fn args)
  (declare (xargs :guard t :mode :logic))
  (if (atom fn)
      (true-listp args)
    (apply$-lambda-guard fn args)))

(defun non-trivial-encapsulate-ee-entries (embedded-event-lst)
  (cond ((endp embedded-event-lst)
         nil)
        ((and (eq (caar embedded-event-lst) 'encapsulate)
              (cadar embedded-event-lst))
         (cons (car embedded-event-lst)
               (non-trivial-encapsulate-ee-entries (cdr embedded-event-lst))))
        (t (non-trivial-encapsulate-ee-entries (cdr embedded-event-lst)))))

(defun all-function-symbolps (fns wrld)
  (declare (xargs :mode :logic
                  :guard (plist-worldp wrld)))
  (cond ((atom fns) (equal fns nil))
        (t (and (symbolp (car fns))
                (function-symbolp (car fns) wrld)
                (all-function-symbolps (cdr fns) wrld)))))

(defconst *unknown-constraints*

; This value must not be a function symbol, because functions may need to
; distinguish conses whose car is this value from those consisting of function
; symbols.

  :unknown-constraints)

(defun unknown-constraints-table-guard (key val wrld)
  (let ((er-msg "The proposed attempt to add unknown-constraints is illegal ~
                 because ~@0.  See :DOC partial-encapsulate."))
    (cond
     ((eq key :supporters)
      (let ((ee-entries (non-trivial-encapsulate-ee-entries
                         (global-val 'embedded-event-lst wrld))))
        (cond
         ((null ee-entries)
          (mv nil
              (msg er-msg
                   "it is not being made in the scope of a non-trivial ~
                    encapsulate")))
         ((cdr ee-entries)
          (mv nil
              (msg er-msg
                   (msg "it is being made in the scope of nested non-trivial ~
                         encapsulates.  In particular, an enclosing ~
                         encapsulate introduces function ~x0, while an ~
                         encapsulate superior to that one introduces function ~
                         ~x1"
                        (caar (cadr (car ee-entries)))
                        (caar (cadr (cadr ee-entries)))))))
         ((not (all-function-symbolps val wrld))
          (mv nil
              (msg er-msg
                   (msg "the value, ~x0, is not a list of known function ~
                         symbols"
                        val))))
         ((not (subsetp-equal (strip-cars (cadr (car ee-entries)))
                              val))
          (mv nil
              (msg er-msg
                   (msg "the value, ~x0, does not include all of the ~
                         signature functions of the partial-encapsulate"
                        val))))
         (t (mv t nil)))))
     (t (mv nil nil)))))

(table unknown-constraints-table nil nil
       :guard
       (unknown-constraints-table-guard key val world))

(defmacro set-unknown-constraints-supporters (&rest fns)
  `(table unknown-constraints-table
          :supporters

; Notice that by including the newly-constrained functions in the supporters,
; we are guaranteeing that this table event is not redundant.  To see this,
; first note that we are inside a non-trivial encapsulate (see
; trusted-cl-proc-table-guard), and for that encapsulate to succeed, the
; newly-constrained functions must all be new.  So trusted-cl-proc-table-guard
; would have rejected a previous attempt to set to these supporters, since they
; were not function symbols at that time.

          (let ((ee-entries (non-trivial-encapsulate-ee-entries
                             (global-val 'embedded-event-lst world))))
            (union-equal (strip-cars (cadr (car ee-entries)))
                         ',fns))))

(partial-encapsulate
 ((ev-fncall-rec-logical-unknown-constraints
   (fn args w user-stobj-alist big-n safe-mode gc-off
       latches hard-error-returns-nilp aok
       warranted-fns)
   (mv t t t)))
 nil ; Imagine that extra constraints are just evaluation results.
 (logic)
 (local (defun ev-fncall-rec-logical-unknown-constraints
            (fn args w user-stobj-alist big-n safe-mode gc-off
                latches hard-error-returns-nilp aok
                warranted-fns)
          (declare (ignore fn args w user-stobj-alist big-n safe-mode gc-off
                           latches hard-error-returns-nilp aok
                           warranted-fns))
          (mv nil nil nil))))

(defun non-executable-stobjs-msg (vars wrld non-exec-stobjs)
  (cond ((endp vars)
         (if non-exec-stobjs
             (msg "  Note that ~&0 ~#0~[is a non-executable stobj~/are ~
                   non-executable stobjs~]."
                  (reverse non-exec-stobjs))
           ""))
        (t (non-executable-stobjs-msg
            (cdr vars)
            wrld
            (if (and (stobjp (car vars) t wrld)
                     (getpropc (car vars) 'non-executablep nil wrld))
                (cons (car vars) non-exec-stobjs)
              non-exec-stobjs)))))

(defun scan-to-event (wrld)

; We roll back wrld to the first (list order traversal) event landmark
; on it.

  (cond ((null wrld) wrld)
        ((and (eq (caar wrld) 'event-landmark)
              (eq (cadar wrld) 'global-value))
         wrld)
        (t (scan-to-event (cdr wrld)))))

(defun logical-defun (fn wrld)

; Returns the defun form for fn that was submitted to ACL2,, if there is one;
; else nil.

  (let ((ev (get-event fn wrld)))
    (and (consp ev) ; presumably same as (not (null ev))
         (case (car ev)
           (defun ev)
           (mutual-recursion (assoc-eq-cadr fn (cdr ev)))
           ((defstobj defabsstobj)
            (and (eq (cadr ev) ; expect true except for st itself
                     (getpropc fn 'stobj-function nil wrld))
                 (let* ((index (getpropc fn 'absolute-event-number nil wrld))
                        (wrld2 (assert$
                                index
                                (lookup-world-index 'event index wrld)))
                        (ev (get-event fn (scan-to-event (cdr wrld2)))))
                   (and (eq (car ev) 'defun) ; always true?
                        ev))))
           (verify-termination-boot-strap

; For some functions, like binary-append and apply$, we wind up in this case.
; Note that the defun will declare :mode :logic even if the original did not;
; that's because verify-termination-boot-strap uses the same definition as is
; generated by verify-termination, which adds that declare form.  See comments
; in cltl-def-from-name and check-some-builtins-for-executability for why we
; can rely on getting the correct result from cltl-def-from-name (in short,
; because we know that fn is not non-executable).

            (cltl-def-from-name fn wrld))
           (otherwise nil)))))

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
     (t (let ((def (logical-defun fn wrld)))
          (cond
           ((null def)
            (er hard! 'guard-raw
                "Unable to find defining event for ~x0."
                fn))
           (t (mv-let
                (dcls guard)
                (dcls-guard-raw-from-def (cdr def) wrld)
                (declare (ignore dcls))
                guard))))))))

(defun ev-fncall-guard-er (fn args w user-stobj-alist latches extra)

; This function is called only by ev-fncall-rec-logical, which we do not expect
; to be executed.

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

(defun ev-fncall-rec-logical (fn arg-values arg-exprs w user-stobj-alist big-n
                                 safe-mode gc-off latches
                                 hard-error-returns-nilp aok warranted-fns)

; This is the "slow" code for ev-fncall-rec, for when raw-ev-fncall is not
; called.

; The following guard is simply a way to trick ACL2 into not objecting
; to the otherwise irrelevant hard-error-returns-nilp.  See the comment
; in ev, below, for a brief explanation.  See hard-error for a more
; elaborate one.

; Keep this function in sync with *primitive-formals-and-guards*.

; Warranted-fns is a list of function symbols that are to be treated as though
; they have true warrants.  See ev-fncall+-w.

  (declare (xargs :guard (and (plist-worldp w)
                              (symbol-listp warranted-fns))))
  (cond
   ((zp-big-n big-n)
    (mv t
        (cons "Evaluation ran out of time." nil)
        latches))
   (t
    (let* ((x (car arg-values))
           (y (cadr arg-values))
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
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (BINARY-*
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (acl2-numberp y)))
                (mv nil
                    (* x y)
                    latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (BINARY-+
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (acl2-numberp y)))
                (mv nil (+ x y) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (UNARY--
         (cond ((or guard-checking-off
                    (acl2-numberp x))
                (mv nil (- x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (UNARY-/
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (not (= x 0))))
                (mv nil (/ x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (<
         (cond ((or guard-checking-off
                    (and (real/rationalp x)
                         (real/rationalp y)))
                (mv nil (< x y) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (CAR
         (cond ((or guard-checking-off
                    (or (consp x)
                        (eq x nil)))
                (mv nil (car x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (CDR
         (cond ((or guard-checking-off
                    (or (consp x)
                        (eq x nil)))
                (mv nil (cdr x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (CHAR-CODE
         (cond ((or guard-checking-off
                    (characterp x))
                (mv nil (char-code x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (CHARACTERP
         (mv nil (characterp x) latches))
        (CODE-CHAR
         (cond ((or guard-checking-off
                    (and (integerp x)
                         (<= 0 x)
                         (< x 256)))
                (mv nil (code-char x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (COMPLEX
         (cond ((or guard-checking-off
                    (and (real/rationalp x)
                         (real/rationalp y)))
                (mv nil (complex x y) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
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
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (CONS
         (mv nil (cons x y) latches))
        (CONSP
         (mv nil (consp x) latches))
        (DENOMINATOR
         (cond ((or guard-checking-off
                    (rationalp x))
                (mv nil (denominator x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (EQUAL
         (mv nil (equal x y) latches))
        #+:non-standard-analysis
        (FLOOR1
         (cond ((or guard-checking-off
                    (realp x))
                (mv nil (floor x 1) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
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
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (INTEGERP
         (mv nil (integerp x) latches))
        (INTERN-IN-PACKAGE-OF-SYMBOL
         (cond ((or guard-checking-off
                    (and (stringp x)
                         (symbolp y)))
                (mv nil (intern-in-package-of-symbol x y) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (NUMERATOR
         (cond ((or guard-checking-off
                    (rationalp x))
                (mv nil (numerator x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (PKG-IMPORTS
         (cond ((or guard-checking-off
                    (stringp x))
                (mv nil (pkg-imports x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (PKG-WITNESS
         (cond ((or guard-checking-off
                    (and (stringp x) (not (equal x ""))))
                (mv nil (pkg-witness x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
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
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (STRINGP
         (mv nil (stringp x) latches))
        (SYMBOL-NAME
         (cond ((or guard-checking-off
                    (symbolp x))
                (mv nil (symbol-name x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
                                      extra))))
        (SYMBOL-PACKAGE-NAME
         (cond ((or guard-checking-off
                    (symbolp x))
                (mv nil (symbol-package-name x) latches))
               (t (ev-fncall-guard-er fn arg-values w user-stobj-alist latches
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
          ((and (eq fn 'apply$-userfn)
                (consp warranted-fns)       ; hence :nil! is not the value
                (member-eq x warranted-fns) ; hence x is a symbol
                (or guard-checking-off
                    (true-listp arg-values)))
           (ev-fncall-rec-logical x y

; A warranted function does not traffic in stobjs, so arg-exprs is irrelevant
; below.

                                  nil ; arg-exprs
                                  w user-stobj-alist big-n safe-mode gc-off
                                  latches hard-error-returns-nilp aok
                                  warranted-fns))
          ((and (eq fn 'badge-userfn)
                (consp warranted-fns) ; hence :nil! is not the value
                (member-eq x warranted-fns))
           (mv nil (get-badge x w) latches))
          ((and (null arg-values)
                (car (stobjs-out fn w)))
           (mv t
               (ev-fncall-creator-er-msg fn)
               latches))
          (t
           (let ((alist (pairlis$ (formals fn w) arg-values))
                 (body (body fn nil w))
                 (attachment (and aok
                                  (not (member-eq fn
                                                  (global-val 'attach-nil-lst
                                                              w)))

; We do not use (all-attachments w) below, because attachments are omitted from
; that structure when they are made to warrants or made with defattach
; specifying non-nil :skip-checks.

                                  (cdr (attachment-pair fn w)))))
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
                 (ev-fncall-guard-er fn arg-values w user-stobj-alist latches extra))
                ((and (eq fn 'hard-error)
                      (not hard-error-returns-nilp))

; Before we added this case, the following returned nil even though the result
; was t if we replaced ev-fncall-rec-logical by ev-fncall-rec.  That wasn't
; quite a soundness bug, event though the latter is defined to be the former,
; because ev-fncall-rec is untouchable; nevertheless the discrepancy was
; troubling.

;   (mv-let (erp val ign)
;           (ev-fncall-rec-logical 'hard-error '(top "ouch" nil) nil (w state)
;                                  (user-stobj-alist state)
;                                  100000 nil nil nil nil t nil)
;           (declare (ignore ign val))
;           erp)


                 (mv t (illegal-msg) latches))
                ((eq fn 'throw-nonexec-error)
                 (ev-fncall-null-body-er nil
                                         (car arg-values)  ; fn
                                         (cadr arg-values) ; args
                                         latches))
                ((member-eq fn '(pkg-witness pkg-imports))
                 (mv t (unknown-pkg-error-msg fn (car arg-values)) latches))
                (attachment ; hence aok
                 (ev-fncall-rec-logical attachment arg-values arg-exprs w
                                        user-stobj-alist
                                        (decrement-big-n big-n)
                                        safe-mode gc-off latches
                                        hard-error-returns-nilp aok
                                        warranted-fns))
                ((null body)

; At one time we always returned in this case:
;   (ev-fncall-null-body-er (and (not aok) attachment) fn arg-values latches)
; where (and (not aok) attachment) is actually equal to attachment.  However,
; that doesn't explain the behavior when evaluating a function introduced with
; partial-encapsulate that has raw Lisp code for evaluation.  So we just punt
; here with a generic function introduced with partial-encapsulate.  We don't
; expect to hit this case in practice, since normally ev-fncall-rec calls
; raw-ev-fncall to get its result.  If we do hit it in practice, we could
; consider giving a raw Lisp definition to
; ev-fncall-rec-logical-unknown-constraints that calls the partially
; constrained functions.

                 (cond
                  ((eq (car (getpropc fn 'constrainedp nil w))
                       *unknown-constraints*)
                   (ev-fncall-rec-logical-unknown-constraints
                    fn arg-values w user-stobj-alist
                    (decrement-big-n big-n)
                    safe-mode gc-off latches hard-error-returns-nilp aok
                    warranted-fns))
                  (t ; e.g., when admitting a fn called in its measure theorem
                   (ev-fncall-null-body-er attachment ; hence aok
                                           (car arg-values) ; fn
                                           (cadr arg-values) ; args
                                           latches))))
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
                            (if latches
                                (actual-stobjs-out fn arg-exprs w)
                              (stobjs-out fn w))
                            val
                            latches)))))))))))))))))

(defun ev-fncall-rec (fn arg-values arg-exprs w user-stobj-alist big-n
                         safe-mode gc-off latches hard-error-returns-nilp aok)
  (declare (xargs :guard (plist-worldp w)))
  #-acl2-loop-only
  (cond (*ev-shortcut-okp*
         (cond ((fboundp fn)

; If fn is unbound and we used the logical code below, we'd get a
; hard error as caused by (formals fn w).

                (return-from ev-fncall-rec
                             (raw-ev-fncall fn arg-values arg-exprs latches w user-stobj-alist
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
  (ev-fncall-rec-logical fn arg-values arg-exprs w user-stobj-alist big-n
                         safe-mode gc-off latches hard-error-returns-nilp aok
                         nil))

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
                        (msg "Unbound var ~x0.~@1"
                             form
                             (non-executable-stobjs-msg (list form) w nil))
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

; (Remember: the quoted lambda of wormhole-eval is not related to apply$)

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
                      (body-er (mv body-er body-val latches))
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
                  (test-er (mv test-er test latches))
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
                     (cond (args-er (mv args-er args latches))
                           (t (mv nil (car (last args)) latches))))))))
        (t (mv-let (args-er args latches)
                   (ev-rec-lst (fargs form) alist w user-stobj-alist
                               (decrement-big-n big-n) safe-mode gc-off
                               latches
                               hard-error-returns-nilp
                               aok)
                   (cond
                    (args-er (mv args-er args latches))
                    ((flambda-applicationp form)
                     (ev-rec (lambda-body (ffn-symb form))
                             (pairlis$ (lambda-formals (ffn-symb form)) args)
                             w user-stobj-alist
                             (decrement-big-n big-n) safe-mode gc-off
                             latches
                             hard-error-returns-nilp
                             aok))
                    (t (ev-fncall-rec (ffn-symb form) args (fargs form)
                                      w user-stobj-alist
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
      (ev-fncall-rec fn args
                     nil ; irrelevant arg-exprs (as latches is nil)
                     w user-stobj-alist (big-n) safe-mode gc-off
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
   (ev-fncall-rec fn args
                  nil ; irrelevant arg-exprs (as latches is nil)
                  w user-stobj-alist (big-n) safe-mode gc-off
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
   (save-ev-fncall-guard-er fn guard stobjs-in args w)
   (let ((form (and (symbolp fn)
                    (cdr (assoc-eq fn (table-alist 'guard-msg-table w))))))
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
           (if (and (symbolp fn) (programp fn w)) 0 1)
           (cons fn (if (symbolp fn)
                        (formals fn w)
                        (lambda-object-formals fn)))
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

(defun untranslate1-lambda-object-edcls (edcls untrans-tbl preprocess-fn wrld)

; This function is only called by translate1-lambda-object (which calls it on
; the edcls of a quoted LAMBDA object appearing in a :FN slot).  The output,
; edcls', of this function is used to form the (DECLARE . edcls') in the
; lambda$ generated by translate1-lambda-object.  Thus, we can remove any
; IGNORE or IGNORABLE declaration because lambda$ will insert an IGNORABLE
; declaration for every formal.

  (cond
   ((endp edcls) nil)
   ((eq (car (car edcls)) 'xargs)
; This is of a fixed form: (XARGS :GUARD g :SPLIT-TYPES T).
    (let ((g (caddr (car edcls))))
      (cons `(XARGS :GUARD ,(untranslate1 g t
                                          untrans-tbl
                                          preprocess-fn wrld)
                    :SPLIT-TYPES T)
            (untranslate1-lambda-object-edcls (cdr edcls)
                                              untrans-tbl
                                              preprocess-fn wrld))))
   ((or (eq (car (car edcls)) 'ignore)
        (eq (car (car edcls)) 'ignorable))
    (untranslate1-lambda-object-edcls (cdr edcls)
                                              untrans-tbl
                                              preprocess-fn wrld))
   (t (cons (car edcls)
            (untranslate1-lambda-object-edcls (cdr edcls)
                                              untrans-tbl
                                              preprocess-fn wrld)))))

(defun untranslate1-lambda-object (x untrans-tbl preprocess-fn wrld)

; X is a well-formed LAMBDA object.  It may be tagged as having come from a
; lambda$ but we cannot trust that tagging since the user could have
; counterfeited such an object with `(lambda (x) (return-last 'progn '(lambda$
; (x) zzz) x)).  We ignore the the tagging -- indeed, we strip it out, and
; untranslate the rest!

  (let* ((formals (lambda-object-formals x))
         (dcl (lambda-object-dcl x))
         (edcls1 (untranslate1-lambda-object-edcls
                  (cdr dcl)
                  untrans-tbl preprocess-fn wrld))
         (body

; At one time we gave special treatment to the tagged lambda case,
; (lambda$-bodyp body), in which case body is (RETURN-LAST 'PROGN '(LAMBDA$
; ...) body2) and we replaced body by (fargn body 3).  However, this caused odd
; behavior for the following thm until we started removing guard-holders from
; lambda bodies (more on that below).

; (defun f1 (lst) (loop$ for x in lst collect (car (cons x (cons x nil)))))
; (defun f2 (lst) (loop$ for x in lst collect (car (list x x))))
; (thm (equal (f1 lst) (f2 lst)))

; The checkpoint looked trivial: equality of something to itself!

;   (EQUAL (COLLECT$ (LAMBDA$ (X)
;                             (DECLARE (IGNORABLE X))
;                             (CAR (LIST X X)))
;                    LST)
;          (COLLECT$ (LAMBDA$ (X)
;                             (DECLARE (IGNORABLE X))
;                             (CAR (LIST X X)))
;                    LST))

; However, after this change we can see the difference:

;   (EQUAL (COLLECT$ (LAMBDA$ (X)
;                             (DECLARE (IGNORABLE X))
;                             (PROG2$ '(LAMBDA$ (X)
;                                               (DECLARE (IGNORABLE X))
;                                               (CAR (CONS X (CONS X NIL))))
;                                     (CAR (LIST X X))))
;                    LST)
;          (COLLECT$ (LAMBDA$ (X)
;                             (DECLARE (IGNORABLE X))
;                             (PROG2$ '(LAMBDA$ (X)
;                                               (DECLARE (IGNORABLE X))
;                                               (CAR (LIST X X)))
;                                     (CAR (LIST X X))))
;                    LST))

; This problem has disappeared when guard-holders are removed from the
; normalized definition bodies.  But rather than rely on that, we just do the
; simple thing here and display the tagged lambdas as they are.  Even if tagged
; lambdas are unlikely to appear in practice, at least we can see what is
; really going on when they do.

          (lambda-object-body x)))
    `(lambda$ ,formals
              ,@(if edcls1
                    `((declare ,@edcls1))
                    nil)
              ,(untranslate1 body nil untrans-tbl preprocess-fn wrld))))

(defun untranslate1-lambda-objects-in-fn-slots
  (args ilks iff-flg untrans-tbl preprocess-fn wrld)
  (cond
   ((endp args) nil)
   ((and (eq (car ilks) :FN)
         (quotep (car args))
         (eq (car (unquote (car args))) 'lambda)
         (well-formed-lambda-objectp (unquote (car args)) wrld))

; The iff-flg of term, above, is irrelevant to the untranslation of a quoted
; lambda among its :FN args.  (In fact, it's always irrelevant here because it
; is always nil when this function is called by
; untranslate1-possible-scion-call.)

    (cons (untranslate1-lambda-object (unquote (car args)) untrans-tbl
                                      preprocess-fn wrld)
          (untranslate1-lambda-objects-in-fn-slots
           (cdr args) (cdr ilks) iff-flg untrans-tbl preprocess-fn wrld)))
   (t (cons (untranslate1 (car args) iff-flg untrans-tbl preprocess-fn wrld)
            (untranslate1-lambda-objects-in-fn-slots
             (cdr args) (cdr ilks) iff-flg untrans-tbl preprocess-fn wrld)))))

(defun untranslate1-possible-scion-call (term iff-flg untrans-tbl preprocess-fn
                                              wrld)

; Term is a function call, (fn . args), where fn is a symbol and there is at
; least one quoted lambda-like object among args.  We call untranslate1 on
; every element of args except for the quoted well-formed LAMBDA objects in :FN
; slots (if any).  We untranslate those special elements to lambda$ terms.

  (declare (ignore iff-flg))
  (let* ((fn (ffn-symb term))
         (args (fargs term))
         (badge (executable-badge fn wrld))
         (ilks (if badge
                   (access apply$-badge badge :ilks)
                   T)))
    (cons fn
          (if (eq ilks T) ; could be unbadged or tame!
              (untranslate1-lst args nil
                                untrans-tbl
                                preprocess-fn
                                wrld)
              (untranslate1-lambda-objects-in-fn-slots
               args ilks nil untrans-tbl preprocess-fn wrld)))))

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
                (all-quoteps (fargs term))
                (let ((uarg2 (unquote (fargn term 2))))
                  (and (consp uarg2)
                       (member-eq (car uarg2) '(syntaxp bind-free)))))

; We store the quotation of the original form of a syntaxp or bind-free
; hypothesis in the second arg of its expansion.  We do this so that we
; can use it here and output something that the user will recognize.

; One can certainly generate calls of synp where this result will be
; misleading, but we aren't compelled to concern ourselves with such a case.

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
; keyword arguments for time$ calls.  It should be reasonably rare to hit this
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
                         (prog2$
                          (cond ((and (quotep (car args))
                                      (consp (unquote (car args)))
                                      (eq (car (unquote (car args)))
                                          :COMMENT))
                                 (list 'comment
                                       (cdr (unquote (car args)))
                                       (cadr args)))
                                (t (cons fn args))))
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
                             ((member-lambda-objectp (fargs term))
                              (untranslate1-possible-scion-call
                               term iff-flg untrans-tbl preprocess-fn wrld))
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

(defun ev-fncall (fn arg-values arg-exprs state latches hard-error-returns-nilp
                     aok)

; See raw-ev-fncall for a discussion of hte arguments, in particular arg-exprs.

  (declare (xargs :guard (state-p state)))
  (let #-acl2-loop-only ((*ev-shortcut-okp* (live-state-p state)))
       #+acl2-loop-only ()

; See the comment in ev for why we don't check the time limit here.

       (ev-fncall-rec fn arg-values arg-exprs
                      (w state) (user-stobj-alist state) (big-n)
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

; Essay on Context-message Pairs (cmp)

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
   (let ((tl (assoc-keyword :allow-other-keys actuals)))
     (er-progn-cmp
      (cond ((assoc-keyword :allow-other-keys (cdr tl))
             (er-cmp *macro-expansion-ctx*
                     "ACL2 prohibits multiple :allow-other-keys because ~
                      implementations differ significantly concerning which ~
                      value to take."))
            (t (value-cmp nil)))
      (bind-macro-args-keys1
       args actuals
       (and tl (cadr tl))
       alist form wrld state-vars)))))

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

; Essay on Lambda Objects and Lambda$

; [Timeline: After drafting the first version of ``Milestones from The Pure
; Lisp Theorem Prover to ACL2'' Moore realized it would be helpful to put dates
; into these essays!  This Essay was added to the sources in October, 2018.
; LAMBDA objects, as data interpreted by apply$, were introduced in the
; original book-version of apply$, which was integrated in the sources for
; release with Version_8.0, which was released in December, 2017.  Shortly
; thereafter, in January 2018, we started thinking about the design of loop$
; (see Essay on loop$) but realized that we needed lambda$.  The work on
; lambda$ explicitly started in June, 2018 and was moved into the sources in
; October, 2018.  After spending time responding to the referee reports on
; ``Limited Second-Order Functionality in a First-Order Setting'' we returned
; to the design of loop$.  See the Essay on Loop$.]

; Executive Summary: When apply$ was introduced in Version_8.0, lambda objects
; were all of the form (LAMBDA formals body) with an implicit guard of T.  Body
; has to be fully translated, closed, and tame for the lambda object to have
; the expected meaning under apply$.  But the defuns of apply$ and ev$ do not
; check anything but tameness and so can meaningfully interpret some ill-formed
; lambda objects.  To support top-level execution, Version_8.0 had a cache that
; mapped well-formed lambda objects to their compiled counterparts.  It used
; the Tau System at apply$-time to do CLTL compliance checking (against the
; implicit input guard of T).

; After Version_8.1 we introduced a second form of lambda object, (LAMBDA
; formals dcl body), allowing for guards and the compiler directives TYPE and
; IGNORE.  This was motivated by the desire to support CLTL's loop efficiently.

; But top-level forms to be evaluated may involve lambda objects that have
; never been seen before, e.g., because the user just typed a lambda object
; to some mapping function or, more likely, used a macro like loop that
; generates lambda objects.  Thus, to apply$ a lambda object at the
; top-level to some ground input it may be necessary to prove the guard clauses
; to confirm that the lambda object is CLTL compliant and then run the guard
; on the ground input to confirm that the lambda object's guard is satisfied.

; The manipulation of non-trivial guards, including both the generation of
; guard clauses and the attempt to prove them with Tau, during the top-level
; evaluation of forms suggests that lambda objects should always be found in
; some standard form so that fully translated guards encorporating all TYPE
; declarations can be recovered quickly from the object.

; Another new feature after Version_8.1 is that when verify-guards is called on
; a function name, we generate the guard obligation clauses for the well-formed
; lambda objects in the defun.  The user can thus provide :hints, etc., to
; prove those obligations and the lambda objects are marked as being CLTL
; compliant (by being stored on the world global common-lisp-compliant-lambdas)
; and entered as such into the lambda cache.  This means we less often have to
; rely on Tau to verify guards of lambda objects.  Of course, lambda objects
; typed by the user for top-level evaluation still rely on Tau for guard
; verification.

; To mitigate Tau's inadequacies still further, after Version_8.1 the user may
; call verify-guards on a lambda object, again gaining the opportunity to
; supply :hints, etc., and to record the object as compliant.  Of course, to
; use this feature the user would have to realize his top-level evaluations are
; slowed by failure to establish compliance.  So we've extended the lambda
; cache to provide more information in this regard.

; To make it easier to enter well-formed lambda objects, after Version_8.1 we
; added a new ``macro'' named lambda$ which allows the user to type lambda-like
; objects that are appropriately translated, checked, and normalized to produce
; well-formed quoted lambda objects.  Such a facility is essential if the user
; is going to type untranslated loop bodies (which are turned into lambda
; objects).  To preserve soundness, lambda$ can only be used in :FN slots --
; where we know the object is destined only for apply$ -- because the quoted
; object generated by a lambda$ in a :logic mode defun will be different from
; the quoted object appearing in the same location of the raw Lisp version of
; that defun.

; Lambda$ is not actually a macro but is built into translate because it must
; inspect the world.  It will allow us to implement loop as a macro that
; generates lambda$ expressions from untranslated loop statements.  E.g.,

; (loop for v in lst sum (+ 1 v))

; can be defmacro'd to expand to

; (sum (lambda$ (v) (+ 1 v)) lst)

; and the subsequent expansion of lambda$ will take care of the untranslated
; arithmetic expression, rendering (binary-+ '1 v).

; Lambda$ forms may, of course, be used in defuns and thus will find their way
; into raw Lisp defuns.  Because of loading of precompiled files and other
; book-related issues, raw Lisp cannot handle lambda$s in defuns simply by
; calling translate: the world may not be the same as the logical world in
; which the defun was (will be) processed.  So raw Lisp must macroexpand
; lambda$ expressions in a world-independent way.  In raw Lisp, lambda$ is a
; macro that just expands to a quoted but marked constant containing the
; original lambda$ expression.  See the raw Lisp defmacro for lambda$.  The raw
; Lisp marker is *lambda$-marker*, whose value is in the ACL2_INVISIBLE
; package.  If and when the strange lambda$ object reaches the raw lisp version
; of apply$ it will be mapped to its translation by virtue of the following
; feature.

; When non-erroneous lambda$s are encountered during defun-processing in the
; ACL2 loop, a world global alist, lambda$-alist, is updated to map the
; original lambda$ expression to its :logic translation.  This alist is used by
; the raw lisp version of apply$.

; [Remark.  The above idea -- that lambda$ expands in raw Lisp to a marked
; untranslated object whose translation is obtained from a world global set
; during defun-processing in the ACL2 loop -- is going to FAIL if the lambda$
; is apply$'d during pre-loading of files!  See the hard error in the defun of
; apply$-lambda in apply-raw.lisp.  End of Remark.]

; However, in order to construct the new entries to this alist from the
; translated body of a defun we have to be able to identify which lambda
; objects in it were produced by lambda$ expansion.  To do that we arrange for
; the expansion of lambda$ to tag the body of the resultant lambda object with
; a return-last form which includes the original lambda$ expression as a quoted
; object.  See tag-translated-lambda$-body and lambda$-bodyp.  Thus, after
; successful translation we can sweep the translated body and find all the
; untranslated lambda$ expressions.

; While we expect users to enter most (if not all) lambda objects via lambda$
; syntax, there is no way to prevent the user from just typing a quoted lambda
; object.  When a quoted object occupies a :FN slot during translation,
; translate checks that it is either a (tame) function symbol or a well-formed
; lambda object and causes an error otherwise.

; Translate does not check that quoted lambda objects outside :FN slots are
; well-formed because the regression contains hundreds of such objects that
; are, in fact, never destined for apply$ but instead are fed to various
; macros, like those in books/data-structures/defalist.lisp, to generate code.

; It is possible for macros, metafunctions, or even user-typein to cons up a
; lambda object destined for apply$, eliminating all hope that every lambda
; object will have been checked by translate.

; So the translate-time support for well-formed lambda objects must be
; regarded purely as a convenience for the user.  The ACL2 system developers
; may not assume that every lambda object has been checked by translate and
; is thus well-formed!  That must be explicitly checked with
; well-formed-lambda-objectp before looking for :guards, verifying guards,
; compiling, etc.

; Finally, to make this fairly complex process more efficient, the compiled
; lambda cache of Version_8.0 has been extensively elaborated.  We discuss
; caching in the Essay on the CL-Cache Implementation Details.  Like the
; Version_8.0 cache, the cache is based on a circular alist of default size
; 1000.  But the entries are no longer just (lambda-object . compiled-code)
; pairs.  Roughly put, each cache line contains a lambda object, a status, the
; max absolute event number of a world, possibly the compiled code for the
; guard and lambda expression, plus other items.  The status of each line is
; :GOOD, :BAD, :UGLY, or :UNKNOWN and tells us about the lambda object relative
; to the current world.

; :GOOD means that the lambda is well-formed and guard verified in the current
; world.  The max absolute event number is the number of the event in which the
; object was shown to be :GOOD.  If apply$-lambda is asked to apply a :GOOD
; lambda object, it runs the compiled code for the guard to check whether it
; holds on the actuals.  If the guard holds, it runs the compiled code for the
; lambda.  If the guard doesn't hold, we use the slow *1*apply$-lambda which
; interprets the object formally.

; :BAD generally means the lambda used to be :GOOD but the world has been
; rolled back and we have so far been unable to confirm well-formedness and
; compliance in the current world.  If apply$-lambda is asked to apply a :BAD
; lambda object it just uses *1*apply$-lambda.

; :UGLY means the object is so ill-formed it won't be :GOOD in any world.
; Examples of :UGLY lambdas are (lambda (t) '123) which has an illegal formal
; variable, (lambda (x) (cadr x)), which uses a primitive macro in an allegedly
; fully translated body, (lambda (x) (setq x '3)) which calls a function symbol
; that can never be defined by the user, and (lambda (x) (cons (foo x) (foo x
; x))), which would require foo to be defined with two different arities.
; Apply$-lambda always reverts to *1*apply$-lambda on :UGLY lambdas.

; :UNKNOWN means that the lambda object used to be either :GOOD or :BAD but the
; world has changed since the last time apply$-lambda saw this object.  In this
; case, apply$-lambda tries to revalidate the line by checking well-formedness
; and guard obligations (using Tau for the latter).  This either sets the
; :status to :GOOD or :BAD in the current world and apply$-lambda then behaves
; as described for the new status.

; To maintain these meanings of status we have to invalidate certain cache
; lines every time the world changes.  When the world is extended, as by a new
; DEFUN, VERIFY-GUARDS, or DEFTHM (or any other event), all :BAD lines are
; changed to :UNKNOWN.  When the world is retracted, as by :ubt, all :GOOD
; lines whose event numbers are now too big are changed to :UNKNOWN.

; The cache is managed in raw Lisp and updated destructively.  For example, if
; an undo is performed, producing a line with :UNKNOWN status, and then that
; line's lambda object is used in a mapping function, the first apply$-lambda
; will see the :UNKNOWN and destructively resolve it to :GOOD or :BAD, at the
; expense of well-formedness checks and guard verification.  Subsequent
; apply$-lambdas done as part of that map will be faster.

; Note: It is possible for a lambda object to be perfectly well-formed but to
; have guard obligations that are unprovable.  Such an object will end up with
; :status :BAD when it ought to have status :UGLY.  The expense of classifying
; such an object as merely :BAD is that every time the world is extended and we
; subsequently try to apply the object, we will attempt again to verify its
; guards.  It would be more efficient to classify it as :UGLY.  Ah, if only we
; could solve the decideability problem of this logic!

; The rest of this essay is an assortment of random details that may help fill
; in the gaps.  Topics are separated by three hyphens.

; ---

; For translate (actually translate11) to know whether it's looking at a :FN
; slot, translate11 has been given an extra argument, ilk, after Version_8.1.
; As it recurs through an untranslated term it keeps track of the ilk of each
; subterm.  See ilks-per-argument-slot.

; Aside: A problem with translate being sensitive to ilks arises from the fact
; that mapping functions are introduced in two steps: a defun and then a
; defwarrant.  So the user may (DEFUN map (fn lst) ...)  with the intention of
; later doing (defwarrant map) and having fn classified as having ilk :FN.
; But perhaps before calling defwarrant on map, the user defuns another
; function and uses (map (lambda$ vars dcls* body) lst) in its body.  That will
; fail because the lambda$ is not in a :FN slot.  Our attitude is: tough luck!
; We cause an error if the user writes a lambda$ term in a slot not known to be
; a :FN slot.  Call defwarrant before using map elsewhere!

; ---

; When translate sees a quoted object, (quote x), in a :FN slot it insists
; that x be a tame function symbol or a well-formed lambda object.  But there
; is an exception: translate will allow a quoted non-tame function symbol in
; the :FN slot of apply$.  The reason for this is that the warrant for non-tame
; function fn involves (apply$ 'fn ...).

; Instead of using well-formed-lambda-objectp to check lambda objects,
; translate checks individual properties so it can generate better error
; messages.

; ---

; When translate sees (lambda$ ...) it must be in a :FN slot or an error is
; caused.

; ---

; For what it is worth, apply$ itself does not care much about well-formedness.
; It treats any cons as a lambda!  Furthermore, while badge and tameness
; analysis only work when :FN slots are either formal variables or quoted
; objects, the defun of apply$ does not care where the fn comes from.  (How
; could it know?)  E.g., in the logic we can prove

; (thm (equal (sum `(lamby-pamby (x) x) '(1 2 3)) 6)
;      :hints (("Goal" :in-theory (enable applY$))))

; Note the backquote, meaning this ``lambda object'' was consed up fresh and
; could have been generated any number of ways.  Had we tried to simply quote
; this object a translate error would have been caused.  (Here we are relying
; on the fact that the ACL2 backquote reader -- see the function, backquote, in
; acl2-fns.lisp -- reads such a backquote as a call of cons.)

; We can execute such ill-formed ``lambda objects'' (although we may need to set
; guard-checking to :NONE, depending on how ill-formed the object is):

; ACL2 >(apply$ `(lamby-pamby (x) (cons x (cons y z))) '(one))
; (ONE NIL)

; Here, free variables y and z are treated as though they're bound to nil by
; ev$.

; The motivation for checking well-formedness of lambda objects is three-fold.
; First, apply$ really only works as ``expected'' on well-formed objects.
; Second, we can only do badge and tameness analysis on (pretty) well-formed
; lambda objects, so quietly allowing the user to inject bad objects may block
; subsequent analysis.  Third, we can only guard check and compile well-formed
; lambda objects, so bad objects prevent fast execution.

; ---

; Intentionally using an ill-formed lambda object can be an instructive way
; to explore the behavior of apply$, ev$, etc.

; The user who intentionally wants to inject an ill-formed lambda object
; into a term should probably just backquote the object.  For example,

; `(lambda (x) (cons x y))

; looks like a lambda object but is actually being consed up fresh (i.e., it's
; not obviously a constant).  It is ill-formed and would not be permitted in a
; :FN slot if written with a single quote mark.

; If the user objects to the repeated consing up of this lambda ``object'' he
; or she might

; (defconst *my-ill-formed-lambda* `(lambda (x) (cons x y)))

; and then use *my-ill-formed-lambda* in :FN slots as desired.  Translate goes
; out of its way to support this idiom.

; ---

; The following are examples of well-formed lambda objects.  Slight
; variations may not be well-formed!

; '(lambda (x) (binary-+ '1 x))          ; body must be closed and translated

; '(lambda (x)
;    (declare (xargs :guard (natp x)     ; :guard must come first
;                    :split-types t))    ; :split-types must always be T
;    (binary-+ '1 x))

; '(lambda (x)
;    (declare (type integer x)           ; TYPE, IGNORE, IGNORABLE allowed
;             (xargs :guard (if (integerp x) (natp x) 'nil) ; guard must be
;                    :split-types t))                       ; translated and
;   (binary-+ '1 x))                                        ; include types

; One can write lambda$ expressions (in :FN slots) like:

; (lambda$ (x) (declare (type integer x)) (+ 1 x))

; which will translate to the well-formed lambda object:

;  '(LAMBDA (X)
;     (DECLARE (TYPE INTEGER X)
;              (XARGS :GUARD (INTEGERP X)
;                     :SPLIT-TYPES T))
;     (RETURN-LAST 'PROGN                  ; tagged as coming from lambda$
;                  '(LAMBDA$ (X)
;                            (DECLARE (TYPE INTEGER X))
;                            (+ 1 X))
;                  (BINARY-+ '1 X)))

; ---

; Here is a careful explanation of well-formedness.  The notion of a
; well-formed lambda object is formalized by the :program mode function
; well-formed-lambda-objectp.

; A well-formed lambda object has one of two forms:

; '(LAMBDA vars body')          ; ``simple''  lambda object
; '(LAMBDA vars dcl' body')     ; ``declared'' lambda object

; where

; (a) vars is a list of distinct legal variable names

; (b) dcl', if present, is a DECLARE containing, at most, TYPE, IGNORE,
;     IGNORABLE, and XARGS keys.

; (c) If an XARGS key is present it has exactly this form (XARGS :GUARD guard
;     :SPLIT-TYPES T), where guard is a fully translated logic mode term
;     involving only the formal variables, vars.  Note that the user of lambda$
;     may supply :SPLIT-TYPES NIL and may do so before or after the :GUARD, but
;     the resulting lambda object has the form described here.  Note: One might
;     wonder why we do not allow other XARGS keywords in lambda DECLAREs.
;     There is a discussion of that in the comment after
;     *acceptable-dcls-alist*.

; (d) The :GUARD specified in XARGS must include as a conjunct every TYPE
;     expression generated by any TYPE specs.  That is consistent with the
;     :SPLIT-TYPES T setting and means the quoted guard does not need to be
;     extended any further with the TYPES.  The point of this restriction is to
;     guarantee that the guard implies the types declared to the compiler.  But
;     this is a purely syntactic check and so may at times require entering
;     silly-looking guards.  For example, (declare (type rational x) (xargs
;     :guard (integerp x) :split-types t)) is ruled ill-formed because
;     (rationalp x) is not a conjunct of the guard, even though it is logically
;     implied by the guard.  So you'd have to use (declare (type rational x)
;     (xargs :guard (if (integerp x) (rationalp x) 'nil) :split-types t)).
;     Note that the guard is a fully translated conjunction, i.e., an IF, not
;     an AND!  Order of the conjuncts does not matter.

; (e) body' is a fully translated, tame, logic mode term, involving no free
;     variables and respecting the declared IGNORE and IGNORABLE declarations.
;     Note: The guard need not be tame (or even fully badged) because guards
;     are irrelevant to the axioms of apply$.  But guards must be in :logic
;     mode from the outset because we may have to prove guard obligations
;     on-the-fly in evaluation (no time for converting functions called from
;     :program to :logic mode).

;     Furthermore, in the case of a lambda object generated by lambda$, body'
;     is a tagged version of the translation of the given body.  Tagging
;     involves use of a special form generated by tag-translated-lambda$-body
;     and recognized by lambda$-bodyp.  This form contains the untranslated
;     lambda$ expression as well as the translation of its body.  We say such a
;     lambda object was ``tagged by lambda$'' or simply ``tagged'' in this
;     context.  For example, (LAMBDA$ (X) (+ 1 X)) translates to the tagged
;     lambda object '(LAMBDA (X) (RETURN-LAST 'PROGN 'orig-form tbody)), where
;     orig-form is (LAMBDA$ (X) (+ 1 X)) and tbody is (BINARY-+ '1 X).

; (f) A sort of negative property: There is no assurance that the :GUARD
;     guarantees that body' is well guarded.  That is, no guard verification is
;     done by translate.

; ---

; The reader may wonder why well-formed lambda objects handle DECLAREd types
; differently than, say, fully translated LET expressions containing DECLARED
; types.  For example, if you write:

; (let ((x expr)) (declare (type integer x)) (/ x 2))

; you get an application of a lambda-expressions whose body encodes the
; guard:

; ((LAMBDA (X)
;          (RETURN-LAST 'PROGN
;                       (CHECK-DCL-GUARDIAN (integerp X)
;                                           '(integerp X))
;                       (BINARY-* X (UNARY-/ '2))))
;  expr')

; So why, when you write

; (lambda$ (x)
;          (declare (type integer x))
;          (/ x 2))

; don't we translate it to the quoted version of the lambda-expression above?
; Put another way, why did we elect for our lambda objects to preserve the
; DECLARE form instead of building it into the body of the lambda in a way that
; allows guard verification to account for it?

; The answer is that lambda objects are compiled when they're applied and so
; the DECLARE forms, in particular, the TYPE, IGNORE, and IGNORABLE
; declarations, must be present for the compiler to see.

; ---

; The raw Lisp expansion of (lambda$ ...) is (quote (,*lambda-marker*
; . (lambda$ ...))), where *lambda-marker* is a raw lisp constant symbol whose
; value is in the ACL2_INVISIBLE package.  Any raw Lisp object thus marked
; had to have come from a successfully translated lambda$ which means the
; (lambda$ ...) form will be on the lambda$-alist world global.

; We cannot translate a lambda$ expression in raw Lisp because during loading
; of books, etc., we do not know the world will be the same as the world in
; which the expression was first used.

; Because the raw Lisp object generated by lambda$ is different from the ACL2
; object generated in the ACL2 loop, we cannot allow lambda$ anywhere but :FN
; slots, where we know the object will only be seen by apply$.

; ---

; This translation stuff just provides a convenience for the user.  System code
; encountering a lambda object may not assume the object is well-formed.
; That must be checked at runtime with well-formed-lambda-objectp.

; No amount of translate-time enforcement or tagging logically prevents
; ill-formed lambda objects from finding their way into terms or into apply$!

; Termp does not enforce well-formedness of lambda objects.

; ACL2 system developers must not assume well-formedness.

; ---

; We have a confusing variety of concepts competing for the job of recognizing
; lambda expressions.  We **highlight** the names of the various available
; recognizers and then summarize them below.

; (1) Apply$ considers any **consp** object passed into the :FN slot to be a
; lambda expression.  We defined apply$ that way to keep the logic definition
; simple, thereby simplifying proofs about it.  Note that apply$ makes
; absolutely no use of the DECLARE that might be found in a lambda object.

; (2) But we can only analyze ilks for objects that more truly resemble Lisp
; lambda expressions.  We need to know that the binding environments really
; assign distinct variable symbols, and we need to know that the bodies are
; closed terms wrt the formals.  Again, the optional DECLARE is irrelevant.  We
; define the function named **weak-well-formed-lambda-objectp** to recognize
; the lambda-like objects we can do ilk analysis on.

; (3) We also need to recognize when a lambda expression is tame so apply$ can
; dive into it safely.  Since this is a :logic mode activity we want to keep it
; as simple as possible while still enabling guard verification of the apply$
; clique and the existence of the model of apply$.  It is sufficient to check
; merely that the formals are symbols (not necessarily distinct variables) and
; the body is tame (but not necessarily closed).  The optional DECLARE is
; irrelevant.  So for this purpose we define the :LOGIC mode **tamep-lambdap**.
; We define an executable version of that concept (i.e., one that takes the
; world so we're not relying on the attachment theory to execute it) called
; **executable-tamep-lambdap**.  By the way, these two lambda recognizers use
; lambda-object-shapep to check that the expression is either (LAMBDA & &) or
; (LAMBDA & & &), but we don't consider lambda-object-shapep per se as a
; recognizer, just a way to keep the logic code in tamep-lambdap short.

; (4) Finally, we want to compile any lambda for which we can do guard
; verification.  This imposes many constraints, including the legitimacy of the
; DECLARE form, the legality of the variable names, etc.  For this purpose we
; define **well-formed-lambda-objectp**.  Even this function does not
; completely finish the job needed to compile and run the lambda: this function
; doesn't check that the guard and body are composed of guard verified
; functions or that the guard implies the guards of the body.
; Well-formed-lambda-objectp is partitioned into two phases, a syntactic one
; called syntactically-plausible-lambda-objectp and one that inspects the TYPE
; expressions, guard and body (supplied by the successful syntactic
; plausibility check) wrt the world to check things like termp and tameness.
; By dividing the work this way we can partition cl-cache lines into :GOOD,
; :BAD, and :UGLY status and save some work at apply$ time.  (We actually
; introduce a stricter test than syntactic plausibility in managing the cache.
; Syntactic plausibility is independent of the world; the stricter test takes
; the world as an argument and uses it to determine not just that the body,
; say, is not a termp but that it can NEVER be a termp because it uses a
; primitive in an unacceptable way.  (lambda (x) (cadr x)) and (lambda (x)
; (setq x '3)) are examples of lambdas are syntactically plausible -- among
; other things their bodies are pseudo-terms -- but which in fact fail this
; stricter test.  See potential-termp.)

; Summarizing the lambda recognizers then we have:

; recognizer                        purpose

; consp                             apply$

; weak-well-formed-lambda-objectp   ilk analysis

; tamep-lambdap                     apply$ guard verif and recursion control
;  and executable-tamep-lambdap      in the apply$ clique

; well-formed-lambda-objectp        cl-cache and compilation

; The last three concepts above participate in the generation of precise error
; messages.

; The question arises: can't we eliminate some of these?  For example, can't we
; we use well-formed-lambda-objectp for everything?  The answer is yes, we
; could; but it would complicate logical definitions and proofs.  From the
; user's perspective, apply$ assigns lambda-like meaning to any consp object
; and we can even evaluate such applications, albeit slowly compared to the
; evaluation of applications of well-formed guard verified lambda expressions.
; In short, we haven't minded complicating the system code with these various
; lambda recognizers if it truly gives us a simple logical story for the user
; and clear error messages for situations in which we can't do ilk analysis,
; guard verification, compilation, etc.

; Except for consp, all of these recognizers insist on the object being of one
; of two forms: (LAMBDA formals body) or (LAMBDA formals dcl body).  But do we
; really need to insist on those terminal nils?  We go out of our way to check
; them.

; We could probably have gotten away with looser forms, like (LAMBDA formals
; body . atom) or (LAMBDA formals dcl body . anything), except for
; well-formed-lambda-objectp which really must insist on a CLTL compliant
; lambda expression since we'll compile it.  But we decided we are confused
; enough!  And so we insist for sanity's sake alone that all these recognizers
; (except consp) require that the object be a true-list of length 3 or 4.  Even
; the two accessors lambda-object-dcl and lambda-object-body use (and
; (true-listp x) (eql (len x) ...))  to recognize and distinguish the two
; forms.

; We have not yet explained how lambda$ is handled in raw Lisp.  In the logic,
; apply$ handles lambdas by calling apply$-lambda.  The raw Lisp counterpart to
; apply$-lambda is specially defined in apply-raw.lisp, to implement the
; evaluation theory.  In the following when we refer to apply$-lambda we mean
; the raw Lisp function of that name.

; ---

; The lambda objects given to apply$-lambda for evaluation can actually have
; either of two forms depending on where they originated: either they were
; typed by the user at the top-level loop of ACL2 or they were embedded in
; defuns.

; Suppose the user types

; ACL2 !>(sum (lambda$ (x) (declare (type integer x)) (* x x)) '(1 2 3))

; The entire expression is translated and the lambda$ is expanded to:

; '(LAMBDA (X)                                                   ; [1]
;          (DECLARE (TYPE INTEGER X)
;                   (XARGS :GUARD (INTEGERP X)
;                          :SPLIT-TYPES T))
;          (RETURN-LAST 'PROGN
;                       '(LAMBDA$ (X)
;                                 (DECLARE (TYPE INTEGER X))
;                                 (* X X))
;                       (BINARY-* X X)))

; When the sum is evaluated, the raw Lisp apply$-lambda repeatedly sees the
; fully translated lambda expression [1].  Carrying out the basic idea of
; guard-checked evaluation is straightforward but potentially time consuming:
; Is [1] well formed?  If so, we can recover the guard.  Has [1] been guard
; verified or, if not, can we verify the guards in the current world?  If so,
; is the guard true of whatever we're applying this lambda to?  If all those
; tests succeed, we can compile [1] and apply it with CLTL's apply.  Since sum
; is mapping this lambda over a list of length 3, these questions are
; theoretically raised three times each in the evaluation of this one form.

; We can speed this up by caching the results of the various tests and of the
; compilation.  We discuss caching in the Essay on the CL-Cache Implementation
; Details.

; So far we've considered a lambda object that was literally part of a
; top-level evaluation command.

; Now consider another possibility.  Suppose the user introduces this function:

; (defun sum-sq (lst)
;   (sum (lambda$ (x) (declare (type integer x)) (* x x)) lst))

; Two versions of this defun get into raw Lisp, *1*sum-sq and sum-sq.  The *1*
; function will actually contain the translated lambda$, which is done by
; virtue of oneify calling translate11-lambda-object.  So the *1* version of
; sum-sq is handled as in [1] above.

; But the raw Lisp version of sum-sq will actually contain the lambda$, which
; will macroexpand to

; '(,*lambda$-mark* . (lambda$ (x) (declare (type integer x)) (* x x))) ; [2]

; in accordance with the expansion of lambda$ in raw Lisp.  So if

; ACL2 !>(sum-sq '(1 2 3))

; were evaluated at the top-level, the raw Lisp apply$-lambda would repeatedly
; see the marked untranslated lambda$ object [2].

; If apply$-lambda just followed the basic idea sketched above, it would find
; this untranslated lambda ill-formed.

; What apply$-lambda needs to know is (a) that this marked lambda$ object
; came from a successfully translated lambda$, and (b) what is the logical
; translation of that lambda$?

; We solve (a) by checking for the *lambda-marker* mark, which is only
; generated by the raw Lisp lambda$.

; As for problem (b), apply$-lambda answers that by using the lambda$-alist (a
; world global maintained by defun).  Every time defun successfully concludes
; it updates the lambda$-alist to map each of the lambda$s in the defun to the
; corresponding translated lambda.  One might wonder how we find the lambda$s
; in the fully translated body?  The answer is: we tagged them with the
; RETURN-LAST tagging mentioned earlier.  So even though we explore a fully
; translated body at the end of the defun-processing, we can recover
; untranslated lambda$s.  One might also wonder how the tags stayed in place
; since we remove-guard-holders before storing bodies.  The answer is: these
; RETURN-LAST taggings are inside quoted objects and remove-guard-holders
; does not dive into objects.

; So when apply$-lambda sees the *lambda$-marker* it gets the translated
; version of the lambda$ from the lambda$-alist and then goes to the cache
; as described for [1].

; ---

; We have noted that every well-formed lambda object in a defun is subjected to
; guard verification when guard verification is performed on the defun'd
; function.  First, this is a bit odd since the lambda objects mentioned in the
; body are quoted objects.  So a strange thing about post-Version_8.1
; verify-guards is that it dives into some quoted objects to generate guard
; obligations.  (Think of those quoted objects as non-recursive functions
; defined simultaneously with the defun; we generate guard obligations for all
; of the functions.)

; This has the advantage of allowing the user to provide :hints for the
; successful guard verification of lambda objects used in defuns.  It also
; surreptiously adds those lambda objects to the cache.

; But it is possible that a :GOOD lambda object in the cache gets pushed out by
; 1000 other lambda objects.  To avoid having to re-verify the guards of lambda
; objects verified with verify-guards, we maintain the world global
; common-lisp-compliant-lambdas.  When apply$-lambda encounters a lambda object
; not in the cache it sets up an :UNKNOWN cache line and tries to re-validate
; it (that's the general mechanism for building a :GOOD cache line).  In
; maybe-re-validate-cl-cache-line you'll see we check
; common-lisp-compliant-lambdas to ``instantly'' re-validate formerly known
; compliant lambda objects processed through verify-guards.

; End of Essay on Lambda Objects and Lambda$

; Essay on LOOP$
; Added 23 January, 2019

; [Timeline: This essay started as a design document a year ago, January, 2018.
; But work was delayed as described in the Essay on Lambda Objects and Lambda$
; until December, 2018 when we returned to the design document with lambda$ as
; a feature we could exploit.  We worked simultaneously on the design document
; and the implementation.  Eventually, the design document became this essay.
; As a result, it is somewhat more detailed than we might have written had we
; written it after-the-fact!  The Abstract advertises that we're adding loop to
; ACL2, but we actually add loop$.  We left the Abstract as originally written
; partly because it formed the abstract of a talk given to the ACL2 Seminar on
; 25 January, 2019, and we knew the audience wouldn't know what ``loop$'' was.
; Loop$ was added to the sources in late January, 2019.]

; -----------------------------------------------------------------
; On ACL2 Support for LOOP

; Common Lisp, like other programming languages, supports convenient iteration
; primitives, like FOR- and WHILE-loops.  Mathematical machinery developed for
; several years through early 2019 has created a way to define iterative
; constructs in ACL2.  For example, one can now type

; (loop$ for x in (test-data) when (not (test x)) collect x)

; to collect each x in (test-data) that fails (test x).  Our goals are to make
; loop$s execute as fast as they do in Common Lisp and as easy to reason about
; as equivalent recursive functions.  This will enable the ACL2 user to write
; tests and other code without needing to define recursive functions to model
; iteration.

; As of this writing (February, 2019; after Version_8.1), the current support
; falls short of our goals in three respects: (a) some useful ACL2 expressions
; cannot be used inside loop$s, (b) when used interactively loop$ statements
; execute about 10x slower than in Common Lisp, and (c) we do not yet have a
; library of lemmas to automate routine proofs about loop$s.  The good news is
; that when used in definitions, loop$ statements execute at Common Lisp
; speeds, and we see ways to address the shortcomings above.  We believe that
; when this work is complete loop$ statements will be more common than function
; definitions in ACL2 models and interactive sessions.

; -----------------------------------------------------------------
; Abstract

; We describe a method for handling a small subset of CLTL LOOP statements so
; that when they appear in guard verified defuns they are intact in the raw
; Lisp versions of the defuns (and are thus executed as efficiently compiled
; code).  We assume the reader is familiar with CLTL LOOPs.  One obscure
; feature we exploit is the CLTL OF-TYPE clause, used in [1] below.

; We will concentrate on one form of loop here:

; (LOOP FOR v OF-TYPE spec IN lst SUM expr)                           ; [1]

; the logical semantics of which is, somewhat informally,

; (SUM (LAMBDA$ (v) (DECLARE (TYPE spec v)) expr) lst)                ; [2]

; Loop statement [1] with semantics [2] allows us to explore the key question:

;   What guard conjectures must be generated from [2] to ensure error-free
;   execution of [1] in raw Lisp?

; Related to that question is

;   What lemma machinery do we need to support guard proofs for loops?

; The answers to these questions allow the natural extension of the class of
; loops we handle to include loop operators other than SUM, such as COLLECT,
; ALWAYS, and APPEND.  In addition, the ``target clause'' of the LOOP, e.g., IN
; lst, can easily be extended to include FROM i TO j BY k and ON lst as target
; clauses.  We can also add UNTIL and WHEN clauses in a semantically
; compositional way so that, e.g.,

; (LOOP FOR v IN lst UNTIL p WHEN q COLLECT r)

; is logically

; (COLLECT (LAMBDA$ (v) r)
;          (WHEN (LAMBDA$ (v) q)
;                (UNTIL (LAMBDA$ (v) p) lst)))

; All of the loop features mentioned above are included in what we call
; ``plain'' loops: loops that have a single iteration variable and no other
; free variables.

; After we discuss the semantic and guard issues for plain loops, we introduce
; ``fancy'' loops by adding AS clauses which allow for multiple iteration
; variables over multiple targets, and allow for variables other than the
; iteration variables.  An example of a fancy loop is

; (LOOP FOR v IN vlst AS u IN ulst SUM (+ c u v))

; where c is bound outside the loop and is thus a constant in the loop.  Fancy
; loops require a generalization of the basic semantic form and an elaboration
; of the guard proof machinery.

; There are several paragraphs marked

;;; Possible Future Work on Loop$:

; which describe some possible future work, some of which is actually quite
; desirable.

; -----------------------------------------------------------------
; Section 0:  Limitations

; The translation of

; (LOOP FOR v OF-TYPE spec IN lst SUM expr)                           ; [1]

; into

; (SUM (LAMBDA$ (v) (DECLARE (TYPE spec v)) expr) lst)                ; [2]

; immediately suggests three limitations: (a) expr must be in :logic mode and
; not involve state or other stobjs since apply$ doesn't handle such features,
; (b) expr must be tame since all LAMBDA objects must be tame to be applied,
; and (c) expr may contain no free variables other than the iteration variable
; v.  We will remove limitation (c) by using a more general semantics when
; necessary, as eventually described below.

; But limitations (a) and (b) are currently insurmountable and directly cause a
; practical restriction on the use of loop.  For example, the user may be
; tempted to type loop$ statements to interactively inspect aspects of the ACL2
; state or to print things, and this is generally impossible.

;;; Possible Future Work on Loop$:

;;; It is unfortunate we can't apply$ program mode functions.  Think about a
;;; logical story that allows them at the top-level and in function bodies.
;;; Among the issues will be how do we handle the absence of badges for program
;;; mode symbols?  For example, we don't know which args are :FN or whether the
;;; function traffics in state or stobjs or returns multiple values.  We could
;;; require (and recode defwarrant to allow) program mode functions to be
;;; badged but not warranted -- they can't be warranted since warrants are
;;; logic-mode.

; In addition, loop statements in function defuns may not call the newly
; defined function recursively.  This prevents defuns like:

; (defun varcnt (term)          ; THIS IS INADMISSIBLE!
;   (cond ((variablep term) 1)
;         ((fquotep term) 0)
;         (t (loop for x in (fargs term) sum (varcnt x)))))

; This defun of varcnt causes a translation error because the translation of
; the loop into a scion produces a non-tame LAMBDA object because, at the time
; of translation, the recursively called varcnt is unbadged.  We consider this
; an important limitation deserving of future work.

;;; Possible Future Work on Loop$:

;;; Is there a way to allow loop$ to be used as shown in the currently
;;; inadmissible varcnt above?

; -----------------------------------------------------------------
; Section 1:  Terminology and Basic Setup

; The names used above are not the ones we actually use.  Instead of loop we
; will use loop$.  The scions sum, always, collect, and append used above are
; actually named sum$, always$, thereis$, collect$ and append$, so that the
; scion name is predictable from the loop operator symbol.  (We can't use the
; loop operator names as scion names because for example the names always and
; append are already defined in ACL2.)

; Loop$ is essentially an ACL2 macro so that

; (loop$ for v in lst sum expr)                                       ; [1]

; translates to

; (sum$ (lambda$ (v) expr) lst)                                       ; [2]

; and if there is an OF-TYPE spec modifier in [1] it becomes type declaration
; in the lambda$ in [2]

; But loop$ is not actually a macro because it must do some free variable
; analysis to know whether to use the plain or fancy semantics, which in turn
; means loop$ must translate the until, when, and loop body expressions.
; Macros can't call translate, so loop$ is built into translate.

; (BTW: Since the until, when, and loop body expressions each become the body
; of a lambda$ expression, it is confusing to call the ``loop body expression''
; simply the ``body.''  Instead, we call it the ``lobody expression.'')

; The definition of sum$ is

; (defun sum$ (fn lst)
;   (declare (xargs :guard (and (apply$-guard fn '(nil))
;                               (true-listp lst))
;                   :verify-guards nil))
;   (mbe :logic (if (endp lst)
;                   0
;                   (+ (fix (apply$ fn (list (car lst))))
;                      (sum$ fn (cdr lst))))
;        :exec (sum$-ac fn lst 0)))

; Sum$'s guard just requires that fn be a function symbol or LAMBDA object of
; arity 1, and lst be a true-list.  Sum$ is guard verified, but first we have
; to prove that it returns a number so we can satisfy the guard on the +.  The
; fix is necessary since we don't know fn returns a number.

; A ``loop$ scion'' is any scion used in the translation of loop$ statements.
; The plain ones are sum$, always$, thereis$, collect$, append$, until$, and
; when$ and their fancy counterparts are sum$+, always$+, thereis$+, collect$+,
; append$+, until$+, and when$+.  We discuss the fancy loop$ scions in Section
; 8.

; The plain loop$ scions are informally described as follows, where the
; elements of lst are e1, ..., en:

; (sum$ fn lst): sums all (fix (apply$ fn (list ei)))

; (always$ fn lst): tests that all (apply$ fn (list ei)) are non-nil

; (thereis$ fn lst): tests that some (apply$ fn (list ei)) is non-nil
;                    and returns the first such value

; (collect$ fn lst): conses together all (apply$ fn (list ei))

; (append$ fn lst): appends together all (true-list-fix (apply$ fn (list ei)))

; (when$ fn lst): conses together all ei such that (apply$ fn (list ei))

; (until$ fn lst): conses together all ei until the first i such that
;    (apply$ fn (list ei)) is non-nil

; Note that among the plain loop$ scions, only sum$ and append$ contain
; ``fixers.''

; It is important to realize that if a loop$ statement is typed at the top of
; the ACL2 read-eval-print loop, its logical translation (into loop$ scions) is
; executed.  To make top-level execution as efficient as possible each loop$
; scion is defined with an mbe that provides a tail-recursive :exec version.
; The only exceptions are always$ and always$+ which are tail-recursive
; themselves.

; A loop$ statement typed in a defun becomes a loop$ statement in the raw Lisp
; defun generated.  We define loop$ in raw Lisp as a macro that replaces the
; loop$ symbol by loop.

; We allow the user to add additional guard information to loop$ statements by
; allowing a so-called ``:guard clause'' before the until, when, and loop$
; operator expressions, since these expressions generate LAMBDA objects and, to
; verify the guards on those LAMBDA objects so that compiled code can be run,
; it is sometimes necessary to specify stronger guards than can be expressed
; simply with CLTL's OF-TYPE spec clauses.  For example,

; (loop$ for v of-type integer in lst1
;        as u of-type integer in lst2
;        collect :guard (relp v u) (lobody v u))

; We discuss the :guard clause feature of loop$ later.  When loop$ is
; macroexpanded to loop in raw Lisp, the :guard clauses are stripped out.

; -----------------------------------------------------------------
; Section 2:  The Guard Problem

; The issue we're grappling with is that the guard conjectures generated for
; [2] are insufficient to ensure the error-free raw Lisp execution of [1].

; Consider this concrete example:

; (loop$ for v of-type integer in '(1 2 3 IV) sum (foo 1 v))          ; [1]

; which translates to

; (sum$ (lambda$ (v) (declare (type integer v)) (foo 1 v))            ; [2]
;       '(1 2 3 IV)).

; Let's suppose that the LAMBDA object can be guard verified.

; Recall that sum$ is guard verified with a guard that checks that the
; functional object, fn, is a symbol or a LAMBDA of arity 1 and that the
; target, lst, is a true-listp.  So the actuals in [2] satisfy sum$'s guard.

; If this loop$ expression is typed at the top level of ACL2, *1* sum$ is
; called, the guard successfully checked, and the fast raw Lisp sum$-ac is
; called.  Sum$-ac calls the raw Lisp apply$-lambda on the LAMBDA object and
; successive elements of the target.  Assuming, as we did, that the LAMBDA is
; guard verified, each call of apply$-lambda checks whether the element under
; consideration satisfies the guard of the LAMBDA object.  If so, the compiled
; LAMBDA object is run; if not, either an guard violation is called or the
; logical version of apply$-lambda is used to compute the value of the LAMBDA
; object on the element (depending on set-guard-checking).  If a value is
; computed, it is fixed and added to the running accumulator.  In no case is a
; hard error caused: the guards of sum$ are satisfied by the actuals in [2].

; On the other hand, if the loop$ expression is typed as part of a guard
; verified defun, then the sum$ and the LAMBDA object are both guard verified
; at defun-time.  Then, when the defun'd function is called, the loop$ is
; executed as a raw Lisp loop:

; (loop for v of-type integer in '(1 2 3 IV) sum (foo 1 v))

; There are two sources of hard errors in this execution, stemming from
; conjectures NEVER CHECKED when verifying and checking the guards of [2].

; Special Conjecture (a): The guard of (sum$ fn lst) does not include the test
; that every element of lst satisfies the guard of fn.  (Note that the guard of
; fn would include the type-spec used in the OF-TYPE clause plus whatever extra
; guard might be written explicitly by the user.)  It isn't necessary for (a)
; to be true in order to run [2] without hard error because apply$-lambda
; checks guards at runtime and shifts between fast compiled code and logical
; code as required.  But the raw Lisp loop might call (foo 1 v) on some v not
; satisfying the guard of foo.  Indeed it does here with the fourth element.
; This could cause a hard error.  The root problem is that the raw Lisp loop
; does not use apply$-lambda.

; Special Conjecture (b): The guard of (sum$ fn lst) does not include the test
; that fn returns a number on every element of lst.  This is not necessary
; for our sum$ because it wraps the apply$-lambda in a fix.  But the raw Lisp
; loop expects the lobody to return a number and will cause a hard error
; if it doesn't.  The root problem is that sum$ uses fix and loop doesn't.

; There is also a Special Conjecture (c).  Consider

; (loop for v of type type-spec on lst collect ...)

; The semantics of this will be (collect$ (lambda$ ...) (tails lst)) where
; tails collects the non-empty tails of lst.  The guard of collect$ will insure
; that lst is a true-listp.  But if you run this in Common Lisp you will find
; that the type-spec is checked on EVERY tail of lst, including NIL, not just
; the non-empty ones.  Here is an example, to be tried in raw CCL:

; (declaim (optimize (safety 3))) ; to force CCL to test the type-spec
; (defun my-typep (x)             ; the type-spec we'll use
;   (format t "Next: ~s~%" x)
;   t)
; (defun test-type-spec (lst)
;    (loop for x of-type (satisfies my-typep) on lst
;          until (> (car x) 5)
;          when (<= (car x) 3) collect x))
; (test-type-spec '(1 2 3 4 5))
; Next: (1 2 3 4 5)
; Next: (2 3 4 5)
; Next: (3 4 5)
; Next: (4 5)            ; <--- [1]
; Next: (5)
; Next: NIL              ; <--- [2]
; ((1 2 3 4 5) (2 3 4 5) (3 4 5))

; (test-type-spec '(1 2 3 4 5 6 7))
; Next: (1 2 3 4 5 6 7)
; Next: (2 3 4 5 6 7)
; Next: (3 4 5 6 7)
; Next: (4 5 6 7)
; Next: (5 6 7)
; Next: (6 7)            ; <--- [3]
; ((1 2 3 4 5 6 7) (2 3 4 5 6 7) (3 4 5 6 7))

; These examples show that the type-spec may be called on NIL (see [2]) but may
; not be (see [3]) depending on whether the UNTIL clause cuts off iteration
; before the end is reached.  We will not try to predict whether an until
; clause will exit early and so we always test NIL.

; Also, we see that the type-spec is called on iterations not seen by the
; operator expression (see [1]).

; In addition, trying the same thing with a from-to-by shows that
; special cases are considered:

; (defun test-type-spec (i j k)
;    (loop for x of-type (satisfies my-typep) from i to j by k
;          collect x))
; (test-type-spec 1 7 2)
; Next: 2                ; = k
; Next: 7                ; = j
; Next: 1                ; = i and first value of x
; Next: 3                ; ...
; Next: 5
; Next: 7
; Next: 9                ; first value beyond j
; (1 3 5 7)

; We see that (from-to-by i j k) starts by calling the type-spec on i, j, and
; k, then on every iteration (after the first which is i), and then on the
; value that pushed over the limit j.  Of course, early exit with an until
; can avoid that

; (defun test-type-spec (i j k)
;    (loop for x of-type (satisfies my-typep) from i to j by k
;    until (> x 5)
;    collect x))
; (test-type-spec 1 7 2)
; Next: 2
; Next: 7
; Next: 1
; Next: 3
; Next: 5
; Next: 7
; (1 3 5)

; We will not try to predict whether the until clause will exit early and
; always test the first value beyond j, which is (+ i (* k (floor (- j i) k))
; k).  See the verification of guards for from-to-by in
; books/system/apply/loop-scions.lisp where we show that (+ i (* k (floor (- j
; i) k))) is the last value at or below j.

; The ``purist'' solution, at least to problems (a) and (b), is to strengthen
; the guard of sum$ to include Special Conjectures (a) and (b).  It is
; certainly possible to formalize (b): just define a scion that runs fn across
; lst and checks that every result is a number.  This slows down the guard
; check but would allow us to remove the fix from sum$; in fact, tests show
; that it about doubles the time to compute a well-guarded sum$ expression in
; the ACL2 loop.  (Note: our current sum$, which fixes the result of the
; apply$, takes 0.24 seconds to sum the first million naturals.  The purist sum
; containing the additional guard conjunct for (b) takes about 0.55 because it
; scans the list once to check the guard and again to compute the sum.)

; It might be possible to formalize (a) but it would require introducing a
; :logic mode function that allows a scion such as sum$ to obtain the guard of
; a function symbol, perhaps as a LAMBDA object.  E.g., (guard 'foo) might be
; '(LAMBDA (x) (IF (CONSP x) 'NIL 'T)).  This could probably be implemented by
; extending the current notion of badge to include a guard component along with
; the arity, ilks, etc., of each warranted symbol.  Then, Special Conjecture (a)
; could be formalized by apply$ing the guard of fn to each successive element
; of lst, e.g., (always$ (guard fn) lst).  This is problematic for two reasons.
; The first is that we're violating the rules on warrants by putting a
; non-variable, non-quote term into a slot of ilk :FN.  Exceptions can probably
; be made for (guard fn) given our control of the whole environment.  The
; second is that it involves running a function over the entire target as part
; of the guard check, so like the purist solution to conjecture (b), the purist
; solution to (a) further slows down guard checking.

; But we don't see a purist solution to (c) because, for example, the guard on
; (from-to-by i j k) can't express the idea that the arguments satisfy the
; type-spec of the the LAMBDA because (from-to-by i j k) doesn't contain the
; LAMBDA.  And collect$ can't do it because by the time collect$ executes the
; (from-to-by i j k) will have turned into a list of integers indistiguishable
; from an IN iteration.

; We reject these purist solutions both for their logical complexity (or
; impossibility) (especially (a)) and the slowdown in execution in the ACL2
; loop.

; At the other extreme, we could adopt the Lisp hacker approach and give the
; raw Lisp loop$ a slightly different semantics than loop.  For example,
; we could arrange for

; (loop$ for v of-type integer in '(1 2 3 iv) sum (foo 1 v))

; to expand in raw Lisp to something like:

; (loop for v in '(1 2 3 iv)
;       sum (if (integerp v)
;               (if (check-the-guard-of 'foo (list 1 v))
;                   (fix (foo 1 v))
;                   (guard-violation-behavior ...))
;               (guard-violation-behavior ...)))

; We reject the addition of runtime checks into loop statements because it
; violates the whole goal of this project.  We want guard verified ACL2 loop$
; statements to execute at raw Lisp loop speeds.

; We give our preferred solution in the next section but roughly put it
; leaves the guard on sum$ unchanged so it is easy to check, it leaves the
; fix in place so sum$ can be guard verified with that guard, but it changes
; the guard conjecture generation routine, guard-clauses, to generate extra
; guard conjectures for calls of sum$ on quoted function objects.

; One last note: It should be stressed that the above goal is limited to loop$
; statements in guard verified defuns.  While we want loop$ statements that are
; evaluated at the top-level of the ACL2 to evaluate reasonably fast, we do not
; try to achieve raw Lisp loop speeds.  That would require a wholesale change
; to ACL2's execution model.  The read-eval-print loop in ACL2 reads an
; expression, translates it, and evaluates the translation.  Untranslating
; certain ground sum$ calls into loops for execution is beyond the scope of the
; current work.  We're not even sure it's a project we should add to our todo
; list!  The problem is that loop$ can be executed as loop only if the loop$ is
; guard verified and if we have to do full-fledged theorem-prover based (as
; opposed to tau reasoning) guard verification on every user interaction, we
; need to significantly automate guard verification!  So to summarize: loop$
; statements in guard verified defuns will execute at raw Lisp loop speeds,
; while interactive input to the ACL2 read-eval-print loop will continue to use
; the current model: execute the translation with *1* functions which do
; runtime guard checking and shift to raw Lisp whenever possible.

; To put this in perspective, below we compute a simple arithmetic expression
; over the first one million naturals.  We do it three ways, first at the
; top-level of the ACL2 loop using a loop$ with no type declaration at all (and
; hence a LAMBDA object that cannot be guard verified), second at the top-level
; with a loop$ containing a type declaration, and finally, with that same loop$
; in a guard-verified function defun.  The first takes 3.37 seconds, the second
; takes 0.36 seconds, and the last takes 0.01 seconds.  Not bad!

; ACL2 !>(time$ (loop$ for i
;                      in *m* sum (* (if (evenp i) +1 -1) i)))
; ; (EV-REC *RETURN-LAST-ARG3* . #@125#) took
; ; 3.37 seconds realtime, 3.34 seconds runtime
; ; (160,012,864 bytes allocated).
; 500000

; ACL2 !>(time$ (loop$ for i OF-TYPE INTEGER                   ; note type spec
;                      in *m* sum (* (if (evenp i) +1 -1) i)))
; ; (EV-REC *RETURN-LAST-ARG3* . #@127#) took
; ; 0.36 seconds realtime, 0.36 seconds runtime
; ; (16,000,032 bytes allocated).
; 500000


; ACL2 !>(defun bar (lst)
;           (declare (xargs :guard (integer-listp lst)))
;           (loop$ for i of-type integer
;                  in lst sum (* (if (evenp i) +1 -1) i)))

; Since BAR is non-recursive, its admission is trivial.  We observe that
; the type of BAR is described by the theorem (ACL2-NUMBERP (BAR LST)).
; We used the :type-prescription rule SUM$.

; Computing the guard conjecture for BAR....

; ...

; Q.E.D.

; That completes the proof of the guard theorem for BAR.  BAR is compliant
; with Common Lisp.

; Summary
; Form:  ( DEFUN BAR ...)
; Rules: ...
; Time:  0.04 seconds (prove: 0.01, print: 0.00, other: 0.02)
; Prover steps counted:  455
;  BAR

; ACL2 !>(time$ (bar *m*))
; ; (EV-REC *RETURN-LAST-ARG3* . #@126#) took
; ; 0.01 seconds realtime, 0.01 seconds runtime
; ; (16 bytes allocated).
; 500000

; -----------------------------------------------------------------
; Section 3:  Our Solution to the Special Conjectures

; The approach we advocate is to leave the guard of sum$ as is, with the fix in
; the sum$, but we change guard generation so that in certain special cases we
; generate (and thus have to prove) guard conjectures beyond those strictly
; required by the scion's guard.

; The ACL2 system function guard-clauses is the basic function for generating
; guard conjectures for a term.  It is called in two situations in which the
; term being guard-verified will be turned into raw Lisp code: when it is
; called from within defun (or verify-guards on behalf of a function symbol),
; and when called on a LAMBDA object (as by the raw Lisp apply$-lambda and
; *cl-cache* machinery).  In these situations -- where raw Lisp code will be
; run -- guard-clauses treats certains calls of loop$ scions specially.  In
; particular, if the loop$ scion's function object is a quoted tame function
; symbol of the appropriate arity (depending on whether the loop$ scion is
; plain or fancy) or is a quoted well-formed LAMBDA object of the appropriate
; arity, then guard-clauses adds two guard conjectures not actually required by
; the scion's guard.  These two conjectures formalize Special Conjectures (a)
; and (b) about the function object and target.

;;; Possible Future Work on Loop$:

;;; We might want to apply the same special treatment to the case of guard
;;; verification of theorems.  Otherwise, one could be disappointed when a
;;; theorem is successfully guard-verified but when that theorem is put into
;;; the body of a function, guard verification fails.

; Special Conjecture (a): Every member of the target satisfies the guard of the
; function object.

; Special Conjecture (b): On every member of the target, the function object
; produces a result of the right type, e.g., an acl2-number for SUM and a
; true-listp for APPEND.

; Just focusing on a call of a plain loop$ scion, e.g., (sum$ 'fn target),
; where (i) there is one iteration variable, v, (ii) the quoted function
; object, fn, is a tame function symbol or LAMBDA object of arity 1, (iii) fn
; has a guard of guardexpr, and (iv) the loop$ scion expects a result of type
; typep (e.g., acl2-numberp for sum$ and true-listp for append$), the two
; conjectures are:

; (a) (implies (and <hyps from clause>
;                   (member-equal newvar target))
;              guardexpr/{v <-- newvar})

; (b) (implies (and <hyps from clause>
;                   (member-equal newvar target))
;              (typep (apply$ 'fn (list newvar))))

; (c1) (implies (and <hyps from clause>)        ; target (TAILS lst)
;               type-spec-expr/{v <-- NIL})

; (c2) (implies (and <hyps from clause>)        ; target (from-to-by i j k)
;               (and type-spec-expr{v <-- i}
;                    type-spec-expr{v <-- j}
;                    type-spec-expr{v <-- k}
;                    type-spec-expr{v <-- (+ i (* k (floor (- j i) k)) k)}))

; Here, <hyps from clause> are whatever guard and tests govern the occurrence
; of the call of the loop$ scion, and newvar is a completely new variable
; symbol.  Warrant hypotheses, <warrant hyps>, are added for the warranted
; function symbols that can support simplification of the term; see
; collect-warranted-fns.  It is sound to add these for a given loop$ expression
; because the only purpose of the Special Conjectures is to avoid guard
; violations when evaluating the corresponding raw Lisp loop expression, which
; happens only when *aokp* is true and hence every warrant is true.  We only
; consider warrants that seem potentially necessary, but we can soundly
; consider any warrant we like; thus collect-warranted-fns is allowed to return
; any subset of the list of all warranted function symbols in the given world
; parameter.

; Recall that we will generate these special conjectures even if the user
; did not write a loop$ but instead wrote a scion call that sort of looks
; like a loop$!  C'est la vie.  The user can avoid the special conjectures
; by using different function names defined to be our names.

; The idea in our formalizations of (a) and (b) is that <hyps from clause> tell
; us about properties of the target and the member-equal hypothesis tells us
; that newvar is an (arbitrary) element of the target.  (a) then says that fn's
; guard is satisfied by newvar and (b) says that fn applied to newvar returns a
; result of the right type.

; These two special conjectures are only generated on terms that MIGHT HAVE
; BEEN generated by loop$ statements, i.e., calls of loop$ scions on quoted
; tame well-formed function objects.  Since the function object in question is
; quoted at guard generation time it is easy to extract the guard of the
; object.  (Note: the comparable problem in the so-called purist solution of
; Section 2 was practically daunting because we needed to express formula (a)
; for an unknown fn.)

; Since we generate the ``normal'' guard conjectures for the loop$ scion in
; addition to these two, we know the loop$ scion can run in the ACL2 loop
; without error.

; Since we generate (and have to prove) these guard conjectures for every
; term that might have been produced by a loop$ statement, we are assured that
; the corresponding loop can be executed without hard error in raw Lisp.

; We generate (and thus must prove) conjectures (a) and (b) for all calls of
; loop$ scions on quoted tame well-formed function objects even though the user
; might have entered them WITHOUT using loop$.  We rationalize this decision
; with the thought: the user will use loop$ statements when possible because
; they execute faster.

; But there is a problem with this rationalization that suggests future work
; and an important (but not soundness related) oversight in our current
; handling of LAMBDA objects.  We discuss this in Appendix A below.

; -----------------------------------------------------------------
; Section 4:  Handling ON lst and FROM i TO j BY k

; We handle the ON and FROM/TO/BY clauses by turning them into lists of the
; relevant elements and then appealing to the same loop$ scions we use for
; loop$ with IN clauses.  For example, the translation of

; (loop$ for v on lst sum (len v))

; is essentially

; (sum$ (lambda$ (v) (len v))
;       (tails lst))

; where (tails lst) is defined as the function that collects successive
; non-empty tails of lst.

; To be utterly precise about what we mean by ``essentially'', the
; translation of (loop$ for v on lst sum (len v)) is actually

; (sum$ '(lambda (v)
;                (declare (ignorable v))
;                (return-last 'progn
;                             '(lambda$ (v)
;                                       (declare (ignorable v))
;                                       (len v))
;                             (len v)))
;       (tails lst))

; where the (ignorable v) declaration is there just in case the body doesn't
; use v, and the return-last is just the marker indicating that a lambda$
; produced this quoted LAMBDA object.  But henceforth we will show
; ``translations'' that are just ``essentially translations,'' untranslating
; familiar terms like (binary-+ '1 x) and dropping parts that are irrelevant.

; The translation of

; (loop$ for v from i to j by k sum (* v v))

; is

; (sum$ (lambda$ (v) (* v v))
;       (from-to-by i j k))

; where (from-to-by i j k) collects i, i+k, i+2k, ..., until j is exceeded.  If
; the loop$ expression does not provide a BY k clause, BY 1 is understood.
; Unlike CLTL, we require that i, j, and k be integers.  CLTL already requires
; that k be positive.  This restriction makes it easier to admit from-to-by and
; is tail-recursive counterpart.

;;; Possible Future Work on Loop$: CLTL supports from/downfrom/upfrom and
;;; to/downto/upto/below/above.  Eventually we should change the parse-loop$ to
;;; parse those and provide the necessary translation, defuns of the necessary
;;; enumerators, and proof support.

;;; Possible Future Work on Loop$: Admitting the version of from-to-by that
;;; operates on rationals by a positive rational increment is a good little
;;; arithmetic project.  Admitting the tail-recursive version which counts down
;;; to i to assemble the list in the right order is an interesting project even
;;; for integers.  Hint: You can't necessarily start at j!  See the proof of
;;; the lemma from-to-by-ac=from-to-by-special-case in the book supporting
;;; proofs about loop$.

; In CLTL it is legal to write (loop for i from 1 until (p i) collect (r i))
; but this is impossible in ACL2 because it would require a termination
; argument.  All uses of the ``from i'' clause must be followed by a ``to j''
; clause.

; These translations have two advantages over the perhaps more obvious approach
; of defining a version of sum$ that applies fn to tails of its target instead
; of elements, and a version that applies fn to numbers generated by counting
; by k.  One advantage is that this is compositional.  Lemmas about (tails lst)
; and (from-to-by i j k) can be applied regardless of the loop$ scion involved.
; The other advantage is that we only need one plain sum$ scion, not three, so
; the same basic lemmas about sum$ can be used regardless of the target.

; A disadvantage of this translation is that it makes it a little slower to
; execute at the top-level of ACL2 because the (possibly large) target copied
; by tails or fully enumerated by from-to-by before the loop$ scion starts
; running.  Of course, execution of these kinds of loop$s in guard verified
; defuns is fast: it is done by CLTL loop.  So this inefficiency is only seen
; in top-level evaluation.

; That said, we actually experimented with defining separate scions for every
; legal combination of IN/ON/FROM-TO-BY, UNTIL, WHEN,
; SUM/ALWAYS/COLLECT/APPEND, getting 43 tail-recursive, guard verified
; functions and then timed a few runs.  We learned that the composition
; approach we adopted here is actually faster because CCL consing is so fast.
; For details of that experiment see Appendix B.

; -----------------------------------------------------------------
; Section 5:  Handling UNTIL and WHEN Clauses

; Until and when clauses are handled in the same spirit as ON: copy the target
; and select the relevant elements.

; Let's consider an example.  The constant *tenk-tenk* used below is the
; concatenation of the integers from 1 to 10,000, together with itself, i.e.,
; '(1 2 3 ... 10000 1 2 3 ... 10000).  However, in the translations below we
; will show it as *tenk-tenk*.  This loop$

; (loop$ for v on *tenk-tenk*
;        until (not (member (car v) (cdr v)))
;        when (evenp (car v))
;        collect (car v))

; collects the even elements of the target but stops as soon as the element no
; longer appears later in the list.  So the iteration stops after the first
; 10000 and the loop$ produces (2 4 6 ... 10000).  This, of course, is a silly
; way to collect the evens up to 10000 but stresses our evaluation mechanism.

; The translation is

; (collect$
;  (lambda$ (v) (car v))
;  (when$
;   (lambda$ (v) (evenp (car v)))
;   (until$
;    (lambda$ (v) (not (member (car v) (cdr v))))
;    (tails *tenk-tenk*))))

; That is, first we enumerate the tails of the target, then we cut it off at
; the first tail in which the car is not a member of the cdr, then we select
; the tails whose cars are even, and then we collect the cars of those tails.

; This is relatively easy to reason about because it is compositional: lemmas
; can be proved about the various steps of the operation.  It preserves our
; goal of making the loop$ execute at raw Lisp loop speeds in guard verified
; defuns and it raises the issue of evaluation performance at the top-level of
; the ACL2 loop.  However, we're satisfied with the current top-level
; evaluation performance.

; Let's put some numbers on that.  We start with an empty compiled LAMBDA cache.

; The simplest version of our loop$, containing no declarations, is timed below.

; ACL2 !>(len (time$
;              (loop$ for v
;                     on *tenk-tenk*
;                     until (not (member (car v) (cdr v)))
;                     when (evenp (car v))
;                     collect (car v))))

; 2.48 seconds realtime, 2.48 seconds runtime

; Printing the cache shows that each of the lambdas in the translation has
; status :BAD because tau cannot prove the guard conjectures (e.g., on (car
; v)), so the lambdas are interpreted.

; After clearing the cache, we try again, but this time with an appropriate
; OF-TYPE declaration:

; ACL2 !>(len (time$
;              (loop$ for v of-type (and cons (satisfies integer-listp))
;                     on *tenk-tenk*
;                     until (not (member (car v) (cdr v)))
;                     when (evenp (car v))
;                     collect (car v))))

; 2.76 seconds realtime, 2.76 seconds runtime

; The three lambdas in the translation of this loop$ each have a guard of (and
; (consp v) (integer-listp v)).  Tau spends a little more time, proves the
; guards on the outermost lambda, responsible for collecting (car v), but fails
; on the other two (which involve the guards of member and evenp).  The total
; time is a little more than the undeclared version.

; [Note: Tau is weak and often fails in its role of verifying guards.  We
; live with it.  Perhaps we should worry more about strengthening guard
; verification at apply$ time?  But whatever we do, recognize that this is
; unrelated to our handling of loop$. The failed conjectures above are just
; the ordinary guards of member and evenp.]

; After clearing the cache again, we define a function containing this same
; declared loop$ over a list of integers:

; (defun bar (lst)
;   (declare (xargs :guard (integer-listp lst)))
;   (loop$ for v of-type (and cons (satisfies integer-listp))
;          on lst
;          until (not (member (car v) (cdr v)))
;          when (evenp (car v))
;          collect (car v)))

; This definition is guard verified, but the proofs of the special guard
; conjectures are inductive.  There is one special conjecture for the collect$
; term, one for the when$ term, and one for the until$ term.  The reason there
; is one special conjecture for each loop$ scion rather than two is that
; Special Conjecture (b) is trivial for collect$, when$, and until$ because
; those scions impose no restrictions on the type of result delivered by apply$
; (i.e., they contain no fixers).  Here is conjecture (a) for the collect$
; term:

; Special Conjecture (a) for the collect$ term:
; (implies
;  (and (integer-listp lst)
;       (member-equal newv
;                     (when$ (lambda$ (v) (evenp (car v)))
;                            (until$ (lambda$ (v) (not (member (car v) (cdr v))))
;                                    (tails lst)))))
;  (and (consp newv)
;       (integer-listp newv)))

; This requires showing that if lst is a list of integers and newv is a member
; of the target of the collect$, then newv is a non-empty list of integers.
; (This is true because the target of the collect$ is the list of non-empty
; tails of lst, filtered by the until$ and when$ lambdas.)

; All the lambdas are added to the cache with status :GOOD and compiled.  But
; that is irrelevant because executing bar on a list of integers will not
; actually use apply$ or the lambdas but will run the raw Lisp loop instead.

; ACL2 !>(len (time$ (bar *tenk-tenk*)))

; 0.40 seconds realtime, 0.40 seconds runtime

; Of course, this time includes checking the guard that *tenk-tenk* is a list
; of integers.  That however takes an insignificant amount of time; if we run
; bar in raw Lisp (which doesn't actually check the guard but just plows into
; the compiled raw Lisp loop) the time is 0.38 seconds.

; One other fact of note: having verified the guards on the three lambdas and
; entered them into the cache, we can expect

; ACL2 !>(len (time$
;              (loop$ for v of-type (and cons (satisfies integer-listp))
;                     on *tenk-tenk*
;                     until (not (member (car v) (cdr v)))
;                     when (evenp (car v))
;                     collect (car v))))
; 1.69 seconds realtime, 1.69 seconds runtime

; to run faster because all the lambdas encountered by the top-level are :GOOD
; and compiled.  Recall that when guard verification was left to tau alone
; (which failed on two of the three) we saw a time of 2.48 seconds.

; -----------------------------------------------------------------
; Section 6:  About Member-Equal and the Mempos Correspondence

; The special loop$ guard conjectures for something like

; (loop$ x1 in t1 as x2 in t2 as x3 in t3 ...)

; introduce the hypothesis

; (member-equal newvar (loop$-as (list t1 t2 t3 ...)))

; Newvar represents the values of the iteration variables, x1, x2, x3, ...,
; at an arbitrary point in the scan down the targets.  It is easy to show
; that the member-equal above implies:

; (member-equal (car newvar) t1)   ; x1 is in t1
; (member-equal (cadr newvar) t2)  ; x2 is in t2
; (member-equal (caddr newvar) t3) ; x3 is in t3
; ...

; These facts might be needed to prove guards or type specs on the iteration
; variables from guards on their respective targets.  These implications are
; proved -- at least for loop$s having 1, 2, or 3 iteration variables -- in
; books/projects/apply/loop.lisp.

; But the user might need the stronger fact that the value of x1, x2, x3, ...,
; are in correspondence with the elements of t1, t2, t3, ...

; Books/projects/apply/mempos.lisp also includes a rewrite rule, named
; mempos-correspondence, that rewrites the (member-equal newvar (loop$-as (list
; t1 ... ))) into the salient facts the components of newvar.  However, it only
; handles the first three cases, for (list t1), (list t1 t2), and (list t1 t2
; t3), as well as the ``0 case'' where there is no loop$-as.  (Other cases can
; easily be proved.  Just look at the comment before mempos-correspondence in
; the above book.)  The mempos book also reproduces for mempos the various
; lemmas in the loop.lisp book that use member-equal.

; The ``salient facts,'' say for the case of (member-equal newvar (loop$-as
; (list t1 t2))), are

; (1) (< (mempos newvar (loop$-as (list t1 t2))) (len
;        (loop$-as (list t1 t2))))

; (2) (true-listp newvar)
; (3) (equal (len newvar) 2)

; (4) (<= (mempos newvar (loop$-as (list t1 t2))) (len t1))
; (5) (<= (mempos newvar (loop$-as (list t1 t2))) (len t2))

; (6) (equal (car newvar)
;            (nth (mempos newvar (loop$-as (list t1 t2))) t1))
; (7) (equal (cadr newvar)
;            (nth (mempos newvar (loop$-as (list t1 t2))) t2))

; To explain these facts, let m be the mempos expression,

; (mempos newvar (loop$-as (list t1 t2)))

; which is known to be a natp.

; Fact (1) is equivalent to the original member-equal and is here just to
; preserve that hypothesis -- albeit in a somewhat awkward form -- without
; sending the rewriter into a loop.  Facts (2) and (3) state the basic shape of
; newvar.  Facts (4) and (5) establish that m is a legal index into the two
; component targets, t1 and t2.  Finally, facts (6) and (7) show that the car
; and cadr of newvar are in fact corresponding elements of t1 and t2
; respectively.  In particular, they are both at position m in their respective
; component targets.

; -----------------------------------------------------------------
; Section 7:  An Example Plain Loop$, the :Guard Clause,
;            and Guard Conjectures

; For this example we define three renamings of integerp: int1p, int2p, and
; int3p.  Each has a guard of t and just tests integerp.  We do this so we can
; avoid ACL2's recognition of some trivial implications and see the interesting
; guards.

; We then define the squaring function but restrict it to int1ps via its guard:

; (defun$ isq (x)
;   (declare (xargs :guard (int1p x)))
;   (* x x))

; We will consider the guard verification of

; (defun sumsqints (lst)
;   (declare (xargs :guard (rational-listp lst)))
;   (loop$ for v of-type rational in lst
;          when (int2p v)
;          sum (isq v)))

; which maps over a list of rationals and sums the squares of the integers
; among them, except it uses int2p to recognize the integers.

; The translation of the loop$ above is

; (sum$ (lambda$ (v)
;                (declare (type rational v))
;                (isq v))
;       (when$ (lambda$ (v)
;                       (declare (type rational v))
;                       (int2p v))
;              lst))

; Note that both lambda$ expressions have the same guard, namely the type
; rational from the of-spec clause of the loop$.  That is all the loop$ knows
; about v.  But now consider the first of the two lambda$ expressions.  It has
; a guard of (rationalp x) but calls (isq v) which expects an integer (in the
; guise of an int1p).  The guard conjectures of this lambda$ are unprovable.

; We thus extend the loop$ notation (and change the raw Lisp version of the
; loop$ macro to strip out extended syntax) so we can write:

; (defun sumsqints (lst)
;   (declare (xargs :guard (rational-listp lst)))
;   (loop$ for v of-type rational in lst
;          when (int2p v)
;          sum :guard (int3p v)
;              (isq v)))

; We allow such :guard clauses immediately after the until, the when, and the
; loop$ operator symbols and before the corresponding expression.  The :guard
; term is inserted as an extra conjunct into the guard of the lambda$ generated
; for the corresponding expression.

; Now the translation of the loop$ above is as follows.  (Later in this Essay
; we will feel free to be cavalier about whether we lay down type declarations
; or :guard and :split-types xargs, taking care only to get the semantics
; right.)

; (sum$ (lambda$ (v)
;                (declare (type rational v)
;                         (xargs :guard (and (rationalp v) (int3p v))
;                                :split-types t))
;                (isq v))
;       (when$ (lambda$ (v)
;                       (declare (type rational v))
;                       (int2p v))
;              lst))

; The two lambda$'s guards are different.  The first lambda$ retains the (type
; rationalp v) declaration from the of-type spec but its :guard now includes
; (int3p v) as an extra conjunct from our added :guard clause in the body of
; the loop$.  By allowing the user to extend the guards generated from the CLTL
; type specs we allow the translation to produce verifiable lambda$
; expressions.  (One could imagine producing this extra guard automatically
; from the when clause, but as the when$ expression gets more complicated we
; believe automatic guard inference will be inadequate.)

; The guard conjectures produced for sumsqints are enumerated below and then
; explained.  Both (when$ fn lst) and (sum$ fn lst) have the normal guard on
; loop$ scions, namely (apply$-guard fn '(nil)) and (true-listp lst).  The
; apply$-guard conjunct is trivially true and not shown below.  (Of course some
; clauses below may be trivial with improved lemma configurations.  In recent
; runs of this same (defun sumsqints ...) clauses [1] and [2] below were
; trivial and not shown.)

; (implies (rational-listp lst)                                       ; [1]
;          (true-listp lst))

; (implies (rational-listp lst)                                       ; [2]
;          (true-listp (when$ (lambda$ (v) (int2p v))
;                             lst)))

; (implies (and (rationalp v) (int3p v))                              ; [3]
;          (int1p v)))

; (implies (and (rational-listp lst)                                  ; [4]
;               (member-equal newv lst))
;          (rationalp newv))

; (implies                                                            ; [5]
;  (and (rational-listp lst)
;       (member-equal newv
;                     (when$ (lambda$ (v) (int2p v))
;                            lst)))
;  (and (rationalp newv) (int3p newv)))

; (implies                                                            ; [6]
;  (and (rational-listp lst)
;       (member-equal newv
;                     (when$ (lambda$ (v) (int2p v))
;                            lst)))
;  (acl2-numberp (isq newv)))

; Explanations:

; In all cases, the (rational-listp lst) comes from the guard on sumsqints
; itself.

; [1] is just the true-listp conjunct of the guard of the when$ term: its
; second argument is a true-listp.

; [2] is the true-listp conjunct of the guard of sum$, namely the when$ in its
; second argument produces a true-listp.

; Together with the trivial apply$-guard conjuncts, [1] and [2] take care of
; the ``normal'' guards for the sum$ and when$.

; But guard verification also verifies the guards of all the lambda$s.

; [3] is the guard conjecture generated for the lambda$ in the sum$ term: if
; the guard on the lambda$ holds, namely (int3p v) and (rationalp v), then it
; is ok to call isq, namely (int1p v).  This is the obligation we couldn't have
; proved before adding the :guard (int3p v) clause.  The other lambda$ in the
; problem, inside the when$ term, generates no guard obligations because the
; guard of int2p is t.

; [4] is Special Conjecture (a) for the when$ term: if newv is in lst,
; it satisfies the guard of the lambda$ in the when$ term.

; [5] is Special Conjecture (a) for the sum$ term: if newv is in the output
; of the when$, it satisfies the guard of the lambda$ in the sum$.

; [6] is Special Conjecture (b) for the sum$ term: if newv is in the output of
; the when$, then the sum$'s lambda$ produces a number on newv.

; All of these must be proved in order to justify the use of the loop$ in
; sumsqints.

; Unfortunately, [5] and [6] as written cannot be proved because a warrant on
; int2p is needed to prove [5] and one on isq is needed for [6].  However,
; since we only need that the guards hold in the evaluation theory, we can
; assume the warrants.  Thus, as actually generated by the prover, guard
; conjectures [5] and [6] provide warrant hypotheses.

; We don't need warrants for int1p and int3p because they are just used in
; guards.

; -----------------------------------------------------------------
; Section 8:  Fancy Loop$s

; Fancy loop$s involve AS clauses, so that there are multiple iteration
; variables, and/or involve variables other than the iteration variables in the
; until, when, or lobody expressions.  For succinctness we refer to variables
; other than the iteration variables as ``global'' variables in this
; discussion.

; Here is an example of a fancy loop$.

; (loop$ for x in '(a b c) as i from 1 to 10
;   collect (list hdr x i));

; Here x and i are iteration variables and hdr is a global variable (which of
; course must be bound in the environment containing the loop$).

; For example:
; ACL2 !>(let ((hdr "Header"))
;          (loop$ for x in '(a b c) as i from 1 to 10
;                 collect (list hdr x i)))
; (("Header" A 1) ("Header" B 2) ("Header" C 3))

; Here is the same basic loop$ except we've added of-type expressions to help
; illuminate the translation and a :guard to restrict the type of hdr.

; (loop$ for x of-type symbol in lst1
;        as  i of-type integer from 1 to 10
;        collect :guard (stringp hdr) (list hdr x i))

; The translation is

; (collect$+
;  (lambda$ (loop$-gvars loop$-ivars)
;           (declare (xargs :guard (and (true-listp loop$-gvars)
;                                       (equal (len loop$-gvars) '1)
;                                       (true-listp loop$-ivars)
;                                       (equal (len loop$-ivars) '2)
;                                       (stringp (car loop$-gvars))
;                                       (symbolp (car loop$-ivars))
;                                       (integerp (car (cdr loop$-ivars)))
;                                       )))
;           (let ((hdr (car loop$-gvars))
;                 (x (car loop$-ivars))
;                 (i (car (cdr loop$-ivars))))
;             (declare (type symbol x)
;                      (type integer i))
;             (list hdr x i)))
;  (list hdr)
;  (loop$-as (list lst1 (from-to-by '1 '10 '1))))

; Collect$+ is the fancy version of collect$.  All fancy loop$ scions take
; three arguments, a function object of arity 2, a list of values for the
; ``globals'' used by the function object, and a target that combines the
; targets of all the iteration variables.

; The combined targets produced by the translation of a fancy loop$ is always
; built by calling the loop$-as function.  Loop$-as is a function that takes a
; tuple of individual targets and produces a list of lists of corresponding
; elements until the shortest individual target is exhausted.

; ACL2 !>(loop$-as (list '(a b c)
;                        '(1 2 3 4 5 6 7 8 9 10)))
; ((A 1) (B 2) (C 3))

; The function object of the fancy scion takes two arguments, always named
; loop$-gvars and loop$-ivars.  Loop$-gvars takes on the list of global values
; and loop$-ivars takes on the successive elements in the combined targets.

; The lambda$ object produced in the translation of a fancy loop$ then binds
; the iteration variables and global variables to the corresponding components
; of loop$-gvars and loop$-ivars.

; Treatment of the of-type specs and generation of the guard for the lambda$ is
; obvious from the example above.

; The definition of collect$+ is:

; (defun$ collect$+ (fn globals lst)
;   (declare (xargs :guard (and (apply$-guard fn '(nil nil))
;                               (true-listp globals)
;                               (true-list-listp lst))
;                   :verify-guards nil))
;   (mbe :logic
;        (if (endp lst)
;            nil
;            (cons (apply$ fn (list globals (car lst)))
;                  (collect$+ fn globals (cdr lst))))
;        :exec (collect$+-ac fn globals lst nil)))

; Note the guard: the function object is of arity 2, globals is a true-listp,
; and the target lst is a list of lists.

; Let us consider two ``pathological'' cases.  One is for loop$s that have
; multiple iteration variables and no globals, and the other is for loop$s that
; have a single iteration variable but one or more globals.  We use the fancy
; scions for both, rather than supporting the two pathological cases with
; special-purpose scions.  For an example of the second of these:

; (loop$ for x in lst collect (list hdr x))

; translates to a collect$+

; (collect$+
;  (lambda$ (loop$-gvars loop$-ivars)
;           (let ((hdr (car loop$-gvars))
;                 (x (car loop$-ivars)))
;             (list hdr x)))
;  (list hdr)
;  (loop$-as (list lst)))

; even though there is only one iteration variable.  Note the target over which
; x ranges is (needlessly) lifted with loop$-as to a list of singletons which
; is then dropped back down in the lambda$.  Similarly, a loop$ with multiple
; iteration variables and no globals translates to a collect$+ called with nil
; for the list of globals.

; As noted, we have fancy scions sum$+, always$+, thereis$+, collect$+, and
; append$+.  The first and last have fixers as do their plain counterparts.
; All but always$ and thereis$ have tail-recursive :exec counterparts for
; faster evaluation at the top-level.

; -----------------------------------------------------------------
; Section 9:  An Example Fancy Loop$ and Its Guard Conjectures

; (defun sum-pos-or-neg (signs lst)
;   (declare (xargs :guard (and (symbol-listp signs)
;                               (integer-listp lst))))
;   (loop$ for sign of-type symbol in signs                           ; [1]
;          as i of-type integer in lst
;          sum (* (if (eq sign '+) +1 -1) i)))

; The translation of the loop$ is

; (sum$+                                                              ; [2]
;  (lambda$ (loop$-gvars loop$-ivars)
;           (declare (xargs :guard (and (true-listp loop$-gvars)
;                                       (equal (len loop$-gvars) '0)
;                                       (true-listp loop$-ivars)
;                                       (equal (len loop$-ivars) '2)
;                                       (symbolp (car loop$-ivars))
;                                       (integerp (car (cdr loop$-ivars))))))
;           (let ((sign (car loop$-ivars))
;                 (i (car (cdr loop$-ivars))))
;             (declare (type symbol sign)
;                      (type integer i))
;             (* (if (eq sign '+) 1 -1) i)))
;  nil
;  (loop$-as (list signs lst)))

; Here are the non-trivial guard conjectures:

; (and
;  (implies (and (integer-listp lst)                                  ; [3]
;                (symbol-listp signs))
;           (true-list-listp (list signs lst)))
;  (implies (and (integer-listp lst)                                  ; [4]
;                (symbol-listp signs))
;           (true-list-listp (loop$-as (list signs lst))))
;  (implies (and (symbol-listp signs)                                 ; [5]
;                (integer-listp lst)
;                (member-equal newv (loop$-as (list signs lst))))
;           (and (true-listp newv)
;                (equal (len newv) 2)
;                (symbolp (car newv))
;                (integerp (cadr newv))))
;  (implies                                                           ; [6]
;   (and (symbol-listp signs)
;        (integer-listp lst)
;        (member-equal newv (loop$-as (list signs lst))))
;   (acl2-numberp
;    (apply$ (lambda$ (loop$-gvars loop$-ivars)
;                     (let ((sign (car loop$-ivars))
;                           (i (cadr loop$-ivars)))
;                       (* (if (eq sign '+) 1 -1) i)))
;            (list newv nil)))))

; Conjecture [3] establishes the guard of the AS term in [2]: the hypothesis of
; [3] is the guard of sum-pos-or-neg, [1], and the conclusion is the guard of
; (loop$-as (list signs lst)).

; Conjecture [4] establishes the only non-trivial part of the guard of sum$+ in
; [2], namely that the guard on sum-pos-or-neg implies that the combined target
; is a list of lists.

; Conjectures [5] and [6] are the Special Conjectures (a) and (b) for the
; sum$+.  They should be completely familiar by now.

; However, the proofs of [5] and [6] are a little more involved.  Consider [5].
; The hypothesis tells us newv is a member of (loop$-as (list signs lst)).  We
; know that signs is a list of symbols and lst is a list of integers.  We need
; to prove (among other things) that (car newv) is a symbol and (cadr newv) is
; an integer.

; This is done by specialization of this general lemma:

; (defthm general-always$-nth-loop$-as-tuple
;   (implies (and (always$ fnp (nth n tuple))
;                 (member-equal newv (loop$-as tuple))
;                 (natp n)
;                 (< n (len tuple)))
;            (apply$ fnp (list (nth n newv))))
;   :rule-classes nil)

; which says that if every element of the nth component of tuple has property
; fnp and newv is a member of (loop$-as tuple), then the nth component of newv
; has property fnp.

; Various versions of this lemma are made into rewrite rules in the loop$ book.
; E.g., if fnp is 'integer, tuple is (list lst0 lst1), and n is 1, we can prove

; (implies (and (integer-listp lst1)
;               (member-equal newv (loop$-as (list lst0 lst1))))
;          (integerp (cadr newv)))

; although we actually rearrange the corollary to rewrite the member-equal
; to false to address the free-variable problem.

; Member-equal distributes over the fancy when$+ and until$+ just as it does
; the plain scions.

; -----------------------------------------------------------------
; Section 10:  A Book for Helping with Loop$ Guard Proofs

; We have developed a community book books/projects/apply/loop.lisp, which
; supports the guard verification of loop$ translations.  It includes community
; book books/system/apply/loop-scions.lisp, which defines the plain and fancy
; loop$ scions, which are also defined (with the same bodies) in the ACL2
; sources since the semantics of loop$ (aka loop) are built into translate.
; The top-level community book books/projects/apply/top.lisp includes both
; books/projects/apply/loop.lisp and books/projects/apply/base.lisp.  The book
; top.lisp is the single book to include for supporting both reasoning about
; apply$ and reasoning about loop$, especially guard verification.

; -----------------------------------------------------------------
; Appendix A:  An Oversight Requiring Additional Work

; Recall that for every loop$ scion term that might have been generated by a
; loop$ statement we generate two guard conjectures that are not required by
; the guard of the scion.

; Special Conjecture (a): Every member of the target satisfies the guard of the
; function object.

; Special Conjecture (b): On every member of the target, the function object
; produces a result of the right type, e.g., an acl2-number for SUM and a
; true-listp for APPEND.

; Suppose the user writes this at the top-level ACL2 loop:

; (loop$ for i of-type integer from 1 to 1000                         ; [1]
;        sum (loop$ for j of-type integer from 1 to i sum j))

; This translates to

; (sum$                                                               ; [2]
;  '(lambda (i)
;           (declare (type integer i))
;           (sum$ '(lambda (j)
;                          (declare (type integer j))
;                          j)
;                 (from-to-by 1 i 1)))
;  (from-to-by 1 1000 1))

; where both LAMBDA objects are quoted, tame and well-formed.  ACL2 evaluates
; this call of sum$ and successively uses apply$-lambda to apply the outer
; LAMBDA object to the elements of (from-to-by 1 1000 1).  The first time
; apply$-lambda sees the outer LAMBDA object it generates its guard conjectures
; and tries to prove them.  The guard conjectures include (a) and (b).  For
; example, (a) for the inner sum$ call is

; Special Conjecture (a) generated for inner sum$:
; (implies (and (integerp i)
;               (member-equal newv (from-to-by '1 i '1)))
;          (integerp newv))

; which says we need to prove that newv is an integer since it is a member of
; (from-to-by 1 i 1).  This is an easy proof by the theorem prover.  But the
; tau system cannot prove it.

; As a result of the tau system's inability to establish this conjecture, the
; outer LAMBDA object enters the cache as :BAD.  Thus, it is interpreted -- a
; thousand times -- by the logical apply$-lambda.

; If these two calls of sum$ are replaced by an equivalent scion, say
; simple-sum, that does not provoke us to generate conjectures (a) and (b), the
; outer LAMBDA object is guard verified because tau can prove the simpler guard
; conjectures.  So the LAMBDA object enters the cache with status :GOOD, is
; compiled, and runs faster than interpreting the outer LAMBDA object in [2].

; Note that the user who wrote [1] followed our advice: he used loop$ whenever
; possible.  But we've just shown that had he written a simple-sum instead he
; would have gotten more speed.

; This raises a more basic problem: the handling of LAMBDA objects in raw code.
; LAMBDA objects, even those written in defuns, aren't compiled until they are
; applied -- even though they are guard verified at defun-time.  Furthermore,
; when they are compiled apply$-lambda does not compile the user-written code
; (which can be found in the ACL2_INVISIBLE::LAMBDA$-MARKER object) but
; compiles its translation!

; So right now we are doing the work to justify any loop$ inside any LAMBDA
; object but NEVER actually getting to run the corresponding loop because we
; compile the call of the loop$ scion.

; We regard this as a major todo item in the handling of loop$ and LAMBDA
; objects in general.

;;; Possible Future Work on Loop$: Perhaps the solution is to define sum$,
;;; etc., in raw Lisp as a pretty fancy macro that untranslates back into a
;;; loop?  This might be hard since we have no guarantee it actually came from
;;; a loop$.  We should think about about the questions ``when is a sum$
;;; actually a loop'' and ``when does a sum$ cause us to generate the Special
;;; Conjectures (a) and (b)?'' and then make sure they have the same answer.
;;; Also, we have to think about the other clauses (when and until) and the
;;; various target enumerators (from-to-by and loop$-as) so that we untranslate
;;; complicated nested scions into a single loop when possible.

;;; Possible Future Work on Loop$: From time to time we've asked ourselves: is
;;; there a way to allow a loop$ written at the top-level to execute as a loop?
;;; If apply$ could be used on program-mode functions, then perhaps the use of
;;; loop$ could just signal a special error (from translate11), suggesting the
;;; use of TOP-LEVEL.  Then we could avoid the more complicated ideas just
;;; below.

;;; Alternatively, and this would be a fundamental change, we could somehow
;;; arrange to execute certain instances of loop$ scions as loops, perhaps by
;;; ``untranslating'' them.  We need to have the translated form of the loop$
;;; to generate and check guards.  Anyway, it's something to think about if
;;; users start complaining that top-level loops are slow.

; -----------------------------------------------------------------
; Appendix B:  A Scion for Every Combination

; Recall in Sections 4 and 5 when we discussed ON, FROM/TO/BY, UNTIL, and WHEN
; we mentioned that enumerating/copying the target to select the relevant
; elements seemed potentially inefficient compared to doing that computation in
; a special-purpose scion for each legal loop$ combination.

; Before deciding to use the compositional approach, which makes proofs easier
; and maintains CLTL speed in guard verified loop$ in defuns, we experimented
; with top-level ACL2 evaluation of various special-purpose scions.  We actually
; defined and guard verified all 43 of the necessary scions.  (This list was
; written when the only supported loop$ operators were sum, always, collect, and
; append.)

; sum$-until$-when$-ac
; sum$-until$-ac
; sum$-when$-ac
; sum$-ac
; always$-until$
; ranches
; collect$-until$-when$-ac
; collect$-until$-ac
; collect$-when$-ac
; collect$-ac
; append$-until$-when$-ac
; append$-until$-ac
; append$-when$-ac
; append$-ac
; sum$-until$-when$-on-ac
; sum$-until$-on-ac
; sum$-when$-on-ac
; sum$-on-ac
; always$-until$-on
; always$-on
; collect$-until$-when$-on-ac
; collect$-until$-on-ac
; collect$-when$-on-ac
; collect$-on-ac
; append$-until$-when$-on-ac
; append$-until$-on-ac
; append$-when$-on-ac
; append$-on-ac
; sum$-until$-when$-from-to-by-ac
; sum$-until$-from-to-by-ac
; sum$-when$-from-to-by-ac
; sum$-from-to-by-ac
; always$-until$-from-to-by
; always$-from-to-by
; collect$-until$-when$-from-to-by-ac
; collect$-until$-from-to-by-ac
; collect$-when$-from-to-by-ac
; collect$-from-to-by-ac
; append$-until$-when$-from-to-by-ac
; append$-until$-from-to-by-ac
; append$-when$-from-to-by-ac
; append$-from-to-by-ac

; (Some combinations are illegal, like always$-when$. Furthermore, always$ is
; tail-recursive so ``-ac'' versions of it weren't needed.)

; Then we experimented in CCL with:

;  (loop$ for i from 1 to 1000000 by 1
;         until (equal i nil)
;         when (not (equal i -1))
;         sum (* (fix i)(fix i)))

; which sums the squares of the first 1 million positive integers -- note that
; the until and when clauses are no-ops but of course have to be tested.

; Three successive runs of the compositional semantics

;  (time$                                                             ; [1]
;   (sum$ `(LAMBDA (I)
;                  (RETURN-LAST 'PROGN
;                               '(LAMBDA$ (I) (* (FIX I) (FIX I)))
;                               (BINARY-* (FIX I) (FIX I))))
;         (when$ `(LAMBDA (I)
;                         (RETURN-LAST 'PROGN
;                                      '(LAMBDA$ (I) (NOT (EQUAL I -1)))
;                                      (NOT (EQUAL I '-1))))
;                (until$ `(LAMBDA (I)
;                                 (RETURN-LAST 'PROGN
;                                              '(LAMBDA$ (I) (EQUAL I NIL))
;                                              (EQUAL I 'NIL)))
;                        (from-to-by 1 1000000 1)))))

; allocated 128,004,080 bytes each time and took an average of
; (/ (+ 0.81 0.79 0.80) 3) = 0.80 seconds

; while three succesive runs of the special-purpose semantics

;  (time$                                                             ; [2]
;   (sum$-until$-when$-from-to-by-ac
;    `(LAMBDA (I)
;             (RETURN-LAST 'PROGN
;                          '(LAMBDA$ (I) (* (FIX I) (FIX I)))
;                          (BINARY-* (FIX I) (FIX I))))
;    `(LAMBDA (I)
;             (RETURN-LAST 'PROGN
;                          '(LAMBDA$ (I) (EQUAL I NIL))
;                          (EQUAL I 'NIL)))
;    `(LAMBDA (I)
;             (RETURN-LAST 'PROGN
;                          '(LAMBDA$ (I) (NOT (EQUAL I -1)))
;                          (NOT (EQUAL I '-1))))
;    1 1000000 1 0))

; only allocated 16,004,048 bytes each time but took an average of
; (/ (+ 0.95 0.96 0.95) 3) = 0.953 seconds.  So apparently it's faster -- at
; least in CCL -- to just do the consing than to be fancier.

; This experiment convinced us to keep it simple and just translate all legal
; loop$ statements into compositions of scions in the style of [1].  Of course,
; we define :exec versions of each scion to use tail recursion, etc.

(defun tag-loop$ (loop$-stmt meaning)

; Given a loop$ statement and its formal meaning as a loop$ scion term we
; produce a ``marked loop$'' which is semantically just the meaning term.

  `(RETURN-LAST 'PROGN
                ',loop$-stmt
                ,meaning))

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
    (defuns ignore ignorable irrelevant type optimize xargs)
    (lambda ignore ignorable type xargs)
    (lambda$ type xargs)))

; In the case of lambda-object we allow XARGS but we only handle the keywords
; :GUARD and :SPLIT-TYPES.  The other XARGS keywords and why they were omitted
; are (as of ACL2 Version_8.1):

; :GUARD-DEBUG - proof time (see below)
; :GUARD-HINTS - proof time
; :GUARD-SIMPLIFY - proof time
; :HINTS - recursion (see below)
; :MEASURE - recursion
; :MEASURE-DEBUG - recursion
; :MODE - all lambda objects have to be in :LOGIC mode because APPLY$ can't
;         run programs
; :NON-EXECUTABLE - irrelevant for lambda objects?
; :NORMALIZE - might this flag be useful someday?
; :OTF-FLG - proof time
; :RULER-EXTENDERS - recursion
; :STOBJS - lambda objects must be stobj-free
; :VERIFY-GUARDS - proof time
; :WELL-FOUNDED-RELATION - recursion

; Notes:

; Proof time: The keywords marked ``proof time'' are only relevant when we're
; doing guard verification.  Lambda objects can occur in four contexts: in
; DEFUN, DEFTHM, and VERIFY-GUARDS events, or in top-level evaluations.  Guard
; verification of DEFUN and DEFTHM events allow the provision of goal-specific
; hints, which can be used to guide the proofs of obligations stemming from
; lambda objects being guard verified.  Top-level evaluation is not intended to
; require heavy duty proofs: either we knock out the proof obligations and do
; fast evaluation or we don't and do slow evaluation, but we don't expect the
; user to interact with the proof attempt while trying to evaluate something at
; the top-level.  If the user wants fast evaluation there he or she ought to
; define a suitable function and verify its guards instead of using a lambda
; object.

; Recursion:  The keywords marked "recursion" are relevant only to recursive
; functions and lambda objects are never recursive.

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
  '((ignore "(IGNORE v1 ... vn), where the vi are introduced in the ~
             immediately superior lexical environment")
    (ignorable "(IGNORABLE v1 ... vn), where the vi are introduced in the ~
                immediately superior lexical environment")
    (ignore-and-ignorable "(IGNORE v1 ... vn) and (IGNORABLE v1 ... vn), ~
                           where the vi are introduced in the immediately ~
                           superior lexical environment")
    (irrelevant "(IRRELEVANT v1 ... vn)")
    (type "(TYPE type v1 ... vn), as described on pg 158 of CLTL")
    (xargs "(XARGS :key1 val1 ... :keyn valn), where each :keyi is a ~
            keyword (e.g., :GUARD or :SPLIT-TYPES)")))

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

; If both IGNORE and IGNORABLE are in syms we replace them by a single symbol,
; IGNORE-AND-IGNORABLE so we can simplify the explanation.

  (let ((syms (if (and (member-eq 'ignore syms)
                       (member-eq 'ignorable syms))
                  (cons 'ignore-and-ignorable
                        (remove1-eq 'ignore
                                    (remove1-eq 'ignorable
                                                syms)))
                  syms)))
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
                          unacceptable here.  ~#5~[~/ It is never necessary ~
                          to make IGNORE or IGNORABLE declarations in lambda$ ~
                          expressions because lambda$ automatically adds an ~
                          IGNORABLE declaration for all of the formals.~]  ~
                          See :DOC declare."
                         temp
                         (if (eq binder 'flet) 0 1)
                         binder
                         (tilde-*-conjunction-phrase temp
                                                     *dcl-explanation-alist*)
                         entry
                         (cond ((and (eq binder 'lambda$)
                                     (or (eq dcl 'ignore)
                                         (eq dcl 'ignorable)))
                                1)
                               (t 0))))
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

; Warning: If you weaken the test above to (>= (length entry) 2), then consider
; changing type-expressions-from-type-spec, whose definition has a comment
; saying that a "nil answer is unambiguous".

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

; Given a bunch of expanded dcls we find all the (TYPE x v1 ... vn) dcls among
; them and make a list of untranslated terms expressing the type restriction x
; for each vi.  (If we ever need to make a list of translated terms, replace
; the nil in the call of translate-declaration-to-guard-gen-var-lst below
; with t.)

  (cond ((null edcls) nil)
        ((eq (caar edcls) 'type)
         (append (translate-declaration-to-guard-var-lst
                  (cadr (car edcls))
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

; Warning: Keep this in sync with the handlng of 'return-last in oneify.

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

; Bound-vars and value-forms are lists of the same length.  Return the result
; of extending the list acc by each member of bound-vars for which the
; corresponding element of value-forms (i.e., in the same position) is a call
; of hide.  Since translate11 inserts a call of hide for each bound var, this
; function returns a list that contains every variable declared ignored in the
; original let form binding bound-vars to value-forms (or the corresponding
; untranslations of the terms in value-forms).

; We might not need this function if users never write lambda applications.
; But consider the following example.

; ((lambda (a) t) (hide x))

; Translate11 first converts this to

; (let ((a (hide x))) t)

; and that, in turn, is passed to translate11-let.  Notice that a is not
; declared ignored; however, it is treated as ignored because of
; augment-ignore-vars, where a trace shows that (augment-ignore-vars (a) ((hide
; x)) nil) returns (A).  This functionality might not seem important, but on
; 6/24/2019 we tried eliminating augment-ignore-vars and found that community
; book
; books/workshops/2009/verbeek-schmaltz/verbeek/instantiations/scheduling/circuit-switching-global/circuit.lisp
; failed to certify because of a form (definstance genericscheduling
; check-compliance-ct-scheduling ...), which generates a lambda using hide
; forms in order to deal with ignored variables.  So apparently people have
; relied on this use of hide!

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
    brr-evisc-tuple
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

(defun stobjs-in-out1 (stobjs-in args wrld alist new-stobjs-in-rev)

; See stobjs-in-out for additional background.

; We are translating the application of a function to args.  We assume that
; stobjs-in is a true-list consisting of nil and/or stobjs and that args is a
; true-list of the same length as stobjs-in.  (Moreover, at the top level,
; alist and new-stobjs-in-rev are nil.)  We return (mv failp alist
; new-stobjs-in).  Ideally, new-stobjs-in is a list of known stobjs without
; duplicates, of the same length as stobjs-in, such that for each natp i <
; (length stobjs-in), (nth i stobjs-in) and (nth i new-stobjs-in) are either
; both nil or are congruent stobjs (possibly equal).  In that case, alist is a
; list, in any order, consisting of pairs (s1 . s2) in (pairlis$ stobjs-in
; new-stobjs-in) such that s1 and s2 are not equal.

; The goal is thus to return a new stobjs-in, together with a corresponding
; mapping from old stobjs-in to new stobjs-in, such that we can legally view
; the (implicit) function as having the new stobjs-in.  We adjust the
; stobjs-out correspondingly in stobjs-in-out.

; Otherwise, we are in a failure case (mv failp nil nil) where failp is
; non-nil.  (It is fine if failp is t, but we are free to return any non-nil
; value, which might provide information that is helpful for debugging.)  That
; case happens, in particular, when there are duplicate stobjs: for example
; consider the case that stobjs-in is (st1 st2) where st1 and st2 are congruent
; stobjs and args is (st1 st1).  There is no reasonable way to return a
; suitable new-stobjs-in.

; The failure case can also happen when we get "stuck".  For example, again
; suppose that st1 and st2 are congruent stobjs; now consider the case that
; stobjs-in is (st1 st2) and args is (st2 nil).  We could return new-stobjs-in
; as (st2 st1), but then the error message from translate11-call will complain
; that nil was returned where st1 was expected.  But do we really expect st1 in
; the second argument?  Suppose that st3 is also congruent to st1 and there is
; a typo, so that args is (st2 st3a).  Surely what was "expected" was st3, not
; st1.  In this case, and in any situation where we aren't confident that the
; error message involving new-stobjs-in is clear, we return the faiure case.

; That said, we prefer to avoid the failure case when that won't make error
; messages more confusing.  See for example (5) in the comments in
; translate11-call.

  (cond ((endp stobjs-in)
         (mv nil alist (reverse new-stobjs-in-rev)))
        ((null (car stobjs-in))
         (stobjs-in-out1 (cdr stobjs-in) (cdr args) wrld alist
                         (cons nil new-stobjs-in-rev)))
        (t
         (let ((s ; Since (car stobjs-in) is a stobj, s is also a stobj.
                (if (or (eq (car stobjs-in) (car args)) ; optimization

; The following implies that (car args) is a stobj in wrld, because (car
; stobjs-in) is a stobj in wrld.

                        (and (car args) ; perhaps not necessary
                             (symbolp (car args))
                             (congruent-stobjsp (car stobjs-in)
                                                (car args)
                                                wrld)))
                    (car args)
                  (car stobjs-in))))
           (cond
            ((member-eq s new-stobjs-in-rev)
             (mv s nil nil))
            (t
             (stobjs-in-out1 (cdr stobjs-in) (cdr args) wrld
                             (if (eq (car stobjs-in) s)
                                 alist
                               (acons (car stobjs-in) s alist))
                             (cons s new-stobjs-in-rev))))))))

(defun stobjs-in-matchp (stobjs-in args)
  (cond ((endp stobjs-in) (null args))
        ((endp args) nil)
        ((or (null (car stobjs-in))
             (eq (car stobjs-in) (car args)))
         (stobjs-in-matchp (cdr stobjs-in) (cdr args)))
        (t nil)))

(defun stobjs-in-out (fn args stobjs-out known-stobjs wrld)

; We are translating an application of fn to args, where fn has the indicated
; stobjs-out and args has the same length as fn, ideally satisfying the stobjs
; discipline of passing a stobj name to a stobjs-in position (though we don't
; assume that here); see the comment about this discipline in translate11-call.

; Our goal is to create modified stobjs-in and stobjs-out that correspond to
; the call of fn on args.  If we cannot compute "improved" such stobjs-in and
; stobjs-out using congruence of stobjs, then we return the stobjs-in and
; stobjs-out unmodified.

; We return an alist that represents a one-to-one map from the stobjs-in of fn,
; which is computed from fn if fn is a lambda.  This alist associates each
; stobj st in its domain with a corresponding congruent stobj, possibly equal
; to st (as equal stobjs are congruent).  We return (mv alist new-stobjs-in
; new-stobjs-out), where new-stobjs-in and new-stobjs-out result from stobjs-in
; and stobjs-out (respectively) by applying alist to each of them, except that
; stobjs-out is not modified if it is a symbol rather than a list. (In the case
; of a symbol, translate11 is trying to determine a stobjs-out for that
; symbol.)  Note that we do not put equal pairs (s . s) into alist; hence,
; alist represents the identity function if and only if it is nil.

  (let ((stobjs-in (cond ((consp fn)
                          (compute-stobj-flags (lambda-formals fn)
                                               known-stobjs
                                               wrld))
                         (t (stobjs-in fn wrld)))))
    (cond
     ((stobjs-in-matchp stobjs-in args)
      (mv nil stobjs-in stobjs-out))
     (t
      (mv-let
        (failp alist new-stobjs-in)
        (stobjs-in-out1 stobjs-in args wrld nil nil)
        (cond
         (failp (mv nil stobjs-in stobjs-out))
         (t (mv alist
                new-stobjs-in
                (cond ((symbolp stobjs-out)
                       stobjs-out)
                      ((null alist) ; optimization
                       stobjs-out)
                      (t (apply-symbol-alist alist stobjs-out nil)))))))))))

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
; - bound-vars is a list of symbols;
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
             list of legal variable names without duplicates."
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

(defun split-values-by-keys (keys alist lst1 lst2)

; This function partitions the values of alist into (mv lst1' lst2'), where
; lst1' accumulates into lst1 the values associated with keys and lst2'
; accumulates into lst2 the rest.

  (declare (xargs :guard (and (true-listp keys)
                              (symbol-alistp alist))))
  (cond ((endp alist) (mv lst1 lst2))
        ((member-eq (caar alist) keys)
         (split-values-by-keys keys (cdr alist)
                               (cons (cdar alist) lst1)
                               lst2))
        (t
         (split-values-by-keys keys (cdr alist)
                               lst1
                               (cons (cdar alist) lst2)))))

(defun no-duplicatesp-checks-for-stobj-let-actuals/alist (alist producer-vars)
  (cond
   ((endp alist) nil)
   (t
    (let ((pairs (cdar alist)))
      (cond
       ((or (null (cdr pairs))
            (let ((indices (strip-cdrs pairs)))
              (and (nat-listp indices)
                   (no-duplicatesp indices))))
        (no-duplicatesp-checks-for-stobj-let-actuals/alist (cdr alist)
                                                           producer-vars))
       (t
        (mv-let (producer-indices other-indices)
          (split-values-by-keys producer-vars pairs nil nil)
          (cond
           ((null producer-indices)
            (no-duplicatesp-checks-for-stobj-let-actuals/alist (cdr alist)
                                                               producer-vars))
           (t
            (cons `(with-guard-checking
                    t

; The use below of with-guard-checking guarantees that the guard will be
; checked by running chk-no-stobj-array-index-aliasing inside *1* code for
; stobj-let.  We are relying on invariant-risk handling to ensure that the *1*
; function is executed when there are updates, and hence those no-duplicatesp
; checks will be performed.  Invariant-risk plays its usual role for
; :program-mode wrappers, hence causes the no-duplicatesp checks to be
; enforced.  Note that the no-duplicates checks are avoided when there are only
; accesses but no updates.

; We considered a simpler approach: (or (no-duplicatesp-eql-exec lst) (er hard
; ...)).  However, the error didn't occur during proofs, and as a result the
; theorem true-and-false-is-contradictory-2 in community book
; books/system/tests/nested-stobj-tests.lisp succeeded with that change.  The
; failure was restored by changing (er hard ...) to (er hard! ...), but at the
; cost of seeing lots of error messages during the proof.  Rather than think
; all that through, we reverted to the approach below, which relies on guard
; checking (which fails silently during proofs) to enforce the lack of
; duplicate array indices; see chk-no-stobj-array-index-aliasing.  Note that
; these checks are skipped in raw Lisp, since raw-Lisp stobj-let does not
; include them.  But as noted above, we can rely on invariant-risk.

                    (chk-no-stobj-array-index-aliasing
                     (list ,@producer-indices)
                     (list ,@other-indices)))
                  (no-duplicatesp-checks-for-stobj-let-actuals/alist
                   (cdr alist) producer-vars)))))))))))

(defun concrete-accessor (accessor tuples-lst)

; Accessor is a stobj accessor for a stobj st.  Tuples-lst is nil if st is a
; concrete stobj; otherwise its car is the :absstobj-tuples field of the
; 'absstobj-info property of st and its cdr is (recursively) a list of such
; tuples starting with the underlying stobj for st.

  (cond ((endp tuples-lst) accessor)
        (t (let* ((tuples (car tuples-lst))
                  (accessor$c (caddr (assoc-eq accessor tuples))))
             (assert$ accessor$c
                      (concrete-accessor accessor$c (cdr tuples-lst)))))))

(defun no-duplicatesp-checks-for-stobj-let-actuals-1
    (bound-vars exprs producer-vars tuples-lst alist)

; It is useful to introduce the notion that st$c "ultimately underlies" a stobj
; st: st$c is just st if st is a concrete stobj, and otherwise (recursively)
; st$c is the concrete stobj that ultimately underlies the foundational stobj
; for st.

; Function chk-stobj-let/accessors1 checks for explicit duplication of
; accessors in the bindings of a stobj-let form, F.  The present function, by
; contrast, deals with duplicate indices for accessing array fields of the
; stobj that ultimately underlies st.  We return either nil or a term, chk,
; that serves as such a check for duplicate indices: if chk is not nil then F
; is treated as (prog2$ chk F) by translate and oneify.

; Alist accumulates an association of array field accessor names with
; corresponding lists of index terms.  Those accessor names are for the
; concrete stobj that ultimately underlies the stobj st.

  (cond
   ((endp exprs)
    (let ((lst (no-duplicatesp-checks-for-stobj-let-actuals/alist
                alist producer-vars)))
      (if (cdr lst)
          (cons 'progn$ lst)
        (car lst))))
   (t (no-duplicatesp-checks-for-stobj-let-actuals-1
       (cdr bound-vars)
       (cdr exprs)
       producer-vars
       tuples-lst
       (let ((bound-var (car bound-vars))
             (expr (car exprs)))
         (cond
          ((eql (length expr) 3) ; array case, (fldi index st)
           (let* ((name (car expr))
                  (index (cadr expr))
                  (index (if (consp index)
                             (assert$ (and (eq (car index) 'quote)
                                           (natp (cadr index)))
                                      (cadr index))
                           index))
                  (fld$c (concrete-accessor name tuples-lst))
                  (entry (assoc-eq fld$c alist)))
             (put-assoc-eq fld$c
                           (cons (cons bound-var index) (cdr entry))
                           alist)))
          (t alist)))))))

(defrec absstobj-info

; For a given abstract stobj st, the 'absstobj-info property is one of these
; records, where st$c is the corresponding foundational stobj and
; absstobj-tuples is a list of tuples (name logic exec . updater), where
; updater is non-nil only when name is a child stobj accessor (hence exec is a
; child stobj accessofr for st$c).  The first tuple is for the recognizer, the
; second is for the creator, and the rest are for the exports, in order of
; the exports in the original defabsstobj event.

  (st$c . absstobj-tuples)
  t)

(defun absstobj-tuples-lst (st wrld)
  (let ((abs-info (getpropc st 'absstobj-info nil wrld)))
    (cond ((null abs-info) nil)
          (t (cons (access absstobj-info abs-info :absstobj-tuples)
                   (absstobj-tuples-lst (access absstobj-info abs-info :st$c)
                                        wrld))))))

(defun no-duplicatesp-checks-for-stobj-let-actuals
    (bound-vars exprs producer-vars st wrld)
  (let ((tuples-lst (absstobj-tuples-lst st wrld)))
    (no-duplicatesp-checks-for-stobj-let-actuals-1
     bound-vars exprs producer-vars tuples-lst nil)))

(defun stobj-let-fn (x)

; Warning: Keep this in sync with stobj-let-fn-raw and with the handling of
; stobj-let in both translate11 and oneify.

; Warning: Do not merge stobj-let-fn and stobj-let-fn-raw into a single
; function.  We call stobj-let-fn in oneify, so we need that logical code even
; in raw Lisp.

; Warning: This function does not do all necessary checks.  Among the checks
; missing here but performed by translate11 (via chk-stobj-let) are duplicate
; accessor expressions in the bindings, which could lead to aliasing errors.
; The anti-aliasing check for duplicate array indices, which laid down in the
; translation of a stobj-let expression after the chk-stobj-let check passes,
; is also missing in this function.  Many of the checks need the world, which
; is not available in stobj-let-fn; in particular, aliasing need not be
; lexical, as two different accessors can lead via a chain of foundational
; stobjs (available in the world) to the same access of a single concrete
; stobj.

; Our use in oneify requires the actuals and stobj, so we return those as well
; in the non-error case.

; See the Essay on Nested Stobjs.

  (mv-let
    (msg bound-vars actuals stobj producer-vars producer updaters
         corresp-accessor-fns consumer)
    (parse-stobj-let x)
    (declare (ignore corresp-accessor-fns))
    (cond
     (msg (mv (er hard 'stobj-let "~@0" msg) nil nil nil nil))
     (t (let* ((guarded-producer
                `(check-vars-not-free (,stobj) ,producer))
               (guarded-consumer
                `(check-vars-not-free ,bound-vars ,consumer))
               (updated-guarded-consumer
                `(let* ,(pairlis-x1 stobj (pairlis$ updaters nil))
                   ,guarded-consumer))
               (form
                `(let* (,@(pairlis$ bound-vars (pairlis$ actuals nil)))
                   (declare (ignorable ,@bound-vars))
                   ,(cond
                     ((cdr producer-vars)
                      `(mv-let ,producer-vars
                         ,guarded-producer
                         ,updated-guarded-consumer))
                     (t `(let ((,(car producer-vars) ,guarded-producer))
                           ,updated-guarded-consumer))))))
          (mv form bound-vars actuals producer-vars stobj))))))

#-acl2-loop-only
(defun non-memoizable-stobj-raw (name)
  (assert name)
  (let ((d (get (the-live-var name) 'redundant-raw-lisp-discriminator)))
    (assert (member (car d) '(defstobj defabsstobj)
                    :test #'eq))
    (assert (cdr d))
    (access defstobj-redundant-raw-lisp-discriminator-value
            (cdr d)
            :non-memoizable)))

#-acl2-loop-only
(defun stobj-let-fn-raw (x)

; Warning: Keep this in sync with stobj-let-fn and with the
; handling of stobj-let in translate11.

; Warning: Do not merge stobj-let-fn and stobj-let-fn-raw into a single
; function.  We call stobj-let-fn in oneify, so we need that logical code even
; in raw Lisp.

; See the Essay on Nested Stobjs.

  (mv-let
    (msg bound-vars actuals stobj producer-vars producer updaters
         corresp-accessor-fns consumer)
    (parse-stobj-let x)
    (declare (ignore corresp-accessor-fns))
    (cond (msg (er hard 'stobj-let "~@0" msg))
          (t
           (let* ((updated-consumer
                   `(let* ,(pairlis-x1 stobj (pairlis$ updaters nil))
                      ,consumer))
                  #+hons
                  (flush-form

; Here is a proof of nil in ACL2(h)  6.4 that exploits an unfortunate
; "interaction of stobj-let and memoize", discussed in :doc note-6-5.  This
; example led us to add the call of memoize-flush in flush-form, below.  A
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

                   (and (intersection-eq producer-vars bound-vars)
                        (not (non-memoizable-stobj-raw stobj))
                        `(memoize-flush ,(congruent-stobj-rep-raw
                                          stobj))))
                  (form0
                   `(let* ,(pairlis$ bound-vars (pairlis$ actuals nil))
                      (declare (ignorable ,@bound-vars))
                      ,(cond
                        ((cdr producer-vars)
                         `(mv-let ,producer-vars
                            ,producer
                            ,(cond
                              #+hons
                              (flush-form
                               `(progn ,flush-form ,updated-consumer))
                              (t updated-consumer))))
                        (t `(let ((,(car producer-vars) ,producer))
                              #+hons
                              ,@(and flush-form (list flush-form))
                              ,updated-consumer))))))
             (if (and (eq (car (get (the-live-var stobj)
                                    'redundant-raw-lisp-discriminator))
                          'defabsstobj)

; When an abstract stobj's update is incomplete, the resulting state should be
; considered an illegal state (see the Essay on Illegal-states) since the
; abstract stobj recognizer might not hold for the corresponding live stobj.
; However, if we know that the stobj has not been updated -- because none of
; the producer variables represents a child stobj (by virtue of being in
; bound-vars) -- then we do not need to mess with illegal states here.

                      (intersectp-eq bound-vars producer-vars))
                 (with-inside-absstobj-update (gensym) (gensym) x form0)
               form0))))))

(defun stobj-field-accessor-p (fn stobj wrld)

; Return non-nil when fn is a child accessor (not updater) for the given stobj.
; If stobj is an abstract stobj, this means that fn is an export with an
; :updater field.  For more background see the Essay on the Correctness of
; Abstract Stobjs.

  (and

; We believe that the first check is subsumed by the others, but we leave it
; here for the sake of robustness.

   (eq (getpropc fn 'stobj-function nil wrld)
       stobj)

; The 'stobj property of stobj is (*the-live-var* recognizer creator ...).

   (member-eq fn (cdddr (getpropc stobj 'stobj nil wrld)))

; The remaining tests are different for concrete and abstract stobjs.

   (let ((abs-info (getpropc stobj 'absstobj-info nil wrld)))
     (cond
      (abs-info

; Stobj is an abstract stobj.  The cdddr of the tuple for fn is the
; corresponding updater, if any -- for an abstract stobj, having an updater is
; equivalent to fn being a field accessor, as required for accessor calls in
; stobj-let bindings.

       (cdddr (assoc-eq fn (access absstobj-info abs-info :absstobj-tuples))))
      (t (and

; At this point, fn could still be a constant.

          (function-symbolp fn wrld)

; Now distinguish accessors from updaters.

          (not (eq (car (stobjs-out fn wrld))
                   stobj))))))))

(defun chk-stobj-let/bindings (stobj acc-stobj first-acc bound-vars actuals
                                     wrld)

; The bound-vars and actuals have been returned by parse-stobj-let, so we know
; that some basic syntactic requirements have been met and that the two lists
; have the same length.  See also chk-stobj-let.

; Stobj is the variable being accessed/updated.  Acc-stobj is the stobj
; associated with the first accessor; we have already checked in chk-stobj-let
; that this is congruent to stobj.  First-acc is the first accessor, which is
; just used in the error message when another accessor's stobj doesn't match.

; We do an additional check in chk-stobj-let/accessors to ensure, in the
; abstract stobj case, that two different accessors aren't aliases for the same
; underlying concrete stobj accessor.  See chk-stobj-let/accessors

  (cond ((endp bound-vars) nil)
        (t (let* ((var (car bound-vars))
                  (actual (car actuals))
                  (accessor (car actual))
                  (st (car (last actual))))
             (assert$
              (eq st stobj) ; guaranteed by parse-stobj-let
              (cond ((not (stobj-field-accessor-p accessor acc-stobj wrld))
                     (msg "The name ~x0 is not the name of a field accessor ~
                           for the stobj ~x1.~@2~@3"
                          accessor acc-stobj
                          (if (eq acc-stobj stobj)
                              ""
                            (msg "  (The first accessor used in a stobj-let, ~
                                  in this case ~x0, determines the stobj with ~
                                  which all other accessors must be ~
                                  associated, namely ~x1.)"
                                 first-acc acc-stobj))
                          (let* ((abs-info (getpropc st 'absstobj-info nil
                                                     wrld))
                                 (tuples (and abs-info
                                              (access absstobj-info abs-info
                                                      :absstobj-tuples))))
                            (cond
                             ((assoc-eq accessor tuples)
                              (msg "  Note that even though ~x0 is an ~
                                      abstract stobj primitive (for ~x1), it ~
                                      is not an accessor because it is not ~
                                      associated with an :UPDATER."
                                   accessor st))
                             (t "")))))
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
                           duplicated expressions, but in the following form, ~
                           more than one variable is bound to the expression, ~
                           ~x0."
                          actual))
                    (t (chk-stobj-let/bindings stobj acc-stobj first-acc
                                               (cdr bound-vars)
                                               (cdr actuals)
                                               wrld))))))))

(defun chk-stobj-updaters1 (accessors updaters lst source)

; Lst is the cdddr of the 'stobj property of a stobj in an implicit world,
; accessors is a list of field accessors for that stobj, and updaters is a list
; of the same length as accessors.  We check that for each i < (length
; accessors), the ith updater is indeed the stobj field updater corresponding
; to the ith accessor.  Recall that the 'stobj property is a list of the form
; (*the-live-var* recognizer creator ...), and that each field updater
; immediately follows the corresponding field accessor in that list.  Source is
; as in chk-stobj-updaters.

  (cond ((endp updaters) nil)
        (t (let* ((updater (car updaters))
                  (accessor (car accessors))
                  (accessor-tail (member-eq (car accessors) lst))
                  (actual-updater (cadr accessor-tail)))
             (assert$

; This assertion should be true because of the check done by a call of
; stobj-field-accessor-p in chk-stobj-let/bindings.

              accessor-tail
              (cond
               ((eq updater actual-updater)
                (chk-stobj-updaters1 (cdr accessors) (cdr updaters)
                                     lst source))
               (t (msg "The ~@0 have specified that the stobj ~
                        field updater corresponding to accessor ~x1 is ~x2, ~
                        but the actual corresponding updater is ~x3."
                       source accessor updater actual-updater))))))))

(defun chk-stobj-updaters (accessors updaters stobj wrld source)

; Source is a string or message such as "stobj-let bindings" or "defabsstobj
; exports", indicating (as a plural noun phrase) what has specified that the
; given updater functions are supposed to correspond to the given accessor
; functions.

  (chk-stobj-updaters1
   accessors
   updaters
   (cdddr ; pop live-var, recognizer, and creator
    (getpropc stobj 'stobj nil wrld))
   source))

(defun chk-stobj-let/updaters (updater-calls corresp-accessor-fns stobj wrld)
  (chk-stobj-updaters corresp-accessor-fns
                      (strip-cars updater-calls)
                      stobj wrld "stobj-let bindings"))

(defun alist-to-doublets (alist)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) nil)
        (t (cons (list (caar alist) (cdar alist))
                 (alist-to-doublets (cdr alist))))))

(defun chk-stobj-let/accessors2 (alist producer-vars wrld)

; Alist contains entries (fn$c (var1 . expr1) (var2 . expr2) ... (varn
; . exprn)), where each expri is a call of a child stobj accessor that
; ultimately invokes the concrete stobj field accessor, fn$c.  If n > 1 and
; some vari is in producer-vars, then we return a message that reports aliasing
; involving the field accessed by fn$c that is not completely read-only.
; Otherwise we return nil.

  (cond
   ((endp alist) nil)
   (t (let* ((msg1 (chk-stobj-let/accessors2 (cdr alist) producer-vars wrld))
             (key (caar alist))
             (indexp (consp key))
             (fn$c (if indexp
                       (car key)
                     key))
             (pairs (and (cdr (cdar alist)) ; not just one pair
                         (reverse (cdar alist))))
             (bad-vars (strip-cars (restrict-alist producer-vars pairs)))
             (msg2 (and bad-vars
                        (msg "The stobj-let bindings ~x0 ultimately access ~
                              the same field ~x1 of concrete stobj ~x2~@3.  ~
                              Since variable~#4~[ ~&4 is~/s ~&4 are~] to be ~
                              updated (i.e., ~#4~[it is~/they are~] among the ~
                              stobj-let form's producer variables), this ~
                              aliasing is illegal."
                             (alist-to-doublets pairs)
                             fn$c
                             (getpropc fn$c 'stobj-function nil wrld)
                             (if indexp
                                 " (with identical array indices)"
                               "")
                             bad-vars))))
        (cond
         ((null msg1) msg2)
         ((null msg2) msg1)
         (t (msg "~@0~|Also: ~@1" msg2 msg1)))))))

(defun chk-stobj-let/accessors1 (bound-vars actuals producer-vars
                                            tuples tuples-lst wrld alist)

; Tuples is the :absstobj-tuples field of an absstobj-info record for an
; abstract stobj st, actuals is the values in the bindings of a stobj-let form,
; and tuples-lst is the list of :absstobj-tuples for the chain of foundational
; stobjs starting with the foundational stobj for st.  We look for aliasing
; caused by ultimately invoking the same concrete stobj export).  However we do
; not handle aliasing caused by non-identiccal array indices; for that, see
; no-duplicatesp-checks-for-stobj-let-actuals-1, which generates guard
; obligations rather than causing an error like the present function (but more
; precisely, the present function can return a msg, which is passed up the call
; chain until causing an error in defabsstobj-fn1).

; We assume that we are here because of a chk-stobj-let call that invoked
; chk-stobj-let/accessors after a corresponding check already done with
; chk-stobj-let/bindings (see comment on assert$ below).

; Note that duplicated actuals are already checked in chk-stobj-let/bindings;
; here we are checking that two (distinct) actuals do not represent the same
; update for the same concrete stobj.  We could actually avoid that previous
; check in the case of abstract stobjs because the check is done here, but we
; need the other check anyhow for concrete stobjs.  The price seems small for
; the duplicated effort here, so we aren't concerned about that.

  (cond
   ((endp bound-vars) ; equivalently, (endp actuals)
    (chk-stobj-let/accessors2 alist producer-vars wrld))
   (t (let* ((var (car bound-vars))
             (actual (car actuals))
             (fn (car actual))
             (tuple (assoc-eq fn tuples))
             (fn$c0 (caddr tuple))
             (fn$c (concrete-accessor fn$c0 tuples-lst))
             (index (and (= (length actual) 3)
                         (cadr actual)))
             (key (if index
                      (cons fn$c index) ; array case
                    fn$c))
             (new (cons var actual))
             (old (cdr (assoc-equal key alist))))
        (chk-stobj-let/accessors1 (cdr bound-vars) (cdr actuals) producer-vars
                                  tuples tuples-lst wrld
                                  (put-assoc-equal key
                                                   (cons new old)
                                                   alist))))))

(defun collect-some-triples-with-non-nil-cdddrs (keys alist)

; Collect each triple from alist that has a non-nil cdddr and whose car belongs
; to keys.

  (cond ((endp alist) nil)
        ((and (cdddr (car alist))
              (member-eq (caar alist) keys))
         (cons (car alist)
               (collect-some-triples-with-non-nil-cdddrs keys (cdr alist))))
        (t (collect-some-triples-with-non-nil-cdddrs keys (cdr alist)))))

(defun chk-stobj-let/accessors (st bound-vars actuals producer-vars wrld)

; This function adds checks on the given actuals of the bindings of a stobj-let
; form for stobj st, beyond those in chk-stobj-let/bindings.  It returns a msgp
; to print upon failure, else nil.  This function is only relevant for abstract
; stobjs: it always returns nil if st is a concrete stobj.

; We ensure, in the abstract stobj case, that two different accessors aren't
; aliases for the same underlying concrete stobj accessor.  This notion of
; "underlying" refers to following the chain of foundational stobjs until a
; concrete stobj is reached.  (This is the notion of "ultimately underlies"
; introduced in no-duplicatesp-checks-for-stobj-let-actuals-1.)

; Note that this function checks (by way of chk-stobj-let/accessors1) for
; aliasing in the form of explicit duplication of accessors (modulo the
; corresponding underlying concrete stobj accessor) in the bindings of a
; stobj-let form.  See no-duplicatesp-checks-for-stobj-let-actuals-1 for how we
; deal with duplicate array indices by generating a runtime check that, in
; turn, generates a suitable guard obligation.

  (let ((abs-info (getpropc st 'absstobj-info nil wrld)))
    (and abs-info ; st is an abstract stobj
         (let* ((tuples (access absstobj-info abs-info :absstobj-tuples))
                (st$c (access absstobj-info abs-info :st$c))
                (tuples-lst (absstobj-tuples-lst st$c wrld)))
           (chk-stobj-let/accessors1 bound-vars actuals producer-vars
                                     tuples tuples-lst wrld nil)))))

(defun chk-stobj-let (bound-vars actuals stobj producer-vars updaters
                                 corresp-accessor-fns known-stobjs wrld)

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
         ((chk-stobj-let/accessors acc-stobj bound-vars actuals producer-vars
                                   wrld))
         (t nil))))))

(defun all-nils-or-x (x lst)
  (declare (xargs :guard (and (symbolp x)
                              (true-listp lst))))
  (cond ((endp lst) t)
        ((or (eq (car lst) x)
             (null (car lst)))
         (all-nils-or-x x (cdr lst)))
        (t nil)))

(defun absstobj-field-fn-of-stobj-type-p (fn tuples)

; Fn is an exported function for some abstract stobj st, and at the top level,,
; exports is the list of exported functions for st (including fn) and tuples is
; the cddr of the :absstobj-tuples field of the absstobj-info property of st.
; Hence tuples is a list of elements (name logic exec . updater) corresponding
; to the exported functions; see absstobj-info.  We return t when fn is a child
; stobj accessor or updater, else nil.  We do this by cdring through tuples,
; looking for the tuple corresponding to fn, which should be among the exports.
; We return t if we find that fn is a stobj field accessor (as evidenced by
; presence of a non-nil updater component of the corresponding tuple) or a
; stobj field updater (as evidenced by finding fn as such an updater
; component).

  (cond
   ((endp tuples)
    (er hard 'absstobj-field-fn-of-stobj-type-p
        "Implementation error: Failed to find ~x0 among the exports of an ~
         (implicit) abstract stobj."
        fn))
   (t (let* ((tuple (car tuples))
             (updater (cdddr tuple)))
        (cond ((eq fn (car tuple))
               (and updater t))
              ((eq fn updater)
               t)
              (t (absstobj-field-fn-of-stobj-type-p fn (cdr tuples))))))))

(defun stobj-field-fn-of-stobj-type-p (fn wrld)

; Fn is a function symbol of wrld.  Return true if for some stobj st (concrete
; or abstract), fn is the accessor or updater for a field fld of st of stobj
; type.  For fn the accessor or updater for fld, this is equivalent to taking
; or returning that stobj type, respectively, which is equivalent to taking or
; returning some stobj other than st.  Note that all of this applies not only
; to concrete stobjs, but also to abstract stobjs with child stobj fields
; (whose accessors have the :UPDATER keyword in their function specs, and whose
; updaters are the values of those :UPDATER keywords).

  (let ((st (getpropc fn 'stobj-function nil wrld)))
    (and st
         (let ((abs-info (getpropc st 'absstobj-info nil wrld)))
           (cond
            (abs-info ; st is an abstract stobj
             (let ((stobj-prop (getpropc st 'stobj nil wrld)))
               (and (not (eq fn (cadr stobj-prop)))  ; recognizer
                    (not (eq fn (caddr stobj-prop))) ; creator
                    (absstobj-field-fn-of-stobj-type-p
                     fn
; We take the cddr to remove the tuples for the recognizer and creator.
                     (cddr (access absstobj-info abs-info
                                   :absstobj-tuples))))))
            (t ; st is a concrete stobj
             (or (not (all-nils-or-x st (stobjs-in fn wrld)))
                 (not (all-nils-or-x st (stobjs-out fn wrld))))))))))

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
; whenever we like.  We rely on a version of translate to finish the job;
; indeed, it should be the case that when translate11 is called on x with the
; following arguments, it returns the same result regardless of whether
; macroexpand1*-cmp is first called to do some expansion.

; stobjs-out   - :stobjs-out
; bindings     - ((:stobjs-out . :stobjs-out))
; known-stobjs - t
; flet-alist   - nil

; Warning: Keep this in sync with translate11 -- especially the first cond
; branch's test below.

  (cond ((or (atom x)
             (eq (car x) 'quote)
             (not (true-listp (cdr x)))
             (not (symbolp (car x)))
             (member-eq (car x) '(mv
                                  mv-let
                                  pargs
                                  translate-and-test
                                  with-local-stobj
                                  stobj-let
                                  swap-stobjs

; It's not clear that progn! needs to be included here.  But before we excluded
; macros from *ttag-fns* (when that constant was named *ttag-fns-and-macros*),
; progn! was the unique macro in that list and was checked here by virtue of
; being in that list; hence we continue to check it here.

                                  progn!))
             (not (getpropc (car x) 'macro-body nil wrld))
             (and (member-eq (car x) '(pand por pargs plet))
                  (eq (access state-vars state-vars
                              :parallel-execution-enabled)
                      t)))
         (value-cmp x))
        (t
         (mv-let
           (erp expansion)
           (macroexpand1-cmp x ctx wrld state-vars)
           (cond
            (erp (mv erp expansion))
            (t (macroexpand1*-cmp expansion ctx wrld state-vars)))))))

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

(defun match-stobjs (lst1 lst2 wrld acc)

; Lst1 and lst2 are proposed stobjs-out values.  So they are lists of symbols,
; presumably each with nil as the only possible duplicate.  We return t when
; the following conditions are all met: lst1 and lst2 have the same length; and
; for each i < (length lst1), (nth i lst1) and (nth i lst2) are both nil or
; else they are congruent stobjs.

  (cond ((endp lst1) (null lst2))
        ((endp lst2) nil)
        ((not (eq (null (car lst1))
                  (null (car lst2))))
         nil)
        ((or (null (car lst1))
             (eq (car lst1) (car lst2)))
         (match-stobjs (cdr lst1) (cdr lst2) wrld acc))
        ((not (congruent-stobjsp (car lst1) (car lst2) wrld))
         nil)
        (t (let ((pair (assoc-eq (car lst1) acc)))
             (cond ((null pair)
                    (match-stobjs (cdr lst1)
                                  (cdr lst2)
                                  wrld
                                  (acons (car lst1) (car lst2) acc)))
                   (t (er hard! 'match-stobjs
                          "Implementation error: expected no duplicate stobjs ~
                           in stobjs-out list!")))))))

(defun make-lambda-term (formals actuals body)

; Warning: If you consider making a call of this function, ask yourself whether
; make-lambda-application would be more appropriate; the answer depends on why
; you are calling this function.  For example, make-lambda-application will
; drop an unused formal, but the present function does not (though its caller
; could choose to "hide" such a formal; see translate11-let).

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

(defun all-unbadged-fnnames (term wrld acc)

; Returns the list of all unbadged function symbols in term.

  (cond ((variablep term) acc)
        ((fquotep term) acc)
        (t
         (all-unbadged-fnnames-list
          (fargs term)
          wrld
          (cond
           ((flambda-applicationp term)
            (all-unbadged-fnnames
             (lambda-body (ffn-symb term))
             wrld
             acc))
           ((executable-badge (ffn-symb term) wrld)
            acc)
           (t (add-to-set-eq (ffn-symb term) acc)))))))

(defun all-unbadged-fnnames-list (terms wrld acc)
  (cond ((endp terms) acc)
        (t (all-unbadged-fnnames-list
            (cdr terms) wrld
            (all-unbadged-fnnames (car terms) wrld acc))))))

(defconst *gratuitous-lambda-object-restriction-msg*
  "See :DOC gratuitous-lambda-object-restrictions for a workaround if you ~
   really mean to have an ill-formed LAMBDA-like constant in your code.  You ~
   may see this message without having explicitly typed a LAMBDA if you used ~
   a loop$ statement.  Loop$ statements are translated into calls of scions ~
   that use LAMBDA objects generated from the UNTIL, WHEN, and operator ~
   expressions.  If you are defining a function that calls itself recursively ~
   from within a loop$ you must include the xargs :LOOP$-RECURSION T and an ~
   explicit :MEASURE.")

(defun edcls-from-lambda-object-dcls (dcls x bindings cform ctx wrld)

; Dcls is the part of the lambda/lambda$ expression after the formals and
; before the body.  X is either a LAMBDA or LAMBDA$ form.  In general ACL2
; permits multiple DECLARE expressions, each of which may contain TYPE and
; XARGS.  However, in the case of LAMBDA there can be at most one DECLARE.  We
; check that each TYPE is well-formed and mentions only the formals of the
; purported lambda expression x.  The XARGS on lambda objects are restricted.
; We check that XARGS occurs at most once and may specify, at most, a :GUARD
; and :SPLIT-TYPES.  See the comment after *acceptable-dcls-alist* for a
; discussion of omitted XARGS keywords.  LAMBDAs must specify both :GUARD and
; :SPLIT-TYPES T, if XARGS is present at all.  We return the resulting edcls,
; without yet translating the :GUARD.  A typical answer might be ((TYPE INTEGER
; X Y) (XARGS :GUARD (AND (NATP X) (EVENP Y)) :SPLIT-TYPES NIL) (TYPE CONS
; AC)).

; Keep this function in sync with edcls-from-lambda-object-dcls-short-cut.

  (cond
   ((and (eq (car x) 'LAMBDA)
         (< 1 (length dcls)))
    (trans-er+? cform x
                ctx
                "A lambda object must have no more than one DECLARE form and ~
                 ~x0 has ~x1.  ~@2"
                x
                (length dcls)
                *gratuitous-lambda-object-restriction-msg*))
   (t
    (mv-let (erp edcls)
      (collect-declarations-cmp dcls (cadr x)
                                (car x) ; binder = 'LAMBDA or 'LAMBDA$
                                ctx wrld)

; Even if we are in the lambda-casep we do the collection above to check for the
; legality of the vars used in the TYPE/IGNORE/IGNORABLE declarations.

      (cond
       (erp (mv erp edcls bindings))
       (t (let ((xargs (assoc-eq 'XARGS edcls)))
            (cond
             ((null xargs) (trans-value edcls))
             ((assoc-eq 'XARGS (cdr (member xargs edcls)))
              (trans-er+? cform x
                          ctx
                          "Lambda objects and lambda$ expressions are allowed ~
                           to have at most one XARGS declaration.  ~@0"
                          *gratuitous-lambda-object-restriction-msg*))
             ((not (and (true-listp xargs)
                        ;; (eq (car xargs) 'XARGS)
                        (or (and (eql 3 (length xargs))
                                 (eq (cadr xargs) :GUARD))
                            (and (eql 5 (length xargs))
                                 (or (and (eq (cadr xargs) :GUARD)
                                          (eq (cadddr xargs) :SPLIT-TYPES))
                                     (and (eq (cadr xargs) :SPLIT-TYPES)
                                          (eq (cadddr xargs) :GUARD)))))
                        (member-eq (cadr (assoc-keyword :SPLIT-TYPES (cdr xargs)))
                                   '(NIL T))))
              (trans-er+? cform x
                          ctx
                          "The XARGS of a lambda object or lambda$ ~
                           expression, when present, must specify a :GUARD, ~
                           may additionally specify :SPLIT-TYPES, and must ~
                           not specify any other keywords.  For quoted ~
                           LAMBDAs the :SPLIT-TYPES keyword must be present, ~
                           must follow the :GUARD keyword and value, and must ~
                           be assigned T.  For lambda$s, the keywords may ~
                           appear in either order and :SPLIT-TYPES, if ~
                           present, must be assigned NIL or T.  ~x0 violates ~
                           this.  ~@1"
                          xargs
                          *gratuitous-lambda-object-restriction-msg*))
             ((eq (car x) 'LAMBDA)
              (cond ((not (and (eq (cadr xargs) :GUARD)
                               (eq (cadddr xargs) :SPLIT-TYPES)
                               (eq (car (cddddr xargs)) T)))
                     (trans-er+? cform x
                                 ctx
                                 "The XARGS declaration of a lambda object, ~
                                  when present, must have the form (XARGS ~
                                  :GUARD term :SPLIT-TYPES T) -- the order of ~
                                  the keys matters! -- and ~x0 does not have ~
                                  this form.  ~@1"
                                 xargs
                                 *gratuitous-lambda-object-restriction-msg*))
                    (t (trans-value edcls))))
             (t (trans-value edcls))))))))))

(defun edcls-from-lambda-object-dcls-short-cut (tail)

; Tail is initially the cddr of a lambda$ expression that is known to have been
; successfully translated, typically ((DECLARE . edcls1) ... (DECLARE . edclsk)
; body).  We append together all the edclsi.  This function is just a fast way
; to compute edcls-from-lambda-dcls, without all the error checking, since we
; know the initial lambda$ expression was well-formed.

; Keep this function in sync with edcls-from-lambda-object-dcls.

  (cond
   ((endp (cdr tail)) nil)
   (t (append (cdr (car tail))
              (edcls-from-lambda-object-dcls-short-cut (cdr tail))))))

; In raw Lisp, (lambda$ ...) expands to just (quote (,*lambda$-marker*
; . (lambda$ ...))), where *lambda$-marker* is a symbol in the ACL2_INVISIBLE
; package.

#-acl2-loop-only
(defconst *lambda$-marker* 'acl2_invisible::lambda$-marker)

#-acl2-loop-only
(defmacro lambda$ (&rest args)
  `(quote (,*lambda$-marker* . (lambda$ ,@args))))

(defconst *loop$-keyword-info*
;            plain     fancy
; loop op    scion     scion     req on apply$ output
  '((sum     sum$      sum$+     acl2-numberp)
    (always  always$   always$+  t)
    (thereis thereis$  thereis$+ t)
    (collect collect$  collect$+ t)
    (append  append$   append$+  true-listp)
    (nil     until$    until$+   t)             ; the nil key indicates a loop$-related
    (nil     when$     when$+    t)             ; scion that is not a loop$ op
    ))

; This is a list of every function symbol used in the translation of loop$
; statements.  Built into our code, e.g., make-plain-loop$, make-fancy-loop$,
; chk-lambdas-for-loop$-recursion, etc, is the knowlege that every plain scion
; takes the lambda expression in arg 1 and the domain (over which mapping
; occurs) in arg 2.  Every fancy scion takes the lambda expression in arg 1 and
; the domain in arg 3.

; Because of Special Conjectures (a), (b), and (c) -- see the Essay on Loop$ --
; we have to be careful not to evaluate ground calls of these symbols during
; guard clause generation.  If any of these functions were to be evaluated we
; would fail to recognize the need for some special conjectures.  For example,
; (collect$ (lambda$ ...) (tails '...)) is a pattern that triggers Special
; Conjecture (c) because it represents ON iteration, and that pattern would not
; be present if (tails '...) turned into a constant.  See the call of
; eval-ground-subexpressions1 in guard-clauses+ for where we use this list.

; Before we avoided evaluating ground calls of these symbols we saw the
; following bug:

; (value :q)
; (declaim (optimize (safety 3))) ; causes CCL to check type specs at runtime
; (lp)

; (defun below-3p (x) (declare (xargs :guard t)) (and (natp x) (< x 3)))

; (defun bug ()
;   (declare (xargs :guard t))
;   (loop$ for x of-type (satisfies below-3p) in '(1 2 3 4 5) collect x))

; (bug)

; ***********************************************
; ************ ABORTING from raw Lisp ***********
; ********** (see :DOC raw-lisp-error) **********
; Error:  The value 3 is not of the expected type
; (OR NULL (SATISFIES BELOW-3P)).
; While executing: BUG3
; ***********************************************

(defconst *loop$-special-function-symbols*
  '(sum$ sum$+ always$ always$+ thereis$ thereis$+
         collect$ collect$+ append$ append$+
         until$ until$+ when$ when$+
         loop$-as tails from-to-by))

(defun loop$-operator-scionp (fn alist)
  (cond ((endp alist) nil)
        ((and (car (car alist)) ; operator?
              (or (eq (cadr (car alist)) fn)    ; :plain?
                  (eq (caddr (car alist)) fn))) ; :fancy?
         t)
        (t (loop$-operator-scionp fn (cdr alist)))))

(defun loop$-scion-style (fn alist)

; Fn is a symbol and alist is a tail of *loop$-keyword-info*.  We determine
; whether fn is either a plain or fancy loop$ scion.  We return nil, :plain, or
; :fancy.

  (cond
   ((endp alist) nil)
   ((eq (cadr (car alist)) fn)
    :plain)
   ((eq (caddr (car alist)) fn)
    :fancy)
   (t (loop$-scion-style fn (cdr alist)))))

(defun loop$-scion-restriction (fn alist)

; Fn is a symbol and alist is a tail of *loop$-keyword-info*.  We determine
; whether fn imposes a restriction on the output of its apply$.  We return nil
; or the name of the predicate that checks that the apply$ is returning
; something of the right kind.

; The need for this function arises in guard conjecture generation.

  (cond
   ((endp alist) nil)
   ((or (eq (cadr (car alist)) fn)
        (eq (caddr (car alist)) fn))
    (if (eq (cadddr (car alist)) t)
        nil
        (cadddr (car alist))))
   (t (loop$-scion-restriction fn (cdr alist)))))

; We need some terminology.  There are three terms in our supported loop
; statements: the UNTIL term, the WHEN term, and the body of the loop term.  In
; (loop$ for ... UNTIL t1 WHEN t2 COLLECT t3), the terms in question are t1,
; t2, and t3.  Each of these three terms will be incorporated into lambda$
; expressions where they'll be the bodies of their respective lambda$s.  So we
; need a name for t3, aka ``the body of the loop,'' that is shorter and not
; confused with the body of a lambda.  We'll call t3 the ``loop$ body'' or
; ``lobody.''

; The syntax of our loop$ adds three optional terms: guard terms for each of
; the above because it is sometimes necessary to specify guards for the
; lambda$s we construct so that the lambda$s can be guard verified.  The
; syntax we've chosen is:

; (loop$ for ... UNTIL :guard g1 t1 WHEN :guard g2 t2 COLLECT :guard g3 t3)

; We considered something like ... UNTIL (with-guard g1 t1) ... but didn't want
; to suggest a guard can just be dropped anywhere in a term as the ``function''
; with-guard does.  The raw Lisp expansion of loop$ will strip out the :guard g
; elements.

; If a :guard is specified, it is added as an additional conjunct to the guard
; we can compute from from the TYPE specs.

; We'll build lambda$ expressions for each of these pairs of terms, e.g.,
; (lambda$ (v) (declare (xargs :guard g1)) t1) might be the lambda$ expression
; for the UNTIL clause above.  We'll call g1 the ``guard term'' and t1 the
; ``body term'' of the lambda$.  But we'll need both the translated and
; untranslated versions of both g1 and t1 -- we'll put the untranslated ones in
; our lambda$ but use the translated ones to do free-variable analysis.

; At first we coded this with twelve variable names, e.g.,
; untranslated-until-guard, translated-until-guard, untranslated-until-body,
; translated-until-body.  But this just gets confusing.  So now we put all four
; objects, the untranslated guard and body and the translated guard and body,
; into one thing which we call a ``carton'' and we define a convenient
; accessor.  (We could have used a defrec structure but prefer our accessor
; idiom.)

; When we first make a carton we won't generally have the translated terms, so
; we'll fill those slots with nils.  We call such a carton ``unfinished.''  We
; don't provide an idiom for ``filling'' a carton, we just make a ``finished''
; carton when we have what we need.

; So during the translation of a loop$ statement we'll use three variables,
; untilc, whenc, and lobodyc, where the ``c'' can be thought of as standing for
; ``clause'' as in the loop terminology, e.g., ``the WHEN clause,'' but
; actually stands for ``carton.''

(defun make-carton (uguard tguard ubody tbody)
  (cons (cons uguard tguard) (cons ubody tbody)))

(defmacro excart (u/t g/b carton)

; Here u/t is :untranslated or :translated, g/b is :guard or :body, and carton
; is a carton.  Typical call (excart :untranslated :body carton).  The name
; ``excart'' is short for ``extract from carton.''

  (declare (xargs :guard (and (or (eq u/t :untranslated)
                                  (eq u/t :translated))
                              (or (eq g/b :guard)
                                  (eq g/b :body)))))

  (if (eq g/b :guard)
      (if (eq u/t :untranslated)
          `(car (car ,carton))
          `(cdr (car ,carton)))
      (if (eq u/t :untranslated)
          `(car (cdr ,carton))
          `(cdr (cdr ,carton)))))

(defun symbol-name-equal (x str)
  (declare (xargs :guard (stringp str)))
  (and (symbolp x)
       (equal (symbol-name x) str)))

(defun assoc-symbol-name-equal (sym alist)
  (declare (xargs :guard (and (symbolp sym)
                              (symbol-alistp alist))))
  (cond
   ((endp alist) nil)
   ((symbol-name-equal sym (symbol-name (caar alist)))
    (car alist))
   (t (assoc-symbol-name-equal sym (cdr alist)))))

(defun parse-loop$-accum (stmt args ans)

; We're parsing the loop$ statement stmt and have gotten down to args, a tail of
; stmt that is supposed to be a loop$ operator, optional :guard, and body.
; We add two things to ans, the op and the (unfinished) carton for the op's
; term.  We return two results, (mv msg ans'), where msg is nil if the parse
; was successful and an error msg otherwise, and ans' is the accumulated
; answer.  BTW: All the intermediate parsing functions accumulate the
; components in reverse onto ans and the top-level parse-loop$ will reverse
; them.

; Warning: It is critical that we not allow loop$s containing :guard as the
; body, as in (loop$ for v in lst collect :guard).  See the warning in
; remove-loop$-guards.

  (case-match args
    ((op ':GUARD gexpr expr)
     (cond
      ((and (symbolp op)
            (not (null op))
            (assoc-symbol-name-equal op *loop$-keyword-info*))
       (mv nil (cons
                (make-carton gexpr nil expr nil)
                (cons
                 (car (assoc-symbol-name-equal op *loop$-keyword-info*))
                 ans))))
      (t (mv (msg "Parsing stopped at position ~x0, where we read ~x1 but ~
                   expected one of the loop$ operators ~*2."
                  (- (length stmt) (length args))
                  (nth 0 args)
                  (list "" "~x*" "~x* or " "~x*, "
                        (collect-non-x nil (strip-cars *loop$-keyword-info*))))
             args))))
    ((op expr)
     (cond
      ((and (symbolp op)
            (not (null op))
            (assoc-symbol-name-equal op *loop$-keyword-info*)
            (not (eq expr :guard)))
       (mv nil
           (cons
            (make-carton T *T* expr nil)
            (cons
             (car (assoc-symbol-name-equal op *loop$-keyword-info*))
             ans))))
      ((and (symbolp op)
            (not (null op))
            (assoc-symbol-name-equal op *loop$-keyword-info*)
            (eq expr :guard))
       (mv (msg "Parsing stopped at position ~x0, where we read :GUARD but ~
                 expected it to be followed by a guard test and loop$ body. ~
                 If you really want :GUARD to be the loop$ body write ':GUARD ~
                 instead."
                (+ 1 (- (length stmt) (length args))))
           args))
      (t (mv (msg "Parsing stopped at position ~x0, where we read ~x1 but ~
                   expected to see one of the loop$ operators ~*2."
                  (- (length stmt) (length args))
                  (nth 0 args)
                  (list "" "~x*" "~x* or " "~x*, "
                        (collect-non-x nil (strip-cars *loop$-keyword-info*))))
             args))))
    (& (cond
        ((and (symbolp (car args))
              (not (null (car args)))
              (assoc-symbol-name-equal (car args) *loop$-keyword-info*))
         (cond
          ((and (eq (cadr args) :guard)
                (null (cddr args)))
           (mv (msg "Parsing stopped at position ~x0, where we read :GUARD ~
                     but expected a loop$ body expression.  If you want the ~
                     body to be :GUARD, use ':GUARD instead. The bare keyword ~
                     :GUARD here must be followed by a guard test and a loop$ ~
                     body expression."
                    (+ 1 (- (length stmt) (length args))))
               args))
          (t (mv (msg "Parsing stopped just after position ~x0, where we read ~
                       ~x1 while expecting it to be followed by either a ~
                       single loop$ body expression or the keyword :GUARD ~
                       followed by a guard test and a loop$ body expression.  ~
                       But your loop$ has ``... ~*2)''."
                      (- (length stmt) (length args))
                      (car args)
                      (list "" "~x*" "~x* " "~x* " args))
                 args))))
        ((car ans)
; This means we've seen a WHEN, so all that's left is a loop$ operator.
         (mv (msg "Parsing stopped at position ~x0, where we ~#1~[ran off the ~
                   end of the loop$ statement~/read ~x2 but expected one of ~
                   the loop$ operators ~*3~]."
                  (- (length stmt) (length args))
                  (if (null args) 0 1)
                  (car args)
                  (list "" "~x*" "~x* or " "~x*, "
                        (collect-non-x nil (strip-cars *loop$-keyword-info*))))
             args))
        (t
; This means we saw no WHEN, which may mean the culprit was meant to be part of
; a when clause.
         (mv (msg "Parsing stopped at position ~x0, where we ~#1~[ran off the ~
                   end of the loop$ statement~/read ~x2 but expected WHEN or ~
                   one of the loop$ operators ~*3~]."
                  (- (length stmt) (length args))
                  (if (null args) 0 1)
                  (car args)
                  (list "" "~x*" "~x* or " "~x*, "
                        (collect-non-x nil (strip-cars *loop$-keyword-info*))))
             args))))))

(defun possible-typop (lst1 lst2)

; Both arguments are lists of characters spelling out two symbol names.  We
; think of the first symbol as something the user wrote and the second as what
; he or she might have meant.  The question is whether the user made a simple
; typo.  We check that the two lists contain the same chars in the same order
; with just three exceptions: lst1 has exactly one extra char, lst1 is missing
; exactly one char, or two adjacent chars have been swapped.

  (cond
   ((endp lst1)
    (or (endp lst2)
        (endp (cdr lst2))))
   ((endp lst2)
    (endp (cdr lst1)))
   ((eql (car lst1) (car lst2))
    (possible-typop (cdr lst1) (cdr lst2)))
   (t (or (equal (cdr lst1) lst2)           ; this is an extra char in lst1
          (equal lst1 (cdr lst2))           ; this is a missing char in lst1
          (equal (cdr lst1) (cdr lst2))     ; lst1 used a different char here
          (and (eql (car lst1) (cadr lst2)) ; swapped adjacent chars
               (eql (cadr lst1) (car lst2))
               (equal (cddr lst1) (cddr lst2)))))))

(defun maybe-meant-but-didnt-write (written intended)

; In a situation in which the second argument is a suitable input the user
; wrote the first argument instead.  We determine whether this is likely just a
; typo caused by different symbol packages or one trivial typing mistake:
; adding or deleting a character or swapping two adjacent characters.

  (and (symbolp written)
       (symbolp intended)
       (not (eq written intended))
       (or (equal (symbol-name written)
                  (symbol-name intended))
           (possible-typop (coerce (symbol-name written) 'list)
                           (coerce (symbol-name intended) 'list)))))

(defun parse-loop$-when (stmt args ans)

; We add one entry to ans for the WHEN clause.  If there is a when clause, we
; add an unfinished carton.  If there's no WHEN clause we add nil.  One might
; think we could represent the absence of a WHEN clause with WHEN T but we need
; to know if a WHEN clause was present since it's illegal in CLTL to have a
; WHEN with an ALWAYS and we don't want to translate a loop$ that generates an
; illegal CLTL loop in raw Lisp.  As explained in parse-loop$-accum, we return
; (mv msg ans').

; Warning: It is critical that we not allow loop$s containing :guard as the
; test of a WHEN, as in (loop$ for v in lst when :guard collect v).  See the
; warning in remove-loop$-guards.  We test expliticly for this below, but it
; can only happen on loop$s that are ill-formed anyway!  See the comment below.

  (case-match args
    (((quote~ WHEN) ':GUARD gtest test . rest)
     (parse-loop$-accum stmt rest
                        (cons (make-carton gtest nil test nil) ans)))
    (((quote~ WHEN) test . rest)
     (cond
      ((eq test :guard)

; This test is meant to catch the case where the user specifies an un-guarded
; WHEN test of :guard.  To do so requires writing something like (loop$ for v
; in lst when :guard collect v).  Except that doesn't work because that is
; parsed with a guarded when with test v (guarded by collect).  The only time
; this test can succeed is if the user wrote something like (loop$ for v in lst
; when :guard) or (loop$ for v in lst when :guard body) because if he or she
; writes two or more things after ``when :guard'' it is parsed by the first
; case above.  Note that both inputs that make this test true are ill-formed
; anyway.  But our points in having this test here are to (a) make clear we
; don't allow naked ... when :guard ... and (b) give what we think is a better
; error message than just running off the end of the accumulator clause.

       (mv (msg "Parsing stopped at position ~x0, where we read :GUARD as the ~
                 WHEN test.  We prohibit this. If you really want to use ~
                 :GUARD as the WHEN test then write ':GUARD instead, but we ~
                 see no reason to use this idiom at all!  In addition, this ~
                 loop$ statement ends without specifying an accumulator loop$ ~
                 body."
                (+ 1 (- (length stmt) (length args))))
           args))

      (t (mv-let (msg ans1)
           (parse-loop$-accum stmt rest (cons (make-carton T *T* test nil) ans))
           (cond
            (msg
             (cond
              ((eq (cadr args) :GUARD)
               (mv (msg "Parsing stopped at position ~x0, where we read ~
                         :GUARD but expected it to be followed by an ~
                         expression but the statement ends prematurely.  No ~
                         WHEN test, loop$ accumulator, or loop$ body is ~
                         provided!"
                        (+ 1 (- (length stmt) (length args))))
                   ans1))
              ((maybe-meant-but-didnt-write test :GUARD)
               (mv (msg "~@0~%~%This error might be due to an earlier problem ~
                         with the purported loop$ statement.  You wrote ``... ~
                         WHEN ~x1 ...'' and perhaps you meant ``... WHEN ~
                         :GUARD ...''.  Given what you actually wrote, ~x1 is ~
                         being parsed as the (unguarded) WHEN term."
                        msg
                        (cadr args))
                   ans1))
              (t (mv msg ans1))))
            (t (mv msg ans1)))))))
    (& (mv-let (msg ans1)
         (parse-loop$-accum stmt args (cons nil ans))
         (cond
          (msg
           (cond
            ((and (eq (car args) 'when)
                  (maybe-meant-but-didnt-write (cadr args) :GUARD))
             (mv (msg "~@0~%~%This error might be due to an earlier problem ~
                       with the purported loop$ statement.  You wrote ``... ~
                       WHEN ~x1 ...'' and perhaps you meant ``... WHEN :GUARD ~
                       ...''.  Given what you actually wrote, ~x1 is being ~
                       parsed as the (unguarded) WHEN term."
                      msg
                      (cadr args))
                 ans1))
            ((maybe-meant-but-didnt-write (car args) 'when)
             (mv (msg "~@0~%~%This error might be due to an earlier ~
                          problem with the purported loop$ statement.  You ~
                          wrote ``...  ~x1 ...'' and perhaps you meant ``... ~
                          WHEN ...''."
                      msg
                      (car args))
                 ans1))
            (t (mv msg ans1))))
          (t (mv msg ans1)))))))

(defun parse-loop$-until (stmt args ans)

; We add one entry to ans for the UNTIL clause, an unfinished carton or nil.
; As explained in parse-loop$-accum, we return (mv msg ans').

; Warning: It is critical that we not allow loop$s containing :guard as the
; test of a WHEN, as in (loop$ for v in lst when :guard collect v).  See the
; warning in remove-loop$-guards.  We test expliticly for this below, but it
; can only happen on loop$s that are ill-formed anyway!  See the comment below.

  (case-match args
    (((quote~ UNTIL) ':GUARD gtest test . rest)
     (parse-loop$-when stmt rest (cons (make-carton gtest nil test nil) ans)))
    (((quote~ UNTIL) test . rest)
     (cond
      ((eq test :guard)

; This test is meant to catch the case where the user specifies an un-guarded
; UNTIL test of :guard.  To do so requires writing something like (loop$ for v
; in lst until :guard collect v).  Except that doesn't work because that is
; parsed with a guarded until with test v (guarded by collect).  The only time
; this test can succeed is if the user wrote something like (loop$ for v in lst
; until :guard) or (loop$ for v in lst until :guard body) because if he or she
; writes two or more things after ``until :guard'' it is parsed by the first case
; above.  Note that both inputs that make this test true are ill-formed anyway.
; But our points in having this test here are to (a) make clear we don't allow
; naked ... until :guard ... and (b) give what we think is a better error
; message than just running off the end of the accumulator clause.

       (mv (msg "Parsing stopped at position ~x0, where we read :GUARD as the ~
                 UNTIL test.  We prohibit this. If you really want to use ~
                 :GUARD as the UNTIL test then write ':GUARD instead, but we ~
                 see no reason to use this idiom at all!  In addition, this ~
                 loop$ statement ends without specifying an accumulator loop$ ~
                 body."
                (+ 1 (- (length stmt) (length args))))
           args))
      (t
       (mv-let (msg ans1)
         (parse-loop$-when stmt rest (cons (make-carton T *T* test nil) ans))
         (cond
          (msg
           (cond
            ((eq (cadr args) :GUARD)
             (mv (msg "Parsing stopped at position ~x0, where we read :GUARD ~
                       but expected it to be followed by an expression but ~
                       the statement ends prematurely.  No UNTIL test, loop$ ~
                       accumulator, or loop$ body is provided!"
                      (+ 1 (- (length stmt) (length args))))
                 ans1))
            ((maybe-meant-but-didnt-write test :GUARD)
             (mv (msg "~@0~%~%This error might be due to an earlier problem ~
                       with the purported loop$ statement.  You wrote ``... ~
                       UNTIL ~x1 ...'' and perhaps you meant ``... UNTIL ~
                       :GUARD ...''.  Given what you actually wrote, ~x1 is ~
                       being parsed as the (unguarded) UNTIL term."
                      msg
                      (cadr args))
                 ans1))
            (t (mv msg ans1))))
          (t (mv msg ans1)))))))
    (& (mv-let (msg ans1)
         (parse-loop$-when stmt args (cons nil ans))
         (cond
          (msg
           (cond
            ((and (eq (car args) 'until)
                  (maybe-meant-but-didnt-write (cadr args) :GUARD))
             (mv (msg "~@0~%~%This error might be due to an earlier problem ~
                       with the purported loop$ statement.  You wrote ``... ~
                       UNTIL ~x1 ...'' and perhaps you meant ``... UNTIL ~
                       :GUARD ...''.  Given what you actually wrote, ~x1 is ~
                       being parsed as the (unguarded) UNTIL term."
                      msg
                      (cadr args))
                 ans1))
            ((maybe-meant-but-didnt-write (car args) 'until)
             (mv (msg "~@0~%~%This error might be due to an earlier ~
                          problem with the purported loop$ statement.  You ~
                          wrote ``...  ~x1 ...'' and perhaps you meant ``... ~
                          UNTIL ...''."
                      msg
                      (car args))
                 ans1))
            (t (mv msg ans1))))
          (t (mv msg ans1)))))))

(defun parse-loop$-vsts-diagnose-failure (flg1 args args1)

; We know that args was supposed to be a ``properly terminated iteration
; variable phrase'' but failed to be.  Flg1 is t if we successfully parsed args
; as an iteration variable phrase.  Args1, which is relevant only if flg1 is t,
; is the rest of the alleged loop$ statement after the parse and so contains as
; its first element the token that terminated the parse.  Return (mv
; failure-type tail expected-msg), where failure-type is

; 0 -- args is too short to parse as a phrase
; 1 -- args parsed but the loop$ statement ended before we got to the
;      terminator token (AS, UNTIL, WHEN, or a loop$ operator)
; 2 -- args parsed but is terminated by something other than AS, UNTIL,
;      WHEN, or a loop$ operator,
; 3 -- we encountered a mismatch during the parse, e.g., saw FORM instead
;      of FROM (but not all reports are such misspellings).

; Tail is nil (when we ran out tokens) or a non-empty tail of args (and thus, a
; non-empty tail of the original loop$ statement we're trying to parse) where
; the parse started going wrong.  Expected-message is a msg that describes what
; we expected to see when we encountered culprit.

  (cond
   ((endp args1)

; Our caller treats cases 0 and 1 identically: we ran out of tokens before
; completing the parse.  We differentiate them here just to remind ourselves of
; flg1.  Given that args1 is empty, flg1 = t means we parsed a complete
; iteration variable phrase but ran out of tokens on the termination check; and
; flg1 = nil means we ran out of tokens while parsing the phrase itself.

    (mv (if flg1 1 0) nil nil))

   (t
    (let ((unusual-var-msg
           (if (or (member-symbol-name (symbol-name (car args))
                                       '(in on from to by as until when guard))
                   (and (car args)
                        (assoc-symbol-name-equal (car args) *loop$-keyword-info*)))
               (msg ". The unusual variable name, ~x0, which is a reserved word ~
                     in loop$ syntax, might indicate that you forgot to ~
                     specify the iteration variable"
                    (car args))
               (msg ""))))
      (cond
       (flg1

; We parsed a phrase but failed the termination check because we saw (car
; args1) when we expected AS, UNTIL, WHEN, or a loop$ operator.

; However, there is one special case: If the user typed (loop$ for i from 1 to
; 10 bye 3 ...) flg1 is set and the iteration variable phrase was terminated by
; BYE.  While the user might have meant something like (loop$ for i from 1 to
; 10 collect 3) another possibility is that BYE should have been BY and the
; iteration variable phrase wasn't actually terminated!  We check this here.
; Note that if args is (& OF-TYPE & FROM ...) or (& FROM ...) then we're in this
; case because flg1 is t so that part of the input parsed.

        (mv 2
            args1
            (cond
             ((case-match args
                ((& (quote~ OF-TYPE) & (quote~ FROM) & (quote~ TO) & (quote~ BY)) t)
                ((& (quote~ FROM) & (quote~ TO) & (quote~ BY)) t)
                (& nil))
              (msg "to read an expression after it, but the statement ends ~
                    prematurely~@0"
                   unusual-var-msg))
             ((and (maybe-meant-but-didnt-write (car args1) 'BY)
                   (case-match args
                     ((& (quote~ OF-TYPE) & (quote~ FROM) . &) t)
                     ((& (quote~ FROM) . &) t)
                     (& nil)))
              (msg "BY, AS, UNTIL, WHEN, or one of the loop$ operators ~*0~@1"
                   (list "" "~x*" "~x* or " "~x*, "
                         (collect-non-x nil (strip-cars *loop$-keyword-info*)))
                   unusual-var-msg))
             (t
              (msg "AS, UNTIL, WHEN, or one of the loop$ operators ~*0~@1"
                   (list "" "~x*" "~x* or " "~x*, "
                         (collect-non-x nil (strip-cars *loop$-keyword-info*)))
                   unusual-var-msg)))))
       (t

; We failed to parse the phrase.  Args1 is the same as args (and non-nil, so
; there is at least an iteration variable) and we now have to discover where we
; failed!  We start by looking at the token right after the variable, i.e., at
; (nth 1 args), which should be an OF-TYPE, IN, OR, or FROM.  And then we just
; keep working through the cases.  But at least we know there are enough tokens
; to just look at each expected token with nth.

        (cond
         ((not
           (or (symbol-name-equal (nth 1 args) "OF-TYPE")
               (symbol-name-equal (nth 1 args) "IN")
               (symbol-name-equal (nth 1 args) "ON")
               (symbol-name-equal (nth 1 args) "FROM")))
          (mv 3
              (nthcdr 1 args)
              (cond
               ((maybe-meant-but-didnt-write (nth 1 args) 'OF-TYPE)
                (msg "OF-TYPE, IN, ON, or FROM~@0"
                     unusual-var-msg))
               ((and (maybe-meant-but-didnt-write (nth 1 args) 'IN)
                     (maybe-meant-but-didnt-write (nth 1 args) 'ON))
                (msg "IN, ON, FROM, or OF-TYPE~@0"
                     unusual-var-msg))
               ((maybe-meant-but-didnt-write (nth 1 args) 'IN)
                (msg "IN, ON, FROM, or OF-TYPE~@0"
                     unusual-var-msg))
               ((maybe-meant-but-didnt-write (nth 1 args) 'ON)
                (msg "ON, IN, FROM, or OF-TYPE~@0"
                     unusual-var-msg))
               ((maybe-meant-but-didnt-write (nth 1 args) 'FROM)
                (msg "FROM, IN, ON, or OF-TYPE~@0"
                     unusual-var-msg))
               (t (msg "OF-TYPE, IN, ON, or FROM~@0"
                       unusual-var-msg)))))
; Note:  If we get so far as confirming the presence of IN or ON or BY then the
; only way the parse could have failed is that we ran out of tokens, which we've
; already handled.  So we don't need to think about those three cases.
         ((symbol-name-equal (nth 1 args) "FROM")

; We could check (nth 3 args) and possibly (nth 5 args), looking for TO and possibly
; BY.  But we know that TO is missing!  Why?  If TO is present then we would have
; succeeded in parsing FROM/TO (since we didn't run out of tokens).

          (mv 3
              (nthcdr 3 args)
              (msg "TO~@0"
                   unusual-var-msg)))
         ((and (symbol-name-equal (nth 1 args) "OF-TYPE")
               (not
                (or (symbol-name-equal (nth 3 args) "IN")
                    (symbol-name-equal (nth 3 args) "ON")
                    (symbol-name-equal (nth 3 args) "FROM"))))
          (mv 3
              (nthcdr 3 args)
              (cond
               ((and (maybe-meant-but-didnt-write (nth 3 args) 'IN)
                     (maybe-meant-but-didnt-write (nth 3 args) 'ON))
                (msg "IN, ON, or FROM~@0"
                     unusual-var-msg))
               ((maybe-meant-but-didnt-write (nth 3 args) 'IN)
                (msg "IN, ON, or FROM~@0"
                     unusual-var-msg))
               ((maybe-meant-but-didnt-write (nth 3 args) 'ON)
                (msg "ON, IN, or FROM~@0"
                     unusual-var-msg))
               ((maybe-meant-but-didnt-write (nth 3 args) 'FROM)
                (msg "FROM, IN, or ON~@0"
                     unusual-var-msg))
               (t (msg "IN, ON, or FROM~@0"
                       unusual-var-msg)))))
         ((symbol-name-equal (nth 1 args) "FROM")
          (mv 3 (nthcdr 3 args) (msg "TO~@0" unusual-var-msg)))
         (t (mv 3
                (nthcdr 1 args)
                (msg "OF-TYPE, IN, OR, or FROM~0@"
                     unusual-var-msg))))))))))

(defun parse-loop$-vsts (stmt args vsts ans)

; Stmt is a loop$ statement and args is some tail of it.  We try to parse a
; sequence of vsts.  Vsts stands for ``vars, specs, and targets'' and here
; we're looking for multiple occurrences of the variations on ``v OF-TYPE spec
; IN/ON/FROM ...''  separated by ``AS''.  Each occurrence generates a ``vst
; tuple,'' e.g., (v spec (IN lst)) and we collect them all in reverse order
; into vsts.  When we have processed them all, we add the reverse of vsts to
; ans and start parsing for an UNTIL clause.  If we find no vsts, we indicate
; parse error.  The following case-match could be compacted but we prefer the
; explicit exhibition of the allowed patterns.

; Flg1 indicates whether we found a syntactically acceptable iteration var
; clause.  But we can still fail here unless the next symbol is either AS,
; UNTIL, WHEN, or a loop$ accumulator.  For example, if the user typed (loop$
; for v from 1 to 10 bye 3 collect i) we succeed and treat the iteration var
; clause as ``v from 1 to 10''.  But then the accumulator parse fails because
; it sees BYE.  We want to blame that failure on the iteration var clause, not
; any of the subsequent clauses.

  (mv-let (flg1 args1 vsts1)
    (case-match args
      ((v (quote~ OF-TYPE) spec (quote~ IN) lst . rest)
       (mv t rest (cons `(,v ,spec (IN ,lst)) vsts)))
      ((v (quote~ OF-TYPE) spec (quote~ ON) lst . rest)
       (mv t rest (cons `(,v ,spec (ON ,lst)) vsts)))
      ((v (quote~ OF-TYPE) spec (quote~ FROM) i (quote~ TO) j (quote~ BY) k
          . rest)
       (mv t rest (cons `(,v ,spec (FROM-TO-BY ,i ,j ,k)) vsts)))
      ((v (quote~ OF-TYPE) spec (quote~ FROM) i (quote~ TO) j . rest)
       (mv t rest (cons `(,v ,spec (FROM-TO-BY ,i ,j 1)) vsts)))
      ((v (quote~ IN) lst . rest)
       (mv t rest (cons `(,v T (IN ,lst)) vsts)))
      ((v (quote~ ON) lst . rest)
       (mv t rest (cons `(,v T (ON ,lst)) vsts)))
      ((v (quote~ FROM) i (quote~ TO) j (quote~ BY) k . rest)
       (mv t rest (cons `(,v T (FROM-TO-BY ,i ,j ,k)) vsts)))
      ((v (quote~ FROM) i (quote~ TO) j . rest)
       (mv t rest (cons `(,v T (FROM-TO-BY ,i ,j 1)) vsts)))
      (& (mv nil args vsts)))
    (cond
     ((and flg1
           (consp args1)
           (car args1)
           (symbolp (car args1))
           (or (symbol-name-equal (car args1) "AS")
               (symbol-name-equal (car args1) "UNTIL")
               (symbol-name-equal (car args1) "WHEN")
               (assoc-symbol-name-equal (car args1) *loop$-keyword-info*)))
      (cond
       ((and (consp args1)
             (symbol-name-equal (car args1) "AS"))
        (parse-loop$-vsts stmt (cdr args1) vsts1 ans))
       (t (parse-loop$-until stmt args1 (cons (revappend vsts1 nil) ans)))))
     (t (mv-let (failure-type tail expected-msg)
          (parse-loop$-vsts-diagnose-failure flg1 args args1)
          (cond ((or (eql failure-type 0)
                     (eql failure-type 1))
                 (mv (msg "Parsing stopped at position ~x0, where the loop$ ~
                           statement ends prematurely.  No loop$ accumulator ~
                           or body was provided."
                          (length stmt))
                     args))
                (t (mv (msg "Parsing stopped at position ~x0, where we read ~
                             ~x1 but expected ~@2."
                            (- (length stmt) (length tail))
                            (car tail)
                            expected-msg)
                       args))))))))

(defun parse-loop$ (stmt)

; Stmt is a form beginning with LOOP$.  We parse out the pieces.  We return (mv
; erp ans), where erp T means a parse error was detected and in that case, the
; second result, ans, is actually a msg explaining the error.  Otherwise, erp
; is NIL and ans is the parse of the statement.  The form of a successful parse
; (vsts untilc whenc op lobodyc) where

; Vsts is a list of elements, each of the form (v spec target), where target is
; one of (IN lst), (ON lst), or (FROM-TO-BY i j k).  If multiple vsts are
; returned, they are understood to be combined with AS in the order listed.  If
; no OF-TYPE is provided for v, T is used for its spec.

; Untilc is either an unfinished carton for the UNTIL expression or nil if
; there was no UNTIL clause.

; Whenc is either an unfinished carton for the WHEN expression or nil if there
; was no WHEN clause.

; Op is the loop$'s accumulator operator, e.g., SUM, COLLECT, etc.

; Lobodyc is an unfinished carton for the loop$ body.

; No syntax checking is done here!  For example, v may not be a variable or
; even a symbol, spec may not be a legal type spec, etc.

  (cond ((and (consp stmt)
              (eq (car stmt) 'LOOP$)
              (consp (cdr stmt))
              (symbol-name-equal (cadr stmt) "FOR"))
         (mv-let (msg ans)
           (parse-loop$-vsts stmt (cddr stmt) nil nil)
; When msg is non-nil, it is an error message and ans is irrelevant.
; Otherwise, ans is the reversed parse and we reverse it before returning.
           (cond
            (msg (mv t
                     (msg
                      "Illegal LOOP$ Syntax.  The form ~X01 cannot be parsed ~
                       as a LOOP$ statement.  ~@2"
                      stmt nil msg)))
            (t (mv nil (revappend ans nil))))))
        (t (mv t
               (msg
                "Illegal LOOP$ Syntax.  The form ~X01 cannot be parsed as a ~
                 LOOP$ statement.  The symbol FOR must immediately follow the ~
                 LOOP$ and it does not here."
                stmt nil)))))

(defun make-plain-loop$-lambda-object (v spec carton)

; WARNING: Keep this function in sync with
; recover-loop$-ivars-and-conjoined-type-spec-exprs and vars-specs-and-targets.

; WARNING: This function must return a lambda$ expression.  There may be a
; temptation to simplify (lambda$ (x) (symbolp x)), say, to 'symbolp.  But we
; are counting on finding a quoted LAMBDA object in whatever the output
; produced here translates to.  See, for example, special-loop$-guard-clauses.
; We discuss the opportunity to simplify this special case of lambda$ further
; below.

; We generate a lambda$ for a plain loop with iteration variable v which has
; TYPE spec spec (possibly T, meaning no OF-TYPE was provided).  Carton is a
; finished carton for the guard and body of the lambda$ we're to create.
; (Reminder: this carton might be the untilc, the whenc, or the lobodyc,
; depending on which lambda$ we're making.)

; However, the lambda$ we generate always has the formal loop$-ivar even though
; a more ``natural'' choice of formal would be v.  The reason is that we want
; we want lambdas that beta-reduce to the identical terms to be syntactically
; identical after we rewrite (and thus beta reduce) their bodies.  I.e., we
; want (lambda$ (e) (foo e 23)) and (lambda$ (d) (foo d 23)) to translate to
; lambda objects that when they are rewritten are identical.  In fact, we'll
; produce
; (lambda$ (loop$-ivar) (let ((e loop$-ivar)) (foo e 23))) and
; (lambda$ (loop$-ivar) (let ((d loop$-ivar)) (foo d 23))).
; But then rewriting (beta reducing) the bodies will transform both to:
; (lambda$ (loop$-ivar) (foo loop$-ivar 23))

; We will use the untranslated guard and body in the lambda$ because they're
; prettier.  Even if we used the already-translated versions we wouldn't
; save time because they'd be translated (with no change) anyway.  The
; typical form we produce is

; (lambda$ (loop$-ivar)
;         (declare (type spec loop$-ivar)
;                  (xargs :guard (let ((e loop$-ivar)) uguard)))
;         (let ((e loop$-ivar))
;            ubody))

; But there may be no :guard.  Furthermore, when the lambda$ is translated it
; will may a :split-types at the end of the xargs and it will add an ignorable
; as the last of the edcls.

; To return to WARNING above, we have considered simplifying a special case,
; namely, replacing '(lambda (x) (fn x)) by 'fn provided fn is a tame function
; symbol of arity 1, x is a legal variable, and there is no TYPE spec and no
; guard.  We regard the latter function object as esthetically more pleasing
; than the lambda$.

; But we have decided against this on two grounds.  First, history generally
; teaches that it is a mistake to do ad hoc preprocessing for a theorem prover!
; There are too many opportunities to blow it.  The user can arrange such
; rewrites if he or she wants, with rules like

; (defthm simplify-sum$-fx
;   (implies (and (ok-fnp fn)
;                 (symbolp v))
;            (equal (sum$ `(lambda (,v) (,fn ,v)) lst)
;                   (sum$ fn lst)))
;   :hints (("Goal" :expand ((EV$ (LIST FN V)
;                                 (LIST (CONS V (CAR LST))))
;                            (TAMEP (CONS FN '(X)))
;                            (TAMEP (LIST FN V))))))

; Second, oddly enough, the attractive (sum$ 'sq lst) executes more slowly than
; the bulkier (sum$ '(lambda (v) (sq v)) lst), because the latter might be
; compiled.  For example, on a list of the first million positive integers, the
; former takes 0.42 seconds while the latter takes 0.13 seconds.  Here sq,
; which fixed its argument before squaring it, was guard verified with a guard
; of t.  So this aesthetic decision couldslow down execution!

; WARNING: See vars-specs-and-targets where we explore the form generated here
; to recover the type specs of the variables.

  (cond
   ((eq spec t)
    (cond
     ((equal (excart :translated :guard carton) *t*)
      `(lambda$
        (loop$-ivar)
        (let ((,v loop$-ivar))
          (declare (ignorable ,v))
          ,(excart :untranslated :body carton))))
     (t `(lambda$
          (loop$-ivar)
          (declare
           (xargs
            :guard (let ((,v loop$-ivar))
                     (declare (ignorable ,v))
                     ,(excart :untranslated :guard carton))))
          (let ((,v loop$-ivar))
            (declare (ignorable ,v))
            ,(excart :untranslated :body carton))))))
   ((equal (excart :translated :guard carton) *t*)
    `(lambda$
      (loop$-ivar)
      (declare (type ,spec loop$-ivar))
      (let ((,v loop$-ivar))
        (declare (ignorable ,v))
        ,(excart :untranslated :body carton))))
   (t `(lambda$
        (loop$-ivar)
        (declare (type ,spec loop$-ivar)
                 (xargs
                  :guard (let ((,v loop$-ivar))
                           ,(excart :untranslated :guard carton))))
        (let ((,v loop$-ivar))
          (declare (ignorable ,v))
          ,(excart :untranslated :body carton))))))

; Now we build up to making a fancy loop$ lambda object...

(defun translate-vsts (vsts name bindings cform ctx wrld)

; Vsts is a true-listp of 3-tuples of the form (var spec target), returned by
; parse-loop$.  Name is the symbol used for the formal holding the tuple of
; iteration variable values and is typically 'LOOP$-IVARS.  We check that each
; var is legal, that they're all distinct, and that each spec is legal type
; spec.  We return a list of ``translated vsts'' which are 4-tuples, (var spec
; type-guard target), where type-guard is the UNTRANSLATED guard expression
; (untranslated term) expressing the type spec relative to the corresponding
; car/cdr-component of name.

; For example, if the second element of vsts is (I INTEGER (IN LST)) and name
; is 'LOOP$-IVARS, the second element of our result is (I INTEGER (INTEGERP
; (CAR (CDR LOOP$-IVARS))) (IN LST)).  While that example suggests the
; type-guard produced is fully translated it is NOT and may have macros like
; AND or unquoted numbers in it.  E.g., if the type spec of the second element
; of vsts is (INTEGER 0 7), then the guard produced here is (AND (INTEGERP (CAR
; (CDR LOOP$-IVARS)))) (<= 0 (CAR (CDR LOOP$-IVARS))) (<= (CAR (CDR
; LOOP$-IVARS)) 7)).  Note the presence of the macros AND and <=.  We call this
; the ``lifted'' vst guard because instead of being expressed in terms of the
; iteration variable, e.g., I here, it is expressed in terms of elements of the
; given name, e.g., (CAR (CDR LOOP$-IVARS)).  This is perhaps doubly confusing
; because if the loop$ we're translating turns out to be a plain loop the
; lambda formal is not LOOP$-IVARS and is not a tuple to be car/cdr'd.  We lift
; the type guard as though for for a fancy loop$ because easier to produce the
; ``lifted type guard'' for the single-variable plain loop$.  In any case, do
; not treat this as a translated term, do not confuse it with the entire guard
; of the lambda (the guard of the lobody, for example, is not included in
; type-guard here, and do not think it is in terms of the lambda formal for the
; iteration variable(s)!

; Target, by the way, is one of three forms (IN x), (ON x), or (FROM-TO-BY i j
; k) and x, i, j, and k are untranslated expressions which remain untranslated
; but which MUST be part of the eventual translation of the loop$ statement
; from which vsts came, so that their well-formedness is checked by subsequent
; translation.

; Bindings is here just so we can return with trans-value.

  (cond
   ((endp vsts) (trans-value nil))
   (t (let* ((var (car (car vsts)))
             (spec (cadr (car vsts)))
             (guard (translate-declaration-to-guard spec `(CAR ,name) wrld))
             (target (caddr (car vsts))))
        (cond
         ((not (legal-variablep var))
          (trans-er+? cform var ctx "~x0 is not a legal variable name." var))
         ((assoc-eq var (cdr vsts))
          (trans-er+? cform var ctx "~x0 is bound more than once." var))
         ((null guard)
          (trans-er+? cform var ctx
                      "~x0 is not a legal type specification." spec))
         (t (trans-er-let*
             ((rest (translate-vsts (cdr vsts) `(CDR ,name) bindings cform ctx
                                    wrld)))
             (trans-value (cons (list var spec guard target) rest)))))))))

(defun make-bindings (vars var)
  (cond ((endp vars) nil)
        (t (cons `(,(car vars) (CAR ,var))
                 (make-bindings (cdr vars) `(CDR ,var))))))

(defun collect-tvsts-lifted-guards (tvsts)
  (cond
   ((endp tvsts) nil)
   ((not (eq (cadr (car tvsts)) t))
    (cons (caddr (car tvsts))
          (collect-tvsts-lifted-guards (cdr tvsts))))
   (t (collect-tvsts-lifted-guards (cdr tvsts)))))

(defun make-fancy-loop$-type-specs (tvsts)
  (cond
   ((endp tvsts) nil)
   ((not (eq (cadr (car tvsts)) t))
    (cons `(TYPE ,(cadr (car tvsts)) ,(car (car tvsts)))
          (make-fancy-loop$-type-specs (cdr tvsts))))
   (t (make-fancy-loop$-type-specs (cdr tvsts)))))

(defun lift-fancy-loop$-carton-guard (global-bindings local-bindings carton)

; The (:untranslated and :translated) guards in the carton are expressed in
; terms of the iteration variables and the global variables.  But the guard
; will be placed at the top of the lambda$, outside the LET that binds the
; iteration and global variables using the car/cdrs of the lambda$ formals,
; LOOP$-IVARS and LOOP$-GVARS.  So we have to ``lift'' the guard out.  Since we do this
; via substitution, we need to operate on the :translated guard.  But to try to
; keep the guard as attractive as possible we then flatten it and turn it into
; an UNTRANSLATED conjunction (sadly, with fully translated conjuncts).

  (let ((temp (flatten-ands-in-lit
               (sublis-var (append (pairlis$ (strip-cars global-bindings)
                                             (strip-cadrs global-bindings))
                                   (pairlis$ (strip-cars local-bindings)
                                             (strip-cadrs local-bindings)))
                           (excart :translated :guard carton)))))
    (cond ((null temp) T)
          ((null (cdr temp)) (car temp))
          (t (cons 'AND temp)))))

(defun make-fancy-loop$-lambda-object (tvsts carton free-vars)

; WARNING: Keep this function in sync with
; recover-loop$-ivars-and-conjoined-type-spec-exprs.

; WARNING: This function must return a lambda$ expression or quoted LAMBDA
; object.  There may be a temptation to simplify (lambda$ (x y) (foo x y)),
; say, to 'foo.  But we are counting on finding a quoted LAMBDA object in
; whatever the output produced here translates to.  See, for example,
; special-loop$-guard-clauses.

; Tvsts is ((v1 spec1 guard1 target1) (v2 spec2 guard2 target2) ...).
; Free-vars is a list, (u1 u2 ...), of distinct variables different from the
; vi.  The guardi are UNtranslated terms obtained by translating (TYPE speci
; vi) to a ``term'', except we don't use the variable symbol vi, we use the
; appropriate car/cdr nest around the variable symbol LOOP$-IVARS.  The guardi are
; untranslated terms.  For example, E.g., if speci is (INTEGER 0 7) then guardi
; would be (AND (INTEGERP v) (<= 0 v) (<= v 7)), where the v is a car/cdr nest.
; The macros AND and <= and unquoted numbers really are there!  Don't treat
; this like a term!

; Carton is the carton holding the guard and body of the lambda$ we're to
; create.  The guard and body are in terms of the vi and ui.

; We return a lambda$ expression of the following general form, where all caps
; mean the names are fixed and lower case means values come (somehow) from the
; arguments above.

; (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
;          (DECLARE (XARGS :GUARD guard))
;          (LET ((u1 (car LOOP$-GVARS))
;                (u2 (cadr LOOP$-GVARS))
;                (v1 (car LOOP$-IVARS))
;                (v2 (cadr LOOP$-IVARS))
;                ...
;                )
;            (DECLARE (TYPE spec1 v1)
;                     (TYPE spec2 v2)
;                     ...)
;            body))

; The formals of this lambda$ are fixed: LOOP$-GVARS and LOOP$-IVARS.

; The values of the ui and vi are bound in a LET that gets the values from
; LOOP$-GVARS and LOOP$-IVARS, as shown.

; We know that the vi are distinct legal variables because we check that when,
; in translate11-loop$, we translate the vst 3-tuples, produced by the loop$
; parser, into the tvsts 4-tuples.  We know the ui are legal variables because
; they were extracted from translated terms.  We know the ui are distinct from
; the vi because the ui are the free variables of body after explicitly
; removing the vi.

; Guard is the guard in the carton and is expressed in terms of car/cdr nest
; around LOOP$-GVARS and LOOP$-IVARS.


  (let* ((global-bindings (make-bindings free-vars 'loop$-gvars))
         (local-bindings (make-bindings (strip-cars tvsts) 'loop$-ivars))
         (guard `(and (true-listp loop$-gvars)
                      (equal (len loop$-gvars) ,(len free-vars))
                      (true-listp loop$-ivars)
                      (equal (len loop$-ivars) ,(len tvsts))
                      ,@(collect-tvsts-lifted-guards tvsts)

; This last conjunct is the :guard term, but it is in translated form because
; we need to apply a substitution to it to map the ui and vi to the
; corresponding components of LOOP$-GVARS and LOOP$-IVARS.

                      ,@(if (equal (excart :translated :guard carton)
                                   *t*)
                            nil
                            (list
                             (lift-fancy-loop$-carton-guard global-bindings
                                                            local-bindings
                                                            carton)))))
         (type-specs (make-fancy-loop$-type-specs tvsts))
         (ignorables (append (strip-cars global-bindings)
                             (strip-cars local-bindings))))
    `(lambda$ (loop$-gvars loop$-ivars)
              (declare (xargs :guard ,guard))
              (let (,@global-bindings
                    ,@local-bindings)

; WARNING: See vars-specs-and-targets where we explore the form generated here
; to recover the type specs of the iteration variables.  In particular, the
; function recover-type-spec-exprs is used to dig out the type-specs from the
; nested check-dcl-guardian expressions laid down by translating a (LET (...)
; (DECLARE (TYPE ...) ...) ...).  Note that the global vars cannot possibly
; have type specifications because the type-specs mentions only the iteration
; vars, so even though the global bindings are laid down first above, the
; type-specs in the declare below concern only the ivars.

; Note: We don't know that every local and/or global is actually used, so we
; declare them all ignorable in this LET form.  Furthermore, we know ignorables
; is non-empty even if type-specs is empty.

                ,@`((declare ,@type-specs
                             (ignorable ,@ignorables)))
                ,(excart :untranslated :body carton)))))

(defun make-plain-loop$ (v spec target untilc whenc op lobodyc)

; This function handles plain loop$s, e.g., where there a single iteration
; variable (no AS clauses) and no other variables mentioned in the until, when,
; or body.

; (LOOP FOR v OF-TYPE spec target UNTIL untilx WHEN whenx op bodyx)

; Of course, spec may be t meaning none was provided, the untilc and/or whenc
; cartons may be nil meaning no such clause was provided.

  (let* ((target1 (case (car target)
                    (IN (cadr target))
                    (ON `(tails ,(cadr target)))
                    (otherwise target)))
         (target2 (if untilc
                      `(until$
                        ,(make-plain-loop$-lambda-object v spec untilc)
                        ,target1)
                      target1))
         (target3 (if whenc
                      `(when$
                        ,(make-plain-loop$-lambda-object v spec whenc)
                        ,target2)
                      target2))
         (scion (cadr (assoc-eq op *loop$-keyword-info*))))

; Warning: Do not simplify the lambda$ or LAMBDA object in the first argument
; below!  See special-loop$-guard-clauses.

    `(,scion ,(make-plain-loop$-lambda-object v spec lobodyc)
             ,target3)))

(defun make-fancy-loop$-target (tvsts)
  (cond ((endp tvsts) nil)
        (t (cons (let ((target (cadddr (car tvsts))))
                   (case (car target)
                     (IN (cadr target))
                     (ON `(tails ,(cadr target)))
                     (otherwise target)))
                 (make-fancy-loop$-target (cdr tvsts))))))

(defun make-fancy-loop$ (tvsts untilc until-free-vars
                               whenc when-free-vars
                               op
                               lobodyc lobody-free-vars)

; This handles fancy loop$s, where there is one or more AS clauses and/or where
; the until, when, or body expressions contain variables other than the
; iteration variables.  A full-featured example would be:

; (LOOP FOR v1 OF-TYPE spec1 target1
;       AS v2 OF-TYPE spec2 target2
;       ...
;       UNTIL :guard until-guard until-body
;       WHEN :guard when-guard when-body
;       op
;       :guard lobody-guard lobody-body)

; The tvsts are 4-tuples (var spec spec-term target) and spec may be T meaning
; (probably) no spec was provided.  The untilc, whenc, and lobodyc are the
; respective cartons, but the untilc and whenc ``cartons'' may be nil meaning
; no such clause was provided.  The ...-free-vars are the vars in the
; respective cartons minus the iteration vars (named in the tvsts).

; The basic semantics of a fancy loop$ is suggested by that for a plain loop$
; except we loop$-as together all the targets, use fancy rather than plain
; lambda$ expressions, and use the fancy scions, like sum$+, instead of the
; plain ones.

  (let* ((target1 `(loop$-as (list ,@(make-fancy-loop$-target tvsts))))
         (target2 (if untilc
                      `(until$+
                        ,(make-fancy-loop$-lambda-object
                          tvsts untilc until-free-vars)
                        (list ,@until-free-vars)
                        ,target1)
                      target1))
         (target3 (if whenc
                      `(when$+
                        ,(make-fancy-loop$-lambda-object
                          tvsts whenc when-free-vars)
                        (list ,@when-free-vars)
                        ,target2)
                      target2))
         (scion+ (caddr (assoc-eq op *loop$-keyword-info*))))

; Warning: Do not simplify the lambda$ or LAMBDA object in the first argument
; below!  See special-loop$-guard-clauses.

    `(,scion+
      ,(make-fancy-loop$-lambda-object
        tvsts lobodyc lobody-free-vars)
      (list ,@lobody-free-vars)
      ,target3)))

(defun remove-loop$-guards (args)

; Our loop$ allows such forms as

; (loop$ for x in lst until :guard xxx p when :guard xxx q sum :guard xxx r)

; where the :guard clauses are optional and can only follow UNTIL, WHEN, and
; loop$ ops in *loop$-keyword-info*.  This function removes the :guard xxx
; entries.

; Warning: It is critical that translate prohibit such forms as

; (loop$ for v in lst UNTIL :guard collect v)
; (loop$ for v in lst WHEN :guard collect v)
; (loop$ for v in lst COLLECT :guard)

; even though the corresponding CLTL loop statements are legal.  The reason we
; must prohibit these is so that this function can easily strip out ... :guard
; expr ... without changing the semantics of the CLTL loop.  If (loop$ for v in
; lst COLLECT :guard) were allowed, then the raw Lisp loop$ macro would
; transform it to (loop$ for v in lst COLLECT nil), which is incorrect.  For
; what it's worth, the user wishing to write these prohibited loop$ statements
; could merely use ':guard instead of :guard.

; Note: This function is deceptively subtle because it doesn't re-parse args
; (which is the tail of a successfully parsed loop$ statement).  It just finds
; the left-most UNTIL, WHEN, and op followed by :GUARD and delete the :GUARD
; and the next element!  But of course the user is free to choose arbitrary
; legal variable names and those arbitrary symbols can appear where expressions
; are expected.  E.g., this is a legal loop$

; (loop$ for until in until until until collect until).

; So can the user maliciously create an ``... until :guard x ...'' in a
; well-formed loop$ without that subsequence actually being a guarded until
; clause?  If so, this function would remove :guard and x, probably rendering
; the statement ill-formed.

; We think the answer is no.  Every freely chosen variable or expression MUST
; be followed by a loop$ reserved word, e.g., ``for v IN lst AS ...''.  So no
; maliciously inserted expression, UNTIL, can be followed by :GUARD,
; ... except...  in our optional provision for :guards where two freely chosen
; expressions in a row may occur, e.g., ... until :guard <expr1> <expr2> ...,
; as in

; (loop$ for v in lst until :guard UNTIL :GUARD collect v)  [1]

; Here the UNTIL is the guard and :GUARD is the until-test.  This strange but
; legal form is transformed by this function into

; (loop$ for v in lst until :guard collect v)               [2]

; But [2] is properly transformed because we just deleted the guard and left
; the test.  So it's crucial (but almost natural) that this function sweep from
; left-to-right.  If it found the ``UNTIL :GUARD collect'' first and removed
; the ``:GUARD collect'' we'd be screwed:

; (loop$ for v in lst until :guard UNTIL v)                [3]

; [3] is ill-formed CLTL.

  (cond ((endp args) nil)
        ((and (symbolp (car args))
              (or (symbol-name-equal (car args) "UNTIL")
                  (symbol-name-equal (car args) "WHEN")
                  (assoc-symbol-name-equal (car args) *loop$-keyword-info*))
              (eq (cadr args) :GUARD))
         (cons (car args)
               (cons (cadddr args)
                     (remove-loop$-guards (cddddr args)))))
        (t (cons (car args)
                 (remove-loop$-guards (cdr args))))))

#-acl2-loop-only
(defvar *hcomp-loop$-alist* nil)

#-acl2-loop-only
(defmacro loop$ (&whole loop$-form &rest args)
  (let ((term (or (loop$-alist-term loop$-form
                                    *hcomp-loop$-alist*)
                  (loop$-alist-term loop$-form
                                    (global-val 'loop$-alist
                                                (w *the-live-state*))))))
    `(cond (*aokp* (loop ,@(remove-loop$-guards args)))
           (t ,(or term
                   '(error "Unable to translate loop$ (defun given directly ~
                            to raw Lisp?)."))))))

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

(defun translate11-var-or-quote-exit
  (x term stobjs-out bindings known-stobjs flet-alist
     cform ctx wrld state-vars)

; Term is the translation of x and we know term is a variable symbol or a
; QUOTEed evg.  If term is a variable symbol, it may be a stobj name.  We wish
; to return term as the result of translation, but must first consider the
; specified stobjs-out.  Stobjs-out is fully dereferenced.  So there are three
; cases: (1) we don't care about stobjs-out, (2) stobjs-out tells us exactly
; what kind of output is legal here and we must check, or (3) stobjs-out is an
; unknown but we now know its value and can bind it.

; Note: We pass in the same arguments as for translate11 (except for term which
; is the result of translating x) just for sanity.  We don't use two of them:

  (declare (ignore flet-alist state-vars))
  (cond
   ((eq stobjs-out t) ;;; (1)
    (trans-value term))
   ((consp stobjs-out) ;;; (2)
    (cond
     ((cdr stobjs-out)
      (trans-er+? cform x
                  ctx
                  "One value, ~x0, is being returned where ~x1 values were ~
                   expected."
                  x (length stobjs-out)))
     ((and (null (car stobjs-out))
           (stobjp term known-stobjs wrld))
      (trans-er+? cform x
                  ctx
                  "A single-threaded object, namely ~x0, is being used where ~
                   an ordinary object is expected."
                  term))
     ((and (car stobjs-out)
           (not (eq (car stobjs-out) term)))
      (cond
       ((stobjp term known-stobjs wrld)
        (trans-er+? cform x
                    ctx
                    "The single-threaded object ~x0 is being used where the ~
                     single-threaded object ~x1 was expected."
                    term (car stobjs-out)))
       (t
        (trans-er+? cform x
                    ctx
                    "The ordinary object ~x0 is being used where the ~
                     single-threaded object ~x1 was expected."
                    term (car stobjs-out)))))
     (t (trans-value term))))
   (t ;;; (3)
    (trans-value term
                 (translate-bind
                  stobjs-out
                  (list (if (stobjp term known-stobjs wrld)
                            term
                            nil))
                  bindings)))))

(defun weak-badge-userfn-structure-alistp (x)

; This function checks that x is a true-list of elements (weakly) of the form
; made by make-badge-userfn-structure-tuple and that the warrantp and badge
; slots are occupied by a boolean and a (weakly formed) apply$-badge.  This
; function must be in :logic mode and guard verified for use in
; remove-guard-holders.  We do the verify-termination in
; books/system/remove-guard-holders.lisp.

  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (weak-badge-userfn-structure-tuplep (car x))
                (symbolp (car (car x)))
                (booleanp (access-badge-userfn-structure-tuple-warrantp (car x)))
                (weak-apply$-badge-p
                 (access-badge-userfn-structure-tuple-badge (car x)))
                (weak-badge-userfn-structure-alistp (cdr x))))))

(defun ilks-plist-worldp (wrld)
  (declare (xargs :guard t))
  (and (plist-worldp wrld)
       (let ((tbl (fgetprop 'badge-table 'table-alist
                            nil wrld)))
         (and (alistp tbl)
              (weak-badge-userfn-structure-alistp
               (cdr (assoc-equal :badge-userfn-structure
                                 tbl)))))))

(defun ilks-per-argument-slot (fn wrld)

; This function is used by translate11 to keep track of the required ilk of
; each actual expression being translated.  The ``ilks'' we return include an
; odd non-ilk.  In particular, we give the first arg of APPLY$ an ``ilk'' of
; :FN? instead of :FN.  APPLY$ is allowed looser restrictions on its :fn args
; for purposes of translation.  See the Explanation of a Messy Restriction on
; :FN Slots in translate11.

; FYI: Fn here can be any function symbol, e.g., an unbadged :program mode
; function, because input to the ACL2 read-eval-print loop calls translate on
; every expression typed.  Furthermore, get-badge returns nil on unbadged
; functions of any mode as well as on apply$ primitives and even on apply$ boot
; functions like apply$ which have non-trivial badges.  It just handles apply$
; ``userfns.''  But ilks-per-argument-slot must handle all function symbols.

; All symbols on which get-badge returns nil are here assigned nil as
; the list of ilks, which is treated as a list of n nils, meaning for current
; purposes that translate allows anything but lambda$.

; A consequence of this default is that translate cannot detect the difference
; between a lambda$, say, encountered in an ordinary slot versus one
; encountered in a slot of unknown ilk in a call of an unbadged function.  It
; will just report an illegal occurrence of lambda$.

; Historical Note: Ideally, we would return a list of ilks corresponding to the
; formals of fn, with some list of pseudo-ilks like (:unknown :unknown ...) for
; unbadged fns.  If translate11 always received one of the ``ilks'' :FN, :EXPR,
; NIL, or :UNKNOWN then it could distinguish lambda$s passed into
; known-inappropriate slots from lambda$s passed into unknown slots of unbadged
; functions, thereby possibly alerting the user that defwarrant ought to be
; called on the offending function.

; But this ideal spec would require us to find the badge (or ``pseudo-badge''
; for unbadged functions) of every function encountered by translate11.  To
; determine if a function has a badge we have to scan the 800+ entries in
; *badge-prim-falist*, the six apply$ boot fns, and the entries in the
; :badge-userfn-structure component of the badge-table.  But the only functions
; with non-trivial ilks are apply$ and ev$ among the boot functions and perhaps
; some functions among the userfns.  All other fns are either tame or unbadged
; and by returning nil for those we don't have to search through the primitives
; as we would to implement the ideal spec.

; While this spec is faster to implement than the ideal one it prevents
; translate from distinguishing supplying a lambda$ in an ordinary slot versus
; supplying it to an unbadged function.  Oh well!

  (declare (xargs :guard (and (symbolp fn)
                              (ilks-plist-worldp wrld))))
  (cond ((eq fn 'apply$) '(:FN? NIL)) ; Note change of :FN to :FN?
        ((eq fn 'ev$) '(:EXPR NIL))
        (t (let ((bdg (get-badge fn wrld)))
             (cond
              ((null bdg) ; unbadged fn
               nil)
              (t (let ((ilks (access apply$-badge bdg :ilks)))
                   (if (eq ilks t) ; tame userfn
                       nil
                     ilks))))))))

(mutual-recursion

(defun quote-normal-form1 (form)

; This variant of (sublis-var nil form) avoids looking inside HIDE calls.

  (declare (xargs :guard (pseudo-termp form)))
  (cond ((or (variablep form)
             (fquotep form)
             (eq (ffn-symb form) 'hide))
         (mv nil form))
        (t (mv-let (changedp lst)
                   (quote-normal-form1-lst (fargs form))
                   (let ((fn (ffn-symb form)))
                     (cond (changedp (mv t (cons-term fn lst)))
                           ((and (symbolp fn) ; optimization
                                 (quote-listp lst))
                            (cons-term1-mv2 fn lst form))
                           (t (mv nil form))))))))

(defun quote-normal-form1-lst (l)

; This variant of (sublis-var1-lst nil form) avoids looking inside HIDE calls.

  (declare (xargs :guard (pseudo-term-listp l)))
  (cond ((endp l)
         (mv nil l))
        (t (mv-let (changedp1 term)
                   (quote-normal-form1 (car l))
                   (mv-let (changedp2 lst)
                           (quote-normal-form1-lst (cdr l))
                           (cond ((or changedp1 changedp2)
                                  (mv t (cons term lst)))
                                 (t (mv nil l))))))))
)

(defun quote-normal-form (form)

; This variant of (sublis-var nil form) avoids looking inside HIDE calls.  It
; is used for putting form into quote-normal form so that for example if form
; is (cons '1 '2) then '(1 . 2) is returned.  The following two comments come
; from the nqthm version of sublis-var.

;     In REWRITE-WITH-LEMMAS we use this function with the nil alist
;     to put form into quote normal form.  Do not optimize this
;     function for the nil alist.

;     This is the only function in the theorem prover that we
;     sometimes call with a "term" that is not in quote normal form.
;     However, even this function requires that form be at least a
;     pseudo-termp.

; We rely on quote-normal form for the return value, for example in calls of
; sublis-var in rewrite-with-lemma.  Quote-normal form may also be useful in
; processing :by hints.

  (declare (xargs :guard (pseudo-termp form)))
  (mv-let (changedp val)
          (quote-normal-form1 form)
          (declare (ignore changedp))
          val))

; The following is a complete list of the macros that are considered
; "primitive event macros".  This list includes every macro that calls
; install-event except for defpkg, which is omitted as
; explained below.  In addition, the list includes defun (which is
; just a special call of defuns).  Every name on this list has the
; property that while it takes state as an argument and possibly
; changes it, the world it produces is a function only of the world in
; the incoming state and the other arguments.  The function does not
; change the world as a function of, say, some global variable in the
; state.

; The claim above, about changing the world, is inaccurate for include-book!
; It changes the world as a function of the contents of some arbitrarily
; named input object file.  How this can be explained, I'm not sure.

; All event functions have the property that they install into state
; the world they produce, when they return non-erroneously.  More
; subtly they have the property that when the cause an error, they do
; not change the installed world.  For simple events, such as DEFUN
; and DEFTHM, this is ensured by not installing any world until the
; final STOP-EVENT.  But for compound events, such as ENCAPSULATE and
; INCLUDE-BOOK, it is ensured by the more expensive use of
; REVERT-WORLD-ON-ERROR.

(defun primitive-event-macros ()
  (declare (xargs :guard t :mode :logic))

; Warning: If you add to this list, consider adding to
; find-first-non-local-name and to the list in translate11 associated with a
; comment about primitive-event-macros.

; Warning: Keep this in sync with oneify-cltl-code (see comment there about
; primitive-event-macros).

; Note: This zero-ary function used to be a constant, *primitive-event-macros*.
; But Peter Dillinger wanted to be able to change this value with ttags, so
; this function has replaced that constant.  We keep the lines sorted below,
; but only for convenience.

; Warning: If a symbol is on this list then it is allowed into books.
; If it is allowed into books, it will be compiled.  Thus, if you add a
; symbol to this list you must consider how compile will behave on it
; and what will happen when the .o file is loaded.  Most of the symbols
; on this list have #-acl2-loop-only definitions that make them
; no-ops.  At least one, defstub, expands into a perfectly suitable
; form involving the others and hence inherits its expansion's
; semantics for the compiler.

; Warning: If this list is changed, inspect the following definitions,
; down through CHK-EMBEDDED-EVENT-FORM.  Also consider modifying the
; list *fmt-ctx-spacers* as well.

; We define later the notion of an embedded event.  Only such events
; can be included in the body of an ENCAPSULATE or a file named by
; INCLUDE-BOOK.

; We do not allow defpkg as an embedded event.  In fact, we do not allow
; defpkg anywhere in a blessed set of files except in files that contain
; nothing but top-level defpkg forms (and those files must not be compiled).
; The reason is explained in deflabel embedded-event-form below.

; Once upon a time we allowed in-package expressions inside of
; encapsulates, in a "second class" way.  That is, they were not
; allowed to be hidden in LOCAL forms.  But the whole idea of putting
; in-package expressions in encapsulated event lists is silly:
; In-package is meant to change the package into which subsequent
; forms are read.  But no reading is being done by encapsulate and the
; entire encapsulate event list is read into whatever was the current
; package when the encapsulate was read.

; Here is an example of why in-package should never be hidden (i.e.,
; in LOCAL), even in a top-level list of events in a file.

; Consider the following list of events:

; (DEFPKG ACL2-MY-PACKAGE '(DEFTHM SYMBOL-PACKAGE-NAME EQUAL))

; (LOCAL (IN-PACKAGE "ACL2-MY-PACKAGE"))

; (DEFTHM GOTCHA (EQUAL (SYMBOL-PACKAGE-NAME 'IF) "ACL2-MY-PACKAGE"))

; When processed in pass 1, the IN-PACKAGE is executed and thus
; the subsequent form (and hence the symbol 'IF) is read into package
; ACL2-MY-PACKAGE.  Thus, the equality evaluates to T and GOTCHA is a
; theorem.  But when processed in pass 2, the IN-PACKAGE is not
; executed and the subsequent form is read into the "ACL2" package.  The
; equality evaluates to NIL and GOTCHA is not a theorem.

; One can imagine adding new event forms.  The requirement is that
; either they not take state as an argument or else they not be
; sensitive to any part of state except the current ACL2 world.

  '(
     #+:non-standard-analysis defthm-std
     #+:non-standard-analysis defun-std
     add-custom-keyword-hint
     add-include-book-dir add-include-book-dir!
     add-match-free-override
     comp
     defabsstobj
     defattach
     defaxiom
     defchoose
     defconst
     deflabel
     defmacro
;    defpkg ; We prohibit defpkgs except in very special places.  See below.
     defstobj
     deftheory
     defthm
     defun
     defuns
     delete-include-book-dir delete-include-book-dir!
     encapsulate
     in-arithmetic-theory
     in-theory
     include-book
     logic
     mutual-recursion
     progn
     progn!
     program
     push-untouchable
     regenerate-tau-database
     remove-untouchable
     reset-prehistory
     set-body
     set-override-hints-macro
     set-prover-step-limit
     set-ruler-extenders
     table
     theory-invariant
     value-triple
     verify-guards
     verify-termination-boot-strap
     ))

(defconst *syms-not-callable-in-code-fal*

; At one time, the check in translate11 that uses hons-get on this fast-alist
; was implemented using member-eq, which probably explains why we excluded logic,
; program, set-prover-step-limit, and set-ruler-extenders from this check:
; doing so shortened the list without compromising the check, since expanding
; these macros generates a call of table, which is in (primitive-event-macros).
; We no longer have a need to make such a restriction.

  (make-fast-alist
   (pairlis$ (union-eq '(certify-book
                         defpkg
                         in-package
                         local
                         make-event
                         with-guard-checking-event
                         with-output
                         with-prover-step-limit)
                       (primitive-event-macros))
             nil)))

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
                                nil           ;;; ilks = '(nil ... nil)
                                nil           ;;; stobjs-out = '(nil ... nil)
                                bindings
                                known-stobjs
                                "in a DECLARE form in an FLET binding"
                                flet-alist form ctx wrld state-vars))
        (tbody (translate11 body
                            nil               ;;; ilk
                            new-stobjs-out
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
                       (remove-assoc-eq new-stobjs-out
                                        bindings))))))))))))))))))

(defun translate11-flet (x stobjs-out bindings known-stobjs flet-alist
                           ctx wrld state-vars)

; X is a form whose car is FLET.  When we checked in January 2019, only Allegro
; CL and CMUCL complained upon compilation if a function bound by an FLET is
; not called in the body: the former only with a warning, the latter with only
; a note.  Both messages are suppressed inside the ACL2 loop.  Therefore, we do
; not check that all bound functions are actually called in the body, and we do
; not support (declare (ignore (function ...))).

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
                          nil ; ilk
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

; Note: No stobj accessor or updater accepts functional arguments so we can use
; ilk = nil below.

                   (translate11 (cadr call) nil '(nil) bindings known-stobjs
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
                                            nil ; ilk
                                            (list (car bound-vars))
                                            bindings known-stobjs flet-alist
                                            x ctx wrld state-vars)))
                         (trans-value (list val))))
                       (t (translate11-lst (strip-cadrs (cadr x))
                                           nil ; ilks = '(nil nil ...)
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
                   (translate11 (car (last x))
                                nil
                                stobjs-out bindings known-stobjs
                                flet-alist x ctx wrld state-vars)))
                (tdcls (translate11-lst
                        (translate-dcl-lst edcls wrld)
                        nil ; ilks = '(nil nil ...)
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
                                        "The variable~#0~[ ~&0 is~/s ~&0 ~
                                         are~] not used in the body of the ~
                                         LET expression that binds ~&1.  But ~
                                         ~&0 ~#0~[is~/are~] not declared ~
                                         IGNOREd or IGNORABLE.  See :DOC ~
                                         set-ignore-ok."
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
                               nil
                               bound-stobjs-out
                               bindings
                               producer-known-stobjs
                               flet-alist x ctx wrld state-vars))
           (tdcls (translate11-lst (translate-dcl-lst edcls wrld)
                                   nil ; ilks = '(nil nil ...)
                                   (if (eq stobjs-out t)
                                       t
                                     nil) ;;; '(nil ... nil)
                                   bindings known-stobjs
                                   "in a DECLARE form in an MV-LET"
                                   flet-alist x ctx wrld state-vars))
           (tbody (if tbody0
                      (trans-value tbody0)
                    (translate11 (car (last x))
                                 nil
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

; Remember: The quoted lambda of wormholes are not related to apply$.

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

; Recall that wormhole's quoted lambdas are not related to apply$.  Wormhole's
; lambdas are always of length 3, so we just use lambda-formals and lambda-body
; above.

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
                            nil
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
                                stobjs-in-call)

; Here we carve out some code from translate11-call for case where both
; stobjs-out and stobjs-out2 are conses, so that we can invoke it twice without
; writing the code twice.  Msg is as described in translate11-lst.

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
                             (ilks-per-argument-slot fn wrld)
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

            (stobj-recognizer-p fn wrld)
            (translate11-lst args
                             nil ; ilks = '(nil)
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

(defun translate11-call (form fn args stobjs-out-x stobjs-out-fn bindings
                              known-stobjs msg flet-alist ctx wrld state-vars)

; We are translating (for execution, not merely theorems) a call of fn on args,
; where the length of args is the arity of fn in wrld.  Stobjs-out-x and
; stobjs-out-fn are respectively the expected stobjs-out from the present
; context and the stobjs-out from fn, already dereferenced.  Note that each of
; these is either a legitimate (true-list) stobjs-out or else a symbol
; representing an unknown stobjs-out.

; Msg is as described in translate11-lst.

; Note that for this call to be suitable, args has to satisfy the stobjs
; discipline of passing a stobj name to a stobjs-in position.  We take
; advantage of this requirement in stobjs-in-out1, for example.  So it is
; important that we do not call translate11-call on arbitrary lambdas, where an
; arg might not be a stobj name, e.g., ((LAMBDA (ST) ST) (UPDATE-FLD '2 ST)).

; We are tempted to enforce the call-arguments-limit imposed by Common Lisp.
; According to the HyperSpec, this constant has an implementation-dependent
; value that is "An integer not smaller than 50", and is "The upper exclusive
; bound on the number of arguments that may be passed to a function."  The
; limits vary considerably, and are as follows in increasing order.

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
    (alist-in-out stobjs-in-call stobjs-out-call)
    (stobjs-in-out fn args stobjs-out-fn known-stobjs wrld)

; Fn can be viewed as mapping stobjs-in-call to stobjs-out-call; see
; stobjs-in-out.

; In the absence of congruent stobjs, stobjs-in-call and stobjs-out-call are
; just the stobjs-in and (dereferenced) stobjs-out of fn.  But in general,
; alist-in-out associates each element of its domain, which is a stobj, with a
; congruent stobj, and stobjs-in-call and stobjs-out-call are the result of
; applying the mapping represented by alist-in-out to the stobjs-in and
; (dereferenced) stobjs-out of fn.

    (cond
     ((consp stobjs-out-x)
      (cond
       ((consp stobjs-out-call) ; equivalently: (consp stobjs-out-fn)
        (cond
         ((equal stobjs-out-x stobjs-out-call)

; Then we translate the arguments, where we view fn as mapping stobjs-in-call
; to stobjs-out-call; see stobjs-in-out.

          (translate11-call-1 form fn args bindings
                              known-stobjs msg flet-alist ctx wrld state-vars
                              stobjs-in-call))
         (t

; We are definitely in an error case.  That is because stobjs-in-out has
; adjusted the stobjs-in of fn to match args (producing stobjs-in-call), and
; then adjusted stobjs-out-fn accordingly to yield stobjs-out-call, which
; disagrees with the expected stobjs-out-x.  Our job now is to produce a
; helpful error message, blaming the problem either on the inputs or on the
; output.

; Our plan is for the error message to blame an output mismatch if that can be
; determined, and otherwise to blame an input mismatch.  There are many
; examples in community books file books/demos/congruent-stobjs-input.lsp, in
; the section labeled: "Tests referenced in ACL2 source function
; translate11-call".

          (trans-er-let*
           ((tform (if (match-stobjs stobjs-out-x stobjs-out-fn wrld nil)

; Then we cannot in good conscience blame an output mismatch, so we attempt to
; blame an input mismatch.  If there is no error translating inputs, then we
; will blame an output mismatch after all, as in the following example, labeled
; (4) in community books file books/demos/congruent-stobjs-input.lsp.

;   (defun foo (s$1 s$2)
;     (declare (xargs :stobjs (s$1 s$2)))
;     (let ((s$1 (update-fld1 0 s$2)))
;       (mv s$1 s$2)))

; This is a rather interesting case since stobjs-out-call, which is (s$2),
; doesn't match the expected stobjs-out, (s$1), even though that that expected
; stobjs-out does equal (and therefore match) the stobjs-out of update-fld1.
; So what is truly the error?  Is it that the argument s$2 should be s$1, or is
; it that the output s$1 should be s$2?  It seems perhaps most intuitive to
; blame the output over the input; anyhow, that's what we do here!

                       (translate11-call-1 form fn args bindings
                                           known-stobjs msg flet-alist
                                           ctx wrld state-vars
                                           stobjs-in-call)

; Otherwise the output signatures are definitely a mismatched pair, so don't
; even try to get an error by translating the arguments with translate11-call,
; as we prefer reporting the output signature error.  In this case we don't
; care about the second and third values (normally a term and bindings),
; because we are about to cause an error.

                     (mv nil nil nil))))
           (trans-er+ form ctx
                      "It is illegal to invoke ~@0 here because of a ~
                         signature mismatch.  This function call returns a ~
                         result of shape ~x1~@2 where a result of shape ~x3 ~
                         is required."
                      (if (consp fn) msg (msg "~x0" fn))
                      (prettyify-stobjs-out stobjs-out-call)
                      (if alist-in-out ; always true here?
                          " (after accounting for the replacement of some ~
                             input stobjs by congruent stobjs)"
                        "")
                      (prettyify-stobjs-out stobjs-out-x))))))
       (t

; In this case, stobjs-out-call and (equivalently) stobjs-out-call are symbols,
; while stobjs-out-x is a cons.

; The following example illustrates the call of translate-bind below.  Suppose
; that st1 and st2 are congruent stobjs; stobjs-out-x is (st2); fn is f; f has
; input signature (st1); and args is (st2), i.e., we are considering the call
; (f st2).  Then alist-in-out is ((st1 . st2)).  We apply the mapping,
; alist-in-out, in reverse to stobjs-out-x = (st2), to deduce that the
; stobjs-out of fn should be (st1).  Note that if we we then apply alist-in-out
; to this computed stobjs-out of fn, (st1), then we get (st2), which is the
; expected stobjs-out-x.

        (let ((bindings
               (translate-bind stobjs-out-fn
                               (if (consp alist-in-out) ; optimizationa
                                   (apply-inverse-symbol-alist alist-in-out
                                                               stobjs-out-x
                                                               nil)
                                 stobjs-out-x)
                               bindings)))
          (trans-er-let*
           ((args (translate11-lst args
                                   (ilks-per-argument-slot fn wrld)
                                   stobjs-in-call
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)))
           (trans-value (fcons-term fn args)))))))
     ((consp stobjs-out-call) ; equivalently: (consp stobjs-out-fn)

; In this case we know that stobjs-out-x is a symbol representing the expected
; stobjs-out.  So we bind that symbol to the computed stobjs-out, which is
; stobjs-out-call.

      (let ((bindings
             (translate-bind stobjs-out-x stobjs-out-call bindings)))
        (trans-er-let*
         ((targs (trans-or
                  (translate11-lst (if (eq fn 'wormhole-eval)
                                       (list *nil* *nil* (nth 2 args))
                                     args)
                                   (ilks-per-argument-slot fn wrld)
                                   stobjs-in-call
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)

; See the comment above about applying a stobj recognizer to be applied to an
; ordinary object.

                  (stobj-recognizer-p fn wrld)
                  (translate11-lst args
                                   (ilks-per-argument-slot fn wrld)
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
     (t ; both stobjs-out-x and stobjs-out-call are symbols
      (let ((bindings

; If the stobjs-in of fn is compatible with args, but only when mapping at
; least one input stobj to a congruent stobj, then we cannot simply bind
; stobjs-out-fn to the symbol, stobjs-out-x.  For example, suppose st1 and st2
; are congruent stobjs and we are defining a function (f st1 st2) in a context
; where we do not know the expected result signature, say, stobjs-out-x is a
; symbol, g.  Consider the call (f st2 st1).  Then if ultimately the stobjs-out
; of f is (mv st1 st2), then the stobjs-out of g will be that of the call (f
; st2 st1), which is (mv st2 st1).  There is no way currently to extend
; bindings to indicate that f and g have reversed stobjs-out; the only way to
; extend here is to bind f to g to indicate that f and g have the same
; stobjs-out, and that would be incorrect in this case.

             (if (consp alist-in-out)
                 bindings
               (translate-bind stobjs-out-fn stobjs-out-x bindings))))
        (trans-er-let*
         ((args (translate11-lst args
                                 (ilks-per-argument-slot fn wrld)
                                 stobjs-in-call
                                 bindings known-stobjs
                                 msg flet-alist form ctx wrld state-vars)))
         (trans-value (fcons-term fn args))))))))

(defun translate11-lambda-object
  (x stobjs-out bindings known-stobjs flet-alist cform ctx wrld state-vars
     allow-counterfeitsp)

; Warning: The name of this function is a bit of a misnomer.  X is of the form
; (LAMBDA vars dcls* body) or (LAMBDA$ vars dcls* body) and is presumed to be
; destined for apply$.  The car of X is LAMBDA (or LAMBDA$), not QUOTE!

; See the Essay on Lambda Objects and Lambda$ for a discussion of these
; concepts.

; The LAMBDA case will have been found inside a QUOTE and the LAMBDA$ case will
; be translated into a lambda object.  The error-free result will satisfy
; well-formed-lambda-objectp.

; In the case of LAMBDA$, we translate the components and combine multiple
; DECLAREs into a single DECLARE with the various parts listed in the same
; order.  We insist that there is at most one XARGS and that it have only the
; :GUARD and/or :SPLIT-TYPES keys.  A lambda object must look exactly like it
; came from a translated LAMBDA$, including having exactly one DECLARE form.
; We return the translated version of x (in the trans-value format) or cause a
; translate error (in trans-er format).

; We hons-copy the resulting lambda object.  Before we did this, it was
; possible that when looking up a lambda object in the cl-cache, the result
; succeeded with an object EQUAL to it that was not EQ.  Here is an example.

;   (defun sum-doubles (lst)
;     (declare (xargs :guard (integer-listp lst)
;                  :verify-guards nil))
;     (loop$ for x of-type integer in lst sum (+ x x)))
;   (make-event `(defconst *m* ',(loop$ for i from 1 to 10000000 collect i)))
;   ; The following reports:
;   ; 0.92 seconds realtime, 0.93 seconds runtime
;   (time$ (sum-doubles *m*))
;   (verify-guards sum-doubles
;     :hints (("Goal"
;              :in-theory (enable apply$ badge)
;              :expand ((ev$ '(binary-+ x x)
;                            (list (cons 'x (car lst))))))))
;   (u)
;   ; The following reports about double the previous time.
;   (time$ (sum-doubles *m*))
;   ; 2.02 seconds realtime, 2.02 seconds runtime

; Our solution is to apply hons-copy (called just above) so that the translated
; lambda object is unique.  Thus, we now call hons-equal-lite where we formerly
; called equal in fetch-cl-cache-line.  It may seem tempting to call eq there,
; but lambdas in raw Lisp function bodies are very unlikely to be honsed.  We
; might sometime try to fix this by somehow incorporating hons-copy into the
; raw Lisp definition of lambda$.

  (cond
   ((and (eq stobjs-out t)
         (eq (car x) 'LAMBDA))

; Since we are not translating for execution, our intent is simply to let
; normal logic run its course.

    (translate11-var-or-quote-exit
     x
     (hons-copy `(QUOTE ,x))
     stobjs-out bindings known-stobjs flet-alist
     cform ctx wrld state-vars))
   ((and (or (eq (car x) 'LAMBDA)
             (eq (car x) 'LAMBDA$))
         (true-listp x)
         (<= 3 (length x)))
    (let* ((lambda-casep (eq (car x) 'LAMBDA))
           (allow-free-varsp nil)
           (vars (if allow-free-varsp
                     (butlast (cadr x) 1)
                   (cadr x)))
           (dcls (butlast (cddr x) 1))
           (body (car (last x)))
           (stobjs-out-simple (if (eq stobjs-out t)
                                  t
                                '(nil))))
      (cond
       ((not (arglistp vars))
        (trans-er+? cform x
                    ctx
                    "The second element of a well-formed LAMBDA object or ~
                     lambda$ term must be a true list of distinct legal ~
                     variable symbols and ~x0 is not.  ~@1"
                    vars
                    *gratuitous-lambda-object-restriction-msg*))
       (t
        (trans-er-let*
         ((edcls (edcls-from-lambda-object-dcls dcls x bindings
                                                cform ctx wrld)))

; The :GUARD in the edcls is untranslated and may or may not include the TYPEs,
; depending on split-types below.  If split-types is T then the guard must
; include (actually must just imply but we check syntactic inclusion) the TYPEs
; and otherwise the TYPEs will be automatically added to the guard by
; get-guards.  But split-types can be NIL only in the lambda$ case.

; Note on the handling of bindings.  We save the incoming value of bindings in
; binding0 below and restore it after translating the guard.  But we don't
; restore it after subsequently translating the body and that might at first
; seem to be an oversight.  Here's the explanation.

; The call of translate11 on the guard has bindings = nil.  So the bindings
; passed back kind of have nothing to do with the input bindings passed into
; translate11-lambda-object.  So it's good that they're thrown away, and then
; bindings is restored to bindings0.

; On the other hand, those input bindings are passed to the call of translate11
; on the lambda$ body.  If perchance they are extended, then it's good to pass
; back that extension to the rest of the translation process.

; In practice, we do not believe that bindings would be extended by the call of
; translate11 on the lambda$ body.  That's because the only extension would be
; to bind the function(s) being defined, which is impossible because the lambda
; body must call only badged functions and defined functions aren't yet badged.
; But just in case, it's good to pass back the new bindings.

         (let* ((bindings0 bindings)
                (fives (list (list :lambda vars nil edcls body)))
                (xargs (assoc-eq 'XARGS edcls))
                (split-types
                 (or lambda-casep
                     (cadr (assoc-keyword :SPLIT-TYPES (cdr xargs)))))
                (guard1-tail (assoc-keyword :guard (cdr xargs)))

; Guard1 is the the actual, untranslated expression the user supplied with
; XARGS :GUARD.

                (guard1 ; only valid if guard1-tail is non-nil
                 (cadr guard1-tail))

; Guard2 is the untranslated guard expression generated by possibly (according
; to :split-types) conjoining in the TYPE expressions.

                (guard2 (and (not lambda-casep) ; optimization (else, not used)
                             (car (get-guards
                                   fives
                                   (list split-types) ; per 5-tuple above
                                   nil ; collect merged types and guards
                                   wrld))))
                (guard (if lambda-casep
                           (if (null guard1-tail)
                               *T*
                               guard1)
                           guard2))
                (ignores (ignore-vars edcls))
                (ignorables (ignorable-vars edcls)))
           (trans-er-let*
            ((tguard (if lambda-casep
                         (if (termp guard wrld)
                             (trans-value guard)
                           (trans-er+?
                            cform x
                            ctx
                            "The guard of a LAMBDA object must be a fully ~
                             translated term and ~x0 is not.  ~@1"
                            guard
                            *gratuitous-lambda-object-restriction-msg*))
                         (translate11 guard
                                      nil    ; ilk
                                      stobjs-out-simple
                                      nil    ; bindings
                                      nil    ; known-stobjs
                                      nil    ; flet-alist
                                      cform ctx wrld state-vars))))
            (let* ((bindings bindings0) ; Restore original bindings
                   (type-exprs (if split-types
                                   (flatten-ands-in-lit-lst
                                    (get-guards2 edcls '(TYPES) t wrld nil nil))
                                 nil))
                   (guard-conjuncts (if split-types
                                        (flatten-ands-in-lit tguard)
                                      nil))
                   (missing-type-exprs (if split-types
                                           (set-difference-equal
                                            type-exprs
                                            guard-conjuncts)
                                         nil))
                   (free-vars-guard (set-difference-eq (all-vars tguard) vars)))
              (cond
               ((and free-vars-guard (not allow-free-varsp))
                (trans-er+? cform x
                            ctx
                            "The guard of a LAMBDA object or lambda$ term may ~
                             contain no free variables.  This is violated by ~
                             the guard ~x0, which uses the variable~#1~[~/s~] ~
                             ~&1 which ~#1~[is~/are~] not among the formals. ~
                             ~@2"
                            (untranslate tguard t wrld)
                            free-vars-guard
                            *gratuitous-lambda-object-restriction-msg*))
               (missing-type-exprs

; We know by construction that missing-type-exprs will be nil for LAMBDA$ with
; :SPLIT-TYPES NIL, so our error message talks about lambda objects or
; :SPLIT-TYPE T situations only.

                (trans-er+? cform x
                            ctx
                            "In a LAMBDA object or a lambda$ term with ~
                             :SPLIT-TYPES T, every TYPE expression derived ~
                             from the TYPE specifiers must be an explicit ~
                             conjunct in the :GUARD, and the guard ~x0 is ~
                             missing ~&1.  ~@2"
                            tguard ; (untranslate tguard t wrld)
                            missing-type-exprs
                            *gratuitous-lambda-object-restriction-msg*))
               (t
                (trans-er-let*
                 ((tbody
                   (if lambda-casep
                       (if (termp body wrld)
                           (if (and (not allow-counterfeitsp)
                                    (lambda$-bodyp body))
                               (trans-er+?
                                cform x
                                ctx
                                "The body of a LAMBDA object may not be of ~
                                 the form (RETURN-LAST 'PROGN '(LAMBDA$ ...) ~
                                 ...) because that idiom is used to flag ~
                                 LAMBDA objects generated by translating ~
                                 lambda$ terms. But you wrote a LAMBDA object ~
                                 with body ~x0.  ~@1"
                                body
                                *gratuitous-lambda-object-restriction-msg*)
                               (trans-value body))
                           (trans-er+?
                            cform x
                            ctx
                            "The body of a LAMBDA object must be in fully ~
                             translated form and ~x0 is not.  ~@1"
                            body
                            *gratuitous-lambda-object-restriction-msg*))
                       (translate11 body
                                    nil    ; ilk
                                    stobjs-out-simple
                                    bindings
                                    nil ; known-stobjs

; It is perhaps a bit subtle why we use flet-list = nil here.  The function
; apply$-lambda can reduce a call of apply$ on a lambda object to a
; corresponding call of apply on a suitable function.  But what is that
; function?  In Common Lisp, flet creates a lexical environment, and lambda --
; the macro, not the quoted symbol -- creates a closure that uses that lexical
; environment: for example, (flet ((f (x) x)) (apply (lambda (x) (f x)) (list
; 3))) evaluates to 3, regardless of the global definition of f.  So if we used
; closures, we could be in trouble here using nil for flet-alist!  However,
; instead we build the function to be apply'd by compiling the lambda object
; outside the flet lexical environment.  See
; make-compileable-guard-and-body-lambdas and its uses (where its outputs are
; compiled).

; By the way: in Common Lisp, (flet ((f (x) x)) (apply 'f (list 3))) evaluates
; to the same result as (apply 'f (list 3)); that is, the flet binding is
; ignored.

                                    nil ; flet-alist
                                    cform ctx wrld state-vars))))
                 (let* ((body-vars (all-vars tbody))
                        (free-vars-body (set-difference-eq body-vars vars))
                        (used-ignores
                         (and lambda-casep
                              (intersection-eq body-vars ignores)))
                        (unused-not-ignorables
                         (and lambda-casep
                              (set-difference-eq
                               (set-difference-eq
                                (set-difference-eq vars body-vars)
                                ignores)
                               ignorables))))
                   (cond
                    ((and free-vars-body (not allow-free-varsp))
                     (trans-er+? cform x
                                 ctx
                                 "The body of a LAMBDA object or lambda$ term ~
                                  may contain no free variables.  This is ~
                                  violated by the body ~x0, which uses the ~
                                  variable~#1~[~/s~] ~&1 which ~#1~[is~/are~] ~
                                  not among the formals.  ~@2"
                                 (untranslate tbody nil wrld)
                                 free-vars-body
                                 *gratuitous-lambda-object-restriction-msg*))
                    (used-ignores
                     (trans-er+? cform x
                                 ctx
                                 "The body of a LAMBDA object may not use a ~
                                  variable declared IGNOREd.  This is ~
                                  violated by the body ~x0, which uses the ~
                                  variable~#1~[~/s~] ~&1 which ~#1~[is~/are~] ~
                                  declare IGNOREd. ~@2"
                                 (untranslate tbody nil wrld)
                                 used-ignores
                                 *gratuitous-lambda-object-restriction-msg*))
                    (unused-not-ignorables
                     (trans-er+? cform x
                                 ctx
                                 "Every formal variable that is unused in the ~
                                  body of a LAMBDA object must be declared ~
                                  IGNOREd or IGNORABLE.  This is violated by ~
                                  the body ~x0, which fails to use the ~
                                  variable~#1~[~/s~] ~&1 which ~#1~[is~/are~] ~
                                  not declared IGNOREd or IGNORABLE. ~@2"
                                 (untranslate tbody nil wrld)
                                 unused-not-ignorables
                                 *gratuitous-lambda-object-restriction-msg*))
                    (t (let ((bad-fns (all-unbadged-fnnames tbody wrld nil)))
                         (cond
                          (bad-fns
                           (trans-er+
                            x ctx
                            "The body of a LAMBDA object, lambda$ term, or ~
                             loop$ statement should be fully badged but ~&0 ~
                             ~#0~[is~/are~] used in ~x1 and ~#0~[has no ~
                             badge~/have no badges~].  ~@2"
                            (reverse bad-fns)
                            tbody
                            *gratuitous-lambda-object-restriction-msg*))
                          ((not (executable-tamep tbody wrld))
                           (trans-er+?
                            cform x
                            ctx
                            "The body of a LAMBDA object or lambda$ term ~
                             must be tame and ~x0 is not.  ~@1"
                            body
                            *gratuitous-lambda-object-restriction-msg*))
                          (t (translate11-var-or-quote-exit
                              x
                              (hons-copy
                               (if lambda-casep
                                   `(QUOTE ,x)

; We ALWAYS put an (IGNORABLE . vars) entry at the end of our edcls.  If the
; tguard is *T* then we needn't put anything else.  (We know there aren't any
; TYPE declarations if the tguard is *T*.)  If the tguard is not *T* then what
; the user wrote may have been augmented by the TYPE declarations so we have to
; put tguard into the xargs and, in any case, we need to set :SPLIT-TYPES to T.

                                 (let ((edcls1
                                        (if (equal tguard *T*)
                                            `((IGNORABLE ,@vars))
; Note that the IGNORABLE entry is guaranteed to be last because there cannot
; have been an IGNORABLE entry in edcls.  The XARGS entry may be before or
; after any TYPE entries depending on its location originally.
                                            (put-assoc-eq
                                             'IGNORABLE vars
                                             (put-assoc-eq
                                              'XARGS
                                              `(:GUARD ,tguard :SPLIT-TYPES T)
                                              edcls))))
                                       (vars1
                                        (if allow-free-varsp
                                            (append
                                             vars
                                             (revappend free-vars-guard nil)
                                             (set-difference-eq
                                              (revappend free-vars-body nil)
                                              free-vars-guard))
                                          vars)))

                                   (let ((new-tbody
                                          (if (eq stobjs-out t)

; Normally we tag the translated lambda body.  But we don't want to do that
; when proving theorems.  Without this special case for stobjs-out = t, the
; following theorem would not be proved trivially.  (For a related comment
; pertaining to lambdas in definition bodies, rather than at the top level, see
; untranslate1-lambda-object.)

; (thm (equal (loop$ for x in lst collect (car (cons x (cons x nil))))
;             (loop$ for x in lst collect (car (list x x)))))

                                              tbody
                                            (tag-translated-lambda$-body
                                             x tbody))))
                                     `(QUOTE
                                       (LAMBDA
                                        ,vars1
                                        (DECLARE ,@edcls1)
                                        ,new-tbody))))))
                              stobjs-out bindings known-stobjs flet-alist
                              cform ctx wrld state-vars))))))))))))))))))
   (t (trans-er+? cform x ctx
                  "Every LAMBDA object and lambda$ term must be a true list ~
                   of at least 3 elements, e.g., (LAMBDA vars ...dcls... ~
                   body) and ~x0 is not.  ~@1"
                  x *gratuitous-lambda-object-restriction-msg*))))

(defun translate11-loop$
  (x stobjs-out bindings known-stobjs flet-alist cform ctx wrld state-vars)

; Warning: We assume that the translation of a loop$ is always a loop$ scion
; call whose first argument (after full translation) is a quoted LAMBDA
; expression, not a quoted function symbol.  See special-loop$-guard-clauses.

; X here is a form beginning with LOOP$.

; Here we record some ideas that we have begun to consider for augmenting the
; guards generated for the lambda$s in a loop$ expression.

; To refresh our memories, UNTIL, WHEN, and OPERATOR expressions all generate
; lambda$ expressions.  Those lambda$s currently carry guards stated in the
; OF-TYPE clauses together with any :GUARD clauses.

; We have recognized three other sources from which we could augment these
; lambda$ guards:

; (1) If v ranges over ``FROM lo TO hi BY incr'' then we could add things like
; (integerp v) or even bounds like (<= lo v) and (<= v hi).  Note: the upper
; bound may be complicated in the case of the lambda$ for an UNTIL, where the
; upper bound for v is probably one incr step beyond hi.  But for the OPERATOR
; lambda$, it is (<= v hi).  The main point is that the target itself gives us
; some guard information for each lambda$ we generate.

; (2) If v rangers over ``ON lst'' we can augment the guard of the lambda$s
; with (consp v), again being careful to consider giving extra care for the
; UNTIL lambda$ versus the others.

; (3) If there is an ``UNTIL expr'' or a ``WHEN expr'' we could augment the
; guard of the OPERATOR lambda$ with expr.  This could be problematic if expr
; is expensive to compute.  Note also that expr might involve variables other
; than the iteration variables.  If that's the case, we're already generating
; fancy loop$ lambda$s, so it shouldn't be too much trouble to make suitable
; modifications to translate11-loop$.

; It is possible that for all but guard-verified evaluation, these implicit
; guards -- at least for (3) -- might be much more expensive to compute than
; the guard needed for the lambda.

; We see a trade-off: If we implicitly augment the guards of the lambda$s
; maximally, we stand a better chance of verifying the guards of DEFUNs
; containing loop$s, without requiring the user to add explicit :guard clauses
; to the loop$.  There is no obvious downside if all we care about are loop$s
; in guard-verified DEFUNs, where loop$ expressions are evaluated using Common
; Lisp loop.  If we think about other loop$s, the upside is that the augmented
; guards might be provable by tau and get the lambda$ :GOOD status in the cache
; without having required the user to add a :guard clause.  The downside is
; that the augmented guard may be overkill and slow down guard checking except
; in guard-verified execution (using Common Lisp loop).  The trade-off is hard
; to evaluate because if the augmented guard is actually needed for guard
; verification -- e.g., if we're iterating over an ON target the lambda$ might
; actually need the (consp v) that the user didn't bother to write.  In that
; case, tau will fail, the lambda will be marked :BAD, and interpreted.  But it
; all runs silently and the user may never realize that a :guard clause would
; have sped things up.

; A middle ground would, of course, be to augment the guard using (1) and (2)
; but ignore anything we could learn from the UNTIL and WHEN expressions.  Or,
; we could do some cheap syntactic check of the UNTIL and WHEN expressions and
; see if they include, as a syntactic conjunct, (consp v) or (integerp v), and
; add those inferred restrictions.

  (let ((bindings0 bindings) ; save original bindings
        (bindings nil)       ; set bindings to nil for trans-values calls below
        (stobjs-out-simple (if (eq stobjs-out t)
                               t
                             '(nil))))
    (mv-let (erp parse)
      (parse-loop$ x)
      (cond
       (erp
; In this case, parse is the error msg.
        (trans-er+? cform x ctx "~@0" parse))
       (t
        (mv-let (vsts untilc whenc op lobodyc)

; vsts = a list of 1 or more vst tuples, each of the form (var spec target).
;        where var is a ``variable'', spec is the ``type spec'' or T, and
;        target is one of (IN lst), (ON lst), or (FROM-TO-BY i j k).  However,
;        no syntax checks have been made to ensure that var really is a
;        variable, etc.  Either we will need to make these checks or make sure
;        the various components are used in our output in a context that will
;        cause the checks.

; untilc = the carton holding the UNTIL clause guard and body, or nil
; whenc = the carton holding the WHEN clause guard and body, or nil
; op = a *loop$-keyword-info* key other than NIL
; bodyc = the carton holding the lobody guard and body

          (mv (nth 0 parse) ; vsts
              (nth 1 parse) ; untilc
              (nth 2 parse) ; whenc
              (nth 3 parse) ; op
              (nth 4 parse) ; bodyc
              )
          (cond
           ((and whenc (or (eq op 'ALWAYS) (eq op 'THEREIS)))
            (trans-er+? cform x ctx
                        "It is illegal in CLTL to have a WHEN clause with an ~
                         ALWAYS or THEREIS accumulator, so ~x0 is illegal."
                        x))
           (t
            (trans-er-let*
             ((tvsts (translate-vsts vsts 'LOOP$-IVARS nil cform ctx wrld))

; The nil above in the call of translate-vsts is a value for bindings which is
; passed in only so that the signature of that function is the same as that for
; the translate11 calls below.  The calls of trans-value below for tuntil and
; twhen use the local value of bindings, which is nil.

; Recall that tvsts is a list of 4-tuples, (vi type-spec
; type-guard-wrt-LOOP$-IVARS target-thing), and go read the comment in
; translate-vsts for a precise description!

              (translated-until-guard
               (if (and untilc
                        (not (eq (excart :untranslated :guard untilc) t)))
                   (translate11 (excart :untranslated :guard untilc)
                                nil                 ; ilk
                                stobjs-out-simple
                                nil                 ; bindings
                                nil                 ; known-stobjs
                                nil                 ; flet-alist
                                cform ctx wrld state-vars)
                   (trans-value *t*)))
              (translated-until-body
               (if untilc
                   (translate11 (excart :untranslated :body untilc)
                                nil           ; ilk
                                stobjs-out-simple
                                nil           ; bindings
                                nil           ; known-stobjs
                                nil           ; flet-alist
                                cform ctx wrld state-vars)
                   (trans-value *nil*)))

              (translated-when-guard
               (if (and whenc
                        (not (eq (excart :untranslated :guard whenc) t)))
                   (translate11 (excart :untranslated :guard whenc)
                                nil                 ; ilk
                                stobjs-out-simple
                                nil                 ; bindings
                                nil                 ; known-stobjs
                                nil                 ; flet-alist
                                cform ctx wrld state-vars)
                   (trans-value *t*)))
              (translated-when-body
               (if whenc
                   (translate11 (excart :untranslated :body whenc)
                                nil           ; ilk
                                stobjs-out-simple
                                nil           ; bindings
                                nil           ; known-stobjs
                                nil           ; flet-alist
                                cform ctx wrld state-vars)
                   (trans-value *nil*)))

              (translated-lobody-guard
               (if (and lobodyc
                        (not (eq (excart :untranslated :guard lobodyc) t)))
                   (translate11 (excart :untranslated :guard lobodyc)
                                nil                 ; ilk
                                stobjs-out-simple
                                nil                 ; bindings
                                nil                 ; known-stobjs
                                nil                 ; flet-alist
                                cform ctx wrld state-vars)
                   (trans-value *t*)))
              (translated-lobody-body
               (if lobodyc
                   (translate11 (excart :untranslated :body lobodyc)
                                nil           ; ilk
                                stobjs-out-simple
                                nil           ; bindings
                                nil           ; known-stobjs
                                nil           ; flet-alist
                                cform ctx wrld state-vars)
                   (trans-value *nil*))))

; Each of the calls of translate11 above uses bindings nil, so they're not
; sensitive to the input value of bindings.  If the xargs :loop$-recursion is t
; then calls of the about-to-be-defined function, fn, are to be expected, so in
; order to know the output arity of fn (which is known when :loop$-recursion is
; used) chk-acceptable-defuns1 will have stored the stobjs-out of fn before
; calling translate-bodies.  Thus, the nil bindings here are ok: they mean get
; the output arities from the world.

; But, if :loop$-recursion t is not specified but recursion occurs then the
; calls of translate11 might change bindings to allege the output signature of
; one of the functions being defined -- even though ultimately an error will be
; caused by that because recursion is not allowed in LAMBDA objects.  But we
; don't check that in this function, we just produce lambda$ expressions that
; will be further translated.  To try to make sensible error messages -- not
; ones reporting inappropriate signatures -- we will restore bindings to what
; it was before we started changing it.

; BTW: It may at first appear that we needn't translate the extra guardx
; because they'll find their way into the corresponding lambda$s and be
; translated there.  But we need to make some substitutions into them, so we
; need terms!

             (let* ((bindings bindings0)
                    (untilc (if untilc
                                (make-carton
                                 (excart :untranslated :guard untilc)
                                 translated-until-guard
                                 (excart :untranslated :body untilc)
                                 translated-until-body)
                                nil))
                    (whenc (if whenc
                               (make-carton
                                (excart :untranslated :guard whenc)
                                translated-when-guard
                                (excart :untranslated :body whenc)
                                translated-when-body)
                               nil))
                    (lobodyc (make-carton
                              (excart :untranslated :guard lobodyc)
                              translated-lobody-guard
                              (excart :untranslated :body lobodyc)
                              translated-lobody-body))
                    (iteration-vars (strip-cars tvsts))
                    (until-free-vars
                     (if untilc
                         (set-difference-eq
                          (revappend
                           (all-vars1-lst (list (excart :translated :guard untilc)
                                                (excart :translated :body untilc))
                                          nil)
                           nil)
                          iteration-vars)
                         nil))
                    (when-free-vars
                     (if whenc
                         (set-difference-eq
                          (revappend
                           (all-vars1-lst (list (excart :translated :guard whenc)
                                                (excart :translated :body whenc))
                                          nil)
                           nil)
                          iteration-vars)
                         nil))
                    (lobody-free-vars
                     (set-difference-eq
                      (revappend
                       (all-vars1-lst (list (excart :translated :guard lobodyc)
                                            (excart :translated :body lobodyc))
                                      nil)
                       nil)
                      iteration-vars)))

; The cond below selects for either a plain loop$ or a fancy one and builds the
; immediate ``macroexpansion'' of the loop$.  Then we translate that.

               (translate11
                (cond
                 ((and (null (cdr tvsts)) ; No AS clauses
                       (null until-free-vars)
                       (null when-free-vars)
                       (null lobody-free-vars))
; We have a plain loop$.
                  (tag-loop$
                   x

; We assume that the translation of a loop$ is always a loop$ scion called on a
; quoted LAMBDA object.  So don't simplify, say, (collect$ (lambda$ (v)
; (symbolp v)) lst) to (collect$ 'symbolp lst)!  See
; special-loop$-guard-clauses.

                   (make-plain-loop$
                    (car (car tvsts))   ; var
                    (cadr (car tvsts))  ; TYPE spec
                    (cadddr (car tvsts)) ; target
                    untilc
                    whenc
                    op
                    lobodyc)))
                 (t
; We have a fancy loop$.
                    (tag-loop$
                     x

; We assume that the translation of a loop$ is always a loop$ scion called on a
; quoted LAMBDA object.  So don't simplify, say, (collect$+ (lambda$
; (loop$-gvars loop$-ivars) (foo loop$-gvars loop$-ivars)) lst) to (collect$ 'foo lst)!
; See special-loop$-guard-clauses.

                     (make-fancy-loop$
                      tvsts
                      untilc until-free-vars
                      whenc when-free-vars
                      op
                      lobodyc lobody-free-vars))))
                nil stobjs-out bindings known-stobjs flet-alist
                cform ctx wrld state-vars)))))))))))

(defun translate11 (x ilk stobjs-out bindings known-stobjs flet-alist
                      cform ctx wrld state-vars)

; Warning: Keep this in sync with macroexpand1*-cmp.  Also, for any new special
; operators (e.g., let and translate-and-test), consider extending
; *special-ops* in community book books/misc/check-acl2-exports.lisp.

; Warning: If you change this function, consider whether a corresponding change
; is needed in get-translate-cert-data-record.  In particular, some checks done
; in translate11 need to be done in get-translate-cert-data-record.  But not
; all such checks are necessary: for example, defined-constant will be true of
; a given symbol at include-book time if it was true at the original translate
; time, and similarly for a call (termp x wrld).

; Note: Ilk is the ilk of the slot in which x was found, and is always one of
; :FN, :EXPR, or NIL.  It is almost always NIL, e.g., when first entering from
; translate or during the translation of any actual to any ACL2 primitive
; (badged or unbadged) except for the two primitives apply$ and ev$.  In fact,
; the only values of ilk that actually matter are :FN and :FN?.  If x is being
; passed into such a slot then lambda objects and lambda$ expressions are
; allowed.  Otherwise such expressions trigger errors.  So providing an ilk of
; NIL just has the effect of prohibiting x from being a lambda object or
; lambda$.

; (There is no special treatment of ilk :EXPR, i.e., we do not support any way
; for the user to type an untranslated term and have it turn into a quoted
; translated term, because we believe the overwhelmingly more common case is
; the need to pass quoted, fully translated lambda constants.)

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

       (t (trans-er-let*
           ((transx
             (cond
              ((keywordp x) (trans-value (kwote x)))
              ((symbolp x)
               (trans-value
                (cond ((eq vc 'constant) const)
                      (t x))))
              ((atom x) (trans-value (kwote x)))
              ((and (consp (cadr x))
                    (eq (car (cadr x)) 'lambda)
                    (not (global-val 'boot-strap-flg wrld)))

; If a lambda object appears in a :FN or :FN? slot, we enforce the
; well-formedness rules for apply$.

               (if (or (eq ilk :FN) (eq ilk :FN?))
                   (translate11-lambda-object
                    (cadr x)
                    stobjs-out bindings known-stobjs flet-alist
                    cform ctx wrld state-vars nil)

; Historical Note: We once tried to cause an error on lambda objects outside
; :FN slots but found hundreds of problems in the Community Books.  The problem
; is that there are many lambda objects in the regression that have nothing to
; do with apply$ due to utilities like books/data-structures/defalist.lisp that
; encourage users to write lambda expressions that become incorporated into
; macro-generated defuns.  So instead of causing an error now we just allow it.

                   (trans-value x)))
              (t (trans-value x)))))
            (cond

; Explanation of a Messy Restriction on :FN Slots

; If we are in a :FN slot and see a quoted object, then we insist the object be
; a badged symbol or a LAMBDA.  If it's a LAMBDA we know it's well-formed by the
; use of translate11-lambda-object in the binding of transx above.  So we focus
; here on all manner of quoted objects except conses starting with LAMBDA and
; we cause an error unless it's a badged symbol.  However, there are three
; exceptions.

; (1) We allow an unbadged symbol into the :FN slot of APPLY$ because the
; warrants for mapping functions call APPLY$ on quoted non-badged symbols, e.g.,
; (APPLY$ 'COLLECT$ ...) = (COLLECT$ ...).  Recall that the ``ilk'' for the
; first arg of APPLY$ is :FN? as per ilks-per-argument-slot.

; (2) We allow a defconst symbol to slip any kind of quoted object into a :FN
; slot.  This is a deliberate choice.  We wanted an escape mechanism for the
; rules on :fn slots and chose defconsts.

; (3) Anything goes during boot-strapping, for obvious reasons.

; The following test recognizes the error cases.  Read this as follows: we're
; looking at fn slot containing a quoted object that didn't come from a
; defconst and that arose after boot-strapping.  The quoted object is not a
; LAMBDA (because we know any lambda here is well-formed).  So then consider
; the cases on ilk.  If it's :FN we insist the quoted object is a badged symbol
; and if it's :FN?, which means we're in an APPLY$ call, it must at least be a
; symbol.

             ((and (or (eq ilk :FN)
                       (eq ilk :FN?))
                   (quotep transx)
                   (not (eq vc 'constant))
                   (not (global-val 'boot-strap-flg wrld))
                   (not (and (consp (unquote transx))
                             (eq (car (unquote transx)) 'lambda)))
                   (cond
                    ((eq ilk :FN)
                     (not (and (symbolp (unquote transx))
                               (executable-badge (unquote transx) wrld))))
                    (t ; ilk is :FN? so we're in apply$
                     (not (symbolp (unquote transx))))))
              (trans-er+?
               cform x
               ctx
               "The quoted object ~x0 occurs in a :FN slot of a function call ~
                but ~x0 ~@1  We see no reason to allow this!  To insist on ~
                having such a call, defconst some symbol and use that symbol ~
                constant here instead but be advised that even this workaround ~
                will not allow such a call in a DEFUN."
               (unquote transx)
               (if (symbolp (unquote transx))
                   (if (function-symbolp (unquote transx) wrld)
                       "does not have a badge."
                       "is not a function symbol.")
                   "is not a function symbol or lambda object")))
             (t
              (translate11-var-or-quote-exit x transx stobjs-out bindings
                                             known-stobjs flet-alist
                                             cform ctx wrld state-vars))))))))
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
              nil ; ilk
              stobjs-out bindings known-stobjs flet-alist x ctx wrld
              state-vars))))
   ((eq (car x) 'lambda$)
    (cond ((not (or (eq ilk :FN)
                    (eq ilk :FN?)))

; We have encountered a LAMBDA$ among the actuals in a non-:FN slot of a call
; of some function fn.  But we don't know which function so we can't
; distinguish a vanilla slot from a slot of an unbadged function.

           (trans-er+? cform x
                       ctx
                       "It is illegal for a LAMBDA$ expression to occur ~
                        except in a :FN slot of a mapping function, and ~x0 ~
                        occurs either in a slot reserved for ~#1~[an ordinary ~
                        object of a badged function or a slot of unknown ilk ~
                        in an unbadged function~/a quoted expression or ~
                        variable of ilk :EXPR~]."
                       x
                       (if (eq ilk :EXPR) 1 0)))
          (t (translate11-lambda-object
              x stobjs-out bindings known-stobjs
              flet-alist cform ctx wrld state-vars nil))))
   ((eq (car x) 'loop$)
    (cond ((eq ilk nil)
           (translate11-loop$ x stobjs-out bindings known-stobjs flet-alist
                              cform ctx wrld state-vars))
          (t (trans-er+? cform x
                         ctx
                         "It is illegal for a LOOP$ expression to occurr in a ~
                          slot of ilk ~x0."
                         ilk))))
   ((and (not (eq stobjs-out t))
         (eq (car x) 'swap-stobjs)

; If the number of arguments is not 2, we'll get an error when we translate
; this call in the normal way (by macroexpansion).

         (= (length (cdr x)) 2))
    (let ((s1 (cadr x))
          (s2 (caddr x)))
      (cond
       ((eq stobjs-out :stobjs-out)
        (trans-er ctx
                  "The macro ~x0 must not be called directly in the ACL2 ~
                   top-level loop, as opposed to being made inside a function ~
                   definition.  The call ~x1 is thus illegal."
                  'swap-stobjs
                  x))
       ((and (stobjp s1 known-stobjs wrld)
             (stobjp s2 known-stobjs wrld)
             (not (eq s1 s2))
             (congruent-stobjsp s1 s2 wrld))
        (mv-let (erp val bindings)
          (translate11 (list 'mv s1 s2)
                       ilk stobjs-out bindings known-stobjs flet-alist
                       cform ctx wrld state-vars)
          (cond (erp (trans-er+? cform x
                                 ctx
                                 "The form ~x0 failed to translate because ~
                                  translation of the corresponding form, ~x1, ~
                                  failed with the following error ~
                                  message:~|~@2"
                                 x
                                 (list 'mv s1 s2)
                                 val))
                (t (trans-value (listify (list s2 s1)))))))
       (t (trans-er ctx
                    "Illegal swap-stobjs call: ~x0.  ~@1  See :DOC swap-stobjs."
                    x
                    (cond
                     ((or (not (stobjp s1 known-stobjs wrld))
                          (not (stobjp s2 known-stobjs wrld)))
                      (msg "Note that ~&0 ~#0~[is not a known stobj name~/are ~
                            not known stobj names~] in the context of that ~
                            call."
                           (if (stobjp s1 known-stobjs wrld)
                               (list s2)
                             (if (stobjp s2 known-stobjs wrld)
                                 (list s1)
                               (list s1 s2)))))
                     ((eq s1 s2)
                      "The two arguments of swap-stobjs must be distinct ~
                       names.")
                     (t ; (not (congruent-stobjsp s1 s2 wrld))
                      "The two arguments fail the requirement of being ~
                       congruent stobjs.")))))))
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
           ((args (translate11-lst (cdr x)
                                   nil ; ilks, where (eq (car x) 'mv)
                                   stobjs-out bindings known-stobjs 'mv
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
                (translate11-lst (cdr x)
                                 nil ; ilks, where (eq (car x) 'mv)
                                 new-stobjs-out
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
              ((args (translate11-lst (cdr x)
                                      nil ;;; ilks = '(nil ... nil)
                                      t bindings known-stobjs nil flet-alist x
                                      ctx wrld state-vars)))
              (trans-value (fcons-term lambda-fn args))))
            (t
             (translate11-call x lambda-fn (cdr x) stobjs-out stobjs-out2
                               bindings known-stobjs
                               (msg "a call of FLET-bound function ~x0"
                                    (car x))
                               flet-alist ctx wrld state-vars)))))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (hons-get (car x) *syms-not-callable-in-code-fal*))
    (trans-er+ x ctx
               "We do not permit the use of ~x0 inside of code to be executed ~
                by Common Lisp because its Common Lisp meaning differs from ~
                its ACL2 meaning.~@1"
               (car x)
               (cond ((eq (car x) 'with-guard-checking-event)
                      (msg "  Consider using ~x0 instead."
                           'with-guard-checking-error-triple))
                     ((eq (car x) 'with-output)
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

; We pass ilk = nil below because a non-erroneous lambda$ always yields a
; quoted object, so there's no reason to support check-vars-not-free dealing
; with lambda$s.

           (translate11 (caddr x)
                        nil ; ilk (see comment above)
                        stobjs-out bindings
                        known-stobjs flet-alist x ctx wrld
                        state-vars))
          ((not (symbol-listp (cadr x)))
           (trans-er+ x ctx
                      "CHECK-VARS-NOT-FREE requires its first argument to be ~
                       a true-list of symbols."))
          (t
           (trans-er-let*
            ((ans (translate11 (caddr x)
                               nil ; ilk
                               stobjs-out bindings
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
              ((ans (translate11 (caddr x)
                                 nil ; ilk
                                 stobjs-out bindings
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
                            nil ; ilk
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
   ((and (assoc-eq (car x) *ttag-fns*)
         (not (ttag wrld))
         (not (global-val 'boot-strap-flg wrld)))
    (trans-er+ x ctx
               "The function ~s0 cannot be called unless a trust tag is in ~
                effect.  See :DOC defttag.~@1"
               (car x)
               (or (cdr (assoc-eq (car x) *ttag-fns*))
                   "")))
   ((and (eq (car x) 'progn!)
         (not (ttag wrld))
         (not (global-val 'boot-strap-flg wrld)))
    (trans-er+ x ctx
               "The macro ~s0 cannot be called unless a trust tag is in ~
                effect.  See :DOC defttag."
               (car x)))
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
       (let ((msg (chk-stobj-let bound-vars actuals stobj producer-vars
                                 updaters corresp-accessor-fns known-stobjs
                                 wrld)))
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
                (translate11 guarded-consumer
                             nil ; ilk
                             stobjs-out bindings known-stobjs
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
                    (dups-check
                     (no-duplicatesp-checks-for-stobj-let-actuals bound-vars
                                                                  actuals
                                                                  producer-vars
                                                                  stobj
                                                                  wrld))
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
                   (cond (dups-check
                          (trans-er-let*
                           ((chk (translate11 dups-check 
                                              nil ; ilk
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
        (t (translate11 expansion
                        ilk
                        stobjs-out bindings known-stobjs flet-alist x
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
   ((eql (arity (car x) wrld) (length (cdr x)))
    (cond ((untouchable-fn-p (car x)
                             wrld
                             (access state-vars state-vars
                                     :temp-touchable-fns))
           (cond ((and (eq (car x) 'untouchable-marker)
                       (consp (cadr x))
                       (eq (car (cadr x)) 'quote)
                       (symbolp (cadr (cadr x)))
                       (getpropc (cadr (cadr x)) 'macro-body nil wrld)
                       (null (cddr (cadr x))))
                  (trans-er+ x ctx
                             "It is illegal to call ~x0 because it has been ~
                              placed on untouchable-fns.  That call may have ~
                              arisen from attempting to expand a call of the ~
                              macro ~x1, ~#2~[if that macro~/which~] was ~
                              defined with ~x3."
                             (car x)
                             (cadr (cadr x))
; We print a slightly more informative error message for the built-in macros
; defined with defmacro-untouchable.
                             (if (member-eq (car x)
                                            '(with-live-state
                                              #+acl2-par f-put-global@par
                                              when-pass-2))
                                 0
                               1)
                             'defmacro-untouchable))
                 (t (trans-er+ x ctx
                               "It is illegal to call ~x0 because it has been ~
                                placed on untouchable-fns."
                               (car x)))))
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
                                  nil ; ilk
                                  (if (eq stobjs-out t)
                                      t
                                    '(nil))
                                  bindings known-stobjs
                                  flet-alist x ctx wrld state-vars)))
              (mv-let
               (erp2 arg2 bindings2)
               (trans-er-let*
                ((arg2 (translate11 (caddr x)
                                    nil ; ilk
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
                                 nil ; ilk
                                 stobjs-out bindings known-stobjs
                                 flet-alist x ctx wrld state-vars)
                    (cond
                     (erp3 (mv erp2 arg2 bindings2))
                     (t (trans-er-let*
                         ((arg2 (translate11 (caddr x)
                                             nil ; ilk
                                             stobjs-out bindings known-stobjs
                                             flet-alist x ctx wrld state-vars)))
                         (trans-value (fcons-term* 'if arg1 arg2 arg3)))))))
                  (t (mv erp2 arg2 bindings2))))
                (t
                 (let ((bindings bindings2))
                   (trans-er-let*
                    ((arg3 (translate11 (cadddr x)
                                        nil ; ilk
                                        stobjs-out bindings known-stobjs
                                        flet-alist x ctx wrld state-vars)))
                    (trans-value (fcons-term* 'if arg1 arg2 arg3)))))))))))
          ((and (eq (car x) 'synp)
                (eql (length x) 4) ; else fall through to normal error
                (eq stobjs-out t))

; Synp is a bit odd.  We typically -- that is, from macroexpansion of syntaxp
; and bind-free calls -- store the quotation of the term to be evaluated in the
; third arg of the synp form.  We store the quotation so that ACL2 will not see
; the term as a potential induction candidate.  (Eric Smith first pointed out
; this issue.)  This, however forces us to treat synp specially here in order
; to translate the term to be evaluated and thereby get a proper ACL2 term.
; Without this special treatment (cadr x), for instance, would be left alone
; whereas it needs to be translated into (car (cdr x)).  This mangling of the
; third arg of synp is sound because synp always returns t.  Note, however,
; that after Version_8.1 we no longer insist that stobjs-out = t or that the
; arguments to synp all be quoted, since these restrictions defeat the ability
; to include synp as a function symbol supplied to defevaluator.

; Robert Krug has mentioned the possibility that the known-stobjs below could
; perhaps be t.  This would allow a function called by synp to use, although
; not change, stobjs.  If this is changed, change the references to stobjs in
; the documentation for syntaxp and bind-free as appropriate.  But before
; making such a change, consider this: no live user-defined stobj will ever
; appear in the unifying substitution that binds variables in the evg of
; (cadddr x).  So it seems that such a relaxation would not be of much value.

           (mv-let
             (erp val bindings)
             (trans-er-let*
              ((vars0 (translate11 (cadr x)
                                   nil    ; ilk
                                   '(nil) ; stobjs-out
                                   bindings
                                   '(state) ; known-stobjs
                                   flet-alist x ctx wrld state-vars))
               (user-form0 (translate11 (caddr x)
                                        nil ; ilk
                                        '(nil) ; stobjs-out
                                        bindings
                                        '(state) ; known-stobjs
                                        flet-alist x ctx wrld
                                        state-vars))
               (term0 (translate11 (cadddr x)
                                   nil    ; ilk
                                   '(nil) ; stobjs-out
                                   bindings
                                   '(state) ; known-stobjs
                                   flet-alist x ctx wrld state-vars)))
              (let ((quoted-vars (if (quotep vars0)
                                     vars0
                                   (quote-normal-form vars0)))
                    (quoted-user-form (if (quotep user-form0)
                                          user-form0
                                        (quote-normal-form user-form0)))
                    (quoted-term (if (quotep term0)
                                     term0
                                   (quote-normal-form term0))))
                (cond ((and (quotep quoted-vars)
                            (quotep quoted-user-form)
                            (quotep quoted-term))
                       (trans-er-let*
                        ((term-to-be-evaluated
                          (translate11 (unquote quoted-term)
                                       nil    ; ilk
                                       '(nil) ; stobjs-out
                                       bindings
                                       '(state) ; known-stobjs
                                       flet-alist x ctx wrld state-vars)))
                        (trans-value
                         (fcons-term* 'synp
                                      quoted-vars
                                      quoted-user-form
                                      (kwote term-to-be-evaluated)))))
                      (t (trans-value
                          (fcons-term* 'synp vars0 user-form0 term0))))))
             (cond (erp
                    (let ((quoted-user-form-original (caddr x)))
                      (case-match quoted-user-form-original
                        (('QUOTE ('SYNTAXP form))
                         (mv erp
                             (msg "The form ~x0, from a ~x1 hypothesis, is ~
                                   not suitable for evaluation in an ~
                                   environment where its variables are bound ~
                                   to terms.  See :DOC ~x1.  Here is further ~
                                   explanation:~|~t2~@3"
                                  form 'syntaxp 5 val)
                             bindings))
                        (& (mv erp val bindings)))))
                   (t (mv erp val bindings)))))
          ((eq stobjs-out t)
           (trans-er-let*
            ((args (translate11-lst (cdr x)
                                    (ilks-per-argument-slot (car x) wrld)
                                    t bindings known-stobjs
                                    nil flet-alist x ctx wrld state-vars)))
            (trans-value (fcons-term (car x) args))))
          ((eq (car x) 'mv-list) ; and stobjs-out is not t
           (trans-er-let*
            ((arg1 (translate11 (cadr x)
                                nil ; ilk
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
                                        nil ; ilk
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
                                   nil ; ilk
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
                                      nil ; ilk
                                      stobjs-out
                                      bindings known-stobjs
                                      flet-alist x ctx wrld state-vars))
                  (targ3 (translate11 arg3
                                      nil ; ilk
                                      stobjs-out bindings known-stobjs
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
                 (translate11 arg2
                              nil ; ilk
                              '(nil)
                              bindings known-stobjs flet-alist x
                              ctx wrld state-vars)
                 (declare (ignore targ2-bindings))
                 (cond
                  (erp (mv erp targ2 bindings))
                  ((throw-nonexec-error-p1 targ1 targ2 :non-exec nil)

; This check holds when x is a non-exec call, and corresponds to similar checks
; using throw-nonexec-error-p in collect-certain-lambda-objects and
; collect-certain-tagged-loop$s.

                   (mv-let
                    (erp targ3 targ3-bindings)
                    (translate11
                     arg3
                     nil ; ilk
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
                    ((targ3 (translate11 arg3
                                         nil ; ilk
                                         stobjs-out bindings known-stobjs
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
              ((args (translate11-lst (cdr x)
                                      (ilks-per-argument-slot (car x) wrld)
                                      computed-stobjs-out bindings
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

(defun translate11-lst (lst ilks stobjs-out bindings known-stobjs
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
          ((x (translate11 (car lst) (car ilks) t bindings known-stobjs
                           flet-alist
                           (car lst) ctx wrld state-vars))
           (y (translate11-lst (cdr lst) (cdr ilks) t bindings known-stobjs msg
                               flet-alist cform ctx wrld state-vars)))
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
           (y (translate11-lst (cdr lst) (cdr ilks) (cdr stobjs-out)
                               bindings known-stobjs msg flet-alist cform ctx
                               wrld state-vars)))
          (trans-value (cons x y))))
        (t (trans-er-let*
            ((x (translate11 (car lst) (car ilks) '(nil) bindings known-stobjs flet-alist

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
             (y (translate11-lst (cdr lst) (cdr ilks) (cdr stobjs-out)
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
     (translate11 x
                  nil ; ilk
                  stobjs-out bindings known-stobjs nil x ctx w state-vars)))
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

(mutual-recursion

(defun logic-fnsp (term wrld)

; We check for the absence of calls (f ...) in term for which the symbol-class
; of f is :program.  If f is a term (not merely a pseudo-term), that's
; equivalent to saying that every function symbol called in term is in :logic
; mode, i.e., has a 'symbol-class property of :ideal or :common-lisp-compliant.

  (declare (xargs :guard (and (plist-worldp wrld)
                              (pseudo-termp term))))
  (cond ((variablep term)
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

(defun collect-user-stobjs (stobjs-out)
  (cond ((endp stobjs-out) nil)
        ((or (null (car stobjs-out))
             (eq (car stobjs-out) 'state))
         (collect-user-stobjs (cdr stobjs-out)))
        (t (cons (car stobjs-out)
                 (collect-user-stobjs (cdr stobjs-out))))))

(defun ev-for-trans-eval (trans stobjs-out ctx state aok
                                user-stobjs-modified-warning)

; WARNING: This function must never be in :logic mode, because it can violate
; single-threadedness!  See :doc user-stobjs-modified-warnings.  Fortunately,
; it depends hereditarily on the function ev, which has raw Lisp code and is
; thus (as of this writing) prevented from being promoted to :logic mode.

; Warning: Keep in sync with ev-w-for-trans-eval.

; Trans is a translated term with the indicated stobjs-out.  We return the
; result of evaluating trans, but formulated as an error triple with possibly
; updated state as described in trans-eval.

; This function is called by trans-eval, and is a suitable alternative to
; trans-eval when the term to be evaluated has already been translated by
; translate1 with stobjs-out = :stobjs-out.

  (let ((alist (cons (cons 'state
                           (coerce-state-to-object state))
                     (user-stobj-alist state)))
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
                            user-stobjs-modified-warnings."
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
(defun ev-w-for-trans-eval (trans stobjs-out ctx state aok
                                  user-stobjs-modified-warning)

; Warning: Keep in sync with ev-for-trans-eval.

; Parallelism wart: add an assertion that stobjs-out does not contain state (or
; any other stobj).  Perhaps the assertion should be that stobjs-out equals the
; representation for an ordinary value.

  (let ((alist (cons (cons 'state
                           (coerce-state-to-object state))
                     (user-stobj-alist state)))
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
          "Global variables, such as ~&0, are not allowed.~@1  See :DOC ASSIGN ~
           and :DOC @."
          (reverse (non-stobjps vars t wrld)) ;;; known-stobjs = t
          (non-executable-stobjs-msg vars wrld nil)))
     (t (ev-for-trans-eval term stobjs-out ctx state aok
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

(defun lambda-object-guard-lst (objs)
  (cond
   ((endp objs) nil)
   (t (let ((guard (lambda-object-guard (car objs))))
        (if guard
            (cons guard (lambda-object-guard-lst (cdr objs)))
            (lambda-object-guard-lst (cdr objs)))))))

(defun lambda-object-body-lst (objs)
  (cond
   ((endp objs) nil)
   (t (cons (lambda-object-body (car objs))
            (lambda-object-body-lst (cdr objs))))))

(defun filter-lambda$-objects (lst)
  (cond ((endp lst) nil)
        ((lambda$-bodyp (lambda-object-body (car lst)))
         (cons (car lst)
               (filter-lambda$-objects (cdr lst))))
        (t (filter-lambda$-objects (cdr lst)))))

(mutual-recursion

(defun collect-certain-lambda-objects (flg term wrld ans)

; We walk through term looking for lambda objects and we collect into ans
; certain ones of them as per flg:

; :all -- every lambda object whether well-formed or not
; :well-formed -- every well-formed lambda object
; :lambda$ -- every well-formed lambda object tagged as having come from
;             a lambda$ translation

; We collect lambda objects within well-formed lambda objects but not within
; ill-formed ones.  In particular, if a lambda object is well-formed we'll dive
; into its :guard and body looking for other lambda objects.  But if we
; encounter an ill-formed lambda object we will not attempt to explore its
; :guard or body since they may be ill-formed.  This means that if a
; well-formed lambda object is hidden inside an ill-formed one we do not
; collect it.

; Motivation: uses of this function include guard verification (where we try to
; verify the guards of every well-formed lambda object in a defun) and the
; pre-loading of the cl-cache.  What are the consequences of not collecting a
; well-formed lambda object hidden inside an ill-formed one?  We wouldn't
; verify the guards of the hidden well-formed lambda object at defun-time.  If
; the ill-formed one is ever applied, the cache will force apply$ to use *1*
; apply$.  As the axiomatic interpretion of the ill-formed lambda object
; proceeds it may encounter the well-formed one and not find it in the
; pre-loaded cache.  But the cache will add a line for the just-found lambda
; object, attempting guard verification then and there just as though the user
; had typed in a new lambda object to apply.  So the consequences of this
; failure to collect is just the weakening of the proof techniques we bring to
; bear while verifying guards on such lambda objects: Had they been collected,
; the user would have the opportunity to add hints to get the guard
; verification to go through, whereas by not collecting them we delay guard
; verification to top-level eval time, where only weaker techniques are tried.

  (cond
   ((variablep term) ans)
   ((fquotep term)
    (let* ((evg (unquote term))
           (lambda-objectp (and (consp evg)
                                (eq (car evg) 'lambda)))
           (well-formedp (and lambda-objectp
                              (well-formed-lambda-objectp evg wrld)))
           (collectp
            (case flg
              (:all lambda-objectp)
              (:well-formed well-formedp)
              (otherwise
               (and well-formedp
                    (lambda$-bodyp (lambda-object-body evg))))))
           (ans1 (if collectp (add-to-set-equal evg ans) ans)))
      (if well-formedp
          (let* ((guard (lambda-object-guard evg))
                 (body (lambda-object-body evg)))
            (collect-certain-lambda-objects
             flg guard wrld
             (collect-certain-lambda-objects flg body wrld ans1)))
          ans1)))
   ((throw-nonexec-error-p term :non-exec nil)
; This check holds when term is the translated version of a non-exec call, as
; does a similar check using throw-nonexec-error-p1 in translate11.
    ans)
   ((flambda-applicationp term)
    (collect-certain-lambda-objects
     flg
     (lambda-body (ffn-symb term))
     wrld
     (collect-certain-lambda-objects-lst flg (fargs term) wrld ans)))
   (t (collect-certain-lambda-objects-lst flg (fargs term) wrld ans))))

(defun collect-certain-lambda-objects-lst (flg terms wrld ans)
  (cond
   ((endp terms) ans)
   (t (collect-certain-lambda-objects
       flg
       (car terms)
       wrld
       (collect-certain-lambda-objects-lst flg (cdr terms) wrld ans)))))
)

(defun tagged-loop$p (term)

; A marked loop$ is a term of the form (RETURN-LAST 'PROGN '(LOOP$ ...) term).
; This is the term created by translate when it encounters (LOOP$ ...).  The
; term in the last argument of the return-last is the semantics of the loop
; expressed as a nest of loop$ scion calls.  Translate prevents the user from
; typing a marked loop$ term.  So if a marked loop$ is found in the output of
; translate it was put there by translating the LOOP$ inside it.

; We assume term is not a variable and not a quote, as per the guard below!

  (declare (xargs :guard (and (nvariablep term)
                              (not (fquotep term)))))
  (and (eq (ffn-symb term) 'return-last)
       (equal (fargn term 1) '(QUOTE PROGN))
       (quotep (fargn term 2))
       (consp (unquote (fargn term 2)))
       (eq (car (unquote (fargn term 2))) 'LOOP$)))

(mutual-recursion

(defun collect-certain-tagged-loop$s (flg term ans)

; We collect certain marked loop$ subterms of term.  If flg is :all we collect
; them all.  If flg is :top we do not collect marked loop$ terms occurring in
; other marked loop$ terms.  For example, the translation of

; (loop$ for v in lst
;        collect (loop$ for u in v collect expr))

; is

;  (return-last
;   'progn
;   '(loop$ for v in lst collect (loop$ for u in v collect expr))
;   (collect$ (lambda$ (v)
;                      (return-last
;                       'progn
;                       '(loop$ for u in v collect expr)
;                       (collect$ (lambda$ (u) expr) v)))
;             lst))

; and if flg is :all we collect both return-last terms but if flg is :top we
; only collect the outermost.

  (cond
   ((variablep term) ans)
   ((fquotep term) ans)
   ((tagged-loop$p term)
    (cond ((eq flg :all)
           (collect-certain-tagged-loop$s flg (fargn term 3)
                                          (add-to-set-equal term ans)))
          (t (add-to-set-equal term ans))))
   ((throw-nonexec-error-p term :non-exec nil)
; This check holds when term is the translated version of a non-exec call, as
; does a similar check using throw-nonexec-error-p1 in translate11.
    ans)
   ((flambda-applicationp term)
    (collect-certain-tagged-loop$s
     flg
     (lambda-body (ffn-symb term))
     (collect-certain-tagged-loop$s-lst flg (fargs term) ans)))
   (t (collect-certain-tagged-loop$s-lst flg (fargs term) ans))))

(defun collect-certain-tagged-loop$s-lst (flg terms ans)
  (cond
   ((endp terms) ans)
   (t (collect-certain-tagged-loop$s
       flg
       (car terms)
       (collect-certain-tagged-loop$s-lst flg (cdr terms) ans)))))
)

(mutual-recursion

(defun ancestral-lambda$s-by-caller1 (caller guard body wrld alist)

; Caller is a symbol or a string.  Guard and body should either both be terms
; or both be nil.  If both are nil, caller must be a function symbol and guard
; and body default to the guard and body of caller.  If guard and body are
; non-nil, then they are used as the guard and body of some ficticious function
; described by the string, caller (which will ultimately be printed by a ~s fmt
; directive).

; By ``ancestors'' in this function we mean function symbols reachable through
; the guard, the body, or the guard or body of any well-formed lambda object in
; caller or any of these ancestors.  We extend alist with pairs (fn
; . lambda$-lst), where fn is any of these extended ancestors and lambda$-lst
; is the list of every lambda object produced by a lambda$ expression in fn.
; We use alist during this calculation to avoid repeated visits to the same fn,
; thus, we will add the pair (fn . nil) whenever fn has no lambda$s in it.  We
; filter out these empty pairs in ancestral-lambda$s-by-caller.

; We do nothing during boot-strap (there should be no lambda$s) and, as an
; optimization, we do not explore apply$-primp callers or the apply$ clique.

  (cond
   ((or (global-val 'boot-strap-flg wrld)
; The following hons-get is equivalent to ; (apply$-primp caller).
        (hons-get caller ; *badge-prim-falist* is not yet defined!
                  (unquote
                   (getpropc '*badge-prim-falist* 'const nil wrld)))
        (eq caller 'apply$)
        (eq caller 'ev$)
        (assoc-eq caller alist))
    alist)
   (t
    (let* ((guard (or guard (getpropc caller 'guard *t* wrld)))
           (body (or body (getpropc caller 'unnormalized-body *nil* wrld)))
           (objs (collect-certain-lambda-objects
                  :well-formed
                  body
                  wrld
                  (collect-certain-lambda-objects
                   :well-formed
                   guard
                   wrld
                   nil)))

; Note: Objs is the list of all well-formed lambda objects in caller.  Objs
; includes all lambda$ objects in caller but may include well-formed lambda
; objects not generated by lambda$.

; Fns is the list of all functions called in the guards or bodies of the just
; collected well-formed lambda object in caller.  We have to explore them too.

           (fns (all-fnnames1
                 nil ; all-fnnames
                 guard
                 (all-fnnames1
                  nil ; all-fnnames
                  body
                  (all-fnnames1
                   t ; all-fnnames-lst
                   (lambda-object-body-lst objs)
                   (all-fnnames1
                    t ; all-fnnames-lst
                    (lambda-object-guard-lst objs)
                    nil))))))
      (ancestral-lambda$s-by-caller1-lst
       fns wrld
       (cons (cons caller (filter-lambda$-objects objs)) alist))))))

(defun ancestral-lambda$s-by-caller1-lst (callers wrld alist)
  (cond ((endp callers) alist)
        (t (ancestral-lambda$s-by-caller1-lst
            (cdr callers)
            wrld
            (ancestral-lambda$s-by-caller1 (car callers) nil nil wrld alist))))))

(defun collect-non-empty-pairs (alist)
  (cond ((endp alist) nil)
        ((cdr (car alist))
         (cons (car alist) (collect-non-empty-pairs (cdr alist))))
        (t
         (collect-non-empty-pairs (cdr alist)))))

(defun ancestral-lambda$s-by-caller (caller term wrld)

; Caller is a string (ultimately printed with a ~s fmt directive) describing
; the context in which we found term.  Explore all function symbols reachable
; from the guards and bodies of functions and well-formed lambda objects in
; term and collect an alist mapping each such reachable function symbol to all
; of the lambda$ expressions occurring in it.  The alist omits pairs for
; function symbols having no lambda$s.  If the result is nil, there are no
; reachable lambda$s.  Otherwise, the function
; tilde-*-lambda$-replacement-phrase5 can create a ~* fmt phrase that
; interprets the alist as a directive to replace, in certain functions, certain
; lambda$s by quoted lambdas.

  (let ((alist (ancestral-lambda$s-by-caller1 caller *T* term wrld nil)))
    (collect-non-empty-pairs alist)))

; The following block of code is currently obsolete but might have some useful
; functionality so we preserve it.  The block ends at the Note after
; tilde-*-lambda$-replacement-phrase5 below.

(mutual-recursion

(defun eliminate-lambda$ (term wrld)
  (cond
   ((variablep term) term)
   ((fquotep term)
    (let ((x (unquote term)))
      (cond ((and (well-formed-lambda-objectp x wrld)
                  (lambda$-bodyp (lambda-object-body x)))
             (let* ((formals (lambda-object-formals x))
                    (dcl (lambda-object-dcl x))
                    (xbody (eliminate-lambda$ (fargn (lambda-object-body x) 3)
                                              wrld))
                    (guardp (assoc-keyword :guard
                                           (cdr (assoc-eq 'xargs (cdr dcl)))))
                    (xguard (if guardp
                                (eliminate-lambda$ (cadr guardp) wrld)
                                nil))
                    (xdcl (if guardp
                              (cons 'DECLARE
                                    (put-assoc-eq
                                     'xargs
                                     `(:GUARD ,xguard :SPLIT-TYPES T)
                                     (cdr dcl)))
                              nil)))
               (list 'quote
                     (make-lambda-object formals xdcl xbody))))
            (t term))))
   ((flambdap (ffn-symb term))
    (fcons-term `(lambda ,(lambda-formals (ffn-symb term))
                   ,(eliminate-lambda$ (lambda-body (ffn-symb term)) wrld))
                (eliminate-lambda$-lst (fargs term) wrld)))
   (t (fcons-term (ffn-symb term)
                  (eliminate-lambda$-lst (fargs term) wrld)))))

(defun eliminate-lambda$-lst (terms wrld)
  (cond ((endp terms) nil)
        (t (cons (eliminate-lambda$ (car terms) wrld)
                 (eliminate-lambda$-lst (cdr terms) wrld)))))
)

(defun tilde-@-lambda$-replacement-phrase1 (lst wrld)
  (cond ((endp lst) nil)
        (t (cons (msg "replace~%~X02 by~%~X12"
                      (unquote (fargn (lambda-object-body (car lst)) 2))
                      (eliminate-lambda$ (kwote (car lst)) wrld)
                      nil)
                 (tilde-@-lambda$-replacement-phrase1 (cdr lst) wrld)))))

(defun tilde-*-lambda$-replacement-phrase2 (lst wrld)
  (list "" "~@*~%" "~@*~%~%and~%~%" "~@*~%"
        (tilde-@-lambda$-replacement-phrase1 lst wrld)))

(defun tilde-@-lambda$-replacement-phrase3 (caller lst wrld)
  (msg "In ~s0:~%~*1"
       caller
       (tilde-*-lambda$-replacement-phrase2 lst wrld)))

(defun tilde-@-lambda$-replacement-phrase4 (alist wrld)
  (cond ((endp alist) nil)
        (t (cons (tilde-@-lambda$-replacement-phrase3 (car (car alist))
                                                      (cdr (car alist))
                                                      wrld)
                 (tilde-@-lambda$-replacement-phrase4 (cdr alist) wrld)))))

(defun tilde-*-lambda$-replacement-phrase5 (alist wrld)
  (list "" "~@*~%~%" "~@*~%~%" "~@*~%~%"
        (tilde-@-lambda$-replacement-phrase4 alist wrld)))

; Note: Once upon a time, (tilde-*-lambda$-replacement-phrase5 alist wrld), where
; alist was the output of ancestral-lambda$s-by-caller, was used as the value of
; #\0 in the following message:

;   "We prohibit certain events, including DEFCONST, DEFPKG, and DEFMACRO, from ~
;    being ancestrally dependent on lambda$ expressions.  Since loop$ ~
;    expressions expand to loop$ scion calls containing lambda$ expressions, ~
;    this prohibition means loop$ statements may not be used in these events ~
;    either.  This prohibition has to do with the loading of compiled books ~
;    before the events in the book are processed.  You must edit this event ~
;    and/or its dependents to remove lambda$ (and any loop$) expressions.  It ~
;    might be easiest to rewrite it just using old-fashioned ACL2 recursive ~
;    definitions!  But you could search through the (translations of the) ~
;    functions mentioned in this event and replace every lambda$ by the ~
;    corresponding fully-translated quoted lambda object.  Loop$ statements ~
;    should be replaced by the corresponding loop$ scion calls (e.g., collect$, ~
;    sum$, etc.) using the quoted lambda objects instead of lambda$s.   The ~
;    following table may help.~%~%~*0")

; That message was printed by simple-translate-and-eval and by defmacro-fn
; where those functions now use prohibition-of-loop$-and-lambda$-msg.  (In the
; latter use, the alist was (union-equal ancestral-lambda$s-in-guard
; ancestral-lambda$s-in-body).)  The error message was thought to be too
; complicated!  So we changed it and now only print the names of the places
; where offending loop$ and lambda$s occur.  So
; tilde-*-lambda$-replacement-phrase5 et al are currently obsolete.  But we
; preserve them and this hint of their use because they explain for each place
; how each lambda$ should be replaced by a fully-translated quoted lambda
; object.

; One reason the message above was so unhelpful is that telling the user to
; replace (LAMBDA$ (LOOP$-IVAR) (LET ((E LOOP$-IVAR)) (CONS 'HI E))) by (LAMBDA
; (E) (CONS 'HI E)) is confusing when the lambda$ doesn't appear in what the
; user actually wrote: (loop$ for e in x collect (cons 'hi e)).

(defun strings-and-others (alist strings others)

; Alist is an alist with strings and symbols as keys and we partition the keys
; into the strings and everything else.  We just throw away the values in the
; alist.

  (cond
   ((endp alist) (mv strings others))
   ((stringp (car (car alist)))
    (strings-and-others (cdr alist)
                        (cons (car (car alist)) strings)
                        others))
   (t
    (strings-and-others (cdr alist)
                        strings
                        (cons (car (car alist)) others)))))

(defun prohibition-of-loop$-and-lambda$-msg (alist)

; Alist was created by ancestral-lambda$s-by-caller.  Its keys are strings and
; symbols indicating where lambda$s (and thus also loop$s) occur in some event.
; The strings are things like "the guard of this event" and the others are
; function names ancestral in the event.  The intent of our message is ``we
; prohibit loop$ and lambda$ in certain events and here are the places you
; should look...''  But the exact form of the phrase depends on how many
; strings and others there are!  English grammar is tricky.  We know there is
; at least one string or other because we wouldn't be causing an error if there
; were none.

  (mv-let (strings others)
    (strings-and-others alist nil nil)
    (let ((i (cond ((null strings)
                    (if (null (cdr others)) 0 1))
                   ((null others) 2)
                   ((null (cdr others)) 3)
                   (t 4))))
      (msg "We prohibit certain events, including DEFCONST, DEFPKG, and ~
            DEFMACRO, from being ancestrally dependent on loop$ and lambda$ ~
            expressions.  But at least one of these prohibited expressions ~
            occurs in ~#0~[~&2 which is ancestral here~/each of ~&2 which are ~
            ancestral here~/~*1~/~*1 and in ~&2 which is ancestral here~/~*1 ~
            and in each of ~&2 which are ancestral here~].  See :DOC ~
            prohibition-of-loop$-and-lambda$."
           i
           (list "" "~s*" "~s* and " "~s*, " strings)
           others))))

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

; Keep in sync with simple-translate-and-eval-cmp.

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
                   (t (let ((ancestral-lambda$s
                             (and (f-get-global 'safe-mode state)
                                  (ancestral-lambda$s-by-caller
                                   "this event"
                                   term wrld))))
                        (cond
                         ((null ancestral-lambda$s)
                          (mv-let (erp val latches)
                            (ev term
                                (append alist
                                        (cons (cons 'state
                                                    (coerce-state-to-object
                                                     state))
                                              (user-stobj-alist state)))
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
                             (t (value (cons term val))))))
                         (t (er soft ctx "~@0"
                                (prohibition-of-loop$-and-lambda$-msg
                                 ancestral-lambda$s))))))))))

(defun error-fms-cw (hardp ctx str alist)

; Note: Recall the imagined invariant on the wormhole-data of
; comment-window-io: it is an alist and any key that is string-equal to one of
; the *tracked-warning-summaries* must be bound to a true-list.  See defmacro
; io? for details.  But this function doesn't touch the data field, so it
; maintains the invariant.

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
                                          (user-stobj-alist state)))
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

(set-guard-msg add-invisible-fns
               (msg "The call ~x0 is illegal, because the arguments are not ~
                     all symbols.  See :DOC add-invisible-fns."
                      (cons 'add-invisible-fns args)))

(set-guard-msg remove-invisible-fns
               (msg "The call ~x0 is illegal, because the arguments are not ~
                     all symbols.  See :DOC remove-invisible-fns."
                    (cons 'remove-invisible-fns args)))
