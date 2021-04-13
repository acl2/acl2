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

; This file, interface-raw.lisp, contains parts of ACL2 which we
; cannot code in ACL2 because they require constructs not in ACL2, such
; as calling the compiler.

; We start with a section that was originally in acl2-fns.lisp, but was moved
; here when sharp-atsign-read started using several functions defined in the
; sources, to avoid compiler warnings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            SUPPORT FOR #@
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro sharp-atsign-read-er (str &rest format-args)
  `(progn (loop (when (null (read-char-no-hang stream nil nil t))
                  (return)))
          (error (concatenate 'string ,str ".  See :DOC set-iprint.")
                 ,@format-args)))

(defun sharp-atsign-read (stream char n &aux (state *the-live-state*))
  (declare (ignore char n))
  (let (ch
        bad-ch
        (zero-code (char-code #\0))
        (index 0)
        (iprint-last-index (iprint-last-index state)))
    (loop
     (when (eql (setq ch (read-char stream t nil t))
                #\#)
       (return))
     (let ((digit (- (char-code ch) zero-code)))
       (cond ((or (< digit 0)
                  (> digit 9))
              (when (not bad-ch)
                (setq bad-ch ch))
              (return))
             (t
              (setq index (+ digit (* 10 index)))))))
    (cond
     (bad-ch
      (sharp-atsign-read-er
       "Non-digit character ~s following #@~s"
       bad-ch index))
     ((symbol-value (f-get-global 'certify-book-info state))
      (sharp-atsign-read-er
       "Illegal reader macro during certify-book, #@~s#"
       index))
     ((iprint-ar-illegal-index index state)
      (sharp-atsign-read-er
       "Out-of-bounds index in #@~s#"
       index))
     (t
      (let ((old-read-state ; bind special
             *iprint-read-state*))
        (cond
         ((eq old-read-state nil)
          (iprint-ar-aref1 index state))
         (t
          (let ((new-read-state-order (if (<= index iprint-last-index)
                                          '<=
                                        '>)))
            (cond
             ((eq old-read-state t)
              (setq *iprint-read-state*
                    (cons index new-read-state-order))
              (iprint-ar-aref1 index state))
             ((eq (cdr old-read-state)
                  new-read-state-order) ; both > or both <=
              (iprint-ar-aref1 index state))
             (t
              (multiple-value-bind
               (index-before index-after)
               (cond
                ((eq (cdr old-read-state) '<=)
                 (values index (car old-read-state)))
                (t ; (eq (cdr old-read-state) '>)
                 (values (car old-read-state) index)))
               (sharp-atsign-read-er
                "Attempt to read a form containing both an index~%~
                 created before the most recent rollover (#@~s#) and~%~
                 an index created after that rollover (#@~s#)"
                index-before index-after))))))))))))

(defun define-sharp-atsign ()
  (set-new-dispatch-macro-character
   #\#
   #\@
   #'sharp-atsign-read))

(eval-when

; Note: CMUCL build breaks without the check below for a compiled function.

 #-cltl2
 (load eval)
 #+cltl2
 (:load-toplevel :execute)
 (when (compiled-function-p! 'sharp-atsign-read)
   (let ((*readtable* *acl2-readtable*))
     (define-sharp-atsign))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;          EVALUATION

; Essay on Evaluation in ACL2

; This essay is structured as follows.  Terminology is explained below.

; A. Introduction
; B. Specification of the problem
; C. Sketch of correctness proof
; D. Why safe mode is necessary
; E. The template for oneification of function definitions
; F. Remarks

; Let us begin.

; A. Introduction

; Evaluation in ACL2, which takes place in the ACL2 loop and during theorem
; proving, is based on the way evaluation was done in Nqthm.  The idea is to
; "oneify" the body of a definition by replacing functions by their so-called
; "executable counterparts," sometimes called "*1* functions."  Also see :doc
; evaluation.  The primitives have *1* functions that reflect their logical
; definitions, so that for example (*1*car x), or more precisely
; (acl2_*1*_lisp::car x), returns nil when x is an atom -- except that an error
; occurs if we are checking guards (or are in so-called safe mode, as explained
; below).  Defined functions have *1* function counterparts that are defined,
; roughly speaking, by replacing each function call in their bodies by a call
; of the corresponding *1* function.

; The evaluation mechanism in ACL2 changed radically in v1-8, when guards were
; removed from the logic.  It has changed again in Version_2.6, due to a hole
; in the existing mechanism, as we explain in Part D of this Essay, below.

; B. Specification of the problem

; Our specification begins with the introduction of three notions of evaluation
; and three notions of macroexpansion.  Evaluation is relative to an (implicit)
; environment, which binds variables to ACL2 values, and operates on ACL2 terms
; that are free of macro calls.  If we want to discuss evaluation of terms that
; involve macro calls, we will compose macroexpansion and evaluation.  This
; composition represents the way that both Common Lisp and the ACL2 loop
; evaluate forms.  We also assume that there is no distinction between
; evaluation of compiled and interpreted code.  Finally, we assume that for all
; of these sorts of evaluation and expansion, macros are expanded before
; function and macro bodies are stored; this is how things are done in the ACL2
; logic and with *1* functions, and it had better be equivalent to how a Common
; Lisp does its evaluation and expansion.

; We extend classes of function symbols to classes of terms in the obvious way:
; a :logic mode term is one whose function symbols are all :logic mode function
; symbols, and similarly for the notion of :common-lisp-compliant.

; Here then are the notions promised above.

;   ACL2 logical evaluation: This procedure is an interpreter that computes
;   using definitions in the logic and obvious properties of primitives (e.g.,
;   (stringp "abc") returns t).

;   ACL2 loop evaluation: This is the procedure used in the ACL2 loop, using
;   so-called *1* functions (and higher-level routines such as raw-ev-fncall).

;   Common Lisp evaluation: As the name implies, this procedure is the one used
;   by Common Lisp.

;   ACL2 logical macroexpansion: This is any procedure that carries out the
;   usual macroexpansion algorithm (outside-in), but entirely using ACL2
;   definitions, including those of :program mode functions.  We assume that
;   macros have already been similarly expanded in function bodies, before
;   evaluation begins.  Macro bodies are evaluated using ACL2 logical
;   evaluation.  This procedure is embodied in the ACL2 definition of the
;   function translate.

;   ACL2 loop macroexpansion: This is the procedure that ACL2 actually applies
;   in order to create terms from user input.  Ideally this procedure returns
;   the same results as does ACL2 logical macroexpansion; the distinction here
;   is between what an appropriate interpreter would return (ACL2 logical
;   macroexpansion) and how ACL2 actually translates a term (ACL2 loop
;   macroexpansion).  ACL2 loop macroexpansion always takes place in safe mode.

;   Common Lisp macroexpansion: This is how Common Lisp (actually, an arbitrary
;   but fixed implementation) macroexpands forms.

; As an aside, we note the following fact that is useful in establishing the
; guarantees below, but whose proof we omit here.

;   (*) If a :common-lisp-compliant function is applied to arguments that
;   satisfy its guard (using Common Lisp evaluation), without error, then the
;   result agrees with that produced by ACL2 logical evaluation.

; Now our top-level guarantees about evaluation and macroexpansion are as
; follows, where for brevity, "evaluation" of a given type is the composition
; of macroexpansion and evaluation for that type.

;   (1) If ACL2 evaluates a :logic mode form without error, then the value
;   returned equals the result of ACL2 logical (macroexpansion and) evaluation
;   of that form.

;   (2) If furthermore that evaluation in done with guard-checking on and the
;   result of ACL2 logical macroexpansion is a :common-lisp-compliant term,
;   then any non-erroneous Common Lisp evaluation returns that same value.

; C. Sketch of correctness proof

; We now outline a proof of these guarantees by breaking them into the
; following sequence of claims.  We write "weakly implements" to mean that two
; procedures give equivalent results on given inputs when they both return
; without error, and we write "implements" if the condition can be weakened to
; assume only that the first procedure returns without error.  That is, proc1
; implements proc2 iff proc1 weakly implements proc2 and whenever proc1 returns
; without error, then so does proc2.  Above, "equivalent" means identical
; except as explained otherwise below.  Implicit in this notion is that the
; input is appropriate for the procedures; for example, our notions of
; evaluation assume that all function symbols in the input are either ACL2
; primitive functions or have been defined as functions (not macros) in ACL2.

; A more rigorous argument would proceed by induction on the length of
; histories, showing that the properties in question hold when one extends the
; history with new function and macro definitions.

;   (1a) ACL2 loop evaluation implements ACL2 logical evaluation on :logic mode
;   terms and, provided safe mode is used, on arbitrary terms.

;   (1b) ACL2 loop macroexpansion implements ACL2 logical macroexpansion.

;   (2a) ACL2 loop evaluation in safe mode weakly implements Common Lisp
;   evaluation.  The same claim holds if the assumption of safe mode is
;   replaced by the assumption that guard-checking is on, provided that the
;   input form expands to a :common-lisp-compliant term.

;   (2b) ACL2 loop macroexpansion weakly implements Common Lisp macroexpansion,
;   where results r1 (from ACL2 loop macroexpansion) and r2 (from Common Lisp
;   macroexpansion) are considered equivalent if for any environment, the ACL2
;   loop evaluation of r1 with guard-checking on returns the same result as the
;   Common Lisp evaluation of r2, provided both evaluations return without
;   error.

; Sketch of proof that guarantees hold.  Clearly (1) follows from (1a) and
; (1b), while (2) follows from (1b) and (2b).  (1a) follows by inspection of
; the template presented below, using (*) above.  (1b) follows from (1a) by
; computational induction on the macroexpansion, because ACL2 loop
; macroexpansion and ACL2 logical macroexpansion differ only in the use of loop
; or logical evaluation of macro bodies.  The first part of (2a) is argued
; similarly to (1a), while the second part is actually quite trivial by
; inspection of the template below.  Finally, (2b) follows from (2a) by a
; computational induction just as (1b) follows from (1a), with a bit of
; complication.  When we encounter a call of a macro first introduced in ACL2
; (either during the boot-strap or by a user), then we evaluate the same macro
; body for ACL2 loop evaluation as for Common Lisp evaluation, except that this
; body has first been macroexpanded using ACL2 loop macroexpansion and Common
; Lisp macroexpansion, respectively.  But these may be viewed as equivalent by
; the inductive hypothesis (where for purposes of this proof we pretend that
; macroexpansion of the body takes place as part of the process).  In the other
; case, the macro already has a Common Lisp definition (as a function or
; macro), and we have arranged that (2) holds.  For example, the ACL2 loop
; macroexpansion of (append x y z) is (binary-append x (binary-append y z)),
; and Common Lisp evaluation of the former clearly agrees with ACL2 loop
; evaluation of the latter.  Q.E.D.

; D. Why safe mode is necessary

; The soundness of ACL2 potentially rests on the principle of not calling raw
; Lisp counterparts of functions with arguments outside their intended domains,
; as specified by their guards.  Here we give three examples illustrating why
; we introduced safe mode in Version_2.6.  The third one is a proof of nil!

; Example 1.  In our first example below, the defun of bar should fail.  It
; does indeed fail starting with Version_2.6, but not in Version_2.5 or (we
; believe) several versions before that.  We discuss below how this can lead
; to unsoundness.

; (defmacro foo (x) (car x))
; (set-guard-checking nil)
; (defun bar (y)
;   (declare (xargs :verify-guards t))
;   (cons (foo y) y))
; :q
; (trace bar)
; (lp)

; Now, the result of evaluating (bar 3) looks as shown below.  Notice that the
; Common Lisp function bar is called.  If the Common Lisp evaluation of the
; form (car 'y) had returned 1 or 2 (say) instead of breaking, then the Common
; Lisp evaluation of (bar 3) would have returned (cons 1 3) or (cons 2 3),
; respectively.  This evaluation could be reflected in theorems (equal (bar 3)
; i) [i=1,2] proved in books certified in two different Common Lisp
; implementations of ACL2.  We could then prove nil by including both books
; into the same session.  Lest one think that one needs different Lisp
; implementations to expose unsoundness, imagine a single Lisp in which (car
; 'y) sometimes returns 1 and sometimes returns 2.

; ACL2 >(bar 3)
;   1> (ACL2_*1*_ACL2::BAR 3)>
;     2> (BAR 3)>
;
; Error: Y is not of type LIST.
; Fast links are on: do (si::use-fast-links nil) for debugging
; Error signalled by CAR.
; Broken at COND.  Type :H for Help.
; ACL2>>

; Here is what ACL2 Version_2.6 prints in an attempt to define function bar,
; above, with guard-checking off.

; ACL2 >(defun bar (y) (foo y))
;
;
; ACL2 Error in ( DEFUN BAR ...):  The guard for the function symbol
; CAR, which is (OR (CONSP X) (EQUAL X NIL)), is violated by the arguments
; in the call (CAR 'Y).  The guard is being checked because this function
; is a primitive and a "safe" mode is being used, perhaps for macroexpansion.
;
;
;
; ACL2 Error in ( DEFUN BAR ...):  In the attempt to macroexpand the
; form (FOO Y), evaluation of the macro body caused an error.
;
;
; Summary
; Form:  ( DEFUN BAR ...)
; Rules: NIL
; Warnings:  None
; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
;
; ******** FAILED ********  See :DOC failure  ******** FAILED ********
; ACL2 >

; Example 2.  Unlike the previous example, this one causes problems even when
; guard-checking is on.  (Thanks to Pete Manolios for helping to construct this
; example, which is simpler than an earlier one we had.)

; (defun my-endp-0 ()
;   (declare (xargs :mode :program))
;   (endp 0))
; (defmacro bad-macro ()
;   (my-endp-0))
; :q
; (trace my-endp-0 endp)
; (lp)
; (thm (equal (bad-macro) 1))

; Now look at the following Version_2.5 trace.  It highlights a behavior of
; Version_2.5: when a :program mode function (here, my-endp-0) is
; called on arguments satisfying its guard (here, implicitly t), the
; corresponding raw Lisp function is invoked.  Thus guards are not checked on
; its subroutines (here, endp).  In this example, endp is being called on an
; argument not satisfying its guard.  In the abstract, this is problematic
; because we use guards to restrict primitives to arguments for which the
; result is implementation independent.  If the result of (endp 0) can depend
; on the implementation, we could prove nil as described in the preceding
; example.

; ACL2 !>(thm (equal (bad-macro) 1))
;   1> (ACL2_*1*_ACL2::MY-ENDP-0)>
;     2> (MY-ENDP-0)>
;       3> (ENDP 0)>
;
; Error: 0 is not of type LIST.
; Fast links are on: do (si::use-fast-links nil) for debugging
; Error signalled by SYSTEM::TRACE-CALL.
; Broken at COND.  Type :H for Help.
; ACL2>>

; The example above may seem contrived (because it is!).  However, our foray
; into this territory began on a rather similar but real example.  In Allegro
; 6.0, the character (code-char (+ 128 65)) is upper case; in particular it is
; not equal to the result of applying char-downcase to it.  However, this is
; not the case for Allegro 5.0.1.  Since the result is
; implementation-dependent, it is natural to restrict the application of
; code-char to standard characters, using ACL2's guard mechanism.  But the
; example above show that we can bypass such restrictions by using macros.

; Example 3.  We can prove nil in Version_2.5 by certifying the following two
; books. The only cheats are that the first book needs to be certified after
; executing the following in the ACL2 loop:

; (set-guard-checking nil)

; First book, call it "ex":

;   (in-package "ACL2")
;
;   (defun my-eq (x y)
;     (declare (xargs :guard t ; "bad" guard
;                     :mode :program))
;     (eq x y))
;
;   (defmacro bad-macro ()
;     (my-eq '(a b) '(a b)))
;
;   (set-verify-guards-eagerness 0)
;
;   (local (verify-termination my-eq))
;
;   (defun bad-fn ()
;     (bad-macro))
;
;   (defthm bad-thm
;     (bad-fn)
;     :rule-classes nil)

; Second book, which includes the one above::

;   (in-package "ACL2")
;
;   (local (include-book "ex"))
;
;   (defthm very-bad
;     nil
;     :hints (("Goal" :use bad-thm))
;     :rule-classes nil)

; In Version_2.6 we get an error when we try to certify the first book above
; ("ex"):

;   ACL2 Error in ( DEFUN BAD-FN ...):  The guard for the function symbol
;   EQ, which is (IF (SYMBOLP X) T (SYMBOLP Y)), is violated by the arguments
;   in the call (EQ '(A B) '(A B)).  The guard is being checked because
;   this function is a primitive and a "safe" mode is being used, perhaps
;   for macroexpansion.
;
;
;
;   ACL2 Error in ( DEFUN BAD-FN ...):  In the attempt to macroexpand the
;   form (BAD-MACRO), evaluation of the macro body caused an error.

; As the first message just above suggests, in Version_2.6 we prevent the bad
; behavior illustrated by the examples above by introducing a "safe mode" for
; use during macroexpansion, in which guards are checked on built-in functions.

; Finally, note that we do not attempt to fix the following "problem."  That
; is, the behavior for the example below is unchanged from Version_2.5 to
; Version_2.6.  The point is that for macroexpansion to behave properly, we
; really need only guarantee consistency between the logic and Common Lisp; it
; is acceptable if in some modes we get errors even when errors are not
; necessary.

; (defun mac-fn (x) (declare (xargs :guard (consp x))) x)
; (defmacro mac (x) (mac-fn x))
; (defun bar (x) (mac x)) ; fails
; :set-guard-checking nil
; (defun bar (x) (mac x)) ; succeeds

; E. The template for oneification of function definitions

; Before we present this template, we give a bit of history and show an
; example.

; The following example shows how *1* functions are handled in Version_2.5 and
; before. The ACL2 definition is:

; (defun foo (x)
;   (declare (xargs :mode :logic :guard (true-listp x)))
;   (if (endp x) 3 (+ 1 (foo (cdr x)))))

; Here is the executable-counterpart in Version_2.5, in gcl:

; ACL2>(symbol-function 'ACL2_*1*_ACL2::FOO) ; in gcl, ACL2 Version_2.5
; (LISP:LAMBDA-BLOCK ACL2_*1*_ACL2::FOO (X)
;   (LABELS ((ACL2_*1*_ACL2::FOO (X)
;                (IF (ACL2_*1*_LISP::ENDP X) '3
;                    (ACL2_*1*_ACL2::BINARY-+ '1
;                        (ACL2_*1*_ACL2::FOO (ACL2_*1*_LISP::CDR X))))))
;     (LET ((ACL2_*1*_ACL2::FOO (SYMBOL-CLASS 'FOO (W *THE-LIVE-STATE*)))
;           (GUARD-CHECKING-ON
;               (F-GET-GLOBAL 'GUARD-CHECKING-ON *THE-LIVE-STATE*)))
;       (COND
;         ((LET ((*HARD-ERROR-RETURNS-NILP*
;                    (OR *HARD-ERROR-RETURNS-NILP*
;                        (NOT GUARD-CHECKING-ON))))
;            (IF (EQ ACL2_*1*_ACL2::FOO :IDEAL)
;                (ACL2_*1*_ACL2::TRUE-LISTP X) (TRUE-LISTP X)))
;          (IF (EQ ACL2_*1*_ACL2::FOO :IDEAL) (ACL2_*1*_ACL2::FOO X)
;              (FOO X)))
;         (GUARD-CHECKING-ON
;             (THROW-RAW-EV-FNCALL
;                 (LIST 'EV-FNCALL-GUARD-ER 'FOO (LIST X) '(TRUE-LISTP X)
;                       '(NIL))))
;         (T (ACL2_*1*_ACL2::FOO X))))))

; Notice the inefficiency of needlessly checking guards in Version_2.5 in the
; :ideal case when guard-checking is off.  We fix that problem in Version_2.6,
; but more importantly, we implement a "safe mode" to be used during
; macroexpansion, so that we can trust that ACL2 and Common Lisp agree when
; they are supposed to, thus avoiding the sort of problem illustrated above
; (function bar and macro mac).  We make this idea precise in our discussion of
; "Guarantees", above.

; ACL2>(symbol-function 'ACL2_*1*_ACL2::FOO) ; in gcl, ACL2 Version_2.6
; (LISP:LAMBDA-BLOCK ACL2_*1*_ACL2::FOO (X)
;   (LABELS ((ACL2_*1*_ACL2::FOO (X)
;                (IF (ACL2_*1*_LISP::ENDP X) '3
;                    (ACL2_*1*_ACL2::BINARY-+ '1
;                        (ACL2_*1*_ACL2::FOO (ACL2_*1*_LISP::CDR X))))))
;     (COND
;       ((TRUE-LISTP X) (RETURN-FROM ACL2_*1*_ACL2::FOO (FOO X)))
;       ((F-GET-GLOBAL 'GUARD-CHECKING-ON *THE-LIVE-STATE*)
;        (RETURN-FROM ACL2_*1*_ACL2::FOO
;          (THROW-RAW-EV-FNCALL
;              (LIST 'EV-FNCALL-GUARD-ER 'FOO (LIST X) '(TRUE-LISTP X)
;                    '(NIL))))))
;     (ACL2_*1*_ACL2::FOO X)))

; Next, we present a basic template (outline, really) for defining executable
; counterparts.  Note that as in the code for Version_2.5, we may optimize away
; consideration of the guard when the guard is t (either implicitly or
; explicitly).  Furthermore, we do some optimization when the symbol-class of
; the function is :common-lisp-compliant, as we do in Version_2.5 for :program
; vs. :logic mode.

; The template below uses some abbreviations <...>, which are defined below the
; template.  See also oneify-cltl-code for more details, special cases, and
; optimizations.  There we also handle the guarded-primitive-p case, which
; pertains to built-in defined functions that need to be responsible for
; checking their guards in safe-mode.  That does not however deal with true
; primitives, which are not defined.  For those, safe-mode is handled with
; calls of gv in their defun-*1* definitions.

; Finally, this template is only approximate and not necessarily up-to-date.
; It is intended to give a sense of how oneify-cltl-code works; see the code
; for up-to-date comments.  You may be better off simply by tracing
; oneify-cltl-code with hiding of the wrld argument, for example with

; (trace! (oneify-cltl-code :entry t :native t))

; -- and then executing each of the following test cases.  Follow each of these
; with (trace$ foo) to see oneification for allowing tracing of recursive calls
; when guard-checking is :none.  Then execute :u before the next defun.  Oh,
; and try guard violations too.

; (defun foo (x)
;   (declare (xargs :guard t))
;   (if (natp x) (if (zp x) 0 (* x (foo (1- x)))) 0))
; (defun foo (x)
;   (declare (xargs :guard t :verify-guards nil))
;   (if (natp x) (if (zp x) 0 (* x (foo (1- x)))) 0))
; (defun foo (x)
;   (declare (xargs :guard t :mode :program))
;   (if (natp x) (if (zp x) 0 (* x (foo (1- x)))) 0))
;
; (defun foo (x)
;   (declare (xargs :guard (natp x)))
;   (if (zp x) 0 (* x (foo (1- x)))))
; (defun foo (x)
;   (declare (xargs :guard (natp x) :mode :program))
;   (if (zp x) 0 (* x (foo (1- x)))))
; (defun foo (x)
;   (declare (xargs :guard (natp x) :verify-guards nil))
;   (if (zp x) 0 (* x (foo (1- x)))))
;
; ; This one reports a guard violation with guard-checking set to :all but not
; ; when it is set to t.
; (defun foo (x)
;   (declare (xargs :guard (evenp x) :verify-guards nil))
;   (if (zp x) 0 (* x (foo (1- x)))))
;
; (defun foo (x)
;   (if (zp x) 0 (* x (foo (1- x)))))


; (defun <*1*fn> <formals>
;   <wormhole-test-for-functions-with-user-stobjs>
;   (let ((<class> (symbol-class '<fn> (w *the-live-state*))))
;     (cond ((eq <class> :common-lisp-compliant)
;            (cond
;             ((or (equal <guard> *t*)
;                  (not (eq <guard-checking-on> :none))
;                  (acl2-system-namep name wrld))
;              (cond (<guard> ; avoid <*1*guard> since guard is known compliant
;                     (cond (<live-stobjp-test> ; test can often be omitted
;                            (return-from <*1*fn> (<fn> . <formals>)))))
;                    (<guard-checking-on> <fail_guard>))
;
; ; Otherwise fall through to final call of *1* function.
;
;            )
;
; ; The next case is not needed for our guarantees.  Rather, it ensures that
; ; evaluation with guard checking on really does check guards at each function
; ; call.
;
;           ((and <guard-checking-on>
;                 (not <*1*guard>))
;            <fail_guard>)
;           ((or (eq <guard-checking-on> :all)
;                (and <safe>
;                     (eq <class> :program)))
;            (return-from <*1*fn> *1*body))
;           ((eq <class> :program)
;            (return-from <*1*fn> (<fn> . <formals>)))
;
; ; If we fall through to here, then we compute in the logic, avoiding further
; ; guard checks in recursive calls (where a "special" declaration will take
; ; care of this if we are in a mutual-recursion nest).
;
;           (maybe-warn-for-guard <fn>)))
;
; ; In the case (eq <class> :program), we conclude by laying down the call (<fn>
; ; . <formals>).  Otherwise, we lay down the following code.
;
;   (labels
;
; ; The following local definition of <*1*fn> executes calls of <fn> in the
; ; logic, without guard-checking (except for primitives under safe-mode; see
; ; below).  Note that it is always legitimate for this local function to cause
; ; an error, so if we want to save space we can fail here, in particular for
; ; :program mode functions encountered during the boot-strap, at least outside
; ; (say) axioms.lisp -- although that would presumably eliminate the ability to
; ; call those functions in macro definitions.
;
;    ((<*1*fn>
;      <formals>
;
; ; Certain functions can take the live state as an argument, and yet do
; ; not ``properly'' handle it in their logic code.  Consider for
; ; example (princ$ '(a b) *standard-co* state).  With guard-checking
; ; off, and a live state, this form used to cause a hard error.  The
; ; problem was that the logical body of princ$ (actually, its
; ; oneification) was being executed.  Consider calling a function such
; ; as open-output-channels, which is really a call of nth, on a live
; ; state!  We believe that our problem is solved by disallowing calls
; ; of certain built-in functions on a live state argument, when passing
; ; to their oneified bodies.  These functions are those in
; ; *super-defun-wart-stobjs-in-alist*, since these are the ones that
; ; pass the state on as though it were a legitimate state object, i.e.,
; ; to functions that take non-state values as arguments.
;
; ; Other functions, such as those defined under defstobj, may have a stobj
; ; name as an argument but do not have an appropriate 'stobjs-in
; ; setting in the world, because we have not yet declared that the
; ; stobj name is a stobj.  These latter functions are characterized by
; ; having a non-nil stobj-flag, said flag being the stobj name.  We
; ; compute here the appropriate stobjs-in.
;
;      <fail_if_live_stobj> ; laid down only in cases as described above
;      *1*body))
;    (*1*fn . formals)))))
;
; WHERE:
;
; <*1*guard>
;  =
; oneification of guard
;
; <formals>
;  =
; list of formals, e.g., (x1 ... xn)
;
; <guard-checking-on>
;  =
; (f-get-global 'guard-checking-on *the-live-state*)
;
; <guard>
;  =
; [guard of the function being defined]
;
; <fail_guard>
;  =
; (throw-raw-ev-fncall
;  (list 'ev-fncall-guard-er '<fn> (list x) '<guard> '(nil) nil))
;
; <fail_safe>
;  =
; (throw-raw-ev-fncall
;  (list 'ev-fncall-guard-er '<fn> (list x) '<guard> '(nil) t))
;
; <class>
;  =
; <*1*fn>
;
; <*1*fn>
;  =
; (*1*-symbol <fn>)
;
; <fn>
;  =
; [function symbol being defined]
;
; <safe>
;  =
; (f-get-global 'safe-mode *the-live-state*)
;
; <fail_if_live_stobj>
;  =
; code for protecting against executing <*1*body> on live stobjs
;
; <live-stobjp-test>
;  =
; test that all of the stobj parameters to the function are indeed the "live"
; stobjs.  This is required because the Common Lisp code for stobj access and
; update functions assumes, starting in v2-8, that user-defined stobj parameters
; are live, a restriction enforced by the corresponding *1* functions before
; passing to Common Lisp.
;
; <wormhole-test-for-functions-with-user-stobjs>
;   =
; a test that is generated to check if one is evaluating a function with
; user-defined stobjs in a wormhole (no wormhole test is performed if the
; function does not take user-defined stobjs as arguments).  Only proper updates
; on state are allowed inside wormholes since the wormhole can properly "undo"
; these side effects upon completion.  No such mechanism exists for user-defined
; stobjs and thus the test.  Before v2-8, this wormhole test was performed in the
; stobj update primitives directly, but it is now performed in the *1* function
; as a matter of efficiency.  The exclusion of read access of user-defined stobjs
; in wormholes simplifies the code to generate the *1* body and while technically
; unnecessary, does not seem to be a relevant over-restriction in practice.

; F. Remarks

; Remark 1.  Notice that safe mode does not by itself force guard-checking in
; all cases, nor does soundness of safe mode require guard-checking as long as
; we do check guards when evaluating calls of functions that are built into
; Common Lisp.  We ensure this in the macro gv, which is changed in Version_2.6
; to cause an error when in safe mode.

; Remark 2.  Consider, in the body of *1*fn, the case that <guard-checking-on>
; holds.  If we were to replace it with (or guard-checking-on program) then we
; would always check guards when in program mode, which would give backward
; compatibility: this scheme would behave exactly as the scheme from
; Version_2.5 for and before did when the new scheme is used in other than safe
; mode.  But we have decided that starting with Version_2.6, we will no longer
; check guards for :program mode functions when 'guard-checking-on has value
; nil (though starting with Version_3.0 you can get this effect when
; 'guard-checking-on has value :none).  After all, even with guard-checking on
; in Version_2.5 you can get nasty Lisp breaks, since we slip directly into
; Common Lisp when a guard holds even though guards cannot be verified for
; :program mode functions.

; End of Essay on Evaluation in ACL2

;          ONEIFICATION

; Here are the *1* functions.  They should be kept in sync with
; *primitive-formals-and-guards*.  We could probably get by with avoiding
; defining those in the list *oneify-primitives*, for example since want to
; avoid calling "slow" functions, e.g., *1*cons instead of cons.  But we prefer
; to follow the simple rule that every function has a *1* counterpart, which is
; easy to remember.  Moreover, in the case of IF we really do want to define
; *1*if to cause an error, because we insist that the oneification of if remain
; lazy.

; WARNING: Any hand-coded *1* definitions for other than the primitives, such
; as the one for mv-list (see below), must be handled in add-trip and
; compile-uncompiled-*1*-defuns (see the handling there of mv-list).

(defmacro gv (fn args val)
  (sublis `((funny-fn . ,fn)
            (funny-args . ,args))
          `(let ((gc-on (not (gc-off *the-live-state*))))
             (if (or gc-on
                     (f-get-global 'safe-mode *the-live-state*))
                 (throw-raw-ev-fncall
                  (list 'ev-fncall-guard-er
                        'funny-fn
                        ,(cons 'list 'funny-args)
                        (guard-raw 'funny-fn (w *the-live-state*))
                        (stobjs-in 'funny-fn (w *the-live-state*))
                        (not gc-on)))
               ,val))))

; We must hand-code the *1* functions for mv-list and return-last, because
; otherwise they will simply call mv-list and return-last (resp.), which can be
; wrong: in the case of return-last, we need the first argument to be a quotep
; for the raw-Lisp macro return-last to do more than lay down a progn.

(defun-*1* mv-list (input-arity x)
  (declare (ignore input-arity))
  x)

(defun-*1* return-last (fn x y)
  (cond ((and (equal fn 'mbe1-raw)
              (f-get-global 'safe-mode *the-live-state*))

; Since return-last is a special form, we can decide how we want to view it
; with respect to guards.  We have decided to check its guard only when in safe
; mode, which is the minimal case needed in order to fix a soundness bug
; related to mbe; see note-4-3.  The following log shows what happened in a
; preliminary implementation of that bug fix, in which oneify laid down a
; *1*return-last call unconditionally; note the unfortunate call of the :exec
; function, f2.  Of course, that call is not the fault of the old version of
; *1*return-last, which is a function called after its arguments are already
; evaluated; there are other places (ev-rec and oneify) where we avoid even
; calling *1*return-last.  But if we do get to this call, for example by way of
; expand-abbreviations calling ev-fncall, at least we can limit the equality
; check here to the case of safe-mode (which is presumably nil, for example,
; under expand-abbreviations).

;   ACL2 !>(defn f1 (x) x)
;    [[... output omitted ...]]
;    F1
;   ACL2 !>(defn f2 (x) x)
;    [[... output omitted ...]];
;    F2
;   ACL2 !>(defun f (x) (mbe :logic (f1 x) :exec (f2 x)))
;    [[... output omitted ...]]
;    F
;   ACL2 !>(trace$ f f1 f2)
;    ((F) (F1) (F2))
;   ACL2 !>(f 3)
;   1> (ACL2_*1*_ACL2::F 3)
;     2> (ACL2_*1*_ACL2::F2 3)
;       3> (F2 3)
;       <3 (F2 3)
;     <2 (ACL2_*1*_ACL2::F2 3)
;     2> (ACL2_*1*_ACL2::F1 3)
;       3> (F1 3)
;       <3 (F1 3)
;     <2 (ACL2_*1*_ACL2::F1 3)
;   <1 (ACL2_*1*_ACL2::F 3)
;   3
;   ACL2 !>

         (if (equal x y)
             y
           (gv return-last (fn x y)
               y)))
        (t y)))

; We must hand-code the *1* function for wormhole-eval because if it were
; automatically generated it would look like this:

; (defun ACL2_*1*_ACL2::WORMHOLE-EVAL (qname qlambda free-vars)
;    (wormhole-eval qname qlambda free-vars))

; (To see where this code would be generated, find the comment beginning
; "Optimization in a common case" in oneify-cltl-code.)

; But the body of the *1* defun above violates the requirement that the
; wormhole-eval macro always be applied to a quoted name and lambda expression.
; In particular, if the default optimized code above is generated and then
; given to raw lisp, a hard error results when the wormhole-eval macro tries to
; cadr into qname.  So what should be here?  Intuitively we ought to lay down
; code that checks that qlambda is a well-formed and appropriate lambda
; expression and then apply it to the wormhole status of the wormhole with the
; name qname.  But in fact this *1* function should never be called except from
; within the theorem prover when we are evaluating wormhole-eval on quoted
; constants.  Thus, we just return nil, it's logical value, without attempting
; to do any of the wormhole stuff.

(defun-*1* wormhole-eval (qname qlambda free-vars)
  (declare (ignore qname qlambda free-vars))
  nil)

; Keep the rest of these in sync with the completion-of-* axioms in
; axioms.lisp.

(defun-*1* acl2-numberp (x)
  (numberp x))

(defun-*1* binary-* (x y)
  (the number
       (if (numberp x)
           (if (numberp y)
               (* x y)
             (gv binary-* (x y) 0))
         (gv binary-* (x y) 0))))

(defun-*1* binary-+ (x y)
  (the number
       (if (numberp x)
           (if (numberp y)
               (+ (the number x) (the number y))
             (gv binary-+ (x y) x))
         (gv binary-+ (x y)
             (if (numberp y)
                 y
               0)))))

(defun-*1* unary-- (x)
  (the number
       (if (numberp x)
           (- x)
         (gv unary-- (x) 0))))

(defun-*1* unary-/ (x)
  (the number
       (if (and (numberp x) (not (= x 0)))
           (/ x)
         (gv unary-/ (x) 0))))

(defun-*1* < (x y)

; If one regards (gv op args val) simply as val, then we can prove that
; the body below is equivalent to the let-expression used for val.  Put
; another way, if we use << as the "familiar" less-than on the rationals
; then this definition of < is equivalent to
; (< x y) = (let ((x1 (if (acl2-numberp x) x 0))
;                 (y1 (if (acl2-numberp y) y 0)))
;            (or (<< (realpart x1) (realpart y1))
;                (and (= (realpart x1) (realpart y1))
;                     (<< (imagpart x1) (imagpart y1)))))
; The consideration of the case where both x and y are rational is just
; an optimization.

  (if (and (rationalp x)
           (rationalp y))
      (< (the rational x) (the rational y))
    (gv < (x y)
        (let ((x1 (if (numberp x) x 0))
              (y1 (if (numberp y) y 0)))
          (or (< (realpart x1) (realpart y1))
              (and (= (realpart x1) (realpart y1))
                   (< (imagpart x1) (imagpart y1))))))))


(defun-*1* apply (x y)
  (error "We have called apply on ~s and ~s, but we thought we were rid of apply."
         x y))

(defun-*1* bad-atom<= (x y)
  (cond ((and (bad-atom x) (bad-atom y))

; The following should never happen.

         (error "We have called (the executable-counterpart of) bad-atom<= on ~
                 ~s and ~s, but bad-atom<= has no Common Lisp definition."
                x y))
        (t (gv bad-atom<= (x y) nil))))

(defun-*1* car (x)
  (cond
   ((consp x)
    (car x))
   ((null x)
    nil)
   (t (gv car (x) nil))))

(defun-*1* cdr (x)
  (cond
   ((consp x)
    (cdr x))
   ((null x)
    nil)
   (t (gv cdr (x) nil))))

(defun-*1* char-code (x)
  (if (characterp x)
      (char-code x)
    (gv char-code (x) 0)))

(defun-*1* characterp (x)
  (characterp x))

(defun-*1* code-char (x)
  (if (and (integerp x)
           (>= x 0)
           (< x 256))
      (code-char x)
    (gv code-char (x) (code-char 0))))

(defun-*1* complex (x y)
  (complex (the rational (if (rationalp x) x (gv complex (x y) 0)))
           (the rational (if (rationalp y) y (gv complex (x y) 0)))))

(defun-*1* complex-rationalp (x)
  (complexp x))

;; Historical Comment from Ruben Gamboa:
;; I added this function to recognize the complex numbers.

#+:non-standard-analysis
(defun-*1* complexp (x)
  (complexp x))

(defun-*1* coerce (x y)
  (cond
   ((equal y 'list)
    (if (stringp x)
        (coerce x 'list)
      (gv coerce (x y) nil)))
   ((character-listp x)
    (if (equal y 'string)
        (coerce x 'string)
      (gv coerce (x y) (coerce x 'string))))
   (t
    (gv coerce (x y)
        (coerce (make-character-list x) 'string)))))

(defun-*1* cons (x y)
  (cons x y))

(defun-*1* consp (x)
  (consp x))

(defun-*1* denominator (x)
  (if (rationalp x)
      (denominator x)
    (gv denominator (x) 1)))

(defun-*1* equal (x y)
  (equal x y))

#+:non-standard-analysis
(defun-*1* floor1 (x)

;; Historical Comment from Ruben Gamboa:
;; I added this function to evaluate the special floor1
;; function, which computes floor with a modulus of 1.

  (if (rationalp x)
      (floor x 1)
    (gv floor1 (x) 0)))

(defun-*1* if (x y z)
  (error "We just can't stand having a non-lazy IF around.  But we attempted ~%~
          to call the executable-counterpart of IF on argument list ~s."
         (list x y z)))

(defun-*1* imagpart (x)
  (if (numberp x)
      (imagpart x)
    (gv imagpart (x) 0)))

(defun-*1* integerp (x)
  (integerp x))

(defun-*1* intern-in-package-of-symbol (x y)
  (if (and (stringp x)
           (symbolp y))
      (intern-in-package-of-symbol x y)
    (gv intern-in-package-of-symbol (x y) nil)))

(defun-*1* pkg-imports (pkg)
  (if (stringp pkg)
      (pkg-imports pkg)
    (gv pkg-imports (pkg) nil)))

(defun-*1* pkg-witness (pkg)
  (if (stringp pkg)
      (pkg-witness pkg)
    (gv pkg-witness (pkg) (intern *pkg-witness-name* "ACL2"))))

(defun-*1* numerator (x)
  (if (rationalp x)
      (numerator x)
    (gv numerator (x) 0)))

(defun-*1* rationalp (x)
  (rationalp x))

;; Historical Comment from Ruben Gamboa:
;; I added realp to recognize real numbers.

#+:non-standard-analysis
(defun-*1* realp (x)
  (realp x))

(defun-*1* realpart (x)
  (if (numberp x)
      (realpart x)
    (gv realpart (x) 0)))

(defun-*1* stringp (x)
  (stringp x))

(defun-*1* symbol-name (x)
  (if (symbolp x)
      (symbol-name x)
    (gv symbol-name (x) "")))

(defun-*1* symbol-package-name (x)
  (if (symbolp x)
      (progn (chk-bad-lisp-object x)
             (symbol-package-name x))
    (gv symbol-package-name (x) "")))

(defun-*1* symbolp (x)
  (symbolp x))

(defun-*1* apply$-lambda (fn args)
  (declare (ftype (function (t t) (values t))
                  ev$))
  (if (apply$-lambda-guard fn args) ; guard
      (apply$-lambda fn args)
    (gv apply$-lambda (fn args) (apply$-lambda-logical fn args))))

;; Historical Comment from Ruben Gamboa:
;; I added *1*-defns for the non-standard predicates.  Note,
;; however, that the non-standard predicates do NOT have an executable
;; counterpart.  (Actually, that's too hasty.  Standard-part could be
;; defined as "identity" and standardp could be "t".
;; Nothing can be done about i-large-integer, though.)  So, these
;; functions simply throw an error [added by Matt...: -- or, they did
;; at one time.  For efficiency it was useful to allow these to compute
;; on valid ACL2 objects (see bad-lisp-objectp); actually Ruben already
;; had made such changes].

#+:non-standard-analysis
(progn

(defun standardp (x)
  (declare (ignore x))
  t)

(defun-*1* standardp (x)
  (declare (ignore x))
  t)

(defun standard-part (x)
 x)

(defun-*1* standard-part (x)
  x)

(defun i-large-integer ()
  (throw-raw-ev-fncall '(ev-fncall-null-body-er nil i-large-integer)))

(defun-*1* i-large-integer ()
  (throw-raw-ev-fncall '(ev-fncall-null-body-er nil i-large-integer)))

)

(defun-one-output macroexpand1! (x)
  (mv-let (erp val state)
          (macroexpand1 x 'oneify *the-live-state*)
          (declare (ignore erp state))
          val))

(mutual-recursion

(defun-one-output oneify-flet-bindings (alist fns w program-p)

; We throw away all type declarations.  If we were to keep a type declaration
; (satisfies fn), we would have to find it and convert it (at least in general)
; to (satisfies *1*fn).  By ignoring such declarations, we may allow a function
; to avoid a guard violation that we might have expected, for example:

; (flet ((foo (x) (declare (type integer x)) x)) 'a)

; This is however perfectly OK, provided we are clear that flet type
; declarations are only relevant for guard verification, not guard checking.

  (cond ((endp alist) nil)
        (t (cons (let* ((def (car alist))
                        (dcls (append-lst
                               (strip-cdrs (remove-strings (butlast (cddr def)
                                                                    1)))))
                        (ignore-vars (ignore-vars dcls))
                        (oneified-body
                         (oneify (car (last def)) fns w program-p)))
                   (list* (*1*-symbol (car def))
                          (cadr def)
                          (if ignore-vars
                              (list `(declare (ignore ,@ignore-vars))
                                    oneified-body)
                            (list oneified-body))))
                 (oneify-flet-bindings (cdr alist) fns w program-p)))))

(defun remove-type-dcls (dcls)

; Before we called this function in oneify, the following caused an error in
; some Lisps (specifically, we have seen it in ACL2 Version_6.5 built on SBCL
; Version 1.2.1).

;   (defun f (x)
;     (declare (xargs :guard (natp x)))
;     (let ((y (1+ x)))
;       (declare (type (integer 0 *) y))
;       y))
;   (set-guard-checking nil)
;   (f -3)

; Our fix is to leave some of the DECLAREs in place, in particular so that the
; compiler can see the IGNOREs, but to fold type declarations into the body as
; a THE wrapper.

  (let* ((alist nil)
         (new-dcls
          (loop for dcl in dcls
                as dcl2 =
                (assert$
                 (and (consp dcl)
                      (eq (car dcl) 'declare))
                 (cond ((assoc-eq 'type (cdr dcl)) ; optimization
                        (let ((dcl2-body
                               (loop for d in (cdr dcl)
                                     when
                                     (cond
                                      ((eq (car d) 'type)
                                       (let ((tp (cadr d)))
                                         (case-match tp
                                           (('or 't . &)

; See the-fn.  We excise this no-op type declaration in order to avoid an
; infinite loop in oneify.

                                            nil)
                                           (&
                                            (loop for v in (cddr d)
                                                  collect
                                                  (push `(,tp . ,v)
                                                        alist)))))
                                       nil)
                                      (t t))
                                     collect d)))
                          (and dcl2-body (cons 'declare dcl2-body))))
                       (t dcl)))
                when dcl2
                collect dcl2)))
    (values new-dcls alist)))

(defun alist-to-the-for-*1*-lst (type-to-var-alist)
  (cond ((endp type-to-var-alist)
         nil)
        (t (cons `(the-for-*1* ,(caar type-to-var-alist)
                               ,(cdar type-to-var-alist) )
                 (alist-to-the-for-*1*-lst (cdr type-to-var-alist))))))

(defun-one-output oneify (x fns w program-p)

; Keep this function in sync with translate11.  Errors have generally been
; removed, since we know they can't occur.

; Fns is a list of fns that have been flet-bound.  It is important not to treat
; any of these as macros.

; Program-p is true when we want an MBE to use its :exec version.  Thus, use
; program-p = t when attempting to approximate raw Lisp behavior.

  (cond
   ((atom x)
    (cond ((keywordp x)
           (kwote x))
          ((symbolp x)

; At one time we returned (defined-constant x w) here in the case that
; (legal-constantp1 x).  But when the constant is replaced by its value, we can
; wind up with slow array accesses, since the constant and the written-out
; value need not be EQ.

           x)
          ((atom x) (kwote x))
          (t x)))
   ((eq (car x) 'quote)
    (cond ((and ; (consp (cdr x)) ; always true
                  (consp (cadr x))
                  (eq (car (cadr x)) 'lambda))

; Just as we apply hons-copy when translating lambda objects in
; translate11-lambda-object, we hons-copy here as well, to support fast lookup
; by fetch-cl-cache-line.

           (hons-copy x))
          (t x)))
   ((eq (car x) 'lambda$)
    (mv-let (flg tx bindings)
      (translate11-lambda-object x
                                 '(nil) ; stobjs-out
                                 nil    ; bindings
                                 nil    ; known-stobjs
                                 nil    ; flet-alist
                                 x
                                 'oneify
                                 w
                                 *default-state-vars*
                                 nil)
      (declare (ignore bindings))
      (if flg
          (interface-er "Implementation error: Translate11-lambda-object in ~
                         oneify encountered an untranslatable LAMBDA$, ~x0, ~
                         even though it was supposedly translated ~
                         successfully earlier.  Please contact the ACL2 ~
                         implementors."
                        x)
          tx)))
   ((eq (car x) 'loop$)
    (mv-let (flg tx bindings)
      (translate11-loop$
       x
       '(nil) ; stobjs-out
       nil    ; bindings
       nil    ; known-stobjs
       nil    ; flet-alist
       x
       'oneify
       w
       *default-state-vars*)
      (declare (ignore bindings))
      (if flg
          `(interface-er "Implementation error: translate11-loop$ in oneify ~
                          encountered an untranslatable LOOP$, ~x0.  We ~
                          thought that this could only happen under a call of ~
                          non-exec, in which case we should never be ~
                          executing this code!  Please contact the ACL2 ~
                          implementors."
                         ',x)
        (oneify tx fns w program-p))))
   ((not (symbolp (car x)))
    (oneify
     (list* 'let (listlis (cadr (car x))
                          (cdr x))
            (cddr (car x)))
     fns w program-p))
   ((eq (car x) 'return-last)

; Warning: Keep this in sync with stobj-let-fn and the handling of stobj-let in
; this function, in particular the case in which stobj-let-fn generates a call
; of prog2$ (or perhaps progn$).

    (let* ((qfn (and (consp (cdr x))
                     (cadr x)))
           (return-last-fn (return-last-fn qfn))
           (fn (or return-last-fn 'progn))
           (arg2 (return-last-arg2 return-last-fn
                                   (oneify (caddr x) fns w program-p))))
      (cond ((eq fn 'ec-call1-raw)

; In the case of ec-call1-raw, we are already oneifying the last argument -- we
; don't want to call return-last on top of that, or we'll be attempting to take
; the *1*-symbol of the *1*-symbol!

             (cond
              ((not (eq program-p 'invariant-risk))
               (oneify (car (last x)) fns w program-p))
              (t

; In the case that program-p is 'invariant-risk, we are in the process of
; oneifying the body of a :program mode function with invariant-risk, for which
; any call of an invariant-risk function is to execute with its *1* function
; but other calls should use raw Lisp functions; see the final case in oneify.
; Here, though, we want to call the *1* function even if it does not have
; invariant-risk, because of the ec-call wrapper.

; We need to be careful in this case that ec-call really does invoke a *1*
; function here, and does so properly.  Consider the following example.

;   (defun f-log () (mbe :logic 'logic :exec 'exec))
;   (defstobj st (fld :type integer :initially 0))
;   (defun f-prog (st)
;     (declare (xargs :stobjs st :mode :program))
;     (let ((st (update-fld 3 st)))
;       (mv (f-log) st)))
;   (f-prog st) ; returns (MV EXEC <updated-state>)
;   (defun f-prog2 (st)
;     (declare (xargs :stobjs st :mode :program))
;     (let ((st (update-fld 3 st)))
;       (mv (ec-call (f-log)) st)))
;   (f-prog2 st) ; should return (MV LOGIC <updated-state>)

; If we use the oneify call above (from the case that (not (eq program-p
; 'invariant-risk))), then EXEC would returned as a first value by the call of
; f-prog2 just above, which is incorrect.  The EXEC return value would be OK if
; f-prog2 were defined with the ec-call wrapper removed, because f-log has no
; invariant-risk and hence we want it to execute fast using the :exec form from
; its mbe.  But the ec-call means that we really want to call *1*f-log -- we
; are no longer slipping into raw Lisp and hence we no longer want the special
; **1*-as-raw* handling, which is inappropriate here since it is intended to
; give the illusion that we are in raw Lisp.  Thus, we call *1*f-log and what's
; more, we bind **1*-as-raw* to nil, to signify that we intend to execute the
; function call in the logic.

               (let ((form (car (last x))))
                 `(let* ((args (list ,@(oneify-lst (cdr form) fns w program-p)))
                         (**1*-as-raw* nil))
                    (apply ',(if (function-symbolp (car form) w)
                                 (*1*-symbol (car form))

; Otherwise, translate11 guarantees that if (car form) is f, then it is an
; abbreviation for f$inline.

                               (assert$
                                (getpropc (car form) 'macro-body nil w)
                                (*1*-symbol (add-suffix (car form)
                                                        *inline-suffix*))))
                           args))))))
            ((eq fn 'mbe1-raw)

; Here we process macroexpansions of mbe calls.

; For :program mode functions (i.e., when program-p is non-nil), an mbe call
; always reduces to its :exec value, and moreover the :logic code is only
; called in safe-mode.  Before changing this behavior, consider the comment in
; put-invariant-risk.

; See the discussion in (defun-*1* return-last ...).  Here, we discuss only the
; special variable **1*-as-raw*.

; A practice important to some users (in particular, Jared Davis has emphasized
; this) is to wrap calls of functions with symbol-class :ideal (i.e., :logic
; mode but not guard-verified) inside calls of :program mode functions, and
; expect efficient behavior.  The following example illustrates that situation.
; When evaluating (pgm st), we would like the :exec form to be executed.  Note
; that this is exactly what happens if the evaluation is in raw Lisp; here in
; oneify, we arrange for that to happen for *1* evaluation as well.

;   (defstobj st (fld :type integer :initially 0))
;
;   (defun lgc (st)
;     (declare (xargs :mode :logic
;                     :stobjs st
;                     :verify-guards nil))
;     (mbe :logic (prog2$ (cw "@@@Hello@@@~%")
;                         (update-fld 3 st))
;          :exec (update-fld 3 st)))
;
;   (defun pgm (st)
;     (declare (xargs :mode :program
;                     :stobjs st))
;     (lgc st))
;
;   (pgm st) ; no "@@@" in output

; Note that we do not give similar treatment to our evaluator (in particular,
; in ev-rec-return-last), since at the top level, we are not inside a function
; body (so there is no issue of :program or :ideal mode).  If however ev-w or
; the like is called in a function body, it will behave as though at the top
; level, thus also not being sensitive to **1*-as-raw* for lexically
; apparent calls.  That's OK.

             (let* ((oneified-logic-body (oneify (cadddr x) fns w program-p))
                    (oneified-exec-body arg2)
                    (logic-fn (and (not program-p) ; optimization
                                   (acl2-gentemp "ONEIFY")))
                    (exec-fn (acl2-gentemp "ONEIFY"))
                    (logic-body (if program-p
                                    oneified-logic-body
                                  (list logic-fn))))
               `(flet (,@(and (not program-p)
                              `((,logic-fn () ,oneified-logic-body)))
                       (,exec-fn () ,oneified-exec-body))
                  (cond
                   ((f-get-global 'safe-mode *the-live-state*)
                    (,(*1*-symbol 'return-last)
                     ,qfn
                     (,exec-fn)
                     ,logic-body))
                   (t ,(if program-p
                           `(,exec-fn)
                         `(if **1*-as-raw*
                              (,exec-fn)
                            ,logic-body)))))))
            (t

; Since fn is not 'ec-call1-raw, the guard of return-last is automatically met
; for the arguments.

             (list fn arg2 (oneify (cadddr x) fns w program-p))))))
   ((or (member-eq (car x) *oneify-primitives*)

; Note that safe-mode for make-event will require addition of the following two
; lines:
;       (member-eq (car x) (primitive-event-macros))
;       (assoc-eq (car x) *super-defun-wart-table*)

        (member-eq (car x) *macros-for-nonexpansion-in-raw-lisp*))
    (let ((args (oneify-lst (cdr x) fns w program-p)))
      (cons (car x) args)))
   ((eq (car x) 'mv-let)
    (multiple-value-bind
     (dcls alist)
     (remove-type-dcls (butlast (cdddr x) 1))
     (let* ((value-form (oneify (caddr x) fns w program-p))
            (new-body (cond (alist
                             `(progn$
                               ,@(alist-to-the-for-*1*-lst alist)
                               ,(car (last x))))
                            (t (car (last x)))))
            (body-form (oneify new-body fns w program-p)))
       `(mv-let ,(cadr x)
                ,value-form
                ,@dcls
                ,body-form))))

;     Feb 8, 1995.  Once upon a time we had the following code here:
;    ((eq (car x) 'the)
;     (let ((value-form (oneify (caddr x) w)))
;       `(the ,(cadr x) ,value-form)))
;    But that led to garbage for a user defined function like
;    (defun foo (x) (declare (xargs :verify-guards nil)) (the integer x))
;    because (foo 3) = 3 but (foo t) would cause a hard error.  We now
;    just macroexpand the just like we would any other macro.  We are not
;    sure why we ever thought we could handle it any other way.

   ((eq (car x) 'flet) ; (flet ((fn1 ...) (fn2 ...) ...) declare-form* body)
    (list 'flet
          (oneify-flet-bindings (cadr x) fns w program-p)
          (oneify (car (last x))
                  (union-eq (strip-cars (cadr x)) fns)
                  w
                  program-p)))
   ((eq (car x) 'translate-and-test)
    (oneify (caddr x) fns w program-p))
   ((eq (car x) 'with-local-stobj)
    (mv-let (erp st mv-let-form creator)
            (parse-with-local-stobj (cdr x))
            (declare (ignore erp)) ; should be nil
            (mv-let-for-with-local-stobj mv-let-form st creator fns w
                                         program-p)))
   ((eq (car x) 'stobj-let)

; Stobj-let is rather complicated, so we prefer to take advantage of the logic
; code for that macro.

    (let ((temp (oneify (stobj-let-fn x)
                        fns w program-p)))
      (case-match temp

; Warning: Keep these cases in sync with stobj-let-fn.

        (('let bindings . rest)
         `(let* ,bindings ,@rest))
        (('progn conjoined-no-dups-exprs
                 ('let bindings . rest))

; Warning: Keep this case in sync with the definition of (prog2$ x y) as
; (return-last 'progn x y), and in sync with the handling of such a return-last
; form by oneify.

         `(progn ,conjoined-no-dups-exprs
                 (let* ,bindings ,@rest)))
        (& (interface-er "Implementation error: unexpected form of stobj-let ~
                          encountered by ~
                          oneify!.~|~%Input:~|~y0~%Output:~|~y1~%Please ~
                          contact the ACL2 implementors."
                         x temp)))))
   ((member-eq (car x) '(let #+acl2-par plet))
    (let* (#+acl2-par
           (granularity-decl (and (eq (car x) 'plet)
                                  (eq (car (cadr x)) 'declare)
                                  (cadr x)))
           (args #+acl2-par (if granularity-decl (cddr x) (cdr x))
                 #-acl2-par (cdr x))
           (bindings (car args))
           (post-bindings (cdr args)))
      (multiple-value-bind
       (dcls alist)
       (remove-type-dcls (butlast post-bindings 1))
       (let* ((value-forms (oneify-lst (strip-cadrs bindings) fns w program-p))
              (new-body (cond (alist
                               `(progn$
                                 ,@(alist-to-the-for-*1*-lst alist)
                                 ,(car (last post-bindings))))
                              (t (car (last post-bindings)))))
              (body-form (oneify new-body fns w program-p)))
         `(,(car x)
           #+acl2-par
           ,@(and granularity-decl
                  `((declare (granularity
                              ,(oneify (cadr (cadr (cadr x))) fns w program-p)))))
           ,(listlis (strip-cars bindings)
                     value-forms)
           ,@dcls
           ,body-form)))))
   #+acl2-par
   ((member-eq (car x) '(pand por pargs))
    (if (declare-granularity-p (cadr x))
        (list* (car x)
               `(declare (granularity
                          ,(oneify (cadr (cadr (cadr x))) fns w program-p)))
               (oneify-lst (cddr x) fns w program-p))
      (cons (car x)
            (oneify-lst (cdr x) fns w program-p))))
   ((eq (car x) 'throw-or-attach) ; already handled in oneify-cltl-code
    (interface-er
     "Implementation error: Unexpected call of throw-or-attach in oneify:~%~x0"
     x))
   ((and (getpropc (car x) 'macro-body nil w)
         (not (member-eq (car x) fns)))
    (oneify (macroexpand1! x) fns w program-p))
   ((eq (car x) 'wormhole-eval)

; We know that in a well-formed term (wormhole-eval x y z), x is a quoted
; constant naming the wormhole, y is a lambda object of either the form (lambda
; (whs) body) or (lambda () body) that will be applied to the wormhole status,
; and z is some well-formed (irrelevant) term.  The oneify of a quote is
; itself, so we don't have to do anything to x.  But with y, we oneify the
; lambda body.  The ``call'' of wormhole-eval laid down below is a reference to
; the macro definition for that symbol in raw Lisp.

    (let* ((qname (cadr x))
           (qlambda (caddr x))
           (formals (cadr (cadr qlambda)))
           (body (caddr (cadr qlambda))))
      (list 'wormhole-eval
            qname
            (list 'quote (list 'lambda formals (oneify body fns w program-p)))
            *nil*)))
   (t
    (let ((arg-forms (oneify-lst (cdr x) fns w program-p))
          (fn (cond ((and (eq program-p 'invariant-risk)
                          (not (getpropc (car x) 'invariant-risk nil w)))

; Oneify was called at the top level with program-p 'invariant-risk.  There is
; no need for sub-functions with no invariant-risk to be called using their *1*
; functions.

                     (car x))
                    (t (*1*-symbol (car x))))))
      (cons fn arg-forms)))))

(defun-one-output oneify-lst (lst fns w program-p)
  (cond ((atom lst) nil)
        (t (let ((x (oneify (car lst) fns w program-p))
                 (y (oneify-lst (cdr lst) fns w program-p)))
             (cons x y)))))

)

(defun-one-output select-stobj (name stobjs terms)
  (cond ((endp stobjs) nil)
        ((eq name (car stobjs)) (car terms))
        (t (select-stobj name (cdr stobjs) (cdr terms)))))

(defun-one-output super-defstobj-wart-stobjs-in (formals stobj-flag)
  (cond ((endp formals) nil)
        ((eq (car formals) stobj-flag)
         (cons stobj-flag
               (super-defstobj-wart-stobjs-in (cdr formals) stobj-flag)))
        (t (cons nil
                 (super-defstobj-wart-stobjs-in (cdr formals) stobj-flag)))))

(defun-one-output oneify-fail-form (er-type fn formals guard super-stobjs-in
                                            wrld extra)

; Warning: If you change this code, see the comment about "When changing
; oneify-fail-form" in oneify-cltl-code.

  `(throw-raw-ev-fncall
    (list ',er-type
          ',fn
          (list ,@formals)
          ',guard
          ',(or super-stobjs-in
                (stobjs-in fn wrld)
                (if formals
                    (er hard 'oneify-cltl-code
                        "I didn't think this could happen, but for fn = ~x0 ~
                         stobjs-in is nil and formals isn't."
                        fn)
                  nil))
          ,extra)))

(defun-one-output get-declared-stobjs (edcls)

; Keep this in sync with get-declared-stobj-names (which does checking and
; returns a value triple).

  (if (endp edcls)
      nil
    (union-eq (and (eq (caar edcls) 'xargs)
                   (let ((stobjs (cadr (assoc-keyword :STOBJS (cdar edcls)))))
                     (cond ((symbol-listp stobjs) stobjs)
                           ((and stobjs (symbolp stobjs)) (list stobjs))
                           (t nil))))
              (get-declared-stobjs (cdr edcls)))))

(defun maybe-warn-for-guard-body (fn state)
  (assert$ (f-get-global 'raw-guard-warningp state)
           (pprogn (f-put-global 'raw-guard-warningp nil state)
                   (warning$ 'top-level "Guards"
                             "Guard-checking will be inhibited for some ~
                              recursive calls, including ~x0; see :DOC ~
                              guard-checking-inhibited."
                             fn))))

(defun-one-output create-live-user-stobjp-test (stobjs)
  (if (endp stobjs)
      t
    (let* ((stj (car stobjs))
           (rst (create-live-user-stobjp-test (cdr stobjs)))
           (tst `(live-stobjp ,stj)))
      (cond ((eq stj 'state) rst)
            ((eq rst t) tst)
            (t `(and ,tst ,rst))))))

(defun labels-form-for-*1* (fn *1*fn formals *1*body
                               ignore-vars ignorable-vars
                               super-stobjs-in super-stobjs-chk
                               guard wrld)
  (let ((*1*fn-binding `(,*1*fn
                         ,formals
                         ,@(and ignore-vars
                                `((declare (ignore ,@ignore-vars))))
                         ,@(and ignorable-vars
                                `((declare (ignorable ,@ignorable-vars))))
                         ,@(and super-stobjs-in

; If the form below is removed, we might expect to get a hard Lisp error from
; the following:

; (defstobj foo (arr :type (array t (10))))
; (set-guard-checking nil)
; (update-arri 20 4 foo)

; The problem would seem to be that an ill-guarded call of update-nth has
; replaced a copy of the stobj array by a list in (user-stobj-alist
; *the-live-state*), which produces a mismatch with *the-live-foo*.

; However, no such error occurs.  At some point we may spend the energy to
; convince ourselves that it is safe to remove this code, but for now, it seems
; harmless enough to leave it here, since super-stobjs-chk is a fast test.

                                `((when ,super-stobjs-chk
                                    ,(oneify-fail-form
                                      'ev-fncall-guard-er fn formals
                                      guard super-stobjs-in wrld
                                      :live-stobj))))
                         ,*1*body)))
    `(labels (,*1*fn-binding)
             (,*1*fn ,@formals))))

(defun oneify-cltl-code (defun-mode def stobj-flag wrld
                          &optional trace-rec-for-none)

; Warning: Keep this in sync with intro-udf-lst2 for the case that defun-mode
; is nil (i.e., the non-executable case).

; This function is called when add-trip encounters a 'cltl-command triple,
; which is laid down by install-event after the triple for the symbol-class is
; laid down.  Thus, the symbol-class for the function at hand has already been
; stored.  Stobj-flag is the name of the stobj (whether from defstobj or
; defabsstobj), if any, that the given definition supports.

; Warning: wrld is not necessarily the ACL2 world at the time def is submitted.
; See the comment below in the binding of cl-compliant-p-optimization.
; However, wrld is a legal ACL2 world, typically, the current ACL2 world.

; See the template above for detailed comments, which however are not
; necessarily kept fully up-to-date.

  (when (and stobj-flag (null (cadr def)))

; We want to know if (car def) is a stobj creator, but it is premature to call
; stobj-creatorp using wrld because the necessary properties have not yet been
; laid down.  So we use the test above.  Keep this null test in sync with the
; one in stobj-creatorp.

    (return-from oneify-cltl-code
                 `(,(*1*-symbol (car def)) nil
                   (throw-raw-ev-fncall ; as in oneify-fail-form
                    (list 'ev-fncall-creator-er ',(car def))))))

  (when (null defun-mode)

; We have a non-executable function, where def is generated by intro-udf-lst2.
; Suppose an attachment is to be invoked.  In the :non-executable :program case
; (i.e., ``proxy'' case, as in defproxy), we pass control to the *1* function
; for the attachment, since :skip-checks t is specified not to do any checking
; in this case (see :DOC defproxy).  Otherwise, we proceed as though all checks
; have been made (again, see :DOC defproxy), in particular going straight to
; the raw Lisp function if we see that the guard is t, since then the guard of
; the attachment is also presumably true.

    (return-from oneify-cltl-code
                 (case-match def
                   ((fn formals ('declare ('xargs ':non-executable ':program))
                        ('throw-or-attach fn formals))
                    `(,(*1*-symbol fn)
                      ,formals
                      (throw-or-attach ,fn ,formals t)))
                   ((fn formals ('declare ('xargs ':guard guard))
                        ('throw-or-attach fn formals))
                    `(,(*1*-symbol fn)
                      ,formals
                      ,(cond ((or (eq guard t)
                                  (equal guard *t*))
                              (car (last def)))
                             (t
                              `(throw-or-attach ,fn ,formals t)))))
                   ((fn formals
                        ('throw-or-attach fn formals)) ; implicit :guard of t
                    (prog2$ formals                    ; avoid compiler warning
                            `(,(*1*-symbol fn) ,@(cdr def))))
                   ((fn formals
                        ('throw-without-attach 'nil fn formals))
                    (prog2$ formals ; avoid compiler warning
                            `(,(*1*-symbol fn) ,@(cdr def))))
                   (& (interface-er
                       "Implementation error: Oneify-cltl-code encountered ~
                        non-executable definition, ~x0, that was not what we ~
                        would expect to be generated by intro-udf-lst2."
                       def)))))
  (mv-let
   (dcls guard)

; We call dcls-guard-raw-from-def both here and via the call of guard-raw in
; oneify-cltl-code, so that the logical behavior for guard violations agrees
; with what is actually executed.

   (dcls-guard-raw-from-def def wrld)
   (let* ((guard-is-t (and (or (eq guard t)
                               (equal guard *t*))

; If stobj-flag is true, normally the guard will not be t because it will
; include a corresponding stobj recognizer call.  But the guard could be t in
; the case of a function exported by a defabsstobj, where the guard is derived
; from the :logic function specified for that export.  We want to avoid the
; optimization of defining the *1* function to call the raw Lisp function in
; this case, so that appropriate live stobj checks can be made.

                           (not (and stobj-flag
; But is it an abstract stobj?
                                     (getpropc stobj-flag 'absstobj-info nil
                                               wrld)))))
          (fn (car def))
          (*1*fn (*1*-symbol fn))
          (cl-compliant-p-optimization
           (and (eq defun-mode :logic)

; One might think that the conjunct above is implied by the one below.  But
; consider this book:

;   (in-package "ACL2")
;   (defun foo (x)
;     (declare (xargs :mode :program))
;     x)
;   (verify-termination foo)
;   (verify-guards foo)

; At one point we checked the symbol-class first, and then did an assert check
; that defun-mode is :logic -- and we got the assertion error during Step 3 of
; certify-book for this example!  The backtrace looked like this:

;   1. THROW-RAW-EV-FNCALL
;   2. (HARD-ERROR ASSERT$ ...)
;   3. ONEIFY-CLTL-CODE
;   4. INSTALL-DEFS-FOR-ADD-TRIP
;   5. HCOMP-BUILD-FROM-STATE-RAW

; The problem was that the world wasn't rolled back by Step 3, and hence foo
; was :common-lisp-compliant at the point where we were processing the first
; defun.  Our solution is to make sure that we are oneifying a function that is
; truly :common-lisp-compliant.

                (eq (symbol-class fn wrld) :common-lisp-compliant)))
          (formals (cadr def))
          (boot-strap-p (f-get-global 'boot-strap-flg *the-live-state*)))
     (cond
      ((or (and guard-is-t cl-compliant-p-optimization)
           (and boot-strap-p ; optimization (well, except for :redef)
                (member-eq fn
                           '(thm-fn
                             make-event-fn
                             certify-book-fn
; Keep the following in sync with primitive-event-macros.
                             defun-fn
                             ;; #+:non-standard-analysis
                             ;; defun-std ; defun-fn
                             defuns-fn ; mutual-recursion
                             ;; defuns ; calls defuns-fn, above
                             defthm-fn
                             ;; #+:non-standard-analysis
                             ;; defthm-std ; calls defthm-fn, above
                             defaxiom-fn
                             defconst-fn
                             defstobj-fn defabsstobj-fn
                             defpkg-fn
                             deflabel-fn
                             deftheory-fn
                             defchoose-fn
                             verify-guards-fn
                             defmacro-fn
                             in-theory-fn
                             in-arithmetic-theory-fn
                             regenerate-tau-database-fn
                             push-untouchable-fn
                             remove-untouchable-fn
                             reset-prehistory-fn
                             set-body-fn
                             table-fn
                             progn-fn
                             encapsulate-fn
                             include-book-fn
                             change-include-book-dir
                             comp-fn
                             verify-termination-fn
                             verify-termination-boot-strap-fn
                             ;; add-match-free-override ; should be fast enough

; Theory-invariant is included in *macros-for-nonexpansion-in-raw-lisp*.  The
; remaining members of primitive-event-macros, after theory-invariant, are
; handled well enough already since we included table-fn above.
                             ))))

; Optimization in a common case: avoid labels function.  Note that if the guard
; is t then there are no stobjs except for the recognizer, whose raw Lisp code
; can handle non-live stobjs.

       `(,*1*fn
         ,formals
         ,(cons fn formals)))
      (t
       (let* ((program-p (eq defun-mode :program))
              (invariant-risk
               (and program-p
                    (getpropc fn 'invariant-risk nil wrld)))
              (super-stobjs-in ; At a "leaf" of a stobj-based computation?
               (if stobj-flag

; Then we are looking at a function introduced by a defstobj or defabsstobj
; event.

                   (let ((temp (super-defstobj-wart-stobjs-in formals
                                                              stobj-flag)))
                     (cond ((find-first-non-nil temp)
                            temp)
                           (t nil)))

; Else see if we are looking at a function that takes state but has logic code
; that does not handle a live state properly (and not just because of calls to
; lower-level functions with that problem).

                 (cdr (assoc-eq fn *super-defun-wart-stobjs-in-alist*))))
              (ignore-vars

; If super-stobjs-in is non-nil, then we will lay down a call (oneify-fail-form
; ... :live-stobj) that refers to all the formals; hence ignore-vars should be
; nil if super-stobjs-in is non-nil.  When changing oneify-fail-form, consider
; changing this code as well.

               (and (not super-stobjs-in) (ignore-vars dcls)))
              (ignorable-vars (ignorable-vars dcls))
              (declared-stobjs (if stobj-flag
                                   (list stobj-flag)
                                 (get-declared-stobjs dcls)))
              (user-stobj-is-arg (and declared-stobjs
                                      (not (equal declared-stobjs '(state)))))
              (live-stobjp-test (create-live-user-stobjp-test declared-stobjs))

; We throw away most declarations and the doc string, keeping only ignore and
; ignorable declarations.  Note that it is quite reasonable to ignore
; declarations when constructing ``slow'' functions.

              (body (car (last def)))
              (*1*body

; WARNING!  We need to be very careful that we only use *1*body in an
; environment where *1*fn refers to the top-level function currently being
; defined.  We should not use *1*body in the scope of a top-level flet or
; labels that rebinds *1*fn, since recursive calls there of *1*fn are
; presumably intended to refer to the top-level function, not the local
; function, so that guards can be checked etc.  We can, however, use *1*body in
; the binding of such a local definition.  We will be free to use *1*body in
; the body of the top-level definition of *1*fn in the case of :program mode
; because we promise not to introduce a top-level flet in that case.

               (oneify body nil wrld program-p))
              (guard-checking-on-form

; Functions in the ev-rec nest have a gc-off parameter that we generally assume
; to correspond with the state global guard-checking-on used here, so that the
; logic-only and raw lisp code agree.  See the comment in *ev-shortcut-okp*.

               (cond (super-stobjs-in
                      '(let ((temp (f-get-global 'guard-checking-on
                                                 *the-live-state*)))
                         (cond ((or (eq temp :none) (eq temp nil))

; Calls of a stobj primitive that takes its stobj as an argument are always
; guard-checked.  If that changes, consider also changing
; ev-fncall-rec-logical.  Note that we rely on this guard-checking for handling
; of invariant-risk; we arrange that evaluation stays with *1* functions up to
; reaching the stobj primitive, which is responsible for causing a guard
; violation rather than allowing an invariant to be violated.

                                t)
                               (t temp))))
                     (t '(f-get-global 'guard-checking-on *the-live-state*))))
              (skip-early-exit-code-when-none
               (and (eq defun-mode :logic) ; :program handled elsewhere

; We generally skip some special "early exit" code when 'guard-checking-on has
; value :none.  But it seems scary to allow :none to avoid raw Lisp for
; built-ins, even in :logic mode, because of efficiency.  So when we are in the
; boot-strap, we do the early exit code (which can call the raw Lisp function)
; even if 'guard-checking-on has value :none.  Exception: We want the-check to
; avoid guard errors when 'guard-checking-on has value :none.

                    (or (not boot-strap-p)
                        (eq fn 'the-check))))
              (guard-checking-is-really-on-form

; This variable should only be used in the scope of the binding expression for
; early-exit-code.

               (cond (super-stobjs-in

; The value of guard-checking-on has already been coerced from :none or nil to
; t, in guard-checking-on-form.

                      t)
                     (skip-early-exit-code-when-none

; As mentioned above, guard-checking-is-really-on-form is only used for
; defining early-exit-code.  But evaluation of early-exit-code is skipped when
; 'guard-checking-on has value :none in the present case, where
; skip-early-exit-code-when-none is true.

                      guard-checking-on-form)
                     (t `(let ((x ,guard-checking-on-form))
                           (and x
                                (not (eq x :none)))))))
              (fail_guard ; form for reporting guard failure
               (oneify-fail-form
                'ev-fncall-guard-er fn formals guard super-stobjs-in wrld
                (and super-stobjs-in
                     '(cond ((member-eq (f-get-global 'guard-checking-on
                                                      *the-live-state*)
                                        '(nil :none))
                             :live-stobj)
                            (t
                             :live-stobj-gc-on)))))
              (fail_safe ; form for reporting guard or safe mode failure
               (oneify-fail-form 'ev-fncall-guard-er fn formals guard
                                 super-stobjs-in wrld t))
              (safe-form

; Functions in the ev-rec nest have a safe-mode parameter that we generally
; assume to agree with the state global safe-mode, so that the logic-only and
; raw lisp code agree.  See the comment in *ev-shortcut-okp*.

               '(f-get-global 'safe-mode *the-live-state*))
              (super-stobjs-chk
               (if stobj-flag
                   (let ((first-non-nil (find-first-non-nil super-stobjs-in)))
                     `(live-stobjp ,first-non-nil))
                 `(live-state-p
                   ,(select-stobj 'state super-stobjs-in formals))))
              (guarded-primitive-p

; We want to check guards on the "leaves" of a computation in safe-mode, for
; example, on a call of EQ.  Evaluation in the ACL2 logic can only diverge from
; evaluation in (raw) Common Lisp when a guard is violated on a function that
; is already defined in Common Lisp.  A function considered here that is at
; risk for such divergence has a non-T guard, is being defined in the
; boot-strap, and is not in the "ACL2" or "ACL2-PC" package (which are unknown
; to Common Lisp).  So as we generate code here, we restrict the additional
; guard-check in safe-mode to such functions.

               (and (not guard-is-t) ; we are trusting guards on the primitives!
                    boot-strap-p
                    (not (member-equal (symbol-package-name fn)
                                       '("ACL2" "ACL2-PC")))))
              (logic-recursive-p
               (and (eq defun-mode :logic)
                    (ffnnamep-mod-mbe fn (body fn nil wrld))))
              (labels-can-miss-guard
               (and logic-recursive-p ; there is no labels form for :program

; If the function is common-lisp-compliant, then the only way we can fall
; through to the labels form is if guard-checking is nil or :none (not :all),
; in which case there is no reason to warn.

                    (not cl-compliant-p-optimization)
                    (not guard-is-t)))
              (trace-rec-for-none

; If trace-rec-for-none is non-nil, then we guarantee that if
; 'guard-checking-on is set to :none, we will see all the recursive calls.
; This is useful for tracing.  Extra code for this case is only necessary for
; :logic mode, since the only issue is the call of a labels function, which
; only occurs in :logic mode and in the invariant-risk case (where we need to
; enter that labels code, which oneifies in a special way to deal with the
; invariant-risk issue).

               (and trace-rec-for-none
                    logic-recursive-p
                    (eq defun-mode :logic)))
              (program-only (and program-p

; Note that because of state global verify-termination-on-raw-program-okp, the
; test for program-p above is not merely an optimization.

                                 (member-eq fn

; If this test becomes an issue, we might consider reimplementing the
; program-only mechanism by way of :program-only xargs, which would place a
; property that we can look up.  Careful though -- at this point we probably
; have not yet installed a world with all the new properties of fn.

                                            (f-get-global
                                             'program-fns-with-raw-code
                                             *the-live-state*))))
              (fail_program-only

; At one time we put down a form here that throws to the tag 'raw-ev-fncall:

;             (oneify-fail-form 'program-only-er fn formals guard
;                               super-stobjs-in wrld
;                               t)

; However, because that throw is caught (in the function raw-ev-fncall), it
; should be accounted for in the function ev-fncall-rec-logical.  However, that
; function does not take state, which is unfortunate since the program-only
; case (under which we lay down this form) is based on state global
; 'program-fns-with-raw-code.  We considered moving that global to the world,
; but were concerned about the effects that would have on ACL2s (see for
; example the use of program-fns-with-raw-code in
; workshops/2007/dillinger-et-al/code/hacker.lisp), and in general we'd have to
; add yet another event and deal with whether the event should be local to
; books.  Instead, we have decided to cause a hard error, which is always
; legitimate (after all, Lisp might cause a resource error).  Note that we are
; dealing only with :program mode functions here, so we don't need to be
; concerned about the kind of error produced when evaluating terms on behalf of
; the rewriter.  Nevertheless, we use hard! to minimize the chance that
; somehow, in a way we don't currently envision, this call of fn will be
; considered to have a value of nil.  If we become truly paranoid about this
; issue, we could follow (er hard! ...) below with a call of error.

               `(progn
                  (save-ev-fncall-guard-er ',fn
                                           ',guard
                                           (stobjs-in ',fn (w *the-live-state*))
                                           (list ,@formals)
                                           (w *the-live-state*))
                  (er hard! 'program-only
                    "~@0"
                    (program-only-er-msg ',fn
                                         (list ,@formals)
                                         ,safe-form))))
              (early-exit-code-main
               (let* ((*1*guard
                       (cond
                        ((and cl-compliant-p-optimization
                              (not live-stobjp-test))
                         (assert$ (not guard-is-t) ; already handled way above
                                  :unused))        ; optimization
                        (t (oneify guard nil wrld program-p))))
                      (cl-compliant-code-guard-not-t
                       (and (not program-only) ; optimization

; We lay down code for the common-lisp-compliant case that checks the guard and
; acts accordingly: if the guard checks, then it returns the result of calling
; fn, and if not, then it fails if appropriate and otherwise falls through.

                            (not guard-is-t) ; optimization for code below
                            (eq defun-mode :logic) ; optimization for code below

; NOTE: we have to test for live stobjs before we evaluate the guard, since the
; Common Lisp guard may assume all stobjs are live.  We actually only need
; stobjs to be live that occur in the guard in other than stobj recognizer
; calls; but we take the easy way out (except for a stobj-flag case below) and
; check that all stobjs are live before evaluating the raw Lisp guard.  After
; all, the cost of that check is only some eq tests.

                            `(cond
                              ,(cond
                                ((eq live-stobjp-test t)
                                 `(,guard
                                   (return-from ,*1*fn (,fn ,@formals))))
                                (t
                                 `((if ,live-stobjp-test
                                       ,(if stobj-flag

; Essay on Stobj Guard Attachments

; We disallow attachments during evaluation of guards on behalf of any stobj
; updater.  The example below, which is a slight modification of one provided
; by Jared Davis, shows why this is important for defstobj.  The idea is that
; in order to preserve the invariant that the stobj recognizer holds, it
; suffices that the initial stobj satisfies that recognizer and that the guard
; holds for each call of an updater.  But suppose for example that an
; attachment is used in evaluating the guard for the first update.  If later
; (perhaps after many more updates) we change that attachment, then that guard
; now may be false, and thus the recognizer may fail to hold after the first
; update and thus fail to hold currently.  On the other hand, if such guard
; evaluation never involves attachments, then since the initial stobj provably
; satisfies the recognizer, then since each updater guard holds (in fact,
; provably holds), the resulting stobjs all satisfy the recognizer.

; The discussion above applies not only in the case of defstobj but also in the
; case of defabsstobj.  Consider an abstract function exported from a
; defabsstobj event that updates a stobj.  The avoidance of attachments
; guarantees that every abstract stobj update satisfies the abstract function's
; guard and hence, by the {preserved} theorems, results in an abstract stobj
; that satisfies the abstract predicate -- provably, since we are dealing with
; ground terms.  Moreover, because of the {guard-thm} theorems we know that the
; concrete predicate provably holds as well, and hence won't be "revoked" as in
; the preceding paragraph.

; Why do we care about guards on concrete stobjs?  For all we know, failure to
; respect those guards could result in corruption of the Lisp process.  An
; obvious case would be if a stobj field is an array of bits, laid out
; compactly according to that spec, and we update with an arbitrary object
; (say, a cons).  Although it seems that only a SATISFIES type declaration
; could result in a attachments being used for guard evaluation, we are
; conservative here.  After all, adding a binding of *aokp* is cheap in the
; context of evaluating just the guard.

; Note that it is not sufficient to ensure for an abstract stobj that the
; corresponding concrete stobj always satisfies its recognizer.  It is easy to
; imagine a defabsstobj :export field that specifies the identify function for
; its :logic component, returning the stobj unchanged, but for the :exec
; component makes an ill-guarded call to update the stobj, corrupting the Lisp
; imagine, before restoring the stobj.  In raw Lisp, this could really happen
; because the export is a macro that calls the :exec function directly; the
; only guard that need be met before this happens is a variant of the :logic
; function's guard, at the level of *1* function of the export.

; Finally, here is the example promised above.

; (progn
;   (defstub foop (x) t)
;   (defun barp (x)
;     (declare (xargs :guard t))
;     (or (not x)
;         (foop x)))
;   (defstobj st
;     (fld :type (satisfies barp)))
;   (defthm barp-of-fld
;     (implies (stp st)
;              (barp (fld st))))
;   (defun my-integerp (x)
;     (declare (xargs :guard t))
;     (integerp x)))
; (defattach foop my-integerp)
; (trace$ foop barp my-integerp)
; (update-fld 3 st) ; note that foop calls its attachment, my-integerp
; (defattach foop consp)
; (barp (fld st)) ; nil (ouch)
; (stp st) ; returns t, but is really (logically) nil

; The code just below ensures that the updater will be evaluated without
; attachments.  It might needlessly ensure that other functions introduced by
; defstobj (for the given stobj-flag) are evaluated without attachments, for
; example if the getprop below returns nil because the necessary property has
; not yet been put into wrld.  But as of this writing, the test seems to apply
; only to stobj updaters and resize functions.

                                            (let ((stobjs-out
                                                   (getpropc fn 'stobjs-out nil
                                                             wrld)))
                                              (cond
                                               ((and stobjs-out ; property is there
                                                     (all-nils stobjs-out))
                                                guard)
                                               (t `(let ((*aokp* nil))
                                                     ,guard))))
                                          guard)
                                     ,*1*guard)
                                   ,(assert$

; No user-stobj-based functions are primitives for which we need to give
; special consideration to safe-mode.

                                     (not guarded-primitive-p)
                                     `(cond (,live-stobjp-test
                                             (return-from ,*1*fn
                                                          (,fn ,@formals))))))))
                              ,@(cond (super-stobjs-in
                                       `((t ,fail_guard)))
                                      (guarded-primitive-p
                                       `((,safe-form
                                          ,fail_safe)
                                         (,guard-checking-is-really-on-form
                                          ,fail_guard)))
                                      (t
                                       `((,guard-checking-is-really-on-form
                                          ,fail_guard))))))))
                 (cond
                  (cl-compliant-p-optimization
                   (assert$ (not guard-is-t) ; already handled way above
                            (list cl-compliant-code-guard-not-t)))
                  (program-only
                   (list `(when (or ,safe-form
                                    ,@(and (not guard-is-t)
                                           `((not ,*1*guard))))
                            ,fail_program-only)))
                  (t
                   (let ((cond-clauses
                          `(,@(and (eq defun-mode :logic)

; If the guard is t, then we want to execute the raw Lisp code in the
; :common-lisp-compliant case even if guard-checking is :none.  This
; early-exit-code is only executed when guard-checking is not :none, so
; we need to handle that special case (:none, guard t) elsewhere, and
; we do so in *1*-body-forms below.

                                   (not guard-is-t)
                                   `(((eq (symbol-class ',fn
                                                        (w *the-live-state*))
                                          :common-lisp-compliant)
                                      ,cl-compliant-code-guard-not-t)))
                            ,@(and (not guard-is-t)
                                   (cond
                                    (super-stobjs-in
                                     `(((not ,*1*guard)
                                        ,fail_guard)))
                                    (guarded-primitive-p
                                     `(((and (or ,safe-form
                                                 ,guard-checking-is-really-on-form)
                                             (not ,*1*guard))
                                        (if ,safe-form
                                            ,fail_safe
                                          ,fail_guard))))
                                    (t
                                     `(((and ,guard-checking-is-really-on-form
                                             (not ,*1*guard))
                                        ,fail_guard)))))
                            ,@(and
                               program-p

; In the boot-strap world we have :program mode functions whose definitions are
; different in raw Lisp from the logic, such as ev and get-global.  If we allow
; :all or :none to serve their purposes for those functions, we can wind up
; with unpleasant guard violations.  For example, wet (when we had it) expanded
; to a call of with-error-trace-fn, and if the idea of :all is applied then we
; get the following sequence of calls in the logic (i.e., using their *1*
; functions): with-error-trace-fn, trans-eval, ev, ev-rec, ev-fncall-rec,
; ev-fncall-rec-logical, w-of-any-state, and finally global-table.  The last of
; these calls causes a guard violation since *the-live-state* is not a true
; list.

; Also, we want to make sure that built-in :program mode functions run fast,
; for example, defthm-fn.

; And finally, this is where we finish handling of safe-mode for
; guarded-primitive-p functions, specifically those in :program mode since if
; such a function is in :logic mode then either it is non-executable or
; :common-lisp-compliant (see check-none-ideal), hence is handled above.

                               (cond
                                (boot-strap-p
                                 `((,safe-form
                                    (return-from ,*1*fn ,*1*body))
                                   ,@(and
                                      invariant-risk
                                      `((t (return-from ,*1*fn ,*1*body))))))
                                (t `(((or (member-eq
                                           ,guard-checking-on-form
                                           '(:none :all))
                                          ,safe-form)
                                      (return-from ,*1*fn ,*1*body)))))))))
                     (and cond-clauses
                          (list (cons 'cond cond-clauses))))))))
              (early-exit-code
               (and early-exit-code-main
                    (cond ((and invariant-risk
                                (not super-stobjs-in))

; If we are under **1*-as-raw*, then our intention is that code executes just
; as it would in raw Lisp (i.e., without forcing execution via *1* function),
; except that guards are checked for stobj primitives.  This special treatment
; is only required in the invariant-risk case; see **1*-as-raw* and state
; global 'check-invariant-risk.  Moreover, we want the normal flow in the *1*
; function for stobj primitives, so we don't give this special treatment when
; super-stobjs-in is true.  It would be sound to make other exceptions as well,
; but that would cause unnecessary guard-checking.  Indeed, unnecessary extra
; guard-checking was done through Version_7.0, which resulted in slowdowns to
; user code that led us to remove that extra guard-checking.

                           `((when (not **1*-as-raw*)
                               ,@early-exit-code-main)))
                          (t early-exit-code-main))))
              (main-body-before-final-call

; This is the code that is executed before we fall through: to the final labels
; function in the :logic mode case, but to the non-*1* call in the :program
; mode case.

               (append
                (and user-stobj-is-arg
                     `((when *wormholep*
                         (wormhole-er (quote ,fn) (list ,@formals)))))
                (and (eq defun-mode :logic) ; else :program
                     guard-is-t
                     (assert$ ; compliant with guard t is handled early above
                      (not cl-compliant-p-optimization)
                      `((when (eq (symbol-class ',fn (w *the-live-state*))
                                  :common-lisp-compliant)
                          (return-from ,*1*fn (,fn ,@formals))))))
                (cond ((and skip-early-exit-code-when-none
                            early-exit-code) ; else nil; next case provides nil
                       (cond (super-stobjs-in early-exit-code) ; optimization
                             (t
                              `((when (not (eq ,guard-checking-on-form :none))
                                  ,@early-exit-code)))))
                      (t early-exit-code))
                (cond (trace-rec-for-none
                       `((return-from ,*1*fn ,*1*body)))
                      (labels-can-miss-guard
                       `((when (eq ,guard-checking-on-form :all)
                           (return-from ,*1*fn ,*1*body)))))
                (and (and labels-can-miss-guard
                          (not trace-rec-for-none)) ; else skip labels form
                     `((when (and (f-get-global 'raw-guard-warningp
                                                *the-live-state*)
                                  (eq ,guard-checking-on-form t))
                         (maybe-warn-for-guard-body ',fn *the-live-state*))))))
              (*1*-body-forms
               (cond ((eq defun-mode :program)
                      (append
                       main-body-before-final-call
                       (cond
                        (invariant-risk ; and (eq defun-mode :program)
                         (let ((check-invariant-risk-sym

; The serialize code seems to cause errors for a symbol with no package.

                                (gentemp))
                               (cont-p (gentemp)))
                           `((let ((,check-invariant-risk-sym
                                    (get-check-invariant-risk
                                     *the-live-state*))
                                   (,cont-p nil))
                               (cond
                                ((and
                                  ,check-invariant-risk-sym
                                  (not (f-get-global 'boot-strap-flg
                                                     *the-live-state*)))
                                 (cond
                                  ((eq ,check-invariant-risk-sym :ERROR)
                                   (state-free-global-let*
                                    ((debugger-enable t))
                                    (cerror
                                     "~%     Continue with invariant-risk ~
                                      mode of T~%     (that is, with state ~
                                      global 'check-invariant-risk bound to ~
                                      T)~%     to complete the current call ~
                                      of ~s.~%     See :DOC invariant-risk."
                                     "Invariant-risk has been detected for a ~
                                      call of function ~s~%(as possibly ~
                                      leading to an ill-guarded call of ~
                                      ~s);~%see :DOC invariant-risk."
                                     ',fn ',invariant-risk))
                                   (setq ,cont-p t))
                                  ((eq ,check-invariant-risk-sym :WARNING)
                                   (warning$ ',fn
                                             "Invariant-risk"
                                             "Invariant-risk has been ~
                                              detected for a call of function ~
                                              ~x0 (as possibly leading to an ~
                                              ill-guarded call of ~x1); see ~
                                              :DOC invariant-risk."
                                             ',fn ',invariant-risk)
                                   (setq ,cont-p t))
                                  (t ; 'check-invariant-risk has value t
                                   t))

; Now that we have perhaps caused a continuable error or a warning for
; invariant-risk, produce the result if an error didn't abort this computation.

                                 (let ((**1*-as-raw* t))

; One reason that we bind **1*-as-raw* above and use labels below is to helps
; compilers remove tail recursions, since we believe that special variable
; binding can get in the way of that.  (We do this regardless of the presence
; of recursion, simply because that is simplest and we expect, or at least,
; hope, that there is only trivial impact on performance.)

                                   ,(let ((labels-form
                                          (labels-form-for-*1*
                                           fn *1*fn formals
                                           (oneify body nil wrld
                                                   'invariant-risk)
                                           ignore-vars ignorable-vars
                                           super-stobjs-in super-stobjs-chk
                                           guard wrld)))
                                     (if cont-p
                                         `(state-free-global-let*
                                           ((check-invariant-risk t))
                                           ,labels-form)
                                       labels-form))))
                                (t (,fn ,@formals)))))))
                        (t `((,fn ,@formals))))))
                     (trace-rec-for-none
                      main-body-before-final-call)
                     (t
                      (append
                       main-body-before-final-call
                       (list
                        (labels-form-for-*1*
                         fn *1*fn formals *1*body
                         ignore-vars ignorable-vars
                         super-stobjs-in super-stobjs-chk
                         guard wrld)))))))
         `(,*1*fn
           ,formals

; At one time we attempted to do some code-sharing using a macro call, by using
; *1*body-call in place of *1*body in the code above, where *1*body-call was
; defined as shown below.  But with an ACL2 image built on Allegro, for (ld
; "books/rtl/rel4/support/merge.lisp") with (set-inhibit-output-lst '(prove
; proof-tree)) after (prof:start-profiler), it took 127.5 seconds to run such a
; modification of oneify-cltl-code, as opposed to 103.5 seconds.  Granted, we
; chose this file because it was shown in some earlier experiments with
; macrolet to have a particularly bad slowdown over previous versions without
; macrolet.  But still, we suffer the extra code for recursive :ideal-mode
; functions rather than generate macrolet forms.  Below are the relevant
; bindings used in a previous version of this code, in case we decide to
; revisit this approach.

;           (*1*body-call-shared-p
;
; ; We want to keep code size down by using macrolet to share the *1*body ;
; ; expression, but preferably not otherwise, to avoid overhead that we seem to ;
; ; have observed, at least in Allegro CL, for expanding (uncompiled) macrolet ;
; ; calls.  The expression below should thus agree with the governing conditions ;
; ; for the occurrences of *1*body-call outside the labels function that will ;
; ; also occur in a corresponding labels function.  The latter rules out the case ;
; ; (eq defun-mode :program). ;
;
;            (ffnnamep fn (body fn nil wrld)))
;           (*1*body-macro (and *1*body-call-shared-p
;                               (acl2-gentemp "*1*BODY-MACRO")))
;           (*1*body-call (if *1*body-call-shared-p
;                             `(,*1*body-macro)
;                           *1*body))
;
; ;;; end of let* bindings .... and here is the replacement for ,@*1*-body-forms
; ;;; below:
;
;           ,@(if *1*body-call-shared-p
;                 `((macrolet ((,*1*body-macro () ',*1*body))
;                     ,@*1*-body-forms))
;               *1*-body-forms)

           ,@*1*-body-forms)))))))


;          PROMPTS

; New ACL2 users sometimes do not notice that they are outside the ACL2
; read-eval-print loop when in a break.  We modify the prompts when we see how
; to do so, so that in a break we see "[RAW LISP]" in the prompt.  For most
; lisps, this seems to require changing the prompt at the top-level too, not
; just in a break.

(defvar *saved-raw-prompt* nil)
(defvar *saved-raw-prompt-p* nil)

#+allegro
(progn

(defun-one-output install-new-raw-prompt ()
  (cond ((not *saved-raw-prompt-p*)
         (setq *saved-raw-prompt* tpl:*prompt*)
         (setq tpl:*prompt*
               (concatenate 'string *saved-raw-prompt* "[RAW LISP] "))
         (setq *saved-raw-prompt-p* t))))

(defun-one-output install-old-raw-prompt ()
  (cond (*saved-raw-prompt-p*
         (setq tpl:*prompt* *saved-raw-prompt*)
         (setq *saved-raw-prompt-p* nil)
         (setq *saved-raw-prompt* nil) ; no longer needed; free storage
         t))))

#+clisp
(progn

(defun-one-output install-new-raw-prompt ()
  (cond ((not *saved-raw-prompt-p*)
         (setq *saved-raw-prompt* custom::*prompt-body*)
         (setq custom::*prompt-body* ; attempt to mimic clisp 2.33
               (function
                (lambda ()
                  (if (equal system::*home-package* *package*)
                      (format nil "[RAW LISP]")
                    (format nil "~a [RAW LISP]" (package-name *package*))))))
         (setq *saved-raw-prompt-p* t))))

(defun-one-output install-old-raw-prompt ()
  (cond (*saved-raw-prompt-p*
         (setq custom::*prompt-body* *saved-raw-prompt*)
         (setq *saved-raw-prompt-p* nil)
         (setq *saved-raw-prompt* nil) ; no longer needed; free storage
         t))))

#+cmu
(progn

(defun-one-output install-new-raw-prompt ()
  (setq debug:*debug-prompt*
        (function (lambda ()
                    (debug::debug-prompt)
                    (format t "[RAW LISP] ")
                    (force-output t)))))

(defun-one-output install-old-raw-prompt ()
  (setq debug:*debug-prompt*
        (function debug::debug-prompt))))

#+ccl
(progn

(defun-one-output install-new-raw-prompt ()
   (cond ((not *saved-raw-prompt-p*)
          (setq *saved-raw-prompt*
                (symbol-function 'ccl::print-listener-prompt))
          (let ((ccl:*warn-if-redefine-kernel* nil))
            (setf (symbol-function 'ccl::print-listener-prompt)
                  (lambda (stream &rest args)
                    (declare (ignore stream))
                    (apply *saved-raw-prompt* *debug-io* args)
                    (format *debug-io* "[RAW LISP] "))))
          (setq *saved-raw-prompt-p* t))))

(defun-one-output install-old-raw-prompt ()
  (cond (*saved-raw-prompt-p*
         (let ((ccl:*warn-if-redefine-kernel* nil))
           (setf (symbol-function 'ccl::print-listener-prompt)
                 *saved-raw-prompt*))
         (setq *saved-raw-prompt-p* nil)
         (setq *saved-raw-prompt* nil) ; no longer needed; free storage
         t))))

#+(and gcl (not cltl2))
; We are a bit sorry that we messed around at this low a level, and choose not
; to do so for ANSI GCL.
(progn

(defun-one-output install-new-raw-prompt ()
  (cond ((not (and (eql si::*gcl-major-version* 2)
                   (eql si::*gcl-minor-version* 6)))
         (cond (*lp-ever-entered-p*
                (er hard 'install-new-raw-prompt
                    "Install-new-raw-prompt is only supported in GCL 2.6 and ~
                     its sub-versions.  This appears to be a GCL ~s0.~s1."
                    si::*gcl-major-version*
                    si::*gcl-minor-version*))
               (t (setq *saved-raw-prompt-p* t))))
        ((not *saved-raw-prompt-p*)
         (setq si::*debug-prompt-suffix* "[RAW LISP]")
         (setf *saved-raw-prompt* (symbol-function 'si::break-level))
         (setf (symbol-function 'si::break-level)
               (symbol-function 'si::break-level-for-acl2))
         (setq *saved-raw-prompt-p* t))))

(defun-one-output install-old-raw-prompt ()
  (cond (*saved-raw-prompt-p*
         (setq si::*debug-prompt-suffix* "")
         (setf (symbol-function 'si::break-level)

; Since we set si::*debug-prompt-suffix*, we really don't have to revert
; (symbol-function 'si::break-level) -- unless our patch,
; 'si::break-level-for-acl2 is out of sync with the current GCL's
; 'si::break-level.  So we play it safe and revert.

               *saved-raw-prompt*)
         (setq *saved-raw-prompt-p* nil)
         (setq *saved-raw-prompt* nil) ; no longer needed; free storage
         t))))

#-(or allegro clisp cmu ccl (and gcl (not cltl2)))
(progn

(defun-one-output install-new-raw-prompt ()
  nil)

(defun-one-output install-old-raw-prompt ()
  nil)

)

;          DYNAMICALLY MONITOR REWRITES ("dmr")

;;; User-settable dmr variables

; User settable to any positive number, indicating the number of pushes on the
; gstack before *dmr-file-name* is written.
; If you set this, consider also setting Emacs Lisp variable
; *acl2-timer-display-interval*.
(defvar *dmr-interval* 1000)
(defvar *dmr-interval-acl2-par-hack* 300000)
(defvar *dmr-interval-used*)

; This variable's positive integer value indicates the maximum indentation for
; each line in the display.  Lines that otherwise would exceed this indentation
; are instead shown as
;    {x} n. ....
; where x is the 0-based indentation depth.
(defvar *dmr-indent-max* 20)

; User settable, but then you need to set *acl2-monitor-buffer-name* and
; *dmr-file-name* in emacs file monitor.el.  The main reason to change
; this would be if you are running emacs on a different machine than the one on
; which you are running ACL2.
(defvar *dmr-file-name*)

(defun dmr-file-name ()
  (let ((user (or (getenv$-raw "USER")
                  (progn (format t "Warning: Unable to determine USER ~
                                    environment variable for ~
                                    dmr-file-name.~%Will treat USER as ~
                                    SOME-USER.  In emacs, evaluate:~%(setq ~
                                    *dmr-file-name* ~
                                    \"/tmp/acl2-dmr-SOME-USER\")~%")
                         "SOME-USER"))))
    (concatenate 'string "/tmp/acl2-dmr-" user)))

;;; Code implementing dmr in ACL2

(defg *dmr-stream*

; This variable is nil by default, but is non-nil exactly when dmr is active.

  nil)

(defg *dmr-counter*

; For the sake of GCL, we may want to consider consider using a 0-dimensional
; fixnum array instead.  If so, then consider whether *dmr-interval* should
; also be similarly changed.

  0)

#+acl2-par
(defun dmr-acl2-par-hack-p ()
  (f-get-global 'waterfall-parallelism *the-live-state*))

(defun dmr-stop-fn-raw ()
  (when *dmr-stream*
    (let ((str *dmr-stream*))
      (setq *dmr-stream* nil)
      (close str))))

(defun initialize-dmr-interval-used ()
  (setq *dmr-interval-used*
        #+acl2-par
        (cond ((dmr-acl2-par-hack-p) *dmr-interval-acl2-par-hack*)
              (t *dmr-interval*))
        #-acl2-par
        *dmr-interval*))

(defun dmr-start-fn-raw (state)
  (initialize-dmr-interval-used)
  (or (boundp '*dmr-file-name*)
      (setq *dmr-file-name* (dmr-file-name)))
  (setq *dmr-stream*
        (open *dmr-file-name*
              :if-exists
              :supersede ; :overwrite doesn't open non-existent file in CCL
              :direction :output
              #+acl2-par :sharing
              #+acl2-par :lock ; the default of :private is single-threaded
              ))
  state)

(defv *dmr-array*

; The argument of make-array below is somewhat arbitrary.  It was initially
; chosen to be the default length of cw-gstack.

  (make-array 10000))

(defun reverse-into-dmr-array (lst)
  (let ((len-1 (1- (length lst))))
    (when (< (length *dmr-array*) len-1)
      (setq *dmr-array*
            (make-array (* 2 len-1))))
    (loop for i from len-1 downto 0
          as tail on lst
          do (setf (aref *dmr-array* i) (car tail)))
    len-1))

(defparameter *dmr-reusable-string*
  (make-array '(0)
              :element-type

; SBCL and non-ANSI GCL complain about setting the fill-pointer if we use
; 'base-char.

              #+(or sbcl (and gcl (not cltl2))) 'character
              #-(or sbcl (and gcl (not cltl2))) 'base-char
              :fill-pointer 0
              :adjustable t))

(defvar *dmr-indent*)

(defmacro dmr-increment-indent ()
  '(setq *dmr-indent*
         (+ 2 *dmr-indent*)))

(defun tilde-@-bkptr-string (calling-sys-fn called-sys-fn bkptr)

; Warning: Keep this in sync with tilde-@-bkptr-phrase.

; This function builds a ~@ phrase explaining how two adjacent frames
; are related, given the calling sys-fn, the called sys-fn and the
; bkptr supplied by the caller.  See cw-gframe for the use of this
; phrase.

; WARNING: This function can have a side effect of setting
; *dmr-indent*.  It would be cleaner to use multiple values instead; maybe some
; day when we have time (!) or if someone volunteers.

  (case called-sys-fn
        (rewrite
         (cond ((integerp bkptr)
                (cond ((member-eq calling-sys-fn
                                  '(rewrite-with-lemma
                                    rewrite-quoted-constant-with-lemma
                                    add-linear-lemma))
                       (dmr-increment-indent)
                       (format nil " the atom of hypothesis ~s" bkptr))
                      ((eq calling-sys-fn 'simplify-clause)
                       (format nil " the atom of literal ~s" bkptr))
                      (t (format nil " argument ~s" bkptr))))
               ((consp bkptr)
                (dmr-increment-indent)
                (format
                 nil
                 " the ~arhs of hypothesis ~s"
                 (if (eq (car bkptr) 'rhs2) "rewritten " "")
                 (cdr bkptr)))
               ((symbolp bkptr)
                (case bkptr
                      (guard " the guard")
                      (body " the body")
                      (lambda-body " the lambda body")
                      (lambda-object-body " the body of the lambda object")
                      (rewritten-body " the rewritten body")
                      (expansion " the expansion")
                      (equal-consp-hack-car " the equality of the cars")
                      (equal-consp-hack-cdr " the equality of the cdrs")
                      (rhs " the rhs of the conclusion")
                      (meta " the result of the metafunction")
                      (nth-update " the result of the nth/update rewriter")
                      (multiply-alists2 " the product of two polys")
                      (forced-assumption " a forced assumption")
                      (proof-builder " proof-builder top level")
                      (otherwise (er hard 'tilde-@-bkptr-string
                                     "When ~x0 calls ~x1 we get an unrecognized ~
                                      bkptr, ~x2."
                                     calling-sys-fn called-sys-fn bkptr))))
               (t (er hard 'tilde-@-bkptr-string
                      "When ~x0 calls ~x1 we get an unrecognized bkptr, ~x2."
                      calling-sys-fn called-sys-fn bkptr))))
        ((rewrite-with-lemma setup-simplify-clause-pot-lst simplify-clause
                             add-terms-and-lemmas add-linear-lemma
                             non-linear-arithmetic synp)
         "")
        (t (er hard 'tilde-@-bkptr-string
               "When ~x0 calls ~x1 we get an unrecognized bkptr, ~x2."
               calling-sys-fn called-sys-fn bkptr))))

(defvar *dmr-interp-state*
; This tells us whether we have already printed "argument(s)" when printing
; gframes with sys-fn = rewrite.
  0)

(defun dmr-interp-fresh-rewrite-p (calling-sys-fn frame)

; Assumes that (access gframe frame :sys-fn) is rewrite.

  (not (and (eq calling-sys-fn 'rewrite)
            (integerp (access gframe frame :bkptr)))))

(defun dmr-prefix ()
  (if (> *dmr-indent* *dmr-indent-max*)
      (concatenate 'string
                   (aref1 'acl2-built-in-spaces-array
                          *acl2-built-in-spaces-array*
                          *dmr-indent-max*)
                   (format nil
                           "{~s} "
                           *dmr-indent*))
    (aref1 'acl2-built-in-spaces-array
           *acl2-built-in-spaces-array*
           *dmr-indent*)))

(defun dmr-interp (i calling-sys-fn frame)

; Warning: Keep this in sync with cw-gframe.

; This prints a gframe, frame, which is known to be frame number i and
; was called by calling-sys-fn.

  (let ((sys-fn (access gframe frame :sys-fn)))
    (case sys-fn
      (rewrite
       (cond ((dmr-interp-fresh-rewrite-p calling-sys-fn frame)
              (setq *dmr-interp-state* 0)
              (let ((bkptr-string ; evaluate now, before printing
                     (tilde-@-bkptr-string calling-sys-fn
                                           'rewrite
                                           (access gframe frame :bkptr))))
                (format nil
                        "~a~s. Rewriting (to ~a)~a"
                        (dmr-prefix)
                        i
                        (let ((obj (cddr (access gframe frame :args))))
                          (cond ((eq obj nil) "falsify")
                                ((eq obj t) "establish")
                                (t "simplify")))
                        bkptr-string)))
             ((eq *dmr-interp-state* 0)
              (setq *dmr-interp-state* 1)
              (format nil "; argument(s) ~s" (access gframe frame :bkptr)))
             (t
              (format nil "|~s" (access gframe frame :bkptr)))))
      ((rewrite-with-lemma add-linear-lemma rewrite-quoted-constant-with-lemma)
       (format
        nil
        "~a~s. Applying ~s~%"
        (dmr-prefix)
        i
        (get-rule-field (cdr (access gframe frame :args)) :rune)))
      (add-terms-and-lemmas
       (let ((len (length (car (access gframe frame :args)))))
         (format
          nil
          "~a~s. Applying linear arithmetic to ~a ~s term~a~%"
          (dmr-prefix)
          i
          (let ((obj (cdr (access gframe frame :args))))
            (cond ((eq obj nil) "falsify")
                  ((eq obj t) "establish")
                  (t "simplify")))
          len
          (if (eql len 1) "" "s"))))
      (non-linear-arithmetic
       (let ((len (length (access gframe frame :args))))
         (format
          nil
          "~a~s. Applying non-linear arithmetic to ~s var~a~%"
          (dmr-prefix)
          i
          len
          (if (eql len 1) "" "s"))))
      (synp
       (let ((synp-fn (access gframe frame :args)))
         (dmr-increment-indent)
         (format nil
                 "~a~s. Entering ~s for hypothesis ~s~%"
                 (dmr-prefix) i synp-fn (access gframe frame :bkptr))))
      (setup-simplify-clause-pot-lst
       (format nil "~a~s. Setting up the linear pot list~%" (dmr-prefix) i))
      (otherwise

; Note that we leave it to pstk to handle simplify-clause.

       (er hard 'dmr-interp
           "Unrecognized sys-fn, ~x0"
           (access gframe frame :sys-fn))))))

(defvar *dmr-delete-string*

; WARNING: Keep this in sync with monitor.el.

  "delete-from-here-to-end-of-buffer")

(defun dmr-string ()
  #+acl2-par
  (when (dmr-acl2-par-hack-p)
    (return-from dmr-string
                 (print-interesting-parallelism-variables-str)))
  (when (null *pstk-stack*)
    (setq *dmr-counter* *dmr-interval-used*) ; will flush next time
    (setq *deep-gstack* nil)
    (return-from dmr-string *dmr-delete-string*))
  (setf (fill-pointer *dmr-reusable-string*) 0)
  (let* ((pstk-tokens (loop with result = nil
                            for x in *pstk-stack*
                            do (push (cond ((eq (car x) 'waterfall)
                                            (car (nthcdr 8 x))) ; ctx
                                           ((eq (car x) 'ev-fncall)
                                            (list (car x) (cadr x)))
                                           (t (car x)))
                                     result)
                            finally (return result))) ; reversed
         (pstk-tokens-tail pstk-tokens)
         (len-1 (reverse-into-dmr-array *deep-gstack*))
         (calling-sys-fn 'start)
         (*print-pretty* nil)
         (counter 0)
         (*dmr-indent* 3)
         (no-newline-last-time nil))
    (with-output-to-string
      (s *dmr-reusable-string*)
      (loop for token in pstk-tokens
            do
            (progn
              (setq pstk-tokens-tail (cdr pstk-tokens-tail))
              (cond
               ((member-eq token '(rewrite-atm setup-simplify-clause-pot-lst))
                (return))
               (t (princ (format nil " ~s. ~s~%" counter token)
                         s)
                  (incf counter)))))
      (loop for i from 0 to len-1
            do (let* ((frame (aref *dmr-array* i))
                      (sys-fn (access gframe frame :sys-fn)))
                 (when (not (eq sys-fn 'simplify-clause))

; First, print a newline if we didn't print one last time and we are not
; printing args for sys-fn = rewrite.

                   (setq no-newline-last-time (eq calling-sys-fn 'rewrite))
                   (when (and no-newline-last-time ; no newline last time
                              (or ; not printing args for rewrite
                               (not (eq sys-fn 'rewrite))
                               (dmr-interp-fresh-rewrite-p calling-sys-fn
                                                           frame)))
                     (terpri s))
                   (princ (dmr-interp counter calling-sys-fn frame)
                          s)
                   (incf counter))
                 (setq calling-sys-fn (access gframe frame :sys-fn))))
      (when (eq calling-sys-fn 'rewrite) ; no newline last time
        (terpri s))
      (dmr-increment-indent)
      (loop for token in pstk-tokens-tail

; We avoid printing ev-fncall-meta because such a call can invoke mfc-rw,
; creating lower gstack entries, resulting in several ev-fncall-meta tokens
; being printed here (at the bottom of the displayed stack) rather than
; interspersed in the display.  Rather than track gstack/pstk interaction, we
; simply avoid printing ev-fncall-meta tokens, though pstk itself does flush
; the display out to file when entering ev-fncall-meta.

            when (not (eq token 'ev-fncall-meta))
            do
            (progn (princ (if (eq token 'add-polynomial-inequalities)
                              (format nil "~a~s. ~s: ~s calls~%" (dmr-prefix)
                                      counter token *add-polys-counter*)
                            (format nil "~a~s. ~s~%" (dmr-prefix) counter
                                    token))
                          s)
                   (incf counter)))
      (princ *dmr-delete-string* s)))
  *dmr-reusable-string*)

(defun dmr-flush1 (&optional reset-counter)

; This function should only be called when *dmr-stream* is non-nil (and hence
; is a stream).

  (file-position *dmr-stream* :start)
  (princ (dmr-string) *dmr-stream*)
  (without-interrupts

; This use of without-interrupts fixed an "Expected newpos" error in CCL
; (thanks, Gary Byers).  So to increase confidence in this code, we use it for
; all Lisps.

   (force-output *dmr-stream*))
  (when reset-counter
    (setq *dmr-counter* 0))
  t)

#+acl2-par
(defvar *dmr-lock* (make-lock))

(declaim (inline dmr-flush))
(defun dmr-flush (&optional reset-counter)
  (when *dmr-stream*
    (cond #+acl2-par
          ((dmr-acl2-par-hack-p)
           (with-lock *dmr-lock* (dmr-flush1 reset-counter)))
          (t (dmr-flush1 reset-counter)))))

(declaim (inline dmr-display))
(defun dmr-display ()
  (when *dmr-stream*
    (cond ((> *dmr-counter* *dmr-interval-used*)
           (setq *dmr-counter* 0)
           (cond #+acl2-par
                 ((dmr-acl2-par-hack-p)
                  (with-lock *dmr-lock* (dmr-flush1)))
                 (t (dmr-flush1))))
          (t
           (setq *dmr-counter* (1+ *dmr-counter*))))))

(defun cw-gstack-short ()
  (let* ((str (dmr-string))
         (pos (search *dmr-delete-string* str)))
    (princ (if pos (subseq str 0 pos) str) *terminal-io*)))


;          INITIALIZATION OF CURRENT ACL2 WORLD

; Once upon a time (pre-V2.2) we had the following defvar here:

; (defvar *current-acl2-world-key* (make-symbol "*CURRENT-ACL2-WORLD-KEY*"))

; But compiling under cmulisp showed us that we refer to the value
; of this var earlier in the initialization process.  So I have
; moved the defvar to axioms.lisp.

(eval-when #-cltl2 (load eval) #+cltl2 (:load-toplevel :execute)
           (f-put-global 'current-acl2-world nil *the-live-state*)
           (setf (get 'current-acl2-world 'acl2-world-pair)
                 (cons nil *current-acl2-world-key*)))

; EXTENDING AND RETRACTING PROPERTY LIST WORLDS

; We here sketch the entire world management scheme before diving into
; the details.  The software archaeologist might think these summaries
; were written just for his use but that is wrong.  In fact, these are
; design sketches and refresher courses to bring to mind the salient
; details before getting back down to work.  This particular one
; represents the attempt to get back into this frame of mind after
; several days of Christmas preparations, 1990.  (Note: This essay has
; been updated since, to track changes such as the adoption, in April,
; 1994, of the restriction that reincarnated undone defpkgs must
; import only a subset of the old imports.  That attack on the
; "unintern problem" was sketched as the "Alternative Design Proposal"
; in the December, 1990 essay but rejected as unnecessary as it was
; then thought that we handled reincarnation correctly by uninterning
; all symbols except in abort recovery.  But :oops and the second pass
; of include books, etc., exposed the lie.)

; A property list "world" is a list of triples as created by putprop.
; Each triple is of the form (symb key . val).  Such a list is
; accessed by getprop, which, logically speaking, scans down it
; looking for a given symb and key.  Practically however, we allow a
; given world to be "installed" under any given symbolic name.  What
; installation does is assemble into an alist all of the properties of
; each symb in the world and put that alist on the property list of
; the symbol, under some special key that is associated with the name
; of the installed world.

; If name has an 'acl2-world-pair property then name is the name of an
; installed world.  The value of the property will be a pair, (alist .
; world-key), where alist is the (eq) world alist installed and
; world-key is a unique symbol associated with this world name and
; under which each symb's property alist is stored.

; The functions extend-world and retract-world will extend and retract
; a named world.  Logically speaking, these two functions are identity
; functions.  But practically speaking they smash Common Lisp property
; lists.  Extend-world must be given a name and a world that is an
; extension (eq) of the one currently installed under the name and
; will install the new properties.  An analogous remark holds for
; retract-world.  We make these functions available to the ACL2
; programmer.

; We store our own property list world under the name 'current-acl2-
; world.  How do we prevent the ACL2 programmer from smashing our
; properties?  Well, extend-world (which is logically a no-op all the
; time) is even a no-op practically on the name 'current-acl2-world.
; To smash property lists you must call extend-world1 (not an ACL2
; function) and that function works on any name.  Our ACL2 function
; set-w, which installs the current-acl2-world, calls extend-world1 in
; its #-acl2-loop-only code.  Set-w is, of course, untouchable.

; We include special support for retraction, which of course is the
; basis of undoing.  It would suffice, for extension and for getprop,
; if we could expedite the retrieval of the most recently put value of
; every symbol and key.  Suppose the world in question is w, named
; name, and suppose it is installed under the property name world-key.
; Suppose the only three triples on w about symb are (symb key1 . b),
; (symb key1 . a), and (symb key2 . c), occurring in that order on w.
; Then for purposes of extension and getprop alone, we could store
; '((key1 . b) (key2 . c)) under symb's world-key property.  But now
; suppose we wanted to retract back to where (symb key1 . a) was most
; recent.  Then we would need to change the alist stored under symb's
; world-key to '((key1 . a) (key2 . c)) and to find the newly exposed
; value for key1 we would have to search w.  This is what we did for
; the first 18 months of ACL2's development.  This made :ubt suffer
; because when we undid a property -- especially a property on some
; symbol like binary-+ or cons -- we would have to scan all the back
; down the world to the primordial putprops to recover the newly
; exposed values.  This was bad not so much because of the scan time
; but because of the swap time: the world is big and rarely
; referenced, so it tends to get paged out and then when you scan it
; you have to page it back in.  This can take a minute or more.

; To avoid this we actually store a stack for each key.  The stack is
; the list of all past values of the key, topped by the current value.
; An empty stack indicates that no putprop has occurred for that key
; (or, more accurately, that we have retracted back past the first
; putprop for that key).

; There is another twist to this scheme.  To support the execution and
; compilation of ACL2 functions in raw Common Lisp, we interpret a
; certain putprop symb key, namely CLTL-COMMAND GLOBAL-VALUE, as a
; directive to smash the symbol-function, macro-function, or constant
; definition of certain symbols contained in the value.  We only do
; this if we are installing 'current-acl2-world, of course.  To
; support undoing of these smashes we maintain a stack of the past
; settings of those fields.  This is the *undo-stack* of the symb.
; The situation here is complicated and more fully explained in the
; code below.

; The installation of worlds and error recovery are intimately con-
; nected to the problem of uninterning symbols on behalf of undone or
; reincarnated packages.  When the CLTL-COMMAND defpkg is encountered,
; the program defpkg is called to create the package.  Consider what
; would happen if defpkg were coded so as to unintern the symbols in
; the existing package and set the import list as per the new defini-
; tion (as, indeed, we once did, allowing the reincarnation of undone
; packages).  In particular, consider the effect this would have on
; triples yet-to-be installed: if they mentioned symbols in the new
; package then those symbols would suddenly become uninterned.  We
; once thought this was ok because symbols in newly defined packages
; couldn't yet exist in the yet-to-be installed world.  But that is a
; bogus claim: if we are reinstalling a world after an error abort or
; even an :oops the world might contain symbols in the "just defined"
; package.  This is what eventually drove us to implement the restric-
; tion described in :DOC package-reincarnation-import-restrictions.

; Because of the possibility of user interrupts, it is possible that we
; can have effected some but not all of changes necessary to achieve a
; new state and then have the computation aborted.  To handle this,
; extend-world1 and retract-world1 both save the current world alist
; before they begin to make any changes.  If they are interrupted, the
; original configuration is recovered by an unwind-protect cleanup form.

; Inspection of the lisp code for defpkg will reveal that it is
; sensitive to abort recovery in one other aspect.  If we are in abort
; recovery and the "dual package" (the one used to house the lisp
; equivalents of state global variables) already exists, we do not
; unbind all the variables in it but simply leave it untouched.  Since
; neither extending nor retracting changes state globals, the state
; global settings at the time of an abort are what they were when *w0*
; was saved.  Hence, by doing nothing to the dual package we keep the
; installed world and the state globals in the same relationship.

; So much for the sketch of the world management business.  We now get
; down to brass tacks.

(defun-one-output fmakunbound! (name)
  (fmakunbound name)
  (when (macro-function name)
    (error "This Common Lisp implementation seems unable to unbind ~~%
            macro-functions.  Please let the ACL2 implementors know about ~%~
            this problem.")))

(defun-one-output maybe-push-undo-stack (fn name &optional extra)

; This function is evaluated only for side-effect; its return value is
; irrelevant.

; See add-trip below for context.  Fn is one of the raw Lisp function names
; secretly spawned by CLTL-COMMAND forms, e.g., DEFUN, DEFMACRO, DEFCONST,
; DEFPKG, DEFATTACH, or (for the HONS version) MEMOIZE or UNMEMOIZE.  Name is
; generally the symbol or string that is being defined.

; Whenever we smash a CLTL cell we first save its current contents to permit
; redefinition and undoing.  Toward this end we maintain a stack for each
; defined symbol, called the *undo-stack* property of the symbol.  Very roughly
; speaking, the stack contains the previous values of the cells in question.
; Add-trip will push the old value onto the stack before storing the new and
; undo-trip will pop the stack and restore that old value.  Ah, were it only
; that simple...

; There are complications.  First, DEFPKG doesn't have a symbol associated with
; it explicitly, so we have to manufacture one for the *undo-stack*.  We use
; the ``base symbol'' of the package (see chk-acceptable-defpkg).  If the
; symbol-package-name string is "name" then the base symbol is the symbol
; ACL2::name-PACKAGE.  (We use that symbol as a rule name associated with the
; defpkg axiom and so we already check that the name is new.)  Second, DEFPKG
; makes the notion of "current contents" highly abstract because it not only
; creates a package but imports various symbols into it.  So rather than use
; the *undo-stack* to save the "current contents" we use the stack to save a
; form that when evaluated will recreate the "current contents" of the cell in
; question.  When a new value is stored (and the cell is already in use) we
; will manufacture a suitable form for recreating the old value and push it.

; Third, extra (formerly called ignorep because of its connection to the
; ignorep variable in add-trip) is either nil, 'reclassifying or '(defstobj
; . stobj).  When it is 'reclassifying, we only save the *1* def for name.
; Otherwise, we save both defs.

  (cond ((and (symbolp name)
              (fboundp name)
              (not (eq fn 'attachment)))

; We clear the 'acl2-trace-saved-fn property and reinstall the appropriate
; symbol-function if these have been messed with by tracing.  We also do a raw
; Lisp untrace while we're at it, just to be careful.  However, we skip all
; that for defattach, since defattach doesn't mess with symbol-functions -- it
; only messes with special variables.

         (maybe-untrace! name t)))
  (case fn
        ((defun defmacro)

; In Common Lisp, a symbol can be either a macro or function, but the
; symbol-function cell is used in both cases to store the associated code.
; Therefore, if we are about to smash the symbol-function cell, e.g., in
; response to a DEFUN event, then we are obliged to remember whether it was
; previously defined as a macro.

; Notice that we are dealing properly here with :inlined stobj functions as
; well as defabsstobj raw Lisp macros.  See also the comment about this in
; undo-trip.

         (cond
          ((fboundp name)
           (let ((oneified-name (*1*-symbol name))
                 (macro-p (macro-function name)))
             (push `(progn
                      ,@(and (not macro-p)
                             `((maybe-untrace! ',name) ; untrace new function
                               #+hons (maybe-unmemoize ',name)))
                      ,@(if (eq extra 'reclassifying)
                            (assert$
                             (not macro-p)
                             `((setf (symbol-function ',oneified-name)
                                     ',(symbol-function oneified-name))))
                          `(,@(if (not (iff (eq fn 'defmacro) macro-p))

; Avoid errors in (at least) CCL, as in this example.

; (redef!)
; (defun foo (x) x)
; (defmacro foo (x) `(quote ,x))
; (u)

                                  `((fmakunbound! ',name)))
                            ,(cond (macro-p
                                    `(setf (macro-function ',name)
                                           ',(macro-function name)))
                                   (t
                                    `(setf (symbol-function ',name)
                                           ',(symbol-function name))))
                            ,(cond
                              ((fboundp oneified-name)
                               `(setf (symbol-function ',oneified-name)
                                      ',(symbol-function oneified-name)))
                              (t `(fmakunbound! ',oneified-name))))))
                   (get name '*undo-stack*))))
          (t (push `(progn (maybe-untrace! ',name) ; untrace new function
                           #+hons (maybe-unmemoize ',name)
                           (fmakunbound! ',name)
                           (fmakunbound! ',(*1*-symbol name)))
                   (get name '*undo-stack*)))))
        (defconst

; Note: defstobj events use maybe-push-undo-stack with fn = 'defconst
; to save the values of the name, the live name and also of
; '*user-stobj-alist*!

          (cond
           ((boundp name)
            (push `(progn (setf (symbol-value ',name)
                                ',(symbol-value name))
                          (setf (get ',name 'redundant-raw-lisp-discriminator)
                                ',(get name 'redundant-raw-lisp-discriminator)))
                  (get name '*undo-stack*)))
           (t (push `(progn (makunbound ',name)
                            (remprop ',name 'redundant-raw-lisp-discriminator))
                    (get name '*undo-stack*)))))

        (defpkg
          (let ((temp (find-non-hidden-package-entry
                       name
                       (known-package-alist *the-live-state*))))
            (cond
             (temp
              (push `(defpkg ,name ',(package-entry-imports temp))
                    (get (packn (cons name '("-PACKAGE"))) '*undo-stack*))))))
        (attachment
         (cond
          #+hons ; else this branch will be impossible
          ((eq name *special-cltl-cmd-attachment-mark-name*)

; This case arises from a call of table-cltl-cmd for (table badge-table ...);
; so in this case we should not call set-attachment-symbol-form.  Just below,
; we optimize ever so slightly, to avoid making *defattach-fns* really long in
; the case that there are many such badges being added but not many defattach
; events.

           (push `(unless (eq ',name (car *defattach-fns*))
                    (push ',name *defattach-fns*))
                 (get name '*undo-stack*)))
          (t (push `(progn
                      #+hons (push ',name *defattach-fns*)
                      ,(set-attachment-symbol-form
                        name

; Note that (attachment-symbol name) is bound when name is introduced; see
; throw-or-attach-call.

                        (symbol-value (attachment-symbol name))))
                   (get name '*undo-stack*)))))
        #+hons
        (memoize

; We check that the function is actually memoized.  See the comment about this
; in the memoize case of add-trip.

         (push `(when (memoizedp-raw ',name)
                  (unmemoize-fn ',name))
               (get name '*undo-stack*)))
        #+hons
        (unmemoize
         (let* ((entry (gethash name *memoize-info-ht*))
                (condition (access memoize-info-ht-entry entry :condition))
                (inline (access memoize-info-ht-entry entry :inline))
                (commutative
                 (access memoize-info-ht-entry entry :commutative))
                (forget
                 (access memoize-info-ht-entry entry :forget))
                (memo-table-init-size
                 (access memoize-info-ht-entry entry :memo-table-init-size))
                (aokp
                 (and (access memoize-info-ht-entry entry :ext-anc-attachments)
                      t))
                (cl-defun (access memoize-info-ht-entry entry :cl-defun))
                (invoke
                 (access memoize-info-ht-entry entry :invoke)))
           (push `(memoize-fn ',name
                              :condition ',condition
                              :inline ',inline
                              ,@(and commutative
                                     `(:commutative t))
                              ,@(and forget
                                     `(:forget t))
                              ,@(and memo-table-init-size
                                     `(:memo-table-init-size
                                       ',memo-table-init-size))
                              ,@(and aokp
                                     `(:aokp ',aokp))
                              ,@(and cl-defun
                                     `(:cl-defun ',cl-defun))
                              ,@(and invoke
                                     `(:invoke ',invoke)))
                 (get name '*undo-stack*))))
        (otherwise
         (er hard 'maybe-push-undo-stack
             "Unrecognized CLTL-COMMAND spawn ~x0"
             fn))))

(defun-one-output maybe-pop-undo-stack (name)

; See maybe-push-undo-stack.

  (let* ((name (if (symbolp name)
                   name
                 (packn (cons name '("-PACKAGE")))))
         (stk (get name '*undo-stack*)))
    (cond
     ((null stk) nil)
     (t (eval (car stk))
        (setf (get name '*undo-stack*) (cdr stk))))))

; Now we define the two programs that manage the stacks of old
; property values.

; We start with pushing a new value onto the stack for a given key.
; Complicating things is our decision to order the keys in the alists by (a
; priori) frequency of access.  The aim is to speed up getprop.  We record
; the results of many early experiments below.

; Recall that the current-acl2-world is implemented so that the logical
; properties are stored in an alist which is obtained via a raw lisp get of the
; property *current-acl2-world-key*.  That alist is then searched with assoc
; :test #'eq.  Of interest then are both the order of the properties
; encountered by the raw lisp get and the order of the keys encountered by the
; assoc :test #'eq.

; An early basic experiment addressed one particular proof in the Nqthm
; package.  To set the stage, the Nqthm package was loaded and then undone back
; through NQTHM-COUNT-SYMBOL-IS-COUNT-FN-UNPACK, a theorem whose reported proof
; time is 35.23 by the current Version 1.8.  Then that theorem was proved again
; while a patch was in place inside of fgetprop.  The patch collected together
; an alist recording the calls of fgetprop.  In particular the alist entries
; were of the form (symb (key1 . cnt1) ... (keyk . cntk)) indicating that
; (fgetprop symb keyi <some-default> <current-acl2-world>) was called cnti
; times during the proof.  We then wrote and compiled a program that swept the
; alist and repeated every call of fgetprop simply to allow us to measure the
; total time spent in fgetprop.  There were a total of 102781 calls.  To sweep
; the alist with a no-op function of the same arity as fgetprop required 0.25
; seconds.  We therefore consider that to be the overhead of the sweep itself.
; To sweep with fgetprop required 0.75 seconds, indicating that a "net" 0.50
; seconds were actually spent in fgetprop on the actual calls in the sample
; theorem.  (We will use "net" henceforth to mean the measured time minus
; 0.25.)  This gives an expected "per call" time of 4.86E-6.

; For what it is worth, a noop that calls get has an overhead of 0.267 for
; a net of 0.017 or a per call time of 1.65E-7 seconds.  Thus an fgetprop
; is about 30 times slower than a get (with the orderings created by the
; current Version 1.8).

; However, we have noticed that *current-acl2-world-key* is not always the
; first property encountered by the raw lisp get.  Other properties sometimes
; covering it up include *UNDO-STACK*, *PREDEFINED* and SYSTEM:PNAME.  We
; therefore moved *current-acl2-world-key* to the front of every symbol-plist.
; The net sweep time was then 0.30 (for a per call time of 18 gets).

; We now move on to ordering the keys seen by assoc :test #'eq.  In prior
; experiments we had determined the frequency with which the various keys are
; accessed (during the entire Nqthm package proof).  For what it is worth, here
; is the key list we found, in order from most frequently accessed to least:

;   '(COARSENINGS GLOBAL-VALUE CONGRUENCES SYMBOL-CLASS TYPE-PRESCRIPTIONS
;     LEMMAS RUNIC-MAPPING-PAIRS MULTIPLICITY STATE-IN
;     RECURSIVEP DEF-BODIES CONSTRAINEDP LINEAR-LEMMAS
;     FORMALS MACRO-BODY FORWARD-CHAINING-RULES STATE-OUT TABLE-ALIST
;     GUARD MACRO-ARGS ELIMINATE-DESTRUCTORS-RULE CONST LEVEL-NO
;     UNNORMALIZED-BODY THEOREM REDEFINED INDUCTION-MACHINE JUSTIFICATION
;     INDUCTION-RULES CONTROLLER-ALIST QUICK-BLOCK-INFO

; We therefore reordered the alist so that the keys were stored with the most
; frequently accessed ones first.  We added nil COARSENINGS and CONGRUENCES
; properties (and later, as described below, RECURSIVEP) to those function
; symbol property lists for which the value of the property was nil but the
; property was unrecorded.  (This saves the time of cdring through the entire
; list to compute the most frequently seen two properties.)  Technically, we
; extended and reordered the alist found in (get symb
; *current-acl2-world-key*), for each symbol with a *current-acl2-world- key*
; property and that property was always first on the symbol-plist.

; We then repeated the sweep in a net time of 0.22 seconds (per call = 13 gets).

; We then reversed the "optimal" ordering on the property lists and measured a
; net time of 0.31 (down from 0.30 from the random order of Version 1.8).

; Finally, we perturbed the property lists by adding 10 new property keys and
; values to the front of every (get symb *current-acl2-world-key*) and measured
; a net time of 0.50.

; From this experiment one can make the following conclusions: (a) In this
; theorem, fgetprop is responsible for less than 2% of the proof time.  Making
; fgetprop instantaneous would reduce the 35.23 seconds to 34.73 seconds.

; By ordering the properties (in both senses) we can speed fgetprop up from
; about 30 gets to about 13 gets, more than doubling its speed.

; The rest of this essay on experimental results discusses some detailed
; investigations that led to virtually no further improvement (see stats at the
; end of the essay).  The lesson learned is that it may not be worth mucking
; around further with *current-acl2-world-key-ordering*.

; In July 2002, during the development of Version_2.7, we modified the use of
; the fnstack (specifically, being-openedp) so that for recursive functions we
; look up the representative of a clique, thus avoiding the need to look
; through all members every clique for the function at hand.  (A
; mutual-recursion nest with 4,786 defuns at AMD prompted this change.)  As a
; result we saw a 1.8% slowdown in the regression suite, reduced to 0.9% with
; some optimizations.  Presumably the slowdown was due to the more frequent use
; of the RECURSIVEP property.  So we ran experiments using community books
; files books/certify-numbers.lisp and books/rtl/rel2/support/cert.lsp, though
; we aborted the latter part way through lop3.lisp (during the proof of
; BITN-LAM0, which seemed to be bogging down).  The results using
; analyze-fgetprop-stats were as follows.

; books/certify-numbers.lisp:
;
; GLOBAL-VALUE                                        2474980
; COARSENINGS                                         2332094
; TYPE-PRESCRIPTIONS                                  1162730
; RUNIC-MAPPING-PAIRS                                  979110
; CONGRUENCES                                          769460
; RECURSIVEP                                           676128
; TABLE-ALIST                                          675429
; SYMBOL-CLASS                                         415118
; LEMMAS                                               381015
; MACRO-BODY                                           356823
; STOBJS-OUT                                           303906
; FORMALS                                              213447
; STOBJS-IN                                            161261
; STOBJ                                                101845
; GUARD                                                 75749
; MACRO-ARGS                                            75221
; BODY ; changed later to def-bodies                    68867
; CONSTRAINEDP                                          50190
; FORWARD-CHAINING-RULES                                49839
; CONST                                                 25601
; ELIMINATE-DESTRUCTORS-RULE                            19922
; THEOREM                                                9234
; LINEAR-LEMMAS                                          9102
; ...
;
; books/rtl/rel2/support/cert.lsp (aborted as explained above):
;
; COARSENINGS                                        30087445
; GLOBAL-VALUE                                       28366962
; CONGRUENCES                                        27187188
; RUNIC-MAPPING-PAIRS                                13934370
; TYPE-PRESCRIPTIONS                                 12058446
; RECURSIVEP                                         10080678
; TABLE-ALIST                                         4644946
; SYMBOL-CLASS                                        2742519
; LEMMAS                                              1978039
; STOBJS-OUT                                          1943646
; MACRO-BODY                                          1837674
; FORMALS                                             1185024
; STOBJS-IN                                            781274
; BODY ; changed later to def-bodies                   585696
; STOBJ                                                509394
; GUARD                                                390584
; MACRO-ARGS                                           389694
; CONSTRAINEDP                                         332418
; FORWARD-CHAINING-RULES                               211225
; CONST                                                145628
; ABSOLUTE-EVENT-NUMBER                                 93259
; LINEAR-LEMMAS                                         34780
; ...

; As a result, we revised the ordering of keys.  We also noticed that although
; GLOBAL-VALUE is high on the list, most of that was accounted for by looking
; it up for symbols RECOGNIZER-ALIST (which is no longer a world global, after
; Version_8.2) and UNTOUCHABLES, which do not have other properties:

; books/certify-numbers.lisp:
;
; RECOGNIZER-ALIST                               2056058
;  GLOBAL-VALUE                                       2056058
; UNTOUCHABLES                                    261297
;  GLOBAL-VALUE                                        261297
;
; books/rtl/rel2/support/cert.lsp (aborted as explained above):
;
; RECOGNIZER-ALIST                              26193957
;  GLOBAL-VALUE                                      26193957
; UNTOUCHABLES                                   1359647
;  GLOBAL-VALUE                                       1359647

; The user times (in seconds) for running the regression suite using an Allegro
; 6.0 Linux development Version_2.7 were as follows, with successive
; "improvements" shown.

; 15359.38 ; original time
; 15637.45 ; 1.81% slowdown: first cut at new approach to fnstack for mutrec
; 15496.32 ; 0.89% slowdown: optimizations in being-openedp (made a macro)
; 15497.46 ; 0.90% slowdown: new *current-acl2-world-key-ordering*
; 15481.14 ; 0.79% slowdown: always put recursivep property on function symbols

; March 2006: Here are some new numbers, listing in each case down to about 2
; orders of magnitude below the most-used property.  All were obtained with all
; output inhibited.

; ============================================================
;
; stats0 (books/certify-numbers.lisp):
;
; COARSENINGS                                         2527582
; GLOBAL-VALUE                                        2224181
; RUNIC-MAPPING-PAIRS                                 1188675
; TYPE-PRESCRIPTIONS                                  1074218
; CONGRUENCES                                          730666
; DEF-BODIES                                           685868
; TABLE-ALIST                                          642459
; SYMBOL-CLASS                                         400157
; LEMMAS                                               362209
;
; ============================================================
;
; stats1 (books/workshops/1999/compiler/proof1):
;
; COARSENINGS                                         1137397
; DEF-BODIES                                           705063
; GLOBAL-VALUE                                         587267
; TABLE-ALIST                                          360303
; TYPE-PRESCRIPTIONS                                   196192
; CONGRUENCES                                          194726
; SYMBOL-CLASS                                         177363
; LEMMAS                                               167682
; RUNIC-MAPPING-PAIRS                                   75828
; STOBJS-OUT                                            13381
; MACRO-BODY                                            10245
;
; ============================================================
;
; stats2 (:mini-proveall):
;
; COARSENINGS                                           87020
; GLOBAL-VALUE                                          58987
; RUNIC-MAPPING-PAIRS                                   54106
; TABLE-ALIST                                           32902
; DEF-BODIES                                            26496
; TYPE-PRESCRIPTIONS                                    24822
; CONGRUENCES                                           20367
; LEMMAS                                                17938
; SYMBOL-CLASS                                          15271
; FORWARD-CHAINING-RULES                                 4820
; FORMALS                                                1278
; MACRO-BODY                                             1216
; STOBJS-OUT                                             1199
; ELIMINATE-DESTRUCTORS-RULE                              962
;
; ============================================================
;
; stats3 (osets/map):
;
; DEF-BODIES                                           288073
; RUNIC-MAPPING-PAIRS                                  262004
; COARSENINGS                                          235573
; GLOBAL-VALUE                                         171724
; FORMALS                                               84780
; TABLE-ALIST                                           76462
; UNNORMALIZED-BODY                                     61718
; TYPE-PRESCRIPTIONS                                    56193
; LEMMAS                                                54533
; CONSTRAINEDP                                          52642
; SYMBOL-CLASS                                          43824
; CONGRUENCES                                           36786
; MACRO-BODY                                            30206
; STOBJS-OUT                                            27727
; THEOREM                                               15714
;
; ============================================================
;
; stats4 (rtl/rel5/support/drnd):
;
; COARSENINGS                                        20881212
; GLOBAL-VALUE                                       10230404
; RUNIC-MAPPING-PAIRS                                 7726914
; TYPE-PRESCRIPTIONS                                  4177523
; DEF-BODIES                                          2732746
; SYMBOL-CLASS                                         705776
; STOBJS-OUT                                           671763
; TABLE-ALIST                                          664941
; CONGRUENCES                                          497120
; LEMMAS                                               376371
; MACRO-BODY                                           294016
;
; ============================================================
;
; stats5 (rtl/rel2/support/cert.lsp):
;
; COARSENINGS                                        21792912
; GLOBAL-VALUE                                       15497700
; RUNIC-MAPPING-PAIRS                                 8088313
; TYPE-PRESCRIPTIONS                                  6554966
; DEF-BODIES                                          5365470
; TABLE-ALIST                                         2641304
; SYMBOL-CLASS                                        1873984
; CONGRUENCES                                         1562924
; LEMMAS                                              1220873
; STOBJS-OUT                                           420330
; MACRO-BODY                                           364583
; FORMALS                                              248019
; FORWARD-CHAINING-RULES                               245442
;
; ============================================================

; In December 2019 we did several experiments to improve
; *current-acl2-world-key-ordering*, since it had probably been many years
; since that was attempted and also because RECOGNIZER-ALIST had recently been
; added as a new property (with property GLOBAL-VALUE therefore being accessed
; less often).  Several community books were included or LDed, as follows, in
; each case after adding the commented-out call of update-fgetprop-stats to the
; definition of fgetprop (together with the commented-out definitions,
; including the one for update-fgetprop-stats, just above fgetprop's definition
; in axioms.lisp).

;   (include-book "centaur/sv/top" :dir :system)

;   (ld "proof-by-generalization-mult.lisp") ; in workshops/2004/legato/support/

;   (include-book "centaur/gl/gl" :dir :system)

;   (ld "centaur/aignet/cert.acl2" :dir :system)
;   (ld "centaur/aignet/cuts4.lisp" :dir :system)

;   (ld "centaur/bitops/cert.acl2" :dir :system)
;   (ld "centaur/bitops/ihsext-basics.lisp" :dir :system)

;   (include-book "centaur/bitops/ihsext-basics" :dir :system)

;   (include-book "projects/x86isa/top" :dir :system)

;   (ld "projects/x86isa/proofs/popcount/cert.acl2" :dir :system)
;   (ld "projects/x86isa/proofs/popcount/popcount.lisp" :dir :system)

; We then called analyze-fgetprop-stats in each case to get suitable
; statistics.  Finally, we modified *current-acl2-world-key-ordering* by
; inspecting the results.

; End of Experimental Results.

; Below we list the most important property keys according to the results
; above.  Keys are stored in alists in this order, i.e., keys occurring earlier
; in this list are stored earlier in the alists.  When a key not occurring in
; this list is added to the alist it is as though it occurred at the very end
; of this list, i.e., it gets a low priority.  Not all keys used by the current
; system are in this list (see below).

(defparameter *current-acl2-world-key-ordering*
  '(COARSENINGS ; during proofs more than include-book
    GLOBAL-VALUE ; largely for untouchables when including a book
    RECOGNIZER-ALIST ; during proofs more than include-book
    RUNIC-MAPPING-PAIRS ; during proofs more than include-book
    DEF-BODIES ; during proofs more than include-book
    SYMBOL-CLASS
    STOBJS-OUT
    TYPE-PRESCRIPTIONS
    TABLE-ALIST
    LEMMAS
    CONGRUENCES
    PEQUIVS
    MACRO-BODY ; during include-book more than proofs
    FORMALS ; during include-book more than proofs

; Note: As of this writing there are many properties not included above, all of
; which fall into the low priority category.  We have omitted keys simply to
; keep the list shortened and thus to speed up the insertion program
; (merge-into-alist, on behalf of destructive-push-assoc) a little.  This is an
; unanalyzed "optimization".

    ))

(defun-one-output key-lesseqp (key1 key2 ordering)

; We return t if key1 occurs weakly before key2 in the ordering.

  (cond ((null ordering) t)
        ((eq key1 (car ordering)) t)
        ((eq key2 (car ordering)) nil)
        (t (key-lesseqp key1 key2 (cdr ordering)))))

(defun-one-output merge-into-alist (key val alist)

; Alist is a symbol alist, key is a symbol that is not bound in alist.  We wish
; to create the alist that is logically equivalent under assoc-eq to (cons
; (cons key val) alist) but we actually place the new pair in the proper place
; according to the *current-acl2-world-key-ordering*.

  (cond ((null alist) (list (cons key val)))
        ((key-lesseqp key (caar alist) *current-acl2-world-key-ordering*)
         (cons (cons key val) alist))
        (t (cons (car alist) (merge-into-alist key val (cdr alist))))))

(defun-one-output destructive-push-assoc (key value alist world-key)

; We push value onto the stack associated with key in alist.  If key has no
; value in alist, we pretend it has the empty stack.  E.g., if alist is '((a .
; (1))) and we push 2 on 'a we get '((a . (2 1))) and if we then push 0 on 'b
; we get '((b . (0)) (a . (2 1))).  This function is maximally destructive on
; the cons structure of alist and the stacks, but doesn't touch the cons
; structure of the values.  We keep the alists in sorted order iff the
; world-key is our special one, *current-acl2-world-key*.

  (let ((temp (assoc key alist :test #'eq)))
    (cond (temp (setf (cdr temp) (cons value (cdr temp)))
                alist)
          ((eq world-key *current-acl2-world-key*)
           (merge-into-alist key (list value) alist))
          (t (cons (cons key (list value)) alist)))))

(defun-one-output destructive-pop-assoc (key alist)
  (let ((temp (assoc key alist :test #'eq)))
    (cond (temp (setf (cdr temp) (cdr (cdr temp)))
                alist)
          (t alist))))

(defun-one-output remove-current-acl2-world-key (plist)
  (cond ((null plist) plist)
        ((eq (car plist) *current-acl2-world-key*)
         (cddr plist))
        (t (cons (car plist)
                 (cons (cadr plist)
                       (remove-current-acl2-world-key (cddr plist)))))))

; We now develop support for early loading of compiled files, beginning with an
; essay that outlines that development.

; Essay on Hash Table Support for Compilation

; This essay has the following main parts:

; Part 0: High-level summary
; Part 1: A more detailed introduction
; Part 2: Including a certified book
; Part 3: Writing an expansion file for compilation

; Part 0: High-level summary

; We strive for efficiency of include-book.  By doing all compilation at
; certify-book time rather than include-book time, we may greatly speed up
; definitional processing in lisps such as CCL and SBCL, which compile every
; definition on the fly.  We were motivated by profiling results showing that
; such processing can take 45% of include-book time: a test case from Centaur
; using CCL was spending this proportion of time in the installation of a
; Common Lisp symbol-function for each defun event, in add-trip.  The problem
; was that the CCL compiler is called every time a defun is evaluated, and
; although the CCL compiler is impressively fast, it's not instantaneous.  Dave
; Greve has reported observing significant such slowdowns using CCL at Rockwell
; Collins.

; Happily, with this change we found the time cut roughly in half for two
; include-book tests from Centaur provided by Sol Swords.  Other tests suggest
; no noticeable slowdown for certify-book or include-book for GCL or Allegro
; CL, which do not compile on the fly.  For additional tests, see community
; books directory books/system/tests/early-load-of-compiled/, specifically file
; README.txt in that directory.

; Our approach is to try to avoid calling the compiler (which happens in CCL
; and SBCL whenever a definition is evaluated) when a definition is encountered
; by include-book, by instead using existing code previously compiled by
; certify-book, which is loaded before processing of events by include-book.
; Thus, the main efficiency gains from this change are expected to be for ACL2
; built on CCL or SBCL, as these are the Lisps we know of (as of March 2010)
; that compile all definitions at submission time and therefore had been
; compiling on behalf of add-trip.  However, this approach may also boost
; efficiency in some cases even for Lisps other than CCL and SBCL.  For one
; thing, include-book will now install a compiled symbol-function for each
; defun, even for those other Lisps, which can speed up computations in ensuing
; defconst forms and defmacro forms of the book.  Moreover, compiled code will
; be installed for defmacro and defconst forms, which can avoid the need for
; redoing macroexpansion of the bodies of such forms during add-trip.

; A simple-minded approach is to load the compiled file for a book *before*
; processing events in the book.  The obvious problem is that ACL2 demands that
; a function not be pre-defined in raw Lisp when evaluating a defun event, and
; for good reason: we want to protect against accidental previous definition in
; raw Lisp.  So instead, our solution is to arrange that loading compiled files
; does not actually install definitions, but rather, builds hash tables that
; associate symbols with their definitions.  The file to be compiled thus has
; roughly the following structure; the prefix "hcomp" is intended to refer to
; "hash-table-supported compilation".

; (in-package "ACL2")
;;; Introduce some packages, without any imports:
; (maybe-introduce-empty-pkg "MY-PKG")
;;; Save some information about the functions, constants, and macros:
; (setq *hcomp-fn-alist* '((fn1 ..) (fn2 ..) ..))
; (setq *hcomp-const-alist* '((c1 ..) (c2 ..) ..))
; (setq *hcomp-macro-alist* '((mac1 ..) (mac2 ..) ..))
;;; Support compilation of loop$ forms (see Part 3 below):
; (when (eq *readtable* *reckless-acl2-readtable*)
;   (setq *set-hcomp-loop$-alist* t))
; (when *set-hcomp-loop$-alist*
;   (setq *hcomp-loop$-alist* '..))
;;; Build a hash table associating fni, ci, and maci with pre-existing
;;; compiled definitions or special *unbound* mark:
; (hcomp-init)
;;; Generate declaim forms (depending on the Lisp):
; ...
;;; Portcullis commands and events from the book, with make-events expanded:
; ...
;;; *1* definitions to compile:
; ...

; Let's focus on functions (macros and constants have similar handling).  The
; load of each book in raw Lisp (by function load-compiled-book) is followed by
; code that saves the symbol-function for each fni in a hash table,
; *hcomp-fn-ht* (function hcomp-transfer-to-hash-tables), which in turn is
; associated with the full-book-name in a global hash table, *hcomp-book-ht*.
; But first, the (hcomp-init) form arranges to save -- in a global hash table,
; *hcomp-fn-macro-restore-ht* -- an association of each fi with its existing
; symbol-function (or a "not bound" marker).  After all such files are loaded
; in raw Lisp under the top-level included book (by a call of
; include-book-raw-top under include-book-fn), the relevant *hcomp-fn-ht* hash
; tables will have been populated and saved in the global hash table mentioned
; above, *hcomp-book-ht*, keyed on full-book-names.  The top-level include-book
; will finish up after such files are loaded (for that book and subsidiary
; included books), using the global hash table *hcomp-fn-macro-restore-ht* to
; restore the symbol-function of fi (much more typically, to make the
; symbol-function of fi unbound) when the top-level load concludes.

; Above, we say "roughly" because there are numerous complications.  For
; example, *1* functions can be defined twice (once for :program mode and once
; for :logic mode); there may be portcullis commands for subsidiary
; include-book events within the book; and the absence of a missing compiled
; file for a sub-book can cause an abort, so some of the above finishing-up
; might need to be done in the cleanup form of an acl2-unwind-protect.  In this
; Essay we outline our mechanism and explain how we deal with such
; complications.

; We are breaking from ACL2 versions up through  3.6.1, by insisting that the
; compiled file for a book is loaded "early" (if it is loaded at all), i.e.,
; before events are processed from that book.  This approach not only can boost
; efficiency of include-book, but it also provides a solution to a soundness
; bug in the redundancy of :program mode definitions with preceding :logic mode
; definitions, present from Version_3.5 through Version_3.6.1.  To illustrate
; this bug, consider the two books below, which have been certified in ACL2
; 3.6.1 built on GCL.  The problem is that inclusion of bk1 inside bk2 smashes
; the symbol-function of *1*foo, because of loading of compiled file bk1.o.
; (The Allegro CL version merely breaks when attempting to prove BUG.)

; -------------------- bk1.lisp --------------------

; (in-package "ACL2")
; (defun foo (x)
;   (declare (xargs :mode :program))
;   (car x))

; -------------------- bk2.lisp --------------------

; (in-package "ACL2")
; (defun foo (x)
;   (car x))
; (defun bar (x)
;   (foo x))
; (defthm fact
;   (null (bar 3))
;   :rule-classes nil)
; (encapsulate
;   ()
;   (local (include-book "bk1"))
;   (defthm bug
;     (not (null (bar 3)))
;     :rule-classes nil))
; (defthm contradiction
;   nil
;   :hints (("Goal" :use (fact bug)
;                   :in-theory (disable (bar) bar)))
;   :rule-classes nil)

; ----------------------------------------

; The bug occurs because the local include-book of "bk1" loads bk1.o, which
; smashes the symbol-function of *1*foo to its :program mode version, which
; unlike the :logic mode version passes evaluation directly to raw Lisp,
; causing evaluation of (car 3).  Of course we don't really need to solve this
; problem for CCL-based ACL2 images that do not load compiled files.  But that
; seems ugly, as one could then certify a book with CCL that cannot be
; certified with another Lisp.

; Another, less serious problem is also solved by early loading of compiled
; files.  Consider the following books.

;;; bar.lisp
; (in-package "ACL2")
; (defun foo (x)
;   (declare (xargs :guard t))
;   (cons x x))

;;; foo.lisp
; (in-package "ACL2")
; (defun foo (x)
;   (cons x x))

;;; top.lisp
; (in-package "ACL2")
; (include-book "bar")
; (include-book "foo")

; The *1* function generated for foo in bar.lisp is considerably simpler than
; in the case of foo.lisp, because there need be no check that the symbol-class
; of foo is :common-lisp-compliant.  When we include top in Version_3.6.1 or
; earlier, loading compiled files, the compiled file for foo overwrites the one
; for bar, leaving us with the more complicated *1* code.  This is clear if one
; uses CLISP and evaluates (disassemble (*1*-symbol 'foo)) in raw Lisp: 13
; byte-code instructions if one includes foo or top, but only 3 byte-code
; instructions if one includes bar instead.  With early loading of compiled
; files, evaluation of (include-book "top") will define this *1* function when
; including bar, but will not define it again when including foo.

; (The above example isn't convincing of much, really, since if we switch the
; order of the include-book forms in top.lisp then we will get the complicated
; *1* compiled definition of foo, because the definition from bar.lisp will be
; redundant.  But it still seems preferable to avoid loading compiled files
; that overwrite definitions needlessly, for example to put less stress on the
; garbage collector.)

; Of course, these issues disappear if the compiled file is not loaded at all;
; and we support that too, using state global 'compiler-enabled.

; We conclude this Part (High-level summary) with a few words about handling of
; the case that include-book argument :load-compiled-file has argument :comp.
; The basic idea is to wait until the book is included, and then check that
; either the compiled file or the expansion file exists and is not older than
; the certificate; and only then, if the expansion file exists but the compiled
; file does not, do we compile the expansion file and then load it in the
; ordinary way (without messing with hash tables, by leaving the relevant
; variables such as *hcomp-fn-ht* bound to nil).  We considered more complex
; approaches but are quite happy with this simple solution, and we don't say
; anything further about the case of :load-compiled-file :comp in this Essay.

; Part 1: A more detailed introduction

; We now give a more detailed global view of our approach based on hash tables.
; Note that since compilation is inherently a raw-Lisp activity, we code
; shamelessly in raw Lisp when that is convenient.

; The idea is for include-book to load an existing compiled file before
; processing events from the book, even before its portcullis commands are
; processed.  The compiled definitions are stored in hash tables for subsequent
; use by add-trip, then immediately undone so that existing definitions are
; restored (or, much more often, symbols are again unbound).  We must however
; be careful to use these hash tables only when appropriate: in particular,
; verify-termination changes *1* definitions, so there can be two definitions
; generated for the same symbol -- and loading the compiled file provides the
; latter definition, which is inappropriate to use for the first defun but is
; appropriate for the defun generated by the verify-termination.

; (Aside: We might consider using the latter symbol-function for both the
; :program and :logic mode *1* functions.  But it's easy to imagine that the
; :logic code asks about the symbol-class of the function symbol under the
; assumption that it's definitely not :program -- and that assumption would be
; violated if we installed that code when the :program mode version is
; introduced.  Whether or not that problem actually exists, or at least is easy
; to fix, this example nevertheless illustrates that evaluation in ACL2 is
; complex and delicate.  So we prefer to be conservative and not to install a
; :logic mode *1* function definition for a :program mode function.)

; The introduction of make-event in 2006 initiated the writing of what we call
; below an "expansion file", to be compiled instead of the source book,
; creating what we call below the "compiled file".  This feature was further
; exploited by incorporating compiled *1* functions into the compiled file
; (Version_3.2.1).  We take further advantage of these expansion files by
; putting forms into them to implement the plan outlined above.  Note that we
; handle certain events that create 'cltl-command properties, as processed by
; add-trip: defun, defstobj, defabsstobj, defconst, and defmacro, but not
; memoize and unmemoize.  Extra forms near the top of the expansion file will
; be evaluated when loading the compiled file, to store values in hash tables
; for later use, when add-trip deals with 'cltl-command properties.  Those
; extra forms are based on information deduced during the include-book phase of
; book certification, at which time Lisp global *inside-include-book-fn* has
; value 'hcomp-build.  Later, during subsequent include-books, that information
; directs which definitions from the expansion file are to be stored in our
; hash tables.  Additional forms are evaluated after completion of the load of
; the compiled file, to transfer the compiled definitions to hash tables and
; eventually to remove each definition installed by the expansion file
; (restoring any pre-existing definitions).  This eventual removal occurs only
; after a load completes for the top-level compiled file of a book, and hence
; also for all books included therein.

; Portcullis commands and included sub-books present challenges.  Consider for
; example a constant whose value is a symbol in a package defined in a
; sub-book's portcullis commands.  If we load the compiled file for the book
; that defines that constant, but treat the include-book of the sub-book as a
; no-op (as was done through Version_3.6.1), then it doesn't seem clear that
; this constant's value would be interned in any package, since its package is
; defined in the portcullis commands of the not-yet-loaded sub-book.  Indeed,
; we need to consider loading not only the sub-book but also its portcullis
; commands.  At the very least, we want to avoid warnings that could occur when
; encountering a global or function call in the parent book (say, during macro
; expansion) when the definition of that global or function (by defconst or
; defun, respectively) comes from the unloaded sub-book.  And certainly we do
; need a sub-book's portcullis commands when loading it, for example in case
; one of those commands defines a function that is used in a defconst form in
; the book.

; We thus write portcullis commands into the expansion file.  But with some
; reflection one discovers that a book's initial in-package form itself could
; be problematic, since if the package in question is not the "ACL2" package
; then it needs to be defined in some book's portcullis commands!  So we always
; start an expansion file with (in-package "ACL2"), and when we write the forms
; into the expansion file, we always do so relative to the ACL2 package.

; But our problems with packages don't end there!  The setq forms defining
; *hcomp-fn-alist* and the like may involve symbols defined in packages
; introduced in the portcullis commands.  (Why use setq instead of
; defparameter?  Variables such as *hcomp-fn-alist* are already declared
; special using defvar in the ACL2 sources, so setq is certainly legal.  We
; found a case with CCL in which the use of defparameter slowed down
; include-book by a factor of more than 100.)  But we want to lay these down
; before a call of hcomp-init, which will consult *hcomp-fn-alist* and such
; when storing information to let us undo definitions installed by loading the
; compiled file.  This call of hcomp-init, and its preceding definitions of
; *hcomp-fn-alist* and the like, must therefore be laid down before the very
; portcullis commands that may define packages of symbols used in these
; definitions.  Our solution is to use defpackage to introduce packages before
; the symbols are read, and to make a note using special variable
; *defpkg-virgins* that such packages are legitimate targets for the defpkg
; forms to come.

; (Aside: Why does it work to start the expansion file with the introduction of
; an empty package, say "MY-PKG", and then lay down forms like the
; *hcomp-fn-alist* form, above, that may refer to symbols written out at the
; end of book certification?  The only symbols where one might imagine this is
; an issue are ones that are printed differently when "MY-PKG" is fully defined
; (near the end of certification) than when it is introduced with no imports by
; an initial form that introduces the package as "empty" (no imports).  The
; only such symbols are those written without a package prefix, hence included
; in the "ACL2" package, that are in the import list for "MY-PKG".  But such
; symbols aren't a problem after all, because any reference to such a symbol in
; the "ACL2" package is really a reference to a symbol of that name in the
; "MY-PKG" package, once that package is "truly" introduced by defpkg.  And
; until such a defpkg form is evaluated, ACL2 will not dabble in symbols in the
; "MY-PKG" package, other than to save them in *hcomp-fn-alist* and related
; lists near the top of the expansion file.)

; Note that in a break from ACL2 versions up through  3.6.1, where ACL2 could
; load compiled files for uncertified books, the write-date comparison of the
; compiled file (or expansion file) is against the certificate rather than the
; source .lisp file.  (Well, that's not quite true: the comparison remains
; against the source book when include-book is executed in raw mode, since raw
; mode does not involve the certificate file.)

; We designate three "add-trip contexts", according to whether processing of a
; 'cltl-command property by add-trip is assigning a function, a global variable
; (e.g. for defconst), or a macro value.  We refer to the symbol being assigned
; a value as an "add-trip symbol", and we call that value a "relevant value"
; (with respect to that context, which is often implicit) for that symbol.
; Whenever we refer to the add-trip symbols of a book, that reference includes
; add-trip symbols for the book's portcullis commands as well, but not add-trip
; symbols of subsidiary included books.  Note by the way that a *1* function
; symbol can be an add-trip symbol.  The final step after loading a top-level
; compiled file will be to undo the load's assignment of relevant values to
; add-trip symbols.  This step will be done in the cleanup form of an
; unwind-protect, so as to clean up if an error or interrupt occurs during
; loading of the compiled file.  (The clean-up won't be complete for functions
; defined in raw-mode, just as it hasn't been in earlier versions of ACL2 that
; did not load compiled files early.  But raw-mode is ultimately the user's
; responsibility, and we expect problems from such aborts to be rare.)

; We next describe several variables and a constant, which we define before
; include-book-fn.

;   Variables *hcomp-fn-ht*, *hcomp-const-ht*, and *hcomp-macro-ht* are
;   intended to be let-bound to eq hash tables: one for ACL2 user functions and
;   their *1* symbols, one for constants (as with defconst), and one for
;   macros.

;   Variables *hcomp-fn-alist*, *hcomp-const-alist*, and *hcomp-macro-alist*
;   will be be let-bound to alists related to the above hash tables, in senses
;   described below.

;   The variable *hcomp-fake-value* is used as a "fake value", not in any
;   package known in the ACL2 loop, for various purposes below.

;   Variables *hcomp-fn-macro-restore-ht* and *hcomp-const-restore-ht* are
;   globally bound to hash tables that are populated as books are included,
;   storing existing relevant values (or *hcomp-fake-value* when the relevant
;   value is unbound) for add-trip symbols.

;   A hash table variable, *hcomp-book-ht*, holds other hash tables, as
;   follows.

; A key of *hcomp-book-ht* is a full-book-name.  Values in this hash table are
; hcomp-book-ht-entry records, where each record has a status field that
; describes the attempt to load the book's compiled file, and also has optional
; fields corresponding to values of *hcomp-fn-ht*, *hcomp-const-ht*, and
; *hcomp-macro-ht*.  When ACL2 encounters an include-book form during an early
; raw-Lisp load of an include-book whose full-book-name is not already a key of
; the world's 'include-book-alist or of *hcomp-book-ht*, then include-book
; loads that sub-book's compiled file, hence with new let-bindings of the
; *hcomp-xxx-alist* and *hcomp-xxx-ht* variables, along with unwind protection
; using the *hcomp-xxx-restore-ht* values that can restore relevant values
; after transferring them to those hash tables.  Upon exiting include-book
; successfully, the *hcomp-xxx-ht* variables are associated with the
; full-book-name in *hcomp-book-ht*.

; (Note: One might think that the hash tables one gets by loading the compiled
; file could vary with context, which makes it unreasonable to compute them for
; a sub-book before processing events in the main book.  But as long as the
; book and all books under it remain certified and unchanged, we expect that
; all relevant values depend essentially only on the closure under ancestors of
; the events in the sub-book.)

; We next consider the question of whether it really buys us anything to save
; compiled definitions for defconst and defmacro forms.  The answer is (or can
; be) yes, because macros may have been expanded away.  (See the discussion of
; "minimal compilation" in the Common Lisp Hyperspec: it is defined in
; http://www.lispworks.com/documentation/HyperSpec/Body/03_bbb.htm, and it is
; specified for file compilation in #6 of
; http://www.lispworks.com/documentation/HyperSpec/Body/03_bca.htm.)  One
; experiment that drives this point home (we have tried GCL and CCL) is the
; following.  Consider the following files, and see the comments in the
; commands below them.

; .................... tmp.lsp ....................
; (in-package "ACL2")
; (defun foo (n)
;   (cond ((zp n) 1)
;         (t (loop for i from 0 to (1- n)
;                  when (equal (foo i) 2)
;                  do (return i))
;            1)))
; (defmacro mac () (foo 27))
; .................... tmp2.lsp ...................
; (in-package "ACL2")
; (load "tmp") ; load compiled file
; (defmacro mac2 () (mac))
; .................... tmp3.lsp ...................
; (in-package "ACL2")
; (load "tmp") ; load compiled file
; (defconst *c* (mac))
; .................................................

; Now do the following (with both CCL-based and GCL-based ACL2 images):

; <Start ACL2>
; :q
; (compile-file "tmp.lsp") ; fast
; (quit)
; <Start ACL2>
; :q
; (load "tmp2.lsp") ; slow definition of mac2
; (compile-file "tmp2.lsp") ; slow
; (load "tmp2") ; fast definition of mac2 from compiled file
; (quit)
; <Start ACL2>
; :q
; (load "tmp2") ; fast definition of mac2 from compiled file
; (quit)
; <Start ACL2>
; :q
; (load "tmp3.lsp") ; slow definition of *c*
; (compile-file "tmp3.lsp") ; fast
; (load "tmp3") ; fast
; (quit)
; <Start ACL2>
; :q
; (load "tmp3") ; slow(GCL)/fast(CCL) def of *c* from compiled file
; (load "tmp3") ; faster (some kind of memoization?)
; (quit)

; We conclude this Part with a discussion of some tricky issues for the case
; that an expansion or compiled file is loaded by include-book, i.e., the case
; that a book is being included with a non-nil effective value of
; :load-compiled-file, where by "effective value" we mean the value after
; accounting for state global 'compiler-enabled.

; If the compiled file or certificate is missing, or else if the compiled file
; is older than the certificate, we may print a warning and go on, assigning
; 'incomplete status to that book in *hcomp-book-ht* -- but there are a couple
; of exceptions.  If :load-compiled-file is t for the current book or any
; parent include-book in progress (as recorded by special variable
; *load-compiled-stack*), then we cause an error.  If :load-compiled-file is
; not t, then we are content with loading the expansion file in place of the
; compiled file, provided the expansion file is not older than the certificate;
; see load-compiled-book.  In that case we obtain interpreted code when
; add-trip reads a hash table for the value to use, for lisps that do not
; compile on-the-fly; but in that case we are really no worse off than if we
; were computing and evaluating the corresponding definition during event
; processing.

; If however the compiled file is up-to-date with respect to the certificate,
; then we may reasonably assume that the compiled file was valid at one time,
; even if the book is now uncertified.  (We could gain some confidence that the
; book is certified by insisting that the certificate is not older than the
; book.  But some ACL2 users like to update the comments in a book without
; invalidating the certificate.)  We load the compiled file with a suitable
; unwind-protect, restoring relevant values after the load completes (whether
; aborted or not).  If it turns out that the book is uncertified, say because
; its certificate is out-of-date or is for the wrong ACL2 version, we will
; simply avoid using the hash tables computed when loading its compiled file,
; since we don't trust the relevant values stored in those tables.

; What happens if a compiled file is missing for a sub-book (and, if
; :load-compiled-file is not t, the expansion file is also missing)?  Because
; of the possibility of missing packages, at the least, we want to avoid forms
; from the parent book's compiled file (or expansion file -- whichever we are
; loading) that are below the include-book of that sub-book.  So, we abort with
; a throw and a warning, associating the partially-constructed hash tables with
; the parent full-book-name in *hcomp-book-ht*, and leaving it to the cleanup
; form of the surrounding unwind-protect to restore symbol-functions in
; existence before the load of the parent book's compiled file.  Of course, if
; the parent book is itself a sub-book of a book being included, then its
; parent's load is in turn similarly aborted, and so on up the chain.  Note
; that loading the source file in raw Lisp is not an option in general, because
; all of the *hcomp-xxx-alist* setq forms and (hcomp-init) form, not to mention
; that make-event forms in source files are illegal (with the rare exception of
; a consp :check-expansion argument).  Again, the expansion file is a good
; candidate for loading if the compiled file is missing, and this is done in
; order to avoid the aborts described above provided we are not under an
; include-book with :load-compiled-file = t.

; Given a top-level include-book event, it may be helpful to visualize all
; included books and sub-books by arranging them into a tree growing downward,
; with the top-level included book as the root at the top, its sub-books as its
; children from left to right in order of their include-book forms in the
; top-level book, and similarly for sub-books of those sub-books, and
; recursively on downward.  ACL2 will include books with a depth-first
; left-to-right traversal of this tree.  First suppose that the top-level
; include-book form's :load-compile-file argument has an effective value (i.e.,
; accounting for 'compiler-enabled and defaults) other than nil.  At the first
; failure to load a compiled file (either because it is missing or it is out of
; date with respect to the .cert file), all parent books up the tree are
; considered to have incomplete loads of their compiled files.  However, if
; none of these superior books has a :load-compile-file argument with effective
; value of t, then the partially-populated hash tables are considered
; sufficient and the process continues.  To see how warnings and errors are
; handled, suppose we have: book1 includes book2 includes book3 includes book4;
; the compiled file for book4 is missing; and the effective value of
; :load-compile-file for all of these is non-nil.  Then we will see a "Compiled
; file" warning unless either book4 or one of its ancestor books (book1, book2,
; book3) has a :load-compile-file argument of t, in which case an error will
; occur.

; We close this introduction with a partial disclaimer.  The Common Lisp
; Hyperspec does not seem to specify fully which side effects may be caused by
; DEFUN.  Thus, although our approach will install symbol-functions, there
; seems to be no guarantee that it will allow other side-effects caused by
; DEFUN.  No such side-effect is critical for ACL2.  Nevertheless, it is
; fortunate that some such side-effects may still be handled, as illustrated by
; the following experiment in CCL.  First, load a compiled definition of
; function foo from a compiled file, save the symbol-function of foo in
; variable xxx, evaluate (fmakunbound 'foo), and then evaluate (setf
; (symbol-function 'foo) xxx).  After all this: if the defun of foo has a Lisp
; documentation string, then (documentation 'foo 'function) will still return
; that string; and if moreover ccl::*save-source-locations* is t, then
; (disassemble 'foo) will give the same nice result both before the fmakunbound
; and after the setf.

; We turn next to describing how compiled (and expansion) files are used when
; including a certified book.  We defer to Part 3 an explanation of how
; expansion files are created (and thus, how compiled files are created) during
; book certification.

; In this essay, while we occasionally mention the use of raw mode within a
; book, presumably within a progn! form in the presence of a trust tag, we do
; not consider explicitly the evaluation of include-book forms in raw Lisp.
; This case is simpler than evaluation of include-book forms in the ACL2 loop;
; for example, the value of *hcomp-book-ht* is irrelevant for include-book
; performed in raw mode.

; Part 2: Including a certified book

; Fix a book for the following discussion.  An add-trip symbol is "qualified"
; if whenever add-trip is to assign a relevant value by including the book in a
; boot-strap world, that value is equal to the relevant value of the symbol if
; instead the compiled file is loaded.  An add-trip symbol is "semi-qualified"
; if instead add-trip assigns a relevant value exactly twice, where the second
; value equals the relevant value of the symbol at the time the compiled file
; has just been loaded.  This can happen if, and we believe only if (unless
; trust tags or make-event with non-nil :check-expansion are involved), the
; symbol is a *1* function symbol that is defined first in :program mode and
; then in :logic mode, say with verify-termination.  We call an add-trip symbol
; "unqualified" if it is neither qualified nor semi-qualified.

; Include-book processes the book's compiled file using the following sequence
; of steps.  (See also the summary shortly below this description.)

; First, include-book loads the compiled file:

; (1) Each *hcomp-xxx-alist* is an alist assigned by a form (setq
;     *hcomp-xxx-alist* (quote ...)) near the top of the expansion file, after
;     the initial (in-package "ACL2") but before the portcullis commands.  This
;     alist associates values with (and only with) all add-trip symbols: t for
;     qualified, 'semi for semi-qualified, and nil for unqualified.  Note that
;     the values of these setq forms are quoted (laid down during book
;     certification); hence the values of these globals are independent of the
;     environment in which the compiled file is loaded.  We use setq rather
;     than defparameter because we have seen defparameter result in a slowdown
;     of two orders of magnitude in CCL in doing the early load of compiled
;     files.

; (2) Function hcomp-init is called (at load time), to do two things.  For one,
;     it adds to the *hcomp-xxx-restore-ht* hash tables, so that for each
;     add-trip symbol that is not already a key of the suitable such hash
;     table, that symbol is associated with its relevant value, if it has one,
;     and otherwise is associated with a special "unbound" value,
;     *hcomp-fake-value*.  Also, it populates each *hcomp-xxx-ht* by
;     associating each qualified add-trip symbol with t and each semi-qualified
;     add-trip symbol with 'semi.  Note that the domain of each
;     *hcomp-xxx-alist*, representing the set of add-trip symbols, is the same
;     as in Step (1).

; (3) Relevant values are assigned by loading the remainder of the compiled
;     file, which starts with the portcullis commands.  These are wrapped in a
;     progn to maximize sharing using #n# syntax.

; Note however that the load may abort with a throw as described earlier above
; (missing compiled file for a sub-book).  We'll catch any such throw before
; proceeding with the next step.

; (4) Evaluation of the form (hcomp-transfer-to-hash-tables) updates the
;     *hcomp-xxx-ht* hash tables for use by add-trip, as follows.  Let sym be
;     an add-trip symbol with relevant value val and "qualified" status as
;     determined by *hcomp-xxx-alist*.  If sym is qualified, then sym is
;     associated in *hcomp-xxx-ht* with val.  Otherwise, if sym is
;     semi-qualified, then sym is associated with the so-called "reclassifying
;     value" (*hcomp-fake-value* . val).  Otherwise, sym is not a key of the
;     hash table.

; After attempting to load all compiled (or expansion) files under a top-level
; such load, ACL2 executes the following step as it cleans up using
; unwind-protection; see include-book-raw-top.

; (5) Relevant values are restored (which could mean making some symbols have
;     undefined relevant values) for all add-trip symbols, regardless of
;     "qualified" status, to what they were before Step (3), using the
;     *hcomp-xxx-restore-ht* from Step (2).

; In summary, our alist and hash table globals have values as follows during
; the process of including a certified book.  (NOTE that they have different
; values during the process of book certification, as discussed in Part 3
; below.)

; *hcomp-xxx-alist*
;   -- Before evaluating hcomp-init (near the top of the expansion file):
;      Associates each add-trip symbol with t if qualified, 'semi if
;      semi-qualified and otherwise nil

; *hcomp-xxx-ht*
;   -- After evaluating hcomp-init (near the top of the expansion file):
;      Assigns each qualified add-trip symbol to t and each semi-qualified
;      add-trip symbol to 'semi (and these are the only keys)
;   -- After loading compiled definitions, hcomp-transfer-to-hash-tables is
;      called to populate *hcomp-xxx-ht* by associating a value with each
;      qualified or semi-qualified add-trip symbol that has a relevant value,
;      val (and only in those cases), as follows:
;      + a qualified symbol is bound to val
;      + a semi-qualified symbol is bound to the so-called "reclassifying
;        value" (*hcomp-fake-value* . val), where val is a :logic mode *1*
;        definition

; *hcomp-xxx-restore-ht*
;   -- After completing a top-level load of a compiled (or expansion) file:
;      Associates each add-trip symbol with its relevant value if any, else to
;      *hcomp-fake-value*

; So, how is a relevant value assigned to an add-trip symbol when including a
; certified book?  If the symbol is qualified, then its value is obtained from
; the relevant *hcomp-xxx-ht* hash table.  Otherwise add-trip proceeds without
; the help of that hash table.  However, if the symbol is assigned a
; reclassifying value (*hcomp-fake-value* . val) in the hash table, then even
; though add-trip does not use that value to assign a relevant value, the
; symbol is reassigned to val in the hash table; so if and when subsequently
; this *1* symbol is assigned a :logic-mode value by add-trip it will be val,
; i.e., the symbol will be treated as qualified.  That is appropriate because
; if add-trip assigns a new value -- and assuming that redefinition is off,
; which it is unless there is a trust tag -- then the subsequent :logic mode
; definition will be ready for this saved value.

; If raw-mode is entered, then loading the compiled file can assign relevant
; values to symbols other than add-trip symbols.  (By the way, we are not
; talking here about memoize and unmemoize, because these are no-ops in raw
; Lisp.)  Upon completion of the above sequence of five steps, new relevant
; values are only assigned for symbols that are not add-trip symbols, since as
; specified in Step (5) above, relevant values for add-trip symbols are
; restored from the *hcomp-xxx-restore-ht* variables after loading the compiled
; files.  Users need to manage raw-mode carefully with respect to loading
; compiled files when including a book.

; If future enhancements are to allow add-trip to assign more than one relevant
; value for other than *1* symbols, we expect to be able to deal with such
; cases.  If there can in fact be more than two such assignments for the same
; symbol, we can replace a reclassifying value (cons *hcomp-fake-value* val) by
; something like (list* *hcomp-fake-value* count val), where count is initially
; the number of expected re-assignments, it is decremented with each
; assignment, and only when it would be about to decrement to 0 would we
; actually use the hash table's value.  Note that some of the initial
; assignments made during certify-book might not be made during include-book,
; because of redundancy, so the last value is the only one that can reliably be
; assigned (if the count ever gets down to 1).

; Part 3: Writing an expansion file for compilation

; We next consider the writing of the expansion file by certify-book.  This
; process has three main steps.  The first main step is storing relevant values
; in the *hcomp-xxx-ht* hash tables both based on the certification world and
; during the process-embedded-events call during the include-book pass of
; certify-book.  The second main step then determines the value of each
; *hcomp-xxx-alist* for the setq forms to be written to the expansion file.
; The third main step actually writes forms to the expansion file.  We now
; consider these in turn.  Note that we do not access the *hcomp-xxx-alist*
; variables; their part in writing an expansion file is only to occur
; syntactically in the setq forms.

; The first main step populates each *hcomp-xxx-ht*.  We begin by let-binding
; each *hcomp-xxx-ht* to its own eq hash table.  Then we populate these hash
; tables -- first, with hcomp-build-from-state, using the portcullis commands
; of the certification world as well as any events not undone when rolling back
; the world before the include-book phase of certify-book; and then during the
; process-embedded-events phase of include-book-fn -- updating the appropriate
; hash table for each symbol that is assigned a relevant value (because of a
; 'cltl-command property) by add-trip.  (In the case of the portcullis
; commands, we do not actually run add-trip, but rather we mirror its necessary
; effects in function hcomp-build-from-state.)  When we encounter a symbol that
; is not already a key of that hash table, which is the normal case, then we
; associate it with its relevant value.  Otherwise, if the symbol is a *1*
; symbol that already has a value that is not a reclassifying value, and it is
; now being converted from :program to :logic mode, then the symbol is
; associated with the reclassifying value (*hcomp-fake-value* . val), where val
; is its current relevant value.  Otherwise the symbol is other than a *1*
; symbol and already has a relevant value -- presumably something unusual has
; occurred by virtue of a trust tag -- and the symbol is associated with
; *hcomp-fake-value*.  Note that memoize and unmemoize events do not have any
; effect on the populating of *hcomp-xxx-ht*.

; The second main step, computing each *hcomp-xxx-alist*, is carried out by
; hcomp-alists-from-hts and takes place after the return from
; process-embedded-events.  It considers each symbol, sym, and associated value
; in the appropriate *hcomp-xxx-ht*.  If the value is a reclassifying value
; (*hcomp-fake-value* . val) and val equals the current relevant value of sym,
; then sym is semi-qualified and is therefore to be associated with 'semi in
; *hcomp-xxx-alist*.  For any other value, val, besides *hcomp-fake-value*,
; such that val equals the current relevant value of sym, then sym is qualified
; and is therefore to be associated with t in *hcomp-xxx-alist*.  Otherwise VAL
; is unqualified and hence is to be associated with nil in *hcomp-xxx-alist*
; (see function hcomp-alists-from-hts for the check against the current
; relevant value).  This last case is likely to be rather unusual, but can
; happen in the #+hons case if memoization occurs after a definition without
; being followed by unmemoization (more on this in the next paragraph).  It can
; also happen if a function is redefined in raw-mode, though of course a trust
; tag is needed in that case; but we do not guarantee perfect handling of
; raw-mode, as there might be no raw-mode redefinition during the include-book
; phase of book certification and yet there might be raw-mode redefinition
; later during inclusion of the certified book -- anyhow, uses of raw-mode are
; the user's responsibility.  If not for raw-mode, we might simply avoid any
; check and consider every add-trip symbol to be qualified or semi-qualified;
; memoization isn't a problem, since memoize is a no-op in raw Lisp and hash
; tables are populated during early include-books performed in raw Lisp.

; Note that we take a conservative approach, where memoization can make a
; symbol unqualified.  The consequence seems small, since as of this writing,
; memoization is only done in the #+hons version, which is only for ACL2 built
; on CCL, and CCL compiles on-the-fly; so the marking of an add-trip symbol as
; unqualified will not result in interpreted code.  A future optimization might
; be to to avoid disqualification due to memoization in suitable cases, perhaps
; by tracking raw-mode or trust tags, or perhaps by somehow taking advantage of
; the 'old-fn field of the *memoize-info-ht* entry.

; It is instructive to consider the case that a :program mode definition is
; redundant with an earlier :logic mode definition made in the book (or its
; portcullis commands), either directly or by way of a redundant encapsulate,
; as per the following example from Jared Davis:

; (encapsulate () (defun f (x) (declare (xargs :mode :program)) x))
; (verify-termination f)
; (encapsulate () (defun f (x) (declare (xargs :mode :program)) x))

; Recall that the *1* functions written to the expansion file are based on the
; definitional event installed at the end of the include-book phase of
; certify-book.  In this case, that will be the :logic mode definition; the
; redundant event is properly ignored.

; The third main step, writing forms to the expansion file, is rather
; straightforward based on the discussion above.  We bind the current package
; to "ACL2", and then write a sequence of forms as follows.

; - (in-package "ACL2")

; - Forms that introduce packages that may be needed for reading symbols in the
;   initial setq forms.  These are introduced using maybe-introduce-empty-pkg-1
;   and maybe-introduce-empty-pkg-2.  The maybe-introduce-empty-pkg-1 forms
;   introduce all the packages together, just under the initial in-package
;   form, thus avoiding a warning from GCL that can occur unless all defpackage
;   forms immediately follow the initial in-package form.  The
;   maybe-introduce-empty-pkg-2 forms use special variable *defpkg-virgins* to
;   let ACL2 know to accept subsequent corresponding defpkg forms.

; - Setq forms for the *hcomp-xxx-alist* variables as described above
;   (hcomp-init)

; - Declaim forms (if any)

; - The portcullis commands

; - Book contents, modified according to the expansion-alist in the certificate
;   that comes from make-event

; - *1* function definitions from the book (including the portcullis)

; Note that some of these are wrapped together in a progn to maximize sharing
; using #n# syntax.

; Note added February, 2019: We have extended the expansion file to support the
; macroexpansion of loop$ in raw Lisp.  The main idea is to mirror the world
; global, 'loop$-alist, in a Lisp special variable to be consulted during the
; early load of compiled files: *hcomp-loop$-alist*.  See loop$.  The
; discussion below outlines how the expansion file supports the macroexpansion
; of loop$ in raw Lisp.

; The loop$-alist -- whether the value of world global 'loop$-alist or the
; value of special variable *hcomp-loop$-alist* -- needs to distinguish entries
; added for the current book during its certification, because these are the
; only ones that are placed directly in that book's expansion file.  Thus the
; loop$-alist-entry record has a field, :flg, that is usually nil but is t when
; adding an entry during certification and not under include-book (i.e., under
; a sub-book).  The variable *hcomp-loop$-alist* is set to nil in
; include-book-raw-top and then populated in expansion files.  Then each
; expansion file overwrites that variable to the list of loop$-alist-entry
; records appropriate for loop$ forms introduced in that book, not in
; sub-books.  But upon exit from the expansion file, the value of that variable
; from before that overwrite is extended by the final value from the expansion
; file, using the macro wrapper, handle-hcomp-loop$-alist.

; An optimizbation is that *set-hcomp-loop$-alist* is only true when under some
; load of an expansion file (where (eq *readtable* *reckless-acl2-readtable*)).
; In particular, in the normal case that compiled files are loaded,
; *hcomp-loop$-alist* will remain nil, which is fine since the loop$ macros
; will have already been expanded.

; End of Essay on Hash Table Support for Compilation

(defun hcomp-init ()

; For context, see the Essay on Hash Table Support for Compilation.

; This function is called during loading of a compiled or expansion file by
; include-book, immediately after assigning alists to the *hcomp-xxx-alist*
; globals.  The keys of each alist are the add-trip symbols for its type,
; associating value t if qualified, 'semi if semi-qualified, else nil.  This
; function does two things.  First, for each of the three alists, it puts an
; entry into the corresponding *hcomp-xxx-alist* hash table, for each key bound
; to non-nil in the alist.  Second, it updates *hcomp-fn-restore-ht* to support
; the eventual restoration of relevant values for add-trip symbols.  For
; details, see the Essay on Hash Table Support for Compilation.

  (when (or (raw-mode-p *the-live-state*)
            (null *hcomp-fn-ht*))

; In raw mode, or when loading before compiling for include-book with
; :load-compiled-file :comp, we don't bother with hcomp hash tables and such.
; Rather, we expect that loading of compiled files has the effect one normally
; expects for raw Lisp.

    (assert (and (null *hcomp-const-ht*)
                 (null *hcomp-macro-ht*)))
    (return-from hcomp-init nil))
  (dolist (pair *hcomp-fn-alist*)
    (when (cdr pair)
      (setf (gethash (car pair) *hcomp-fn-ht*)
            (cdr pair))))
  (dolist (pair *hcomp-const-alist*)
    (when (cdr pair)
      (setf (gethash (car pair) *hcomp-const-ht*)
            (cdr pair)))
    (when *hcomp-const-restore-ht*
      (multiple-value-bind (old present-p)
          (gethash (car pair) *hcomp-const-restore-ht*)
        (declare (ignore old))
        (when (not present-p)
          (setf (gethash (car pair) *hcomp-const-restore-ht*)
                (cond ((boundp (car pair))
                       (symbol-value (car pair)))
                      (t *hcomp-fake-value*)))))))
  (dolist (pair *hcomp-macro-alist*)
    (when (cdr pair)
      (setf (gethash (car pair) *hcomp-macro-ht*)
            (cdr pair))))
  (when *hcomp-fn-macro-restore-ht*
    (dolist (pair (append *hcomp-macro-alist* *hcomp-fn-alist*))
      (multiple-value-bind (old present-p)
          (gethash (car pair) *hcomp-fn-macro-restore-ht*)
        (declare (ignore old))
        (when (not present-p)
          (setf (gethash (car pair) *hcomp-fn-macro-restore-ht*)
                (let ((mac (macro-function (car pair))))
                  (cond (mac (cons 'macro mac))
                        ((fboundp (car pair))
                         (cons 'function
                               (symbol-function (car pair))))
                        (t *hcomp-fake-value*)))))))))

(defabbrev reclassifying-value-p (x)

; See the Essay on Hash Table Support for Compilation.

  (and (consp x)
       (eq (car x) *hcomp-fake-value*)))

(defmacro make-reclassifying-value (x)

; See the Essay on Hash Table Support for Compilation.

  `(cons *hcomp-fake-value* ,x))

(defmacro unmake-reclassifying-value (x)

; See the Essay on Hash Table Support for Compilation.

  `(cdr ,x))

(defun hcomp-transfer-to-hash-tables ()

; See the Essay on Hash Table Support for Compilation.

; This function populates *hcomp-xxx-ht* hash tables with relevant values of
; qualified and semi-qualified add-trip symbols, after including a compiled or
; expansion file.

  (dolist (pair *hcomp-fn-alist*)
    (let ((qualified (gethash (car pair) *hcomp-fn-ht*)))
      (cond ((and qualified
                  (fboundp (car pair)) ; likely only falsified here by raw mode
                  )
             (setf (gethash (car pair) *hcomp-fn-ht*)
                   (cond
                    ((eq qualified t)
                     (symbol-function (car pair)))
                    (t
                     (assert$
                      (eq qualified 'semi)
                      (make-reclassifying-value
                       (symbol-function (car pair))))))))
            (t (remhash (car pair) *hcomp-fn-ht*)))))
  (dolist (pair *hcomp-const-alist*)
    (let ((qualified (gethash (car pair) *hcomp-const-ht*)))
      (cond ((and qualified
                  (boundp (car pair)) ; likely only falsified here by raw mode
                  )
             (setf (gethash (car pair) *hcomp-const-ht*)
                   (assert$
                    (eq qualified t)
                    (symbol-value (car pair)))))
            (t (remhash (car pair) *hcomp-const-ht*)))))
  (dolist (pair *hcomp-macro-alist*)
    (let ((qualified (gethash (car pair) *hcomp-macro-ht*)))
      (cond ((and qualified
                  (macro-function (car pair)) ; raw mode check, as above
                  )
             (setf (gethash (car pair) *hcomp-macro-ht*)
                   (assert$
                    (eq qualified t)
                    (macro-function (car pair)))))
            (t (remhash (car pair) *hcomp-macro-ht*))))))

(defvar *saved-hcomp-restore-hts* nil)

(defun hcomp-restore-defs ()

; See the Essay on Hash Table Support for Compilation.

; This function undoes the effect of loading compiled and expansion files, in
; the sense that it restores relevant values: every add-trip symbol is given
; the relevant value it had before loading these, if any, else is unbound.

; The variable *saved-hcomp-restore-hts* should have just been been assigned to
; the current value of (list* *hcomp-fn-macro-restore-ht*
; *hcomp-const-restore-ht*).

  (when (null *saved-hcomp-restore-hts*)
    (er hard 'hcomp-restore-defs
        "Apparently an interrupt has occurred at exactly the right time to ~
         thwart ACL2's attempt to clean up by removing certain definitions in ~
         raw Lisp.  You are strongly advised to restart ACL2.  You could ~
         instead try to continue, but you might well encounter errors ~
         regarding having definitions in raw Common Lisp."))
  (let ((fn-macro-restore-ht (car *saved-hcomp-restore-hts*))
        (const-restore-ht (cdr *saved-hcomp-restore-hts*)))
    (when fn-macro-restore-ht
      (maphash (lambda (k val)
                 (cond ((eq val *hcomp-fake-value*)

; We use fmakunbound! instead of fmakunbound in case trust tags have allowed
; some raw Lisp code to overwrite a function definition with a macro
; definition.

                        (fmakunbound! k))
                       ((eq (car val) 'macro)
                        (setf (macro-function k) (cdr val)))
                       (t ; (eq (car val) 'function)
                        (fmakunbound! k) ; remove potential macro-function
                        (setf (symbol-function k) (cdr val)))))
               fn-macro-restore-ht))
    (when const-restore-ht
      (maphash (lambda (k val)
                 (cond ((eq val *hcomp-fake-value*)
                        (remprop k 'redundant-raw-lisp-discriminator)
                        (makunbound k))
                       (t

; The 'redundant-raw-lisp-discriminator property may be wrong here; but really,
; we don't expect this case to occur, since redefinition with defconst is not
; supported (unless perhaps extraordinary measures are taken using trust
; tags).

                        (setf (symbol-value k) val))))
               const-restore-ht))
    nil))

(defun missing-compiled-book (ctx file reason-msg load-compiled-file state)

; This function is called when a compiled file is missing from an attempt to
; include a book.  It either causes an error (because of an include-book called
; with :load-compiled-file t) or returns INCOMPLETE, which may be convenient
; when this result is to be placed into the status field of an
; hcomp-book-ht-entry record or is to be the value returned by
; load-compiled-book or include-book-raw.

; For convenience, we also use this function to report failure to complete the
; load of a compiled file when such a failure has previously been reported, but
; no such report has yet been made involving the files above that missing
; compiled file.  In this case we pass reason-msg = nil.  However, we do not
; expect this case to arise; see the comment about "flaw in our thinking" in
; include-book-raw.

; Warning: Do not change the message printed in the case reason-msg = nil
; without reading the comment in *uninhibited-warning-summaries* about
; "Compiled file".

  (let ((see-doc "  See :DOC include-book."))
    (cond ((null load-compiled-file)
           (er hard ctx
               "Implementation error: the LOAD-COMPILED-FILE argument is ~x0 ~
                in call ~x1."
               nil
               `(missing-compiled-book ',ctx ',file ',reason-msg
                                       ',load-compiled-file state)))
          ((or (eq load-compiled-file t)
               (rassoc-eq t *load-compiled-stack*))
           (let ((stack-msg
                  (cond ((eq load-compiled-file t)
                         (tilde-@-book-stack-msg t *load-compiled-stack*))
                        (t
                         (tilde-@-book-stack-msg
                          (car (rassoc-eq t *load-compiled-stack*))
                          *load-compiled-stack*)))))
             (cond (reason-msg
                    (er hard ctx
                        "Unable to load compiled file~|  ~s0~|because ~@1.~@2~@3"
                        file reason-msg see-doc stack-msg))
                   (t
                    (er hard ctx
                        "Unable to complete load of compiled file for book~|~ ~ ~
                         ~s0,~|as already noted by a warning.~@1~@2"
                        file see-doc stack-msg)))))
          (reason-msg
           (warning$ ctx "Compiled file"
                     "Unable to load compiled file for book~|  ~s0~|because ~
                      ~@1.~@2~@3"
                     file
                     reason-msg
                     see-doc
                     (tilde-@-book-stack-msg nil *load-compiled-stack*)))
          (t
           (warning$ ctx "Compiled file"
                     "Unable to complete load of compiled file for book~|  ~
                    ~s0,~|as already noted by a previous warning.~@1"
                     file
                     (tilde-@-book-stack-msg nil *load-compiled-stack*)))))
  'incomplete)

(defmacro our-handler-bind (bindings &rest forms)
  #-cltl2 (declare (ignore bindings))
  #-cltl2 `(progn ,@forms)
  #+cltl2 `(handler-bind ,bindings ,@forms))

(defun load-compiled-book (file directory-name load-compiled-file ctx state)

; We are processing include-book-raw underneath include-book-fn (hence
; presumably not in raw mode).  File is an ACL2 full-book-name and
; load-compiled-file is non-nil.  We attempt to load the corresponding compiled
; or perhaps expansion file if not out of date with respect to the book's
; certificate file.  Normally, we return COMPLETE if such a suitable compiled
; file or expansion file exists and is loaded to completion, but if file is the
; book being processed by a surrounding include-book-fn and compilation is
; indicated because load-compiled-file is :comp and the expansion file is
; loaded (not the compiled file), then we return TO-BE-COMPILED in that case.
; Otherwise we return INCOMPLETE, that is, either no load is attempted for the
; compiled or expansion file (because they don't exist or are out of date), or
; else such a load but is aborted part way through, which can happen because of
; an incomplete load of a subsidiary include-book's compiled or expansion file.

; As suggested above, we may allow the corresponding expansion file to take the
; place of a missing or out-of-date compiled file.  However, we do not allow
; this if load-compiled-file is t or a parent include-book has
; :load-compiled-file t.

  (assert load-compiled-file)
  (mv-let
   (acl2-cfile state)
   (certificate-file file state)
   (let* ((cfile (and acl2-cfile (pathname-unix-to-os acl2-cfile state)))
          (os-file (pathname-unix-to-os file state))
          (cfile-date (and cfile (file-write-date cfile)))
          (ofile (convert-book-name-to-compiled-name os-file state))
          (ofile-exists (probe-file ofile))
          (ofile-date (and ofile-exists (file-write-date ofile)))
          (ofile-p (and ofile-date cfile-date (>= ofile-date cfile-date)))
          (efile (and (not (eq load-compiled-file t))
                      (expansion-filename os-file)))
          (efile-exists (and efile (probe-file efile)))
          (file-is-older-str
           "the file-write-date of ~x0 is less than that of ~x1"))
     (cond
      ((not cfile)
       (missing-compiled-book ctx
                              file
                              (if (probe-file (convert-book-name-to-cert-name
                                               file t))
                                  "that book is not certified (but note that ~
                                   its .cert file exists and is not readable)"
                                "that book is not certified")
                              load-compiled-file
                              state))
      ((and (not ofile-exists)
            (not efile-exists))
       (missing-compiled-book ctx
                              file
                              "the compiled file does not exist"
                              load-compiled-file
                              state))
      ((not cfile-date)
       (missing-compiled-book
        ctx
        file
        (msg "~x0 is ~x1 (which is odd since file ~x2 exists)"
             `(file-write-date$ ,acl2-cfile state)
             nil
             acl2-cfile)
        load-compiled-file
        state))
      ((not (or ofile-p
                (let ((efile-date (and efile-exists (file-write-date efile))))
                  (and efile-date (>= efile-date cfile-date)))))
       (cond
        (ofile-exists
         (missing-compiled-book
          ctx
          file
          (msg file-is-older-str ofile cfile)
          load-compiled-file
          state))
        (t ; hence efile-exists
         (missing-compiled-book
          ctx
          file
          (msg "the compiled file does not exist and ~@0"
               (msg file-is-older-str
                    (expansion-filename file)
                    acl2-cfile))
          load-compiled-file
          state))))
      ((and (not ofile-p) ; hence efile is suitable to load, except:
            (rassoc-eq t *load-compiled-stack*))
       (missing-compiled-book
        ctx
        file
        (if ofile-exists
            "that compiled file does not exist"
          "that compiled file is out-of-date")
        load-compiled-file
        state))
      (t                      ; either ofile or efile is suitable for loading
       (let ((to-be-compiled-p ; true at top level of include-book-fn with :comp
              (and (not ofile-p)
                   (null *load-compiled-stack*)
                   (eq load-compiled-file :comp)))
             (status 'incomplete))
         (when (and (not ofile-p)
                    (not to-be-compiled-p))

; Hence efile is suitable and we are not in the special case of compiling it on
; behalf of include-book-fn.  Note that for the case of compiling on behalf of
; include-book-fn, either that compilation will succeed or there will be an
; error -- either way, there is no need to warn here.

           (let ((acl2-ofile (convert-book-name-to-compiled-name file state)))
             (warning$ ctx "Compiled file"
                       "Loading expansion file ~x0 in place of compiled file ~
                        ~x1, because ~@2."
                       (expansion-filename file)
                       acl2-ofile
                       (cond (ofile-exists
                              (msg file-is-older-str acl2-ofile acl2-cfile))
                             (t
                              (msg "the compiled file is missing"))))))
         (catch 'missing-compiled-book
; bogus compiler warning in LispWorks 6.0.1, gone in LispWorks 6.1
           (state-global-let*
            ((raw-include-book-dir-alist nil)
             (connected-book-directory directory-name))
            (let ((*load-compiled-stack* (acons file
                                                load-compiled-file
                                                *load-compiled-stack*)))
              (multiple-value-bind
               (er val)
               (catch 'my-book-error
                 (our-handler-bind
                  ((error (function
                           (lambda (c)

; Function hcomp-transfer-to-hash-tables might not have been run, which would
; leave *hcomp-fn-ht* in an odd state.  In the worst case that function would
; have emptied these hash tables; here, we do the easy thing and set them all
; to nil.

                             (setq *hcomp-fn-ht* nil
                                   *hcomp-const-ht* nil
                                   *hcomp-macro-ht* nil)
                             (throw 'my-book-error
                                    (values t (format nil "~a" c)))))))
                  (values nil
                          (cond (ofile-p (load-compiled ofile t))
                                (t (with-reckless-read (load efile)))))))
               (value (setq status
                            (cond (er (setq status val))
                                  (to-be-compiled-p 'to-be-compiled)
                                  (t 'complete))))))))
         (cond
          ((stringp status) ; status is raw Lisp error message
           (warning$ ctx "Compiled file"
                     "The following raw Lisp error occurred when loading ~
                      file~|~s0:~|~s1"
                     (cond (ofile-p ofile)
                           (t efile))
                     status)
           (missing-compiled-book
            ctx
            file
            (msg "an error occurred in raw Lisp (see above)")
            load-compiled-file
            state))
          (t (hcomp-transfer-to-hash-tables)
             (assert$ (member-eq status '(to-be-compiled complete incomplete))
                      status)))))))))

(defvar *set-hcomp-loop$-alist* nil)

(defun extend-hcomp-loop$-alist (new old full-book-name)

; Extend old by new, checking that we never change an existing value.

  (let ((result old))
    (loop for pair in new
          when (let ((old-pair (assoc-equal (car pair) old)))
                 (cond ((null old-pair) t)
                       ((equal (cdr pair) (cdr old-pair)) nil)
                       (t (er hard 'extend-hcomp-loop$-alist
                              "Implementation error: unexpected ~
                               incompatibility in loop$-alists when ~
                               processing the book ~x0.~%new:~%~x1~%old~%~x2"
                              full-book-name new old))))
          do (push pair result)
          finally (return result))))

(defmacro handle-hcomp-loop$-alist (form full-book-name)
  (let ((saved-hcomp-loop$-alist (gensym)))
    `(let ((,saved-hcomp-loop$-alist *hcomp-loop$-alist*))
       (prog1 ,form
         (setq *hcomp-loop$-alist*
               (extend-hcomp-loop$-alist *hcomp-loop$-alist*
                                         ,saved-hcomp-loop$-alist
                                         ,full-book-name))))))

(defun include-book-raw (book-name directory-name load-compiled-file dir ctx
                                   state
                                   &aux ; protect global value
                                   (*set-hcomp-loop$-alist*
                                    *set-hcomp-loop$-alist*))

; This function is generally called on behalf of include-book-fn.  No load
; takes place if load-compiled-file is effectively nil (either nil or else
; compiler-enabled is nil) unless we are in raw mode, in which case we attempt
; to load the source file, book-name.  So suppose load-compiled-file is not
; nil.  When the call is not under certify-book-fn, the effect is to populate
; *hcomp-book-ht* with *hcomp-xxx-ht* hash tables for the given book and
; (recursively) all its sub-books; see the Essay on Hash Table Support for
; Compilation.  Otherwise its effect is as follows: load the compiled file if
; it exists and is up-to-date with respect to the certificate, else load the
; expansion file, else (but only in raw mode) load the source book.  (The
; *hcomp-xxx* variables are irrelevant, by the way, if we are not calling
; add-trip or otherwise involving ACL2 event processing.)

; If directory-name is nil, then book-name is a user-book-name.  Otherwise
; book-name is a full-book-name whose directory is directory-name.
; Load-compiled-file and dir are the arguments of these names from
; include-book.

; Now suppose that we are not in raw mode, i.e., we are evaluating this call
; underneath some call of include-book-fn.  We return nil if no load is
; attempted, for example because load-compiled-file is effectively nil.  If the
; compiled file or expansion file is loaded in its entirety, then we return
; 'complete.  Otherwise we throw to the tag 'missing-compiled-book with the
; status 'incomplete.

  (when (not (member-eq load-compiled-file *load-compiled-file-values*))
    (er hard ctx
        "The only legal values for the :LOAD-COMPILED-FILE keyword argument ~
         of ~x0 are ~&1.  The value ~x2 is thus illegal."
        'include-book
        *load-compiled-file-values*
        load-compiled-file))
  (when *compiling-certified-file*

; See the comment below related to *compiling-certified-file*.

    (return-from include-book-raw nil))
  (let* ((raw-mode-p (raw-mode-p state))
         (load-compiled-file
          (cond ((null (f-get-global 'compiler-enabled state))
                 nil)
                ((eq load-compiled-file :default)
                 :warn)
                (t (or load-compiled-file

; If load-compiled-file is nil but we are in the process of loading the
; compiled file for a superior book, then there is an include-book for such a
; book, B, with a non-nil value of :load-compiled-file.  Even if that value is
; :warn or :comp, hence not t, we still need to try to load a compiled file for
; the present book; of course, if a compiled file is missing for the present
; book or any sub-book, then whether that causes an error or only a warning
; depends on whether some such book B has :load-compiled-file t.

                       (and *load-compiled-stack*
                            :warn))))))
    (when (and (not raw-mode-p)
               (null load-compiled-file))
      (return-from include-book-raw nil))
    (mv-let
     (full-book-name directory-name ignore-familiar-name)
     (cond (directory-name (mv book-name directory-name nil))
           (t (parse-book-name
               (cond (dir (or (include-book-dir dir state)
                              (er hard ctx
                                  "Unable to find the :dir argument to ~
                                   include-book, ~x0, which should have been ~
                                   defined by ~v1.  Perhaps the book ~x2 ~
                                   needs to be recertified."
                                  dir
                                  '(add-include-book-dir add-include-book-dir!)
                                  book-name)))
                     (t (f-get-global 'connected-book-directory state)))
               book-name ".lisp" ctx state)))
     (declare (ignore ignore-familiar-name))
     (cond
      ((let ((true-full-book-name (our-truename full-book-name :safe)))
         (and true-full-book-name
              (assoc-equal (pathname-os-to-unix true-full-book-name
                                                (os (w state))
                                                state)
                           (global-val 'include-book-alist (w state)))))

; In ACL2 Version_4.1 running on Allegro CL, we got an error when attempting to
; certify the following book.

; (in-package "ACL2")
; (include-book "coi/lists/memberp" :dir :system)

; The problem was that truename is (one might say) broken in Allegro CL.
; Fortunately, Allegro CL provides an alternative that seems to work --
; excl::pathname-resolve-symbolic-links -- and we now use that function (see
; our-truename).  The problem goes away if that function is applied to
; full-book-name under the call of assoc-equal below.  But the error occurred
; in the context of loading a file just compiled from a book, and in that
; context there is no reason to execute any raw-Lisp include-book.  Thus, we
; short-circuit in that case -- see the use of *compiling-certified-file* above
; -- and now we never even get to the above assoc-equal test in that case.

; A final comment in the case that we really do get to this point:

; Since all relevant values have been defined, there is no need to transfer to
; hash tables (as per the Essay on Hash Table Support for Compilation).  This
; is the case even if we loaded in raw-mode.  It would be harmless enough to
; load in the raw-mode case, and could be desirable if values are
; context-dependent and it is expected that we re-load, but for now we avoid
; the inefficiency of repeated loads.

       nil)
      ((or raw-mode-p

; If *hcomp-book-ht* is nil and we are not in raw mode, then we are under an
; include-book-fn being performed on behalf of certify-book.  In that case we
; just do a load as we would in raw Lisp, without regard to the hash tables
; described in the Essay on Hash Table Support for Compilation.

           (null *hcomp-book-ht*))
       (state-free-global-let*-safe
        ((connected-book-directory directory-name))
        (let* ((os-file (pathname-unix-to-os full-book-name state))
               (ofile (convert-book-name-to-compiled-name os-file state))
               (os-file-exists (probe-file os-file))
               (ofile-exists (probe-file ofile))
               (book-date (and os-file-exists (file-write-date os-file)))
               (ofile-date (and ofile-exists (file-write-date ofile))))
          (cond ((not os-file-exists)
                 (er hard ctx
                     "The file named ~x0 does not exist."
                     full-book-name))
                ((null load-compiled-file)
                 (assert$ raw-mode-p ; otherwise we already returned above

; If make-event is used in the book, then the following load may cause an
; error.  The user of raw mode who supplied a :load-compiled-file argument is
; responsible for the ensuing behavior.

                          (load os-file)))
                ((and book-date
                      ofile-date
                      (<= book-date ofile-date))
                 (handle-hcomp-loop$-alist
                  (load-compiled ofile t)
                  full-book-name))
                (t (let ((reason (cond (ofile-exists
                                        "the compiled file is not at least as ~
                                         recent as the book")
                                       (t "the compiled file does not exist"))))
                     (cond ((eq load-compiled-file t)
                            (er hard ctx
                                "The compiled file for ~x0 was not loaded ~
                                 because ~@1."
                                reason))
                           (t (let* ((efile (expansion-filename os-file))
                                     (efile-date (and (probe-file efile)
                                                      (file-write-date efile)))
                                     (efile-p (and book-date
                                                   efile-date
                                                   (<= book-date efile-date)))
                                     (lfile (cond (efile-p efile)
                                                  (raw-mode-p os-file)
                                                  (t
                                                   (er hard ctx
                                                       "Implementation error: ~
                                                        We seem to have ~
                                                        called ~
                                                        include-book-raw on ~
                                                        book ~x0 with non-nil ~
                                                        load-compiled-file ~
                                                        argument under the ~
                                                        include-book-fn call ~
                                                        in certify-book-fn."
                                                       book-name)))))
                                (warning$ ctx "Compiled file"
                                          "Attempting to load ~@0 instead of ~
                                           the corresponding compiled file, ~
                                           because ~@1."
                                          (msg (cond
                                                (efile-p "expansion file ~x0")
                                                (t "source file ~x0"))
                                               lfile)
                                          reason)
                                (cond (efile-p
                                       (with-reckless-read
                                        (handle-hcomp-loop$-alist
                                         (load efile)
                                         full-book-name)))
                                      (raw-mode-p (load os-file))))))))))))
      ((let* ((entry (assert$ *hcomp-book-ht* ; not raw mode, e.g.
                              (gethash full-book-name *hcomp-book-ht*)))
              (status (and entry
                           (access hcomp-book-ht-entry entry :status))))

; The status might be nil because of soft links, in analogy to the case for
; soft links described in a comment above.  But as explained in that comment,
; this is harmless; it would simply cause us to fall through and deal with the
; book as though it's newly encountered.

; Below, when status is nil then it is because entry is nil, in which case it
; is correct to fall through to the next top-level COND branch.  See (defrec
; hcomp-book-ht-entry ...) for a comment on the legal (hence non-nil) status
; values.

         (cond (raw-mode-p
                status) ; if nil then there is no entry, so fall through
               ((and
                 (eq status 'incomplete) ; so not from raw-mode include-book
                 *load-compiled-stack*)

; Can the status really be INCOMPLETE?  At first glance it would seem this this
; is impossible.  For, imagine that we are loading a book's compiled file (or
; expansion file) in raw Lisp prior to processing its events.  At the first
; INCOMPLETE status, the tree of include-book forms rooted at that top
; include-book is no longer consulted -- no further loads occur anywhere to the
; right of the branch above the node on which the INCOMPLETE status is
; returned.  Ah, but perhaps the topmost include-book has :load-compiled-file
; nil.  The argument above shows that any book with existing INCOMPLETE status
; must have been processed by some earlier include-book having non-nil
; :load-compiled-file.  But then the offending book has already been included,
; and hence no raw-Lisp load will take place, since the offending book is on the
; 'include-book-alist of the current world.

; But we keep this case, just in case we later find a flaw in our thinking!
; (If this comment is removed, consider the reference to "flaw in our thinking"
; in function missing-compiled-book.)

                (error "Implementation error; see include-book-raw.")

; Code we keep in case our thinking above is flawed:

                (throw 'missing-compiled-book
                       (missing-compiled-book ctx full-book-name nil
                                              load-compiled-file state)))
               (t status))))
      (t ; not raw-mode, and load-compiled-file is non-nil
       (with-hcomp-bindings
        t
        (let ((status
               (let ((*user-stobj-alist*

; Our intention is that the call of load-compiled-book below has no effect on
; the state other than to define some packages and populate *hcomp-xxx-ht* hash
; tables.  We therefore protect the one global managed by add-trip that is not
; managed by those hash tables: *user-stobj-alist*.

                      *user-stobj-alist*))
                 (handle-hcomp-loop$-alist
                  (load-compiled-book full-book-name directory-name
                                      load-compiled-file ctx state)
                  full-book-name))))
          (setf (gethash full-book-name *hcomp-book-ht*)
                (make hcomp-book-ht-entry
                      :status   status
                      :fn-ht    *hcomp-fn-ht*
                      :const-ht *hcomp-const-ht*
                      :macro-ht *hcomp-macro-ht*))
          (cond ((member-eq status '(to-be-compiled complete))
                 status)
                (status
                 (assert$ (eq status 'incomplete)
                          (cond (*load-compiled-stack*
                                 (throw 'missing-compiled-book 'incomplete))
                                (t 'incomplete))))))))))))

(defun include-book-raw-top (full-book-name directory-name load-compiled-file
                                            dir ctx state)
  (handler-bind

; Without this handler-bind, CCL produces redefinition warnings when we attempt
; to include a book.  To see such warnings: certify the following two books,
; remove this handler-bind, and include "book1" and then (to see redefinition
; warnings) "book2".

; book1 has (defmacro foo (x) x)
; book2 has (defun foo (x) x)

   ((warning (lambda (c)
               (declare (ignore c))
               (invoke-restart 'muffle-warning))))
   (let ((*hcomp-fn-macro-restore-ht* (make-hash-table :test 'eq))
         (*hcomp-const-restore-ht* (make-hash-table :test 'eq)))

; We need to be careful about handling interrupts.  On the one hand, we want to
; take advantage of the "idempotency" provided by acl2-unwind-protect that is
; described in the Essay on Unwind-Protect.  On the other hand, cleanup forms
; of acl2-unwind-protect will be evaluated outside the scope of the bindings
; just above.  Our solution is for an unwind-protect cleanup form to do nothing
; more than save the above three hash tables -- which we expect can complete
; without interruption, though we check for that in hcomp-restore-defs -- and
; then for acl2-unwind-protect to do the actual cleanup using those saved
; values.

     (setq *saved-hcomp-restore-hts* nil
           *hcomp-loop$-alist* nil)
     (acl2-unwind-protect
      "include-book-raw"
      (unwind-protect
          (state-global-let*
           ((ld-skip-proofsp

; We have seen information about redundant add-include-book-dir! forms
; generated by this code.  We avoid such output by binding ld-skip-proofs here
; to 'include-book.  That seems harmless enough here, where we know we are
; including a certified book; and it is done anyhow by the
; process-embedded-events call under include-book-fn1.

             'include-book)
            (raw-include-book-dir!-alist
             (assert$ (not (raw-include-book-dir-p state))
                      (table-alist 'include-book-dir!-table (w state)))))
           (progn (include-book-raw
                   full-book-name directory-name
                   load-compiled-file dir ctx state)
                  (value nil)))
        (setq *saved-hcomp-restore-hts*
              (list* *hcomp-fn-macro-restore-ht*
                     *hcomp-const-restore-ht*)
              *hcomp-loop$-alist*
              nil))
      (progn (hcomp-restore-defs)
             (setq *saved-hcomp-restore-hts* nil)
             (setq *hcomp-loop$-alist* nil)
             state)
      (progn (hcomp-restore-defs)
             (setq *saved-hcomp-restore-hts* nil)
             (setq *hcomp-loop$-alist* nil)
             state)))))

(defmacro hcomp-ht-from-type (type ctx)
  `(case ,type
     (defun *hcomp-fn-ht*)
     (defparameter *hcomp-const-ht*)
     ((defmacro defabbrev) *hcomp-macro-ht*)
     (otherwise (er hard ,ctx
                    "Implementation error: Unknown case, ~x0."
                    ,type))))

(defmacro hcomp-build-p ()
  '(and (eq *inside-include-book-fn* 'hcomp-build) ; under certify-book-fn
        *hcomp-fn-ht*                              ; compile-flg is true
        ))

(defun install-for-add-trip-hcomp-build (def reclassifyingp evalp)

; Def is a definition starting with defun, defconst, defmacro, or defabbrev.

  (let* ((type (car def))
         (name (cadr def))
         (ht (hcomp-ht-from-type type 'install-for-add-trip-hcomp-build)))
    (when evalp
      (eval def))
    (assert ht)
    (multiple-value-bind (old present-p)
        (gethash name ht)
      (cond ((eq old *hcomp-fake-value*)) ; then we keep the fake value
            ((and (consp (car (last def)))
                  (eq (car (car (last def))) 'quote))

; See the defconst case in add-trip, with a comment there explaining that the
; defparameter is generated with a quoted body when the original defconst has a
; quoted body that we want to preserve.  This condition of a quoted body
; similarly includes definitions (defun or defmacro) generated by make-event
; whose body is a quoted object that is (or includes) a hons or fast-alist.  In
; such cases we prefer not to save the definition in a hash table, instead
; letting the event come from the certificate file, where the serialize
; read/write mechanism preserves honses and fast-alists.  Presumably the
; penalty of having to recompile (or even of not compiling) is small when the
; body is a quoted constant.

; See also the attachment case in add-trip, which has a comment explaining that
; with potentially more than one attachment it is important to treat the
; attachment-symbol as unqualified.

             (setf (gethash name ht)
                   *hcomp-fake-value*))
            (present-p (cond ((and reclassifyingp
                                   (not (reclassifying-value-p old)))
                              (assert$ (eq type 'defun)

; We expect a *1* function here.  If that is not the case (for some odd reason
; we don't foresee), then we will be making a reclassifying value here that
; presumably won't get used.

                                       (setf (gethash name ht)
                                             (make-reclassifying-value
                                              (symbol-function name)))))
                             (t

; This case is presumably impossible unless raw mode is used somehow to allow
; redefinition.  But we are conservative here.

                              (setf (gethash name ht)
                                    *hcomp-fake-value*))))
            (t
             (setf (gethash name ht)
                   (case type
                     (defun        (symbol-function name))
                     (defparameter (symbol-value name))
                     (otherwise    (macro-function name)))))))))

(defun install-for-add-trip-include-book (type name def reclassifyingp)

; Def is nil if no evaluation of a definition is desired, in which case we
; return true when the definition exists in the appropriate hash table.
; Otherwise def is a definition starting with defun, defconst, defmacro, or
; defabbrev.

  (let ((ht (hcomp-ht-from-type type 'install-for-add-trip-include-book)))
    (when (null ht) ; e.g., including uncertified book
      (return-from install-for-add-trip-include-book
        (when def (eval def))))
    (multiple-value-bind (val present-p)
        (gethash name ht)
      (cond
       (present-p
        (assert$
         (not (eq val *hcomp-fake-value*))
         (cond
          ((reclassifying-value-p val)
           (assert$
            (eq type 'defun) ; presumably a *1* symbol
            (let ((fixed-val (unmake-reclassifying-value val)))
              (setf (gethash name ht) fixed-val)
              (cond (reclassifyingp

; We are converting the definition of some function, F, from :program mode to
; :logic mode.  Since reclassifying-value-p holds of val, the book (including
; its portcullis commands) contains both a :program mode definition of F and a
; :logic mode definition of F, and so far we have processed neither while
; including this book.  Since parameter reclassifyingp is true, we are now
; converting F from :program mode to :logic mode, which may seem surprising
; given that we have not processed the earlier :program mode definition in the
; book.  The situation however is that now, we are including this book in a
; world where F was already defined in :program mode.  Since we are now
; reclassifying to :logic mode, there is no need to go through the usual
; two-step process; rather, we can simply define the function now.  We probably
; don't need to modify the hash table in this case (as we did above); but this
; case is probably unusual so the potential efficiency hit seems trivial, and
; it seems safest to go ahead and keep only the true value in the hash table
; henceforth.

                     (setf (symbol-function name) fixed-val)
                     t)
                    (t (when def (eval def)))))))
          (t (case type
               (defun
                 (setf (symbol-function name) val))
               (defparameter
                 (setf (symbol-value name) val))
               (otherwise
                (assert$ (member-eq type '(defabbrev defmacro))
                         (setf (macro-function name) val))))
             t))))
       (t (when def (eval def)))))))

(defun install-for-add-trip (def reclassifyingp evalp)

; For background on how we use hash tables to support early loading of compiled
; files by include-book, see the Essay on Hash Table Support for Compilation.

; Evalp is only relevant when (hcomp-build), in which case it is passed to
; install-for-add-trip-hcomp-build.

  (cond
   ((eq *inside-include-book-fn* t) ; in include-book-fn, not certify-book-fn
    (install-for-add-trip-include-book (car def) (cadr def) def
                                       reclassifyingp))
   ((hcomp-build-p)
    (install-for-add-trip-hcomp-build def reclassifyingp evalp))
   (t (eval def))))

(defun install-defs-for-add-trip (defs reclassifying-p wrld declaim-p evalp)

; Defs is a list of definitions, each of which is a call of defun, defabbrev,
; or defmacro, or else of the form (ONEIFY-CLTL-CODE defun-mode def
; stobj-name), where def is the cdr of a call of defun.

; This function, which may destructively modify defs, is responsible for
; declaiming and submitting every definition in defs, while avoiding such
; effort when a definition is already available from *hcomp-fn-ht*.  Note that
; if its definition is available from that hash table, then it was already
; declaimed (if necessary) during the load of the expansion file (or the
; compiled version of it) that populated that hash table with its definition.

; The only time we retrieve an existing definition from *hcomp-fn-ht* is during
; include-book-fn but not during certify-book-fn, i.e., when
; *inside-include-book-fn* is t.

; Evalp is only relevant when (hcomp-build),in which case it is passed to
; install-for-add-trip-hcomp-build.

; We start with declaiming of inline and notinline.

  (loop for tail on defs
        do
        (let* ((def (car tail))
               (oneify-p (eq (car def) 'oneify-cltl-code))
               (def0 (if oneify-p (caddr def) (cdr def)))
               (name (symbol-name (car def0))))
          (cond ((equal (caddr def0)
                        '(DECLARE (XARGS :NON-EXECUTABLE :PROGRAM)))

; We allow redefinition for a function introduced by :defproxy, regardless of
; the value of state global 'ld-redefinition-action.  If the original
; definition were inlined, then this redefinition might be ignored, and it
; could reasonably be viewed as our fault, because we would not be able to say
; "all bets are off with the use of ld-redefinition-action".

; If we change or remove this proclaim form, then revisit the comment about
; inlining in redefinition-renewal-mode.

                 (let ((form (list 'notinline
                                   (if oneify-p
                                       (*1*-symbol (car def0))
                                     (car def0)))))
                   (proclaim form)
                   (push (list 'declaim form) *declaim-list*)))
                (oneify-p nil)
                ((terminal-substringp *inline-suffix*
                                      name
                                      *inline-suffix-len-minus-1*
                                      (1- (length name)))
                 (let ((form (list 'inline (car def0))))
                   (proclaim form)
                   (push (list 'declaim form) *declaim-list*)))
                ((terminal-substringp *notinline-suffix*
                                      name
                                      *notinline-suffix-len-minus-1*
                                      (1- (length name)))
                 (let ((form (list 'notinline (car def0))))
                   (proclaim form)
                   (push (list 'declaim form) *declaim-list*))))))
  (loop for tail on defs
        do
        (let* ((def (car tail))
               (oneify-p (eq (car def) 'oneify-cltl-code))
               (def0 (if oneify-p (caddr def) (cdr def))))
          (cond ((and (eq *inside-include-book-fn* t)
                      (cond
                       (oneify-p
                        (install-for-add-trip-include-book
                         'defun
                         (*1*-symbol (car def0))
                         nil
                         reclassifying-p))
                       #+sbcl
                       ((and (not (eq *inside-include-book-fn*

; We don't bother with the special treatment below if we are simply certifying
; a book, both because we don't expect to do much in the resulting world and
; because inlining (the issue here, as described in the comment below) seems to
; be handled without this special treatment.  Note that by avoiding this
; special case when *inside-include-book-fn* is 'hcomp-build, we avoid
; duplicating the declaiming of inline for this function done in the
; (hcomp-build-p) case below.

                                      'hcomp-build))
                             (not (member-eq (car def)
                                             '(defmacro defabbrev)))
                             (let ((name (symbol-name (car def0))))
                               (terminal-substringp *inline-suffix*
                                                    name
                                                    *inline-suffix-len-minus-1*
                                                    (1- (length name)))))

; We are including a book (and not merely on behalf of certify-book, as
; explained above).  Apparently SBCL needs the source code for a function in
; order for it to be inlined.  (This isn't surprising, perhaps; perhaps more
; surprising is that CCL does not seem to have this requirement.)
; See for example community book books/system/optimize-check.lisp, where
; the form (disassemble 'g4) fails to exhibit inlined code without the special
; treatment we provide here.  That special treatment is to avoid obtaining the
; definition from the hash table, instead letting SBCL fall through to the
; (eval (car tail)) below.  If we decide to give this special treatment to
; other host Lisps, we should consider installing the compiled definition from
; the hash table; but SBCL always compiles its definitions, so that seems
; unnecessary other than to save compilation time, which presumably is
; relatively small for inlined functions, and at any rate, appears to be
; unavoidable.

                        nil)
                       (t (install-for-add-trip-include-book
                           (car def)
                           (cadr def)
                           nil
                           reclassifying-p))))
                 (setf (car tail) nil))
                (t (let (form)
                     (cond
                      (oneify-p
                       (let ((*1*-def (cons 'defun
                                            (oneify-cltl-code (cadr def)
                                                              def0
                                                              (cdddr def)
                                                              wrld))))
                         (setf (car tail) *1*-def)

; While it is tempting to do a declaim for a *1* function,
; make-defun-declare-form isn't up to the task as of the development sources on
; 5/2/2013.  Perhaps this would be easy to fix, but since we only declaim for
; GCL, and it is not an important goal to make *1* functions efficient, we skip
; this step.

;                        (when declaim-p
;                          (setq form
;                                (make-defun-declare-form (car def0)
;                                                         *1*-def)))
                         ))
                      ((and declaim-p
                            (not (member-eq (car def)
                                            '(defmacro defabbrev))))
                       (setq form (make-defun-declare-form (cadr def) def))))
                     (when (and form (hcomp-build-p))
                       (push form *declaim-list*))
                     (when evalp
                       (eval form)))))))
  (cond ((eq *inside-include-book-fn* t)
         (loop for tail on defs
               when (car tail)
               do (eval (car tail))))
        ((hcomp-build-p)
         (loop for def in defs
               do
               (install-for-add-trip-hcomp-build def reclassifying-p evalp)))
        (t
         (loop for def in defs
               do (eval def)))))

(defun ifat-defparameter (name val form)

; "Ifat" stands for "install-for-add-trip".

; During certification, install-for-add-trip-hcomp-build and
; hcomp-build-from-state[-raw] store values for subsequent early loading of
; compiled files by include-book.  Defconst forms with quoted values are given
; special treatment: their values are not stored, in case the form was
; generated by (make-event `(defconst ...)) and the value contains a hons or a
; fast alist.  Here we communicate that intent by generating a defparameter
; that uses QUOTE when the original defconst had a quoted value and an alias
; for QUOTE otherwise.

  (if (and (consp form)
           (eq (car form) 'quote))
      `(defparameter ,name (quote ,val))
    `(defparameter ,name (our-quote-macro ,val))))

(defun hcomp-build-from-state-raw (cltl-cmds state)

; Warning: If you change this function, consider making corresponding changes
; to add-trip.  We wrote the present function primarily by eliminating extra
; code from the definition of add-trip, to satisfy the following spec.  We also
; eliminated comments; see add-trip for those.

; Cltl-cmds is a list of cltl-command values, each the cddr of some triple in
; the world.  We are certifying a book, and we want to populate the
; *hcomp-xxx-ht* hash-tables much as we do when processing events in the book.
; We also start populating *declaim-list*.

  (let ((*inside-include-book-fn* 'hcomp-build))
    (dolist (cltl-cmd cltl-cmds)
      (let* ((wrld (w state)))
        (case (car cltl-cmd)
          (defuns
            (let ((ignorep (caddr cltl-cmd))
                  (defun-mode (cadr cltl-cmd))
                  (new-defs nil)
                  (new-*1*-defs nil))
              (dolist
                (def (cdddr cltl-cmd))
                (cond ((and (consp ignorep)
                            (eq (car ignorep) 'defstobj))
                       nil)
                      (t
                       (or ignorep
                           (setq new-defs (cons (cons 'defun def)
                                                new-defs)))
                       (setq new-*1*-defs
                             (cons (list* 'oneify-cltl-code
                                          defun-mode
                                          def
                                          (if (consp ignorep)
                                              (cdr ignorep)
                                            nil))
                                   new-*1*-defs)))))
              (install-defs-for-add-trip (nconc new-defs new-*1*-defs)
                                         (eq ignorep 'reclassifying)
                                         wrld t nil)))
          ((defstobj defabsstobj)
            (let ((name (nth 1 cltl-cmd))
                  (raw-defs (nth 4 cltl-cmd))
                  (ax-defs (nth 6 cltl-cmd))
                  (new-defs nil))
              (dolist
                (def raw-defs)
                (push (cond ((eq (car cltl-cmd) 'defabsstobj)
                             (cons 'defmacro def))
                            ((member-equal *stobj-inline-declare* def)
                             (cons 'defabbrev
                                   (remove-stobj-inline-declare def)))
                            (t (cons 'defun def)))
                      new-defs))
              (dolist
                (def ax-defs)
                (push (list* 'oneify-cltl-code :logic def name)
                      new-defs))
              (setq new-defs (nreverse new-defs))
              (install-defs-for-add-trip new-defs nil wrld t nil)))
          (defconst
            (install-for-add-trip (ifat-defparameter (cadr cltl-cmd)
                                                     (cadddr cltl-cmd)
                                                     (caddr cltl-cmd))
                                  nil
                                  nil))
          (defmacro
            (install-for-add-trip cltl-cmd nil nil))
          (attachment ; (cddr trip) is produced by attachment-cltl-cmd
           (dolist (x (cdr cltl-cmd))
             (let ((name (if (symbolp x) x (car x))))
               (unless (eq name *special-cltl-cmd-attachment-mark-name*)

; See maybe-push-undo-stack for relevant discussion of the condition above.

                 (install-for-add-trip
                  (cond ((symbolp x)
                         (set-attachment-symbol-form x nil))
                        (t (set-attachment-symbol-form name (cdr x))))
                  nil
                  nil)))))

; There is nothing to do for memoize or unmemoize.

          ))))
  (value nil))

(defmacro eq-symbol-function-possibly-unmemoized (fn sym)

; Suppose that a book defines a function symbol sym, which associates sym with
; its symbol-function, fn, in the *hcomp-fn-ht*.  Now suppose that the book
; later memoizes sym.  The expansion file will write out the unmemoized
; definition of sym, which is the correct one to look up when we later include
; the book; so we return t in that case, to indicate that it's fine to use this
; saved definition during a later include-book when defining fn.

  (assert (and (symbolp fn) (symbolp sym))) ; else we should use defabbrev
  `(or (eq ,fn (symbol-function ,sym))
       #+hons
       (let ((entry (gethash ,sym *memoize-info-ht*)))
         (and entry
              (eq ,fn
                  (access memoize-info-ht-entry entry :old-fn))))))

(defun hcomp-alists-from-hts ()
  (let ((fn-alist nil)
        (const-alist nil)
        (macro-alist nil))
    (maphash (lambda (k val)
               (push (cons k
                           (cond ((eq val *hcomp-fake-value*)
                                  nil)
                                 ((not (fboundp k))
                                  nil)
                                 ((reclassifying-value-p val)
                                  (let ((fn (unmake-reclassifying-value val)))
                                    (and (eq-symbol-function-possibly-unmemoized
                                          fn k)
                                         'semi)))
                                 (t (eq-symbol-function-possibly-unmemoized
                                     val k))))
                     fn-alist))
             *hcomp-fn-ht*)
    (maphash (lambda (k val)
               (push (cons k
                           (cond ((eq val *hcomp-fake-value*)
                                  nil)
                                 ((not (boundp k))
                                  nil)
                                 ((eq val (symbol-value k))
                                  t)
                                 (t nil)))
                     const-alist))
             *hcomp-const-ht*)
    (maphash (lambda (k val)
               (push (cons k
                           (cond ((eq val *hcomp-fake-value*)
                                  nil)
                                 ((and val
                                       (eq val (macro-function k)))
                                  t)
                                 (t nil)))
                     macro-alist))
             *hcomp-macro-ht*)
    (mv fn-alist const-alist macro-alist)))

; This concludes development of code for early loading of compiled files
; (though other related such code may be found elsewhere).

(defconst *boot-strap-pass-2-acl2-loop-only-fns*

; Every function in this list must have a custom *1* function.

  '(apply$-prim apply$-lambda))

(defun-one-output add-trip (world-name world-key trip status)

; Warning: If you change this function, consider making corresponding changes
; to hcomp-build-from-state-raw.

; Add-trip is the function that moves a triple, (symb key .  val) from
; a property list world into the von Neumann space of Common Lisp.
; World-name is the name of the world being installed.  World-key is
; the property being used to hold the installed properties of that
; world (i.e., the cdr of its 'acl2-world-pair).

; First we set the properties for the global-symbol and *1*-symbol, so that
; these will ultimately be behind the world-key property (as guaranteed at the
; end of the code for this function).

; For an explanation of status and its connection to the uses of
; without-interrupts below, see the comment in extend-world1 where status is
; bound.

  (global-symbol (car trip))
  (*1*-symbol? (car trip)) ; e.g. hard-error for *1*-symbol with (table :a 3 4)

; Our next step is to push val onto the key stack in (get symb world-key).

  (without-interrupts
   (let ((alist (get (car trip) world-key)))
     (setf (get (car trip) world-key)
           (destructive-push-assoc (cadr trip) (cddr trip) alist world-key))
     (setf (car status) (cadr trip))
     (setf (cdr status) alist)))

; Now, in the case that we are messing with 'current-acl2-world and
; symb is 'CLTL-COMMAND and key is 'GLOBAL-VALUE, we smash the
; symbol-function or symbol-value cell of the appropriate name, first
; saving the old value (form) on the undo-stack.

  (when (and (eq world-name 'current-acl2-world)
             (eq (car trip) 'cltl-command)
             (eq (cadr trip) 'global-value)
             (consp (cddr trip)))
    (let* ((wrld (w *the-live-state*))
           (boot-strap-flg (f-get-global 'boot-strap-flg *the-live-state*))
           (cltl-cmd (cddr trip)))
      (case (car cltl-cmd)
        (defuns

; Cltl-cmd is of the form (defuns defun-mode ignorep def1 ... defn).
; Defun-mode non-nil is stored by DEFUNS and defun-mode nil by :non-executable
; DEFUNS and by ENCAPSULATE when it is defining the constrained fns.
; Oneify-cltl-code relies on the fact that functions with defun-mode nil do a
; THROW.

; Observe that we sometimes use oneify-cltl-code to modify the actual Common
; Lisp code.  Why don't we modify the defi before storing the cltl-command
; tuple?  Because we want to make it easy on ourselves to recover from the
; world the actual defi used to define :program mode functions.  See
; verify-termination.

; Recall that ignorep is non-nil if we are to AVOID storing the
; symbol-functions for names.  If ignorep is non-nil, then it is either
; reclassifying  -- meaning we are reclassifying a symbol from :program
;                   to :logic mode.  We don't want to overwrite its
;                   symbol-function since that might be ACL2 source code.
;                   We still write a *1* definition in this case.
; (defstobj . stobj)
;                -- meaning the names being introduced are actually being
;                   defun'd under (defstobj stobj ...) or (defabsstobj stobj
;                   ...).  We don't want to store the code generated by defun
;                   for these names because defstobj and defabsstobj will
;                   generate a CLTL-COMMAND containing the made-to-order raw
;                   defs.  We also do not store the *1* definition in this
;                   case, because in CCL (at least) this would cause a problem
;                   since the *1* code calls the raw Lisp function, which has
;                   not yet been defined and in the :inline case is actually a
;                   macro.  (See also the comment in defstobj-functionsp.)

; Why do we need the stobj name in the case of ignorep = '(defstobj . stobj)?
; The reason is that when we generate the *1* code for the function, fn, we
; must generate a throw to handle a guard violation and the argument to that
; throw is an object which includes, among other things, the stobjs-in of fn so
; we will know how to print them.  You might think we would get the stobjs-in
; of fn from the world.  But we can't because this defun is being done under,
; and as part of, a defstobj or defabsstobj event, and the event will later
; declare stobj to be a stobj name.  So the stobjs-in of fn in the world right
; now is wrong.  The stobjs-in we need is built into the object thrown and so
; won't be overwritten when the event gets around to declaring stobj a stobj.
; So oneify-cltl-code, called below, takes the stobj name as its input and
; computes the appropriate stobjs-in from the formals.  This is a problem
; analogous to the one addressed by the super-defun-wart table.

          (let ((ignorep (caddr cltl-cmd))
                (defun-mode (cadr cltl-cmd))
                (new-defs

; We avoid potential "undefined" warnings by holding off on compilation until
; all the functions have been defined.  Moreover, in the case of CCL we
; need to hold off even on defining the functions.  So we collect up the
; definitions that need to be made in Common Lisp, proclaiming as we go
; (although proclaiming may be a no-op in some Lisps), then make all the
; definitions, and finally do the compilation as appropriate.

                 nil)
                (new-*1*-defs nil))
            (without-interrupts

; We need all the calls of maybe-push-undo-stack to be done atomically, in
; support of extend-world1 (specifically, the invocation of retract-world1 in
; the cleanup form of extend-world1).  We expect that disabling interrupts here
; will not prevent interruptions from taking place quickly overall, because the
; actions below will be completed very quickly.

             (dolist
               (def (cdddr cltl-cmd))
               (cond ((and boot-strap-flg
                           (not (global-val 'boot-strap-pass-2 wrld)))

; During the first pass of initialization, we insist that every function
; defined already be defined in raw lisp.  During pass two we can't expect this
; because there may be LOCAL defuns that got skipped during compilation and the
; first pass.

                      (or (fboundp (car def))

; Note that names of macros are fboundp, so we can get away with symbols that
; are defined to be macros in raw Lisp but functions in the logic (e.g.,
; return-last).

                          (interface-er "~x0 is not fboundp!"
                                        (car def)))

; But during the first pass of initialization, we do NOT assume that every (or
; any) function's corresponding *1* function has been defined.  So we take care
; of that now.

                      (or (member-eq (car def)

; For explanation of the special handling of the first three of the following
; function symbols, see the comments in their defun-*1* forms.  For
; *defun-overrides*, we have already taken responsibility for defining *1*
; functions that we don't want to override here.

                                     `(mv-list return-last wormhole-eval
                                               ,@*defun-overrides*))
                          (setq new-*1*-defs
                                (cons (list* 'oneify-cltl-code
                                             defun-mode
                                             def

; The if below returns the stobj name being introduced, if any.

                                             (if (consp ignorep)
                                                 (cdr ignorep)
                                               nil))
                                      new-*1*-defs))))
                     ((and (not ignorep)
                           (equal *main-lisp-package-name*
                                  (symbol-package-name (car def))))
                      (interface-er "It is illegal to redefine a function in ~
                                    the main Lisp package, such as ~x0!"
                                    (car def)))
                     ((and (consp ignorep)
                           (eq (car ignorep) 'defstobj))

; We wait for the cltl-command from the defstobj or defabsstobj (which is laid
; down last by defstobj-fn or defabsstobj-fn, using install-event) before
; defining/compiling the *1* functions, in order to avoid potential "undefined"
; warnings and, more importantly, to avoid defining *1* functions in terms of
; undefined macros (for the :inline case of defstobj and for defabsstobj),
; which confuses CCL as described in a comment in defstobj-functionsp.  We
; still save the existing values (if any) of the current def and the current
; *1* def; see the next comment about ignorep.

                      (maybe-push-undo-stack 'defun (car def) ignorep))
                     ((and boot-strap-flg
                           (member-eq (car def)
                                      *boot-strap-pass-2-acl2-loop-only-fns*)))
                     (t (maybe-push-undo-stack 'defun (car def) ignorep)

; Note: If ignorep is '(defstobj . stobj), we save both the current def and the
; current *1* def.  If ignorep is 'reclassifying, we save only the *1* def.
; The former behavior means that in defstobj, when the defun runs for each
; name, we will save both symbol-function cells, even though we store into
; neither.  The code for installing a defstobj CLTL-COMMAND doesn't bother to
; do undo-stack work, because it knows both cells were saved by the defun.

                        (or ignorep
                            (setq new-defs (cons (cons 'defun def) new-defs)))
                        (setq new-*1*-defs
                              (cons (list* 'oneify-cltl-code
                                           defun-mode
                                           def

; The if below returns the stobj name being introduced, if any.

                                           (if (consp ignorep)
                                               (cdr ignorep)
                                             nil))
                                    new-*1*-defs)))))
             (setf (cdr status) 'maybe-push-undo-stack-completed))
            (setq new-defs (nconc new-defs new-*1*-defs))
            (install-defs-for-add-trip new-defs
                                       (eq ignorep 'reclassifying)
                                       wrld
                                       (not boot-strap-flg)
                                       t)
            (cond ((not (eq (f-get-global 'compiler-enabled *the-live-state*)
                            t))
; Then skip compilation.
                   )
                  ((or

; It seems critical to compile as we go in CMUCL 18e during the boot-strap, in
; order to avoid stack overflows.  This seems to cut about 20% off the
; regression time for Allegro builds, so we go ahead and do this in all Lisps.
; See also the long comment for the case (eq fns :some) in
; compile-uncompiled-*1*-defuns.  It is tempting to avoid this on-the-fly
; compilation for GCL, where we have seen build time shrink from over 22 to
; under 7 minutes and have seen roughly a percent or slightly less degradation
; in regression time, probably because of the lack of compilation in that case
; of *1* functions for built-in :program mode functions.  But we have decided,
; at least for now, to keep the code simple by doing the same thing for all
; lisps and be happy with even that small improvement in regression time for
; GCL.  (Note that by using make with
;   LISP='gcl -eval "(defparameter user::*fast-acl2-gcl-build* t)"'
; one can get a faster build, without this on-the-fly compilation, with very
; little performance penalty at runtime.  Something like this could be done
; with any Common Lisp, but there is only a point in GCL; see above.)

                    (and #+gcl (not user::*fast-acl2-gcl-build*)
                         boot-strap-flg) ; delete for build speedup (see above)
                    (and
                     (not *inside-include-book-fn*)
                     (default-compile-fns wrld)))
                   (dolist (def new-defs)
                     (assert$
                      def

; Install-defs-for-add-trip can't make def nil, since either we are in the
; boot-strap or else the value of 'ld-skip-proofsp is not 'include-book.

                      (let ((name (cond ((eq (car def) 'defun)
                                         (cadr def))
                                        ((eq (car def) 'oneify-cltl-code)
                                         (car (caddr def)))
                                        (t (error "Implementation error: ~
                                                   unexpected form in ~
                                                   add-trip, ~x0"
                                                  def)))))
                        (eval `(compile ',name)))))))))
        ((defstobj defabsstobj)

; Cltl-cmd is of the form
; (defstobj-type name the-live-name init raw-defs disc axiomatic-defs)
; where defstobj-type is DEFSTOBJ or DEFABSSTOBJ and disc is the
; redundant-raw-lisp-discriminator for name.

; Init is a form to eval to obtain the initial setting for the live variable.
; Each def in raw-defs and in axiomatic-defs is of the form (name args dcl
; body), where dcl may be omitted.  We make a function or macro definition for
; each raw-def, and we make a defun for the oneification of each axiomatic-def.

         (let* ((absp (eq (car cltl-cmd) 'defabsstobj))
                (name (nth 1 cltl-cmd))
                (the-live-name (nth 2 cltl-cmd))
                (init (nth 3 cltl-cmd))
                (raw-defs (nth 4 cltl-cmd))
                (discriminator (nth 5 cltl-cmd))
                (ax-defs (nth 6 cltl-cmd))
                (non-executable
                 (access defstobj-redundant-raw-lisp-discriminator-value
                         (cdr discriminator)
                         :non-executable))
                (new-defs

; We avoid "undefined function" warnings by Allegro during compilation by
; defining all the functions first, and compiling them only after they have all
; been defined.  But we go further; see the comment in the binding of new-defs
; in the previous case.

                 nil))
           (without-interrupts
            (maybe-push-undo-stack 'defconst '*user-stobj-alist*)
            (setf (cdr status) 'maybe-push-undo-stack-completed))

; Memoize-flush expects the variable (st-lst name) to be bound.  We take care
; of that directly here.  We see no need to involve install-for-add-trip or the
; like.

           #+hons (let ((var (st-lst name)))
                    (or (boundp var)
                        (eval `(defg ,var nil))))

; As with defconst we want to make it look like we eval'd this defstobj or
; defabsstobj in raw lisp, so we set up the redundancy stuff:

           (setf (get the-live-name 'redundant-raw-lisp-discriminator)
                 discriminator)

; The following assignment to *user-stobj-alist* is structured to keep
; new ones at the front, so we can more often exploit the optimization
; in put-assoc-eq-alist.

           (setq *user-stobj-alist*
                 (cond ((assoc-eq name *user-stobj-alist*)

; This is a redefinition!  We'll just replace the old entry.

                        (if non-executable
                            (remove1-assoc-eq name *user-stobj-alist*)
                          (put-assoc-eq name
                                        (eval init)
                                        *user-stobj-alist*)))
                       (non-executable *user-stobj-alist*)
                       (t (cons (cons name (eval init))
                                *user-stobj-alist*))))

; We eval and compile the raw lisp definitions first, some of which may be
; macros (because :inline t was supplied for defstobj, or because we are
; handling defabsstobj), before dealing with the *1* functions.

           (dolist
             (def raw-defs)
             (cond ((and boot-strap-flg
                         (not (global-val 'boot-strap-pass-2 wrld)))

; During the first pass of initialization, we insist that every function
; defined already be defined in raw lisp.  During pass two we can't expect this
; because there may be LOCAL defuns that got skipped during compilation and the
; first pass.

                    (or (fboundp (car def))
                        (interface-er "~x0 is not fboundp!"
                                      (car def))))
                   ((equal *main-lisp-package-name*
                           (symbol-package-name (car def)))
                    (interface-er
                     "It is illegal to redefine a function in the main Lisp ~
                      package, such as ~x0!"
                     (car def)))

; We don't do maybe-push-undo-stack for defuns (whether inlined or not) under
; the defstobj or defabsstobj CLTL-COMMAND, because we did it for their
; defuns.

                   (t
                    (let ((def (cond
                                (absp (cons 'defmacro def))
                                ((member-equal *stobj-inline-declare* def)

; We now handle the case where we are going to inline the function calls by
; defining the function as a defabbrev.  Note that this is allowed for
; access/update/array-length functions for stobjs, but only for these, where
; speed is often a requirement for efficiency.

                                 (cons 'defabbrev
                                       (remove-stobj-inline-declare def)))
                                (t (cons 'defun def)))))
                      (setq new-defs (cons def new-defs))))))
           (dolist
             (def ax-defs)
             (setq new-defs (cons (list* 'oneify-cltl-code :logic def name)
                                  new-defs)))
           (setq new-defs

; We reverse new-defs because we want to be sure to define the *1*
; defs after the raw Lisp defs (which may be macros, because of :inline).

                 (nreverse new-defs))
           (install-defs-for-add-trip new-defs nil wrld (not boot-strap-flg)
                                      t)
           (when (and (eq (f-get-global 'compiler-enabled *the-live-state*)
                          t)
                      (not *inside-include-book-fn*)
                      (default-compile-fns wrld))
             (dolist (def new-defs)
               (assert$

; Install-defs-for-add-trip can't make def nil, since the value of
; 'ld-skip-proofsp is not 'include-book.

                def
                (let ((name (cond ((or (eq (car def) 'defun)
                                       (eq (car def) 'defabbrev)
                                       (eq (car def) 'defmacro))
                                   (cadr def))
                                  ((eq (car def) 'oneify-cltl-code)
                                   (car (caddr def)))
                                  (t (error "Implementation error: ~
                                              unexpected form in add-trip, ~x0"
                                            def)))))

; CMUCL versions 18e and 19e cannot seem to compile macros at the top level.
; Email from Raymond Toy on June 9, 2004 suggests that this appears to be a bug
; that exists in CMUCL 18e sources.  We'll thus give special treatment to any
; version 18 or 19 of CMUCL, but we'll avoid that for CMUCL version 20, since
; 20D at least can compile macros.

                  #+(and cmu (or cmu18 cmu19))
                  (cond ((and (not (eq (car def) 'defabbrev))
                              (not (eq (car def) 'defmacro)))
                         (eval `(compile ',name))))
                  #-(and cmu (or cmu18 cmu19))
                  (eval `(compile ',name))))))))
        (defpkg
          (without-interrupts
           (maybe-push-undo-stack 'defpkg (cadr cltl-cmd))
           (setf (cdr status) 'maybe-push-undo-stack-completed))
          (eval (cons 'defpkg (cdr cltl-cmd))))
        (defconst

; Historical remark on defconstant.

; In the beginning we supported defconstant.  We changed to
; defparameter and then changed to defconst.  As things stand now,
; ACL2 supports defconst, which has the same effect at the raw lisp
; level (i.e., the cltl-command) as defparameter, and in addition
; causes proclaim-file to execute an appropriate proclamation for the
; parameter, knowing as we do that it is really constant.  Here are
; some historical remarks that explain why we have gone down this
; path.

; "Currently we turn defconstants into defparameters at the raw Lisp
; level (that is, the cltl-command for defconstant is a defparameter).
; However, we have begun to contemplate alternatives, as we now
; explain.

; We have run into the following problem with defconstant:  the
; compiler won't let us compile certified books containing defconstant
; forms because it thinks that constants are special variables
; (because that is what the defparameter cltl-command does).  What can
; we do about this problem?  One idea was to temporarily redefine
; defconstant to be defparameter (during the compilation done by
; certify-book), but macrolet has only lexical scope, and anyhow Boyer
; says that it's illegal to redefine a Common Lisp function (as we did
; using setf, macro-function, and unwind-protect).

; Another possibility is to change defconstant-fn so that it really
; does create defconstants.  But the reason we use defparameter now is
; that when we undo we need to unbind (because we're always checking
; to see if something is already bound), and we can't unbind a
; constant.

; Why not just eliminate defconstant in favor of defparameter
; everywhere?  This is very appealing, especially because defconstant
; is inherently not amenable to undoing.  But, Boyer thinks that when
; you defconstant something to a value that is a fixnum, then the
; compiler knows it's a fixnum.  This could be very important for
; speed in type-set reasoning.  Without the consideration of
; arithmetic, Schelter thinks that we're only paying the price of two
; memory references for defparameter vs. one for defconstant; but a
; factor of 80 or so seems like too high a price to pay.

; So, how about allowing both defconstant and defparameter, but not
; allowing any undoing back past a defconstant?  After all, we already
; have a notion of not undoing into the system initialization, so
; we're just talking about a very reasonable extension of that
; protocol.  One problem with this approach is that certify-book
; currently does an include-book after a ubt, and this ubt would
; probably fail.  But perhaps we can force this to work.  The user
; could then develop his work using defparameter, but certify the
; final "toothbrush" book using defconstant.  Perhaps defconst would
; be a convenient macro that could be redefined so as to be one or the
; other of defparameter or defconstant.  With this approach it would
; probably be useful to require answering a query in order to execute
; a defconstant.

; Another option would be to have acl2::defconstant be distinct from
; lisp::defconstant, but as Boyer points out, this violates our desire
; to have such Lisp primitives available to the user that he can count
; on.  Or, we could define a new package that's just like the acl2
; package but doesn't import defconstant.  But note that
; (symbol-package 'defconstant) would create different answers in the
; ACL2 package than in this package -- ouch!"

; Note: cltl-cmd here is (defconst var form val).

          (cond (boot-strap-flg
                 (or (boundp (cadr cltl-cmd))
                     (interface-er "~x0 is not boundp!"
                                   (cadr cltl-cmd)))

; In the boot-strap, there are constants that will not get the necessary
; 'redundant-raw-lisp-discriminator proprerty without the following code.  In
; particular, the constant *badge-prim-falist* is defined under when-pass-2, so
; its defconst form is not processed in raw Lisp.  As a result, without the
; following code we get an error: "The following raw Lisp error occurred when
; loading file <path>/apply-prim.dx64fsl: Illegal attempt to redeclare the
; constant *BADGE-PRIM-FALIST*."  That error prevents loading of the compiled
; file.

                 (or (get (cadr cltl-cmd)
                          'redundant-raw-lisp-discriminator)
                     (setf (get (cadr cltl-cmd)
                                'redundant-raw-lisp-discriminator)
                           (list* 'defconst
                                  (caddr cltl-cmd) ; form
                                  (cadddr cltl-cmd)))))
                ((equal *main-lisp-package-name*
                        (symbol-package-name (cadr cltl-cmd)))
                 (interface-er "It is illegal to redefine a defconst in the ~
                                main Lisp package, such as ~x0!"
                               (cadr cltl-cmd)))
                (t (without-interrupts
                    (let* ((name (cadr cltl-cmd))
                           (form (caddr cltl-cmd))
                           (val (cadddr cltl-cmd)))
                      (maybe-push-undo-stack 'defconst name)

; We do not want to eval (defconst var form) here because that will recompute
; val.  But we make raw Lisp look like it did that.

                      (setf (get name 'redundant-raw-lisp-discriminator)
                            (list* 'defconst form val))
                      (install-for-add-trip (ifat-defparameter name val form)
                                            nil
                                            t))
                    (setf (cdr status)
                          'maybe-push-undo-stack-completed)))))
        (defmacro
            (cond ((and boot-strap-flg
                        (not (global-val 'boot-strap-pass-2 wrld)))

; During the first pass of initialization, we insist that every function
; defined already be defined in raw lisp.  During pass two we can't expect this
; because there may be LOCAL defuns that got skipped during compilation and the
; first pass.

                   (or (fboundp (cadr cltl-cmd))
                       (interface-er "~x0 is not fboundp!"
                                     (cadr cltl-cmd))))
                  ((equal *main-lisp-package-name*
                          (symbol-package-name (cadr cltl-cmd)))
                   (interface-er "It is illegal to redefine a macro in the ~
                                main Lisp package, such as ~x0!"
                                 (cadr cltl-cmd)))
                  (t (without-interrupts
                      (maybe-push-undo-stack 'defmacro (cadr cltl-cmd))
                      (setf (cdr status) 'maybe-push-undo-stack-completed))
                     (install-for-add-trip cltl-cmd nil t))))
        (attachment ; cltl-cmd is produced by attachment-cltl-cmd
         (dolist (x (cdr cltl-cmd))
           (let ((name (if (symbolp x) x (car x))))
             (without-interrupts
              (maybe-push-undo-stack 'attachment name)
              (setf (cdr status) 'maybe-push-undo-stack-completed))
             (unless (eq name *special-cltl-cmd-attachment-mark-name*)

; See maybe-push-undo-stack for relevant discussion of the condition above.

               #+hons (push name *defattach-fns*)
               (install-for-add-trip

; It may be important here that set-attachment-symbol-form generates a
; defparameter whose form is quoted.  That way,
; install-for-add-trip-hcomp-build will treat the symbol as unqualified -- and
; this seems (as of this writing in mid-February 2021) potentially critical in
; the case that more than one attachment is provided to the same function in a
; given book (at the top level, as opposed to being in included books).

                (cond ((symbolp x)
                       (set-attachment-symbol-form x nil))
                      (t (set-attachment-symbol-form name (cdr x))))
                nil
                t)))))
        #+hons
        (memoize

; Should we push onto the undo-stack first or should we memoize first?  The
; danger of memoizing first is that an interrupt could come immediately after
; that, before pushing onto the undo-stack.  This would leave the function
; memoized after cleaning up in extend-world1 (by executing retract-world1).
; So instead, we push first; then if we're interrupted before memoization is
; complete, we are OK because the form pushed by maybe-push-undo-stack checks
; that the function is memoized before unmemoizing it.

         (without-interrupts
          (maybe-push-undo-stack 'memoize (cadr cltl-cmd))
          (setf (cdr status) 'maybe-push-undo-stack-completed))
         (let* ((tuple cltl-cmd)
                (cl-defun (nth 4 tuple)))
           (assert$ cl-defun
                    (with-overhead
                     (nth 13 tuple) ; stats
                     (memoize-fn (nth 1 tuple)
                                 :condition  (nth 2 tuple)
                                 :inline     (nth 3 tuple)
                                 :cl-defun   cl-defun
                                 :formals    (nth 5 tuple)
                                 :stobjs-in  (nth 6 tuple)
                                 :stobjs-out (nth 7 tuple)
                                 :commutative (nth 9 tuple)
                                 :forget     (nth 10 tuple)
                                 :memo-table-init-size (nth 11 tuple)
                                 :aokp       (nth 12 tuple)
                                 :invoke     (nth 14 tuple))))))
        #+hons
        (unmemoize
         (without-interrupts
          (maybe-push-undo-stack 'unmemoize (cadr cltl-cmd))
          (unmemoize-fn (cadr cltl-cmd))
          (setf (cdr status) 'maybe-push-undo-stack-completed))))))

; Finally, we make sure always to leave the *current-acl2-world-key* as the
; first property on the symbol-plist of the symbol.

  (let ((temp (get (car trip) *current-acl2-world-key*))
        (plist (symbol-plist (car trip))))
    (cond ((and temp (not (eq (car plist) *current-acl2-world-key*)))
           (setf (symbol-plist (car trip))
                 (cons *current-acl2-world-key*
                       (cons temp
                             (remove-current-acl2-world-key plist))))))))

(defun-one-output undo-trip (world-name world-key trip)

; Undo-trip is the function that removes from the ``real'' Common Lisp
; the things installed by add-trip.  It works merely by popping the
; appropriate stacks.

  (setf (get (car trip) world-key)
        (destructive-pop-assoc (cadr trip) (get (car trip) world-key)))
  (cond
   ((and (eq world-name 'current-acl2-world)
         (eq (car trip) 'cltl-command)
         (eq (cadr trip) 'global-value)
         (consp (cddr trip)))
    (case (car (cddr trip))
          (defuns

; Note that :inlined defstobj functions as well as defabsstobj exported
; functions are processed by eval-event-lst as though they are ordinary defuns,
; even though they correspond to macros in raw Lisp (defined by defabbrev and
; defmacro, respectively).  We are relying on the fact that
; maybe-push-undo-stack handled defun and defmacro the same, so that the form
; evaluated by maybe-pop-undo-stack will be appropriate even though the
; "function" is actually a macro.

            (dolist (tuple (cdddr (cddr trip)))
                    (maybe-pop-undo-stack (car tuple))))
          ((defstobj defabsstobj)
            (let ((name (nth 1 (cddr trip))))
              (maybe-pop-undo-stack name)
              (maybe-pop-undo-stack '*user-stobj-alist*)))
          (defpkg nil)
          ((defconst defmacro #+hons memoize #+hons unmemoize)
            (maybe-pop-undo-stack (cadr (cddr trip))))
          (attachment ; (cddr trip) is produced by attachment-cltl-cmd
           (let ((lst (cdr (cddr trip))))
             (dolist (x lst)
               (let ((name (if (symbolp x) x (car x))))
                 (maybe-pop-undo-stack name)))))
          (otherwise nil)))))

(defvar *bad-wrld*)

(defun check-acl2-world-invariant (wrld old-wrld)

; Old-wrld is the world currently installed under 'current-acl2-world.
; Wrld is a world we are trying to install there.  We check that
; old-world is in fact the current global value of 'current-acl2-
; world.  We have gotten out of sync on this once or twice.  It is
; cheap to check and pernicious to track down.

  (cond ((not (eq old-wrld
                  (w *the-live-state*)))
         (setq *bad-wrld* wrld)
         (interface-er
          "Extend-world1 or retract-world1 has been asked to install ~
           a world at a moment when the current global value of ~
           'current-acl2-world was not the installed world!  The ~
           world we were asked to install may be found in the variable ~
           *bad-wrld*."))))

(defparameter *known-worlds* nil)

(defvar *saved-user-stobj-alist* nil)

(defvar *saved-non-executable-user-stobj-lst* nil)

(defun update-wrld-structures (wrld state)
  (install-global-enabled-structure wrld state)
  (recompress-global-enabled-structure
   'global-arithmetic-enabled-structure
   wrld)
  (when (not (eq *saved-user-stobj-alist* *user-stobj-alist*))

; On 12/12/2019 we found, using CCL on a Mac, that the time for (include-book
; "centaur/sv/top" :dir :system) was reduced by 2.6% by adding the test above
; before calling recompress-stobj-accessor-arrays.  The time reduction however
; was only 0.2% for (include-book "projects/x86isa/top" :dir :system).  The
; former book involved many more stobjs: 27 after including it, vs. only 4 for
; the latter book.  So this change seems important mainly for scalability.

    (recompress-stobj-accessor-arrays
     (strip-cars *user-stobj-alist*)
     wrld)
    (setq *saved-user-stobj-alist* *user-stobj-alist*))
  (when (not (eq *saved-non-executable-user-stobj-lst*
                 *non-executable-user-stobj-lst*))

; On 12/12/2019 we found, using CCL on a Mac, that the time for (include-book
; "centaur/sv/top" :dir :system) was reduced by 2.6% by adding the test above
; before calling recompress-stobj-accessor-arrays.  The time reduction however
; was only 0.2% for (include-book "projects/x86isa/top" :dir :system).  The
; former book involved many more stobjs: 27 after including it, vs. only 4 for
; the latter book.  So this change seems important mainly for scalability.

    (recompress-stobj-accessor-arrays
     *non-executable-user-stobj-lst*
     wrld)
    (setq *saved-non-executable-user-stobj-lst*
          *non-executable-user-stobj-lst*))
  (when (let ((i (f-get-global 'certify-book-info state)))
          (and i
               (not (access certify-book-info i :include-book-phase))
               (not ; not inside include-book
                (global-val 'include-book-path wrld))))

; The world global 'translate-cert-data is only updated during book
; certification, and not during include-book (especially, not during the
; include-book pass of certify-book); hence the guard above.  The following
; preservation of fast-alist status might only be necessary because of changes
; to translate-cert-data made during make-event expansion.  But we protect the
; fast-alist status of that world global against any change to the world made
; (especially) by xtrans-eval.

    (make-fast-alist (global-val 'translate-cert-data wrld)))
  #+hons
  (update-memo-entries-for-attachments *defattach-fns* wrld state)
  nil)

(defun-one-output extend-world1 (name wrld)

; Wrld must be a world that is an extension of the world currently
; installed under name.

; Warning: Even though this program does not take state as an
; argument, it has the effect of smashing the value of the live state
; global 'current-acl2-world if name is 'current-acl2-world.  In
; particular, we maintain the invariant that the live global value of
; 'current-acl2-world is always the world installed under that name.
; If you don't want these changes to occur to your state, don't call
; this program!

  (let ((status

; This variable is a cons that may be destructively modified.  Its value is
; normally '(nil . nil).  Immediately after add-trip completes a call of
; (destructive-push-assoc key val alist world-key), the value of status becomes
; (cons key alist).  Then if there are maybe-push-undo-stack calls, the value
; is (cons <irrelevant> maybe-push-undo-stack-completed) immediately after they
; are (atomically) completed.  For more on this, see the cleanup form below.

         (cons nil nil))
        (state *the-live-state*)
        (pair (get name 'acl2-world-pair))
        old-wrld world-key new-trips)
    (unwind-protect-disable-interrupts-during-cleanup
     (progn
       (cond
        ((null pair)
         (setq pair (cons nil (if (eq name 'current-acl2-world)
                                  *current-acl2-world-key*
                                (gensym))))
         (pushnew name *known-worlds*)
         (cond ((eq name 'current-acl2-world)
                (f-put-global 'current-acl2-world nil state)))
         (setf (get name 'acl2-world-pair) pair)))
       (setq old-wrld (car pair))
       (setq world-key (cdr pair))

; Pair is of the form (old-wrld . world-key) and means that the world
; currently installed under name is old-wrld and its properties are
; stored at world-key.

       (cond ((eq name 'current-acl2-world)
              (check-acl2-world-invariant wrld old-wrld)))

; We now scan down the about-to-be-installed world and push onto the
; temporary new-trips the triples that constitute the extension.  If
; we fail to find the old world, we will cause a hard error.  It may look
; like we are doing this scan to guarantee that wrld is an extension.
; Were that the reason, we would do this as we installed the properties.
; No, the real reason we do this scan is so that we can collect, in reverse
; order, the triples we must install.  The order in which we push the
; values into the property lists is important!

       (do ((tl wrld (cdr tl)))
           ((equal tl old-wrld)) ; best to avoid eq; see comment in retract-world1
           (cond
            ((null tl)
             (setq *bad-wrld* wrld)
             (er hard 'extend-world1
                 "Extend-world1 was called upon to ``extend'' ~x0.  But the ~
                  world supplied to extend-world1, which is now the value of ~
                  the Lisp global *bad-wrld*, is not an extension of the ~
                  current ~x0.  The alist corresponding to the current ~x0 ~
                  may be obtained via ~x1.  No properties were modified -- ~
                  that is, the symbol-plists still reflect the ~
                  pre-extend-world1 ~x0.  You may report this problem to the ~
                  ACL2 implementors."
                 name
                 `(car (get ',name 'acl2-world-pair))))
            (t (push (car tl) new-trips))))

; It is a bit unfortunate to use with-more-warnings-suppressed below, since we
; have such a call in LP.  However, this is how we see a way to suppress
; complaints about undefined functions during the build, without suppressing
; compiler warnings entirely during the build.  Note that with-compilation-unit
; does not always defer warnings for calls of the compiler in general -- at
; least, we have seen this with CCL and Allegro CL -- but only for calls of
; compile-file.

       (with-more-warnings-suppressed
        (loop
         (when (null new-trips) (return))
         (let ((trip (car new-trips)))
           (setf (cdr status) nil)
           (add-trip name world-key trip status)
           (setq new-trips (cdr new-trips))))
        (setf (car pair) wrld)))

; Now clean up.

     (cond
      ((eq (car pair) wrld) ; everything above completed
       (when (eq name 'current-acl2-world)
         (f-put-global 'current-acl2-world wrld state)
         (update-wrld-structures wrld state)))
      (t

; We should never get here if extend-world1 was called from the cleanup form in
; retract-world1.  That's because the cleanup form is executed without
; interrupts and we don't expect errors or throws during the retraction
; process; thus, we expect the (setf (car pair) wrld) form above would have
; completed.

       (when (eq name 'current-acl2-world)
         (format t
                 "~%~
                  ; *Note*: Interrupt or error detected while extending the~%~
                  ;         ACL2 logical world; now reverting the world with~%~
                  ;         interrupts disabled.  This should complete~%~
                  ;         quickly.~&~%")
         (finish-output))

; Recall that new-trips was originally the list of triples that will extend
; old-world, which was the starting current ACL2 world, to the parameter, wrld.
; When the process above completes normally we expect to process, with
; add-trip, all of new-trips.  But if we reach here then that process was
; incomplete; thus, new-trips contains just those triples that weren't yet
; fully processed.  To a first approximation, then, we retract the extension of
; old-world by new-trips back to old-world.  But that doesn't account for the
; possibility of a partially-processed triple, T0, which is still in new-trips
; (as the car).  There are various cases, which we reference by letter in the
; code below.

; (a) When the cdr of status is maybe-push-undo-stack-completed, then we
;     completed enough of add-trip for T0 to include it in the world that we
;     will retract back to old-world.  Note that in add-trip we are careful
;     that any forms executed after maybe-push-undo-stack are harmless, in that
;     their effects would disappear anyhow during retraction (by undo-trip).

; (b) When the cdr of status is a non-empty alist as indicated above, then T0
;     will not be treated as added, but the destructive-push-assoc that was
;     completed for T0 (on the key and alist stored in status) will be undone
;     explicitly.

; (c) Otherwise the cdr of status is nil, in which case add-trip was never
;     invoked after the last triple popped from new-trips or else nothing was
;     done for T0.

       (let* ((alist (cdr status))
              (remaining (if (eq alist 'maybe-push-undo-stack-completed) ; (a)
                             (assert$ (consp new-trips) ; didn't finish
                                      (1- (length new-trips)))
                           (length new-trips)))
              (w (nthcdr remaining wrld)))
         (when (consp alist) ; (b)
           (assert$ (consp new-trips) ; didn't finish
                    (destructive-pop-assoc (car status) alist)))
         (setf (car pair) w)
         (when (eq name 'current-acl2-world)
           (f-put-global 'current-acl2-world w state)
           (update-wrld-structures w state))
         (retract-world1 name old-wrld))))))

; When we finally get past the unwind-protect above, even if the initial
; attempt is interrupted before proceeding to the cleanup form, we return wrld.

  wrld)

(defun-one-output retract-world1 (name wrld)

; Wrld must be a world that is a retraction of the world currently installed
; under name.

; Warning: Even though this program does not take state as an argument, it has
; the effect of smashing the value of the live state global 'current-acl2-world
; if name is 'current-acl2-world.  In particular, we maintain the invariant
; that the live global value of 'current-acl2-world is always the world
; installed under that name.  We also maintain the invariant that the binding
; of 'current-package is a known package, by setting 'current-package to "ACL2"
; if we have to.  If you don't want these changes to occur to your state, don't
; call this program!

  (let ((state *the-live-state*)
        (pair (get name 'acl2-world-pair))
        (processed 0)
        old-wrld world-key)
    (unwind-protect-disable-interrupts-during-cleanup
     (progn
       (cond
        ((null pair)
         (setq pair (cons nil (if (eq name 'current-acl2-world)
                                  *current-acl2-world-key*
                                (gensym))))
         (pushnew name *known-worlds*)
         (cond ((eq name 'current-acl2-world)
                (f-put-global 'current-acl2-world nil state)))
         (setf (get name 'acl2-world-pair) pair)))
       (setq old-wrld (car pair))
       (setq world-key (cdr pair))

; Pair is of the form (old-wrld . world-key) and means that the world currently
; installed under name is old-wrld and its properties are stored at world-key.

       (cond ((eq name 'current-acl2-world)
              (check-acl2-world-invariant wrld old-wrld)))

; We now scan down old-wrld until we get to wrld, doing a pop for each triple
; in the initial segment of old-wrld.  Note that we do not do the pops in the
; reverse order (as we did the pushes).  It doesn't matter.  All that matters
; is that we one pop for each push that was done.

       (do ((tl old-wrld (cdr tl)))
           ((equal tl

; At one time we used eq here.  But old-wrld and wrld are equal, but not eq,
; when retract-world1 is called in the following example.

; (defun f1 (x) x)
; (defun f2 (x) x)
; :ubt! f1
; (defun f1 (x) x)
; :oops

                   wrld))
           (cond
            ((null tl)
             (setq *bad-wrld* wrld)
             (er hard 'retract-world1
                 "Retract-world1 was called upon to ``retract'' ~x0.  But the ~
                  world supplied to retract-world1, which is now the value of ~
                  the Lisp global variable *bad-wrld*, is not a retraction of ~
                  the currently installed ~x0.  The alist corresponding to ~
                  the current ~x0 may be obtained via ~x1.  Unfortunately, ~
                  this problem was not discovered until all of the properties ~
                  in ~x0 were removed.~@2"
                 name
                 `(car (get ',name 'acl2-world-pair))
                 (cond ((eq name 'current-acl2-world)

; Perhaps we could first evaluate
; (setf (get 'current-acl2-world 'acl2-world-pair) nil)
; to install the empty world, and then call extend-world1 on old-wrld to
; reinstall that world.  That could be slow, however, and anyhow we do not
; expect to get here!  So we probably will wait until we get a complaint about
; this, if ever, before attempting such an enhancement.  In that case we might
; use acl2-query to see if the user really want to attempt such restoration.

                        "  Your session is not recoverable.  You may report ~
                         this issue to the ACL2 implementors, as a workaround ~
                         might be possible.")
                       (t ""))))
            (t (without-interrupts

; We expect undo-trip to be fast, except perhaps in the extremely rare case
; that we are re-memoizing when undoing an unmemoize triple and the compilation
; of the memoized function is expensive.  The simplicity of treating undo-trip
; atomically seems worth that very small exception.

                (undo-trip name world-key (car tl))
                (incf processed)))))
       (setf (car pair) wrld))

; Now clean up.

     (cond
      ((eq (car pair) wrld)
       (when (eq name 'current-acl2-world)
         (f-put-global 'current-acl2-world wrld state)
         (when (not (find-non-hidden-package-entry
                     (current-package state)
                     (known-package-alist state)))

; Note: Known-package-alist returns the new known packages because of a setf
; above!

           (f-put-global 'current-package "ACL2" state))

; It's not clear (as of this writing) that we need to update-wrld-structures if
; we are about to finish by calling retract-world1, but that seems safest and
; relatively cheap.

         (update-wrld-structures wrld state)))
      ((and (eq name 'current-acl2-world)
            (boundp '*bad-wrld*)
            *bad-wrld*))
      (t ; so, never executed (setf (car pair) wrld)

; We should never get here if retract-world1 was called from the cleanup form
; in extend-world1.  That's because the cleanup form is executed without
; interrupts and we don't expect errors or throws during the retraction
; process; thus, we expect the (setf (car pair) wrld) form above would have
; completed.

       (let ((w ; reflect the undo-trip calls that completed above
              (nthcdr processed old-wrld)))
         (setf (car pair) w)
         (when (eq name 'current-acl2-world)
           (f-put-global 'current-acl2-world w state)
           (format t
                   "~%~
                    ; *Note*: Interrupt or error detected while retracting~%~
                    ;         the ACL2 logical world; now extending the~%~
                    ;         world (~s triples) with interrupts disabled.~%~
                    ;         This may take awhile.~&~%"
                   processed)
           (finish-output))
         (extend-world1 name old-wrld))))))

; When we finally get past the unwind-protect above, even if the initial
; attempt is interrupted before proceeding to the cleanup form, we return wrld.

  wrld)

;                              VIRGINITY

; We do not want the ACL2 user to define any symbol that already has
; any sort of definition.

(defun-one-output virginp (name new-type)
  (and (symbolp name)
       (if (member-eq new-type '(function macro constrained-function t))
           (not (or (fboundp name)
                    (macro-function name)
                    (special-form-or-op-p name)))
         t)
       (if (member-eq new-type '(const stobj stobj-live-var t))
           (not (boundp name))
         t)))

(defun-one-output chk-virgin-msg2 (name new-type wrld state)
  (cond ((virginp name new-type) nil)
        ((f-get-global 'boot-strap-flg state)

; The test above is equivalent to (global-val 'boot-strap-flg wrld).

         (setf (get name '*predefined*) t)
         nil)

; A name regains its true virginity the moment we decide to give it a
; 'redefined property, which only happens just after the user has said that
; it's OK to redefine it.

        ((getpropc name 'redefined nil wrld)
         nil)
        (t
         (let ((reason
                (cond ((not (symbolp name)) "it is not a symbol")
                      ((member-eq new-type
                                  '(function macro constrained-function t))
                       (cond
                        ((special-form-or-op-p name) "it is a special form")
                        ((macro-function name) "it has a macro definition")
                        ((fboundp name) "it has a function definition")
                        (t "there is an inconsistency in the definition of ~
                            virginp and chk-virgin2")))
                      ((member-eq new-type '(const stobj stobj-live-var t))
                       (cond
                        ((boundp name) "it has a top level binding")
                        (t "there is an inconsistency in the definition of ~
                            virginp and chk-virgin2")))
                      (t "there is an inconsistency in the definition of ~
                          virginp and chk-virgin2")))
               (suggestion
                (let ((str "  If earlier you accidentally made this ~
                            definition or assignment outside the ACL2 ~
                            loop, then you might consider exiting the ~
                            ACL2 loop and executing appropriate ~
                            Common Lisp to erase those mistakes.  ~
                            This is a potentially perilous act unless ~
                            you are sure these names were introduced ~
                            by you and are not involved in any ~
                            logical code. ~#3~[~/To erase a function ~
                            or macro definition use (fmakunbound! ~
                            '~x0).  ~]~#4~[~/To erase a variable ~
                            setting use (makunbound '~x0). ~]"))
                  (cond ((not (symbolp name)) "")
                        ((member-eq new-type
                                    '(function macro constrained-function t))
                         (cond
                          ((special-form-or-op-p name) "")
                          (t str)))
                        (t ; (member-eq new-type '(const stobj
;                       stobj-live-var t))
                         str)))))
           (msg
            "It is illegal to define ~x0 because ~@1 in raw Common Lisp.~@2"
            name
            reason
            suggestion
            (if (member-eq new-type
                           '(function macro constrained-function t))
                1
              0)
            (if (member-eq new-type '(const stobj stobj-live-var t))
                1
              0))))))


;                           PACKAGE VIRGINITY

(defun-one-output chk-package-reincarnation-import-restrictions2
  (name proposed-imports)

; This routine returns nil or causes a hard error.  It is used in the
; implementation of the logical function chk-package-reincarnation-import-
; restrictions, which axiomatically always returns t but may cause this hard
; error (which can be thought of as a resource error).

; Note: The "2" in the name stems from chk-virgin2, which formerly played a
; similar role in chk-virgin but has been replaced by chk-virgin-msg.
; Chk-virgin1 has been lost in the mist of time, but
; chk-package-reincarnation-import-restrictions1 has never existed!

  (let ((pkg (find-package name))
        (temp (find-package-entry name *ever-known-package-alist*)))
    (cond
     (pkg
      (cond
       (temp
        (check-proposed-imports name temp proposed-imports)
        nil)
       ((member-equal name *defpkg-virgins*)
        nil)
       (t

; The package has been built in this Common Lisp but not by defpkg.

        (interface-er
         "It is illegal to defpkg ~x0 because a package of that name already ~
          exists in this lisp."
         name))))
     (t

; The package has never been built in this Common Lisp.

      nil))))

;                     ACL2 INITIALIZATION ROUTINES

#+gcl
(defvar user::*acl2-keep-tmp-files* nil)

(defun-one-output enter-boot-strap-mode (system-books-dir operating-system)

; If we interrupted an earlier initialization, the following form will undo it.
; This will set the *acl2-unwind-protect-stack* to nil because *ld-level* is
; 0 at the top.

  (acl2-unwind *ld-level* nil)

; Now provide a frame into which the set-w can push its acl2-unwind-protect
; forms.  An abort of the set-w will leave the forms in the frame so that the
; above acl2-unwind will undo them upon the next initialization attempt.  But
; if the set-w is successful, it will leave the then empty frame on the stack.

  (push nil *acl2-unwind-protect-stack*)
  (set-w 'retraction nil *the-live-state*)
  (do-symbols (sym (find-package "ACL2_GLOBAL_ACL2"))
              (makunbound sym))
  (do-symbols (sym (find-package
                    (concatenate 'string
                                 *global-package-prefix*
                                 *main-lisp-package-name*)))
              (makunbound sym))
  (do-symbols (sym (find-package "ACL2_GLOBAL_KEYWORD"))
              (makunbound sym))
  (initialize-state-globals)

; The following patch for save-gprof.lsp may be more heavy-handed than
; necessary, because maybe we don't need to keep all TMP* files.  See also
; "Note: temporary files" in save-gprof.lsp.

; If we want to let the user set other variables, we could replace
; user::*acl2-keep-tmp-files* with a variable whose value associates state
; global symbol names with initial values.  But then we will need to check that
; none is untouchable, and we will need to make a corresponding change in
; save-gprof.lsp.

  #+gcl
  (f-put-global 'keep-tmp-files user::*acl2-keep-tmp-files* *the-live-state*)
  (f-put-global 'global-enabled-structure
                (initial-global-enabled-structure "ENABLED-ARRAY-")
                *the-live-state*)
  (f-put-ld-specials *initial-ld-special-bindings* *the-live-state*)

; The next set-w will avail itself of the empty frame left above.

  (set-w 'extension
         (primordial-world operating-system)
         *the-live-state*)

; Set the system books directory now that the operating-system has been defined
; (needed by pathname-os-to-unix).

  (cond (system-books-dir
         (let* ((dir (unix-full-pathname
                      (cond
                       ((symbolp system-books-dir)
                        (symbol-name system-books-dir))
                       ((stringp system-books-dir)
                        system-books-dir)
                       (t (er hard 'initialize-acl2
                              "Unable to complete initialization, because ~
                                the supplied system books directory, ~x0, is ~
                                not a string."
                              system-books-dir)))))
                (msg (bad-lisp-stringp dir)))
           (when msg
             (interface-er
              "The value of the system-books-dir argument of ~
               ENTER-BOOT-STRAP-MODE, which is ~x0, is not a legal ACL2 ~
               string.~%~@1"
              dir msg))
           (f-put-global 'system-books-dir
                         (canonical-dirname! (maybe-add-separator dir)
                                             'enter-boot-strap-mode
                                             *the-live-state*)
                         *the-live-state*)))
        (t (f-put-global 'system-books-dir
                         (concatenate
                          'string
                          (canonical-dirname! (our-pwd)
                                              'enter-boot-strap-mode
                                              *the-live-state*)
                          "books/")
                         *the-live-state*)))

; Inhibit proof-tree output during the build, including pass-2 if present.

  (f-put-global 'inhibit-output-lst '(proof-tree) *the-live-state*)

; We now pop the empty frame.  There is no way this acl2-unwind will do any
; real work because only an abort would leave stuff in the frame and an abort
; would prevent us from getting here.  Note that in the scheme of things,
; namely within the control structure of initialize-acl2, it is strictly
; unnecessary for us to pop this empty frame: each LD called by initialize-acl2
; will unwind the stack back to nil.  But I do it here out of politeness: the
; stack started empty and ends that way.

  (acl2-unwind *ld-level* nil))

(defun-one-output move-current-acl2-world-key-to-front (wrld)

; This program sweeps the world and makes sure that the current acl2 world key
; is the first property on every property list upon which it is found.  We try
; to maintain that invariant in set-w where we always move the property up when
; we mess with a symbol's plist.  Of course, one must then wonder why this
; program is ever useful.  The reason is that in some lisps, e.g., AKCL, when
; you ask for the symbol-name of a symbol it has the side-effect of storing the
; string on the plist for future use.  Thus, for example, during booting of
; ACL2 we keep the world key at the front but then when we print the name of
; the event we accidentally cover the world key up with a SYSTEM:PNAME
; property.  This doesn't happen for every name.  Apparently for most we access
; the symbol-name during the processing and cause the property to come into
; existence and then store our world key in front of it.  But for some names we
; don't, apparently, ever access the symbol-name during processing and then our
; world key is covered up the first time the name is printed by ACL2.  Among
; the names so covered up by system properties are the names such as |Make
; RECOGNIZER-TUPLE record| INCLUDE-BOOK-ALIST, CERTIFICATION-TUPLE,
; TYPE-SET-INVERTER-RULES, PROVED-FUNCTIONAL-INSTANCES-ALIST, GENERALIZE-RULES,
; WELL-FOUNDED-RELATION-ALIST, WORLD-GLOBALS, and CHK-NEW-NAME-LST.  It is my
; theory that these names are simply never set a second time in booting and
; their initial setting is made before they are first printed.

; In any case, the following sweep takes only a second or two at the end of a
; boot and will make our world key the first property.  We hope to keep it that
; way in add-trip, but we cannot guarantee it, since the Lisp system might
; legally at anytime cover it up with some system property.

  (cond ((null wrld) nil)
        ((eq (car (symbol-plist (caar wrld))) *current-acl2-world-key*)
         (move-current-acl2-world-key-to-front (cdr wrld)))
        (t (let ((temp (get (caar wrld) *current-acl2-world-key*)))
             (cond (temp
                    (setf (symbol-plist (caar wrld))
                          (cons *current-acl2-world-key*
                                (cons temp
                                      (remove-current-acl2-world-key
                                       (symbol-plist (caar wrld)))))))))
           (move-current-acl2-world-key-to-front (cdr wrld)))))

(progn

; Warning: These definitions will replace both the raw Lisp and *1* definitions
; of the first argument of each defun-overrides call.  We must ensure that these
; definitions can't be evaluated when proving theorems unless each has
; unknown-constraints and never returns two values for the same input (which is
; automatically taken care of by passing in live states with unknown oracles).

  (defun-overrides mfc-ts-fn (term mfc state forcep)
    (mv-let (ans ttree)
            (mfc-ts-raw term mfc state forcep)
            (declare (ignore ttree))
            ans))
  (defun-overrides mfc-ts-ttree (term mfc state forcep)
    (mfc-ts-raw term mfc state forcep))

  (defun-overrides mfc-rw-fn (term obj equiv-info mfc state forcep)
    (mv-let (ans ttree)
            (mfc-rw-raw term nil obj equiv-info mfc 'mfc-rw state
                        forcep)
            (declare (ignore ttree))
            ans))
  (defun-overrides mfc-rw-ttree (term obj equiv-info mfc state forcep)
    (mfc-rw-raw term nil obj equiv-info mfc 'mfc-rw state forcep))

  (defun-overrides mfc-rw+-fn (term alist obj equiv-info mfc state forcep)
    (mfc-rw-raw term alist obj equiv-info mfc 'mfc-rw+ state forcep))
  (defun-overrides mfc-rw+-ttree (term alist obj equiv-info mfc state forcep)
    (mv-let (ans ttree)
            (mfc-rw-raw term alist obj equiv-info mfc 'mfc-rw+ state
                        forcep)
            (declare (ignore ttree))
            ans))

  (defun-overrides mfc-relieve-hyp-fn (hyp alist rune target bkptr mfc state
                                           forcep)
    (mfc-relieve-hyp-raw hyp alist rune target bkptr mfc state
                         forcep))
  (defun-overrides mfc-relieve-hyp-ttree (hyp alist rune target bkptr mfc
                                              state forcep)
    (mv-let (ans ttree)
            (mfc-relieve-hyp-raw hyp alist rune target bkptr mfc state
                                 forcep)
            (declare (ignore ttree))
            ans))

  (defun-overrides mfc-ap-fn (term mfc state forcep)
    (mfc-ap-raw term mfc state forcep)))

#+ccl
(defun stack-access-defeat-hook-default (fn)
  (declare (xargs :guard (symbolp fn)))
  (*1*-symbolp fn))

(defun-one-output exit-boot-strap-mode ()

; We need not unwind the *acl2-unwind-protect-stack* because it must be nil for
; us to have gotten here; had an abort occurred, leaving some frames on the
; stack, we would not get here.  The frame we push below is used by the set-w
; and then popped unless an abort occurs.

  (push nil *acl2-unwind-protect-stack*)
  (set-w 'extension
         (end-prehistoric-world (w *the-live-state*))
         *the-live-state*)
  (f-put-global 'boot-strap-flg nil *the-live-state*)
  (acl2-unwind *ld-level* nil)
  (f-put-global 'inhibit-output-lst nil *the-live-state*)
  (f-put-global 'slow-array-action :warning *the-live-state*)

; This is where to start up proof trees if we ever decide that this should be
; the default.  But probably we don't want to do it in MCL.

  (stop-proof-tree-fn *the-live-state*)
  (f-put-global 'ld-skip-proofsp nil *the-live-state*)
  (move-current-acl2-world-key-to-front (w *the-live-state*))
  #+hons
  (progn (initialize-never-memoize-ht)
         (acl2h-init-memoizations))
  #+ccl
  (when (boundp 'ccl::*stack-access-defeat-hook*)
    (locally (declare (special ccl::*stack-access-defeat-hook*))
             (setq ccl::*stack-access-defeat-hook*
                   'stack-access-defeat-hook-default)))
  (setq *hard-error-is-error* nil)
  nil)

(defun-one-output ld-alist-raw (standard-oi ld-skip-proofsp ld-error-action)
  `((standard-oi . ,standard-oi)
    (standard-co . ,*standard-co*)
    (proofs-co . ,*standard-co*)
    (current-package . "ACL2")
    (ld-skip-proofsp . ,ld-skip-proofsp)
    (ld-redefinition-action . nil)
    (ld-prompt . ,(if ld-skip-proofsp nil t))
    (ld-missing-input-ok . nil)
    (ld-pre-eval-filter . :all)
    (ld-pre-eval-print . ,(if ld-skip-proofsp nil t))
    (ld-post-eval-print . :command-conventions)
    (ld-evisc-tuple .

; In order to avoid printing huge forms during initialization when ld-ing files
; that are among the pass two files:

                    ,(abbrev-evisc-tuple *the-live-state*))
    (ld-error-triples . t)
    (ld-error-action . ,ld-error-action)
    (ld-query-control-alist . t)
    (ld-verbose . t)
    (ld-user-stobjs-modified-warning . nil)))

(defun enter-boot-strap-pass-2 ()
; We must provide set-w a frame on which to push its undo forms.
  (push nil *acl2-unwind-protect-stack*)
  (set-w 'extension
         (global-set 'boot-strap-pass-2 t (w *the-live-state*))
         *the-live-state*)
  (acl2-unwind *ld-level* nil)
  #+hons (memoize-init) ; for memoize calls in boot-strap-pass-2-b.lisp

; We use an explicit call of LD-fn to change the defun-mode to :logic just to
; lay down an event in the pre-history, in case we someday want to poke around
; at the boundary.

  (ld-fn (ld-alist-raw '((logic))
                       t
                       :error)
         *the-live-state* nil))

; The following constant should be changed when we add to the collection of
; files to be processed in :logic default-defun-mode.

(defconst *acl2-pass-2-files*

; Note that some books depend on "memoize", "hons", and "serialize", even in
; #-hons.  For example, community book books/misc/hons-help.lisp uses hons
; primitives.

  '("axioms"
    "memoize"
    "hons"
    "serialize"
    "boot-strap-pass-2-a"
    "apply-prim"
    "apply-constraints"
    "apply"
    "boot-strap-pass-2-b"
    ))

(assert (subsetp-equal *acl2-pass-2-files* *acl2-files*))

; Next we define fns-different-wrt-acl2-loop-only, used below in
; check-built-in-constants.

(defun our-update-ht (key val ht when-pass-2-p)

; We aim to store in ht all definitions associated with key, and here we add
; one definition, val.  Perhaps it is only necessary to store the most recent
; definition, but here we store them all, even though that is probably
; needlessly conservative for our purpose of finding where logical and raw Lisp
; definitions differ.

  (let ((old (gethash key ht))
        (val (if when-pass-2-p
                 (list :when-pass-2-p val)
               val)))
    (setf (gethash key ht)
          (cond ((and (consp old)
                      (eq (car old) :multiple))
                 (list* (car old) val (cdr old)))
                (old (list :multiple val old))
                (t val)))))

(defun note-fns-in-form (form ht when-pass-2-p)

; For every macro and every function defined by form, associate its definition
; with its name in the given hash table, ht.  See note-fns-in-files.

  (and (consp form)
       (case (car form)
         ((defun defund defn defproxy defun-nx defun-one-output defstub
            defmacro defmacro-untouchable defabbrev
            defun@par defmacro-last defun-overrides
            defun-with-guard-check defun-sk)
          (our-update-ht (cadr form) form ht when-pass-2-p))
         (save-def
          (note-fns-in-form (cadr form) ht when-pass-2-p))
         (defun-for-state
           (our-update-ht (defun-for-state-name (cadr form)) form ht when-pass-2-p))
         (define-global
           (our-update-ht (define-global-name (cadr form)) form ht when-pass-2-p)
           (our-update-ht (cadr form) form ht when-pass-2-p))
         ((define-pc-atomic-macro define-pc-bind* define-pc-help
            define-pc-macro define-pc-meta define-pc-primitive)
          (let ((name (make-official-pc-command
                       (if (eq (car form) 'define-pc-meta-or-macro-fn)
                           (nth 2 form)
                         (nth 1 form)))))
            (our-update-ht name form ht when-pass-2-p)))
         ((mutual-recursion mutual-recursion@par progn)
          (loop for x in (cdr form)
                do (note-fns-in-form x ht when-pass-2-p)))
         ((when-pass-2)

; When inside when-pass-2, since the #-acl2-loop-only definition of when-pass-2
; is nil, #-acl2-loop-only code is ignored.  So as we collect definitions
; inside when-pass-2, we add a special when-pass-2 marker to help us to cause
; an error (see fns-different-wrt-acl2-loop-only) when such #-acl2-loop-only
; code is detected.  Note also that merely being in a pass-2 file like
; apply.lisp may not be a problem: that is, putting the #-acl2-loop-only
; outside when-pass-2 is enough to get the raw lisp code to be noticed.

          (loop for x in (cdr form)
                do (note-fns-in-form x ht t)))
         ((encapsulate when)
          (loop for x in (cddr form)
                do (note-fns-in-form x ht when-pass-2-p)))
         (partial-encapsulate
          (loop for x in (cdddr form)
                do (note-fns-in-form x ht when-pass-2-p)))
         ((skip-proofs local)
          (note-fns-in-form (cadr form) ht when-pass-2-p))
         (defrec ; pick just one function introduced
           (our-update-ht (record-changer-function-name (cadr form)) form ht
                          when-pass-2-p))
         ((add-custom-keyword-hint
           add-macro-alias
           add-macro-fn
           assert
           #+ccl ccl:defstatic
           declaim
           def-basic-type-sets
           defwarrant
           defattach
           defaxiom
           defconst
           defconstant
           defequiv
           defg
           define-@par-macros
           define-atomically-modifiable-counter
           define-trusted-clause-processor ; should handle :partial-theory
           deflabel
           deflock
           defparameter
           defpkg
           defstruct
           deftheory
           defthm
           defthmd
           deftype
           defun-*1*
           defv
           defvar
           error
           eval ; presumably no ACL2 fn or macro underneath
           eval-when ; presumably no ACL2 fn or macro underneath
           f-put-global ; in axioms.lisp, before def. of set-ld-skip-proofsp
           in-package
           in-theory
           initialize-state-globals
           let ; could be arbitrarily complex, but we can only do so much!
           logic
           make-waterfall-parallelism-constants
           make-waterfall-printing-constants
           memoize
           push
           reset-future-parallelism-variables
           set-duplicate-keys-action
           set-guard-msg
           set-invisible-fns-table
           set-tau-auto-mode
           set-waterfall-parallelism
           setq
           system-events
           system-verify-guards
           table
           value
           verify-guards
           verify-termination-boot-strap

; We are generally unlikely to see make-event in our source files, since
; compilation is so restricted for them.  An exception is the make-event form
; in source file apply-prim.lisp, which is local and hence not compiled.  We
; make things easy on ourselves here and avoid trying to check make-event
; forms.

           make-event
           make-apply$-prim-body-fn-raw
           set-raw-mode
           set-compile-fns
           set-ignore-ok
           set-irrelevant-formals-ok)
          nil)
         (t
          (error "Unexpected type of form, ~s.  See note-fns-in-form."
                 (car form))))))

(defun note-fns-in-file (filename ht)

; For every macro and every function defined in the indicated file, associate
; its definition with its name in the given hash table, ht.  See
; note-fns-in-files.

  (with-open-file
   (str filename :direction :input)
   (let ((avrc (cons nil nil))
         x)
     (loop while (not (eq (setq x (read str nil avrc))
                          avrc))
           do
           (note-fns-in-form x ht nil)))))

(defun note-fns-in-files (filenames ht loop-only-p)

; For every macro and every function defined in filenames, associate its
; definition with its name in the given hash table, ht.  We read each file in
; filenames either with or without feature :acl2-loop-only, according to
; whether loop-only-p is true or false, respectively.

  (let ((*features* (if loop-only-p
                        (cons :acl2-loop-only *features*)
                      (remove :acl2-loop-only *features*))))
    (loop for filename in filenames
          do (note-fns-in-file filename ht))))

(defun raw-source-name-p (filename-without-extension)
  (let ((len (length filename-without-extension)))
    (and (<= 4 len)
         (equal (subseq filename-without-extension (- len 4) len)
                "-raw"))))

; Set the following to t for a more informative error report.
(defvar *check-built-in-constants-debug* nil)

(defun fns-different-wrt-acl2-loop-only (acl2-files)

; For each file in acl2-files we collect up all definitions of functions and
; macros, reading each file both with and without feature :acl2-loop-only.  We
; return (mv when-pass-2-result macro-result program-mode-result
; logic-mode-result), where each return value is a list of symbols unless debug
; variable *check-built-in-constants-debug* is true.  Each symbol is the name
; of a macro, program-mode function, or logic-mode function (respectively, for
; results other than when-pass-2-result) defined with feature :acl2-loop-only,
; which has a different (or absent) definition without feature :acl2-loop-only.
; However, when such a symbol has a definition (raw Lisp, logical, or both)
; under when-pass-2, it is put into the list when-pass-2-result rather than the
; other three.

; This function is typically called with acl2-files equal to *acl2-files*, in
; the build directory.  See the comment about redundant definitions in
; chk-acceptable-defuns-redundancy for a pertinent explanation.

  (flet ((when-pass-2-p (val)
                        (and (consp val)
                             (if (eq (car val) :multiple)
                                 (assoc-eq :when-pass-2-p (cdr val))
                               (eq (car val) :when-pass-2-p)))))
    (let ((logic-filenames (loop for x in acl2-files
                                 when (not (raw-source-name-p x))
                                 collect (concatenate 'string x ".lisp")))
          (raw-filenames (loop for x in acl2-files
                               collect (concatenate 'string x ".lisp")))
          (ht-raw (make-hash-table :test 'eq))
          (ht-logic (make-hash-table :test 'eq))
          (when-pass-2-result nil)
          (macro-result nil)
          (program-mode-result nil)
          (logic-mode-result nil)
          (wrld (w *the-live-state*)))
      (note-fns-in-files raw-filenames ht-raw nil)
      (note-fns-in-files logic-filenames ht-logic t)
      (maphash (lambda (key logic-val)
                 (progn
                   (assert (symbolp key))
                   (let ((raw-val (gethash key ht-raw)))

; We use equalp rather than equal below because in August, 2014 using SBCL
; 1.2.2 (and this might happen with other Lisps in the future), backquote was
; implemented using structures hence equal could fail.  For example, in SBCL
; 1.2.2 we found that (equalp '`,x '`,x) evaluates to t but (equal '`,x '`,x)
; evaluates to nil.  Here is why (again, in SBCL 1.2.2), where first we
; evaluate (setq *print-pretty* nil):

; * '`,x
;
; (SB-INT:QUASIQUOTE #S(SB-IMPL::COMMA :EXPR X :KIND 0))
; *

                     (or (equalp logic-val raw-val)
                         (let ((x (if *check-built-in-constants-debug*
                                      (list key :logic logic-val :raw raw-val)
                                    key))
                               (when-pass-2-p
                                (or (when-pass-2-p logic-val)
                                    (when-pass-2-p raw-val))))
                           (cond ((and when-pass-2-p

; Our approach makes it impossible to recognize exactly those cases in which
; #-acl2-loop-only code appears under a when-pass-2 call, which are the cases
; that we want to catch (since such code is always ignored, because when-pass-2
; calls expand to nil in raw Lisp).  A conservative approach is to cause an
; error whenever there is a discrepancy between the logic and raw values, but
; here we exempt one safe situation: there is no raw value inside when-pass-2.
; In that exceptional case, we fall through to the other branches of this COND.

                                       (not ; the exception is as follows:
                                        (and
                                         (eq (car logic-val) :when-pass-2-p)
                                         (consp raw-val)
                                         (if (eq (car raw-val) :multiple)
                                             (loop for form in (cdr raw-val)
                                                   always
                                                   (not
                                                    (and
                                                     (consp (car form))
                                                     (eq (car form)
                                                         :when-pass-2-p))))
                                           (not (eq (car raw-val)
                                                    :when-pass-2-p))))))
                                  (push x when-pass-2-result))
                                 ((getpropc key 'macro-body nil wrld)
                                  (push x macro-result))
                                 ((eq (symbol-class key wrld)
                                      :program)
                                  (push x program-mode-result))
                                 (t
                                  (push x logic-mode-result))))))))
               ht-logic)
      (maphash (lambda (key raw-val)
                 (progn
                   (assert (symbolp key))
                   (when (not (gethash key ht-logic))
                     (let ((x (if *check-built-in-constants-debug*
                                  (list key :raw raw-val)
                                key)))
                       (cond ((when-pass-2-p raw-val)
                              (push x when-pass-2-result))
                             ((assoc key *primitive-formals-and-guards*
                                     :test 'eq))
                             ((getpropc key 'macro-body nil wrld)
                              (push x macro-result))
                             (t (let ((c ; avoid symbol-class (defaults to :program)
                                       (getpropc key 'symbol-class nil wrld)))
                                  (when c
                                    (if (eq c :program)
                                        (push x program-mode-result)
                                      (push x logic-mode-result))))))))))
               ht-raw)
      (mv when-pass-2-result
          macro-result
          program-mode-result
          logic-mode-result))))

(defun collect-monadic-booleans (fns ens wrld)
  (cond ((endp fns) nil)
        ((and (equal (arity (car fns) wrld) 1)
              (ts= (mv-let (ts ttree)
                           (type-set (fcons-term* (car fns) '(V)) nil nil nil
                                     ens wrld
                                     nil nil nil)
                           (declare (ignore ttree))
                           ts)
                   *ts-boolean*))
         (cons (car fns)
               (collect-monadic-booleans (cdr fns) ens wrld)))
        (t (collect-monadic-booleans (cdr fns) ens wrld))))

(defun check-invariant-risk-state-p ()

; See the comment about this function in initialize-invariant-risk.

  (let ((bad
         (loop for tuple in *super-defun-wart-table*
               when
               (and (not (member-eq (car tuple)
                                    (global-val 'untouchable-fns
                                                (w *the-live-state*))))
                    (member-eq 'state (caddr tuple))

; The next two conjuncts say that there is some non-state input.

                    (cadr tuple)
                    (not (equal (cadr tuple) '(state)))
                    (not (member-eq (car tuple)

; It is important that for each of the following functions, its calls during
; evaluation in the ACL2 loop cannot cause state-p to become false of the live
; state -- unless of course one makes changes using ttags, such as removing
; symbols from the list of untouchable.  If that claim is false of any of these
; function symbols, then it should be added to the value of
; *boot-strap-invariant-risk-symbols* so that it can be given an
; 'invariant-risk property by initialize-invariant-risk.  Also see
; put-invariant-risk.

                                    '(READ-CHAR$
                                      READ-BYTE$
                                      READ-OBJECT
                                      PRINC$
                                      WRITE-BYTE$
                                      PRINT-OBJECT$-SER
                                      MAKUNBOUND-GLOBAL
                                      PUT-GLOBAL
                                      EXTEND-T-STACK
                                      SHRINK-T-STACK
                                      ASET-T-STACK
                                      SHRINK-32-BIT-INTEGER-STACK
                                      OPEN-INPUT-CHANNEL
                                      OPEN-OUTPUT-CHANNEL
                                      GET-OUTPUT-STREAM-STRING$-FN
                                      CLOSE-INPUT-CHANNEL
                                      CLOSE-OUTPUT-CHANNEL))))
               collect (car tuple))))
    (or (subsetp-eq bad
                    *boot-strap-invariant-risk-symbols*)
        (error "It is necessary to modify ~s to include the following ~
                list:~%~s"
               '*boot-strap-invariant-risk-symbols*
               (set-difference-eq bad
                                  *boot-strap-invariant-risk-symbols*)))))

(defun check-built-in-constants (&aux (state *the-live-state*))

; Certain defconsts are problematic because they build in values that one
; cannot know until the system is built!  Getting their values right requires
; some thought or experiment and even then subsequent changes to the system can
; render the values incorrect.  To guard against incorrect (obsolete) values
; for these constants, this function causes an error if doesn't like what it
; sees.  We document only one such constant, *force-xnume*, which more or less
; describes the situation suffered by all of them.

; Our Code requires that *force-xnume* be the nume of (:EXECUTABLE-COUNTERPART
; FORCE).  It would be nice to be able to write: (defconst *force-xnume*
; (fn-rune-nume 'force t t (w state))).  But that suffers TWO problems.  The
; first is that defconst disallows the use of any variable in the initial value
; form.  Thus, state is illegal above.  We tried fixing that, in a hypocritical
; way, by allowing it to ourselves in boot-strap even though we denied it to
; the user.  But even that doesn't work because of the second problem: The
; first time the defconst is processed, no numes are being allocated because
; everything is done in the :program defun-mode.  You might think, therefore,
; we ought to delay the execution of this defconst until after we've done the
; second pass and created the rune in question.  But we cannot do that because
; we use *force-xnume* in our code (namely, in ok-to-force) and that function
; can't be defined until *force-xnume* is defined.  Thus, this seemingly
; hackish way of doing it, where we actually specify ahead of time which nume
; will be assigned, is not as outlandish as it might at first seem.  We check
; that the actual assignment is correct (using this function) after booting.

; First we do a check on *boot-strap-invariant-risk-symbols* and
; *boot-strap-invariant-risk-symbols*.

  (check-invariant-risk-state-p)

  (let ((str "The defconst of ~x0 is ~x1 but should be ~x2.  To fix ~
              the error, change the offending defconst to the value ~
              indicated and rebuild the system.  To understand why the code ~
              is written this way, see the comment in ~
              check-built-in-constants."))
    (cond
     ((not (equal *force-xrune*
                  (fn-rune-nume 'force nil t (w state))))
      (interface-er str
                    '*force-xrune*
                    *force-xrune*
                    (fn-rune-nume 'force nil t (w state)))))
    (cond
     ((not (equal *force-xnume* (fn-rune-nume 'force t t (w state))))
      (interface-er str
                    '*force-xnume*
                    *force-xnume*
                    (fn-rune-nume 'force t t (w state)))))
    (cond
     ((not
       (equal *immediate-force-modep-xnume*
              (fn-rune-nume 'immediate-force-modep t t (w state))))
      (interface-er str
                    '*immediate-force-modep-xnume*
                    *immediate-force-modep-xnume*
                    (fn-rune-nume 'immediate-force-modep t t (w state)))))
    (cond
     ((not
       (equal *tau-system-xnume*
              (fn-rune-nume 'tau-system t t (w state))))
      (interface-er str
                    '*tau-system-xnume*
                    *tau-system-xnume*
                    (fn-rune-nume 'tau-system t t (w state)))))
    (cond
     ((not
       (equal *tau-acl2-numberp-pair*
              (getpropc 'acl2-numberp 'tau-pair)))
      (interface-er str
                    '*tau-acl2-numberp-pair*
                    *tau-acl2-numberp-pair*
                    (getpropc 'acl2-numberp 'tau-pair))))
    (cond
     ((not
       (equal *tau-integerp-pair*
              (getpropc 'integerp 'tau-pair)))
      (interface-er str
                    '*tau-integerp-pair*
                    *tau-integerp-pair*
                    (getpropc 'integerp 'tau-pair))))
    (cond
     ((not
       (equal *tau-rationalp-pair*
              (getpropc 'rationalp 'tau-pair)))
      (interface-er str
                    '*tau-rationalp-pair*
                    *tau-rationalp-pair*
                    (getpropc 'rationalp 'tau-pair))))
    (cond
     ((not
       (equal *tau-natp-pair*
              (getpropc 'natp 'tau-pair)))
      (interface-er str
                    '*tau-natp-pair*
                    *tau-natp-pair*
                    (getpropc 'natp 'tau-pair))))
    (cond
     ((not
       (equal *tau-bitp-pair*
              (getpropc 'bitp 'tau-pair)))
      (interface-er str
                    '*tau-bitp-pair*
                    *tau-bitp-pair*
                    (getpropc 'bitp 'tau-pair))))
    (cond
     ((not
       (equal *tau-posp-pair*
              (getpropc 'posp 'tau-pair)))
      (interface-er str
                    '*tau-posp-pair*
                    *tau-posp-pair*
                    (getpropc 'posp 'tau-pair))))
    (cond
     ((not
       (equal *tau-minusp-pair*
              (getpropc 'minusp 'tau-pair)))
      (interface-er str
                    '*tau-minusp-pair*
                    *tau-minusp-pair*
                    (getpropc 'minusp 'tau-pair))))
    (cond
     ((not
       (equal *tau-booleanp-pair*
              (getpropc 'booleanp 'tau-pair)))
      (interface-er str
                    '*tau-booleanp-pair*
                    *tau-booleanp-pair*
                    (getpropc 'booleanp 'tau-pair))))
    (cond
     ((not
       (and (equal
             *min-type-set*
             #-:non-standard-analysis -16384 #+:non-standard-analysis -131072)
            (equal
             *max-type-set*
             #-:non-standard-analysis 16383 #+:non-standard-analysis 131071)))
      (interface-er
       "The minimal and maximal type-sets are incorrectly built into the ~
        definition of type-alist-entryp.  These type-sets get generated by ~
        the call of def-basic-type-sets in type-set-a.lisp are must be ~
        mentioned, as above, in axioms.lisp.  Evidently, a new type-set bit ~
        was added.  Update type-alist-entryp.")))
    (cond
     ((not
       (equal *primitive-monadic-booleans*
              (collect-monadic-booleans
               (strip-cars *primitive-formals-and-guards*)
               (ens state)
               (w state))))
      (interface-er str
                    '*primitive-monadic-booleans*
                    *primitive-monadic-booleans*
                    (collect-monadic-booleans
                     (strip-cars *primitive-formals-and-guards*)
                     (ens state)
                     (w state)))))
    (cond
     ((not (getpropc 'booleanp 'tau-pair))
      (interface-er
       "Our code for tau-term assumes that BOOLEANP is a tau predicate.  But ~
        it has no tau-pair property!")))
    (let ((good-lst (chk-initial-built-in-clauses *initial-built-in-clauses*
                                                  (w state) nil nil)))
      (cond
       (good-lst
        (interface-er
         "The defconst of *initial-built-in-clauses* is bad because at least ~
          one of the records supplies an :all-fnnames that is different from ~
          that computed by all-fnnames-subsumer.  The correct setting is ~
          shown below. To preserve the comments in the source file it might ~
          be best to compare -- with EQUAL -- the elements below with the ~
          corresponding elements in the current source file and just replace ~
          the ones that have changed.  Here is a correct setting in 1:1 ~
          correspondence with the current setting: ~X01."
         `(defconst *initial-built-in-clauses*
            (list ,@good-lst))
         nil))))
    (cond ((not (equal *bbody-alist*
                       (merge-sort-lexorder
                        (loop for f in *definition-minimal-theory*
                              when (not (eq f 'mv-nth))
                              collect
                              (cons f (body f t (w *the-live-state*)))))))
           (interface-er
            "There is a discrepancy between the value of *bbody-alist* and ~
             its expected value.~%Actual value of ~
             *bbody-alist*:~%~X01~%Expected value of *bbody-alist*:~X21"
            *bbody-alist*
            nil
            (merge-sort-lexorder
             (loop for f in *definition-minimal-theory*
                   when (not (eq f 'mv-nth))
                   collect
                   (cons f (body f t (w *the-live-state*))))))))
    (mv-let (when-pass-2-result macros-found program-found logic-found)
      (fns-different-wrt-acl2-loop-only *acl2-files*)
      (flet ((my-diff (x y)
                      (if *check-built-in-constants-debug*
                          (loop for tuple in x
                                when (not (member (car tuple) y :test 'eq))
                                collect tuple)
                        (set-difference-eq x y))))
        (let ((bad-macros (my-diff macros-found
                                   *initial-macros-with-raw-code*))
              (bad-program (my-diff program-found
                                    *initial-program-fns-with-raw-code*))
              (bad-logic (my-diff logic-found
                                  *initial-logic-fns-with-raw-code*)))
          (when (or when-pass-2-result bad-macros bad-program bad-logic)
            (format t
                    "~%ERROR: Failed check for coverage of functions with~%~
                    acl2-loop-only code differences!  Please send this~%~
                    error message to the ACL2 implementors. Problems are~%~
                    as shown below; use *check-built-in-constants-debug* = t~%~
                    for a verbose report.~%~
                    Note: (lisp-implementation-type) =~%~
                    ~6t~s~%~
                    Note: (lisp-implementation-version) =~%~
                    ~6t~s~%~%"
                    (lisp-implementation-type)
                    (lisp-implementation-version))
            (when when-pass-2-result
              (format t
                      "The following have #-acl2-loop-only code within ~
                       (when-pass-2 ...):~%~s~%~%"
                      when-pass-2-result))
            (when bad-macros
              (format t
                      "The following macros differ in their #+acl2-loop-only~%~
                       and #-acl2-loop-only code:~%~s~%~
                       They probably should be added to ~s.~%~%"
                      bad-macros
                      '*initial-macros-with-raw-code*))
            (when bad-program
              (format t
                      "The following program-mode functions differ in their~%~
                       #+acl2-loop-only and #-acl2-loop-only code:~%~s~%~
                       They probably should be added to ~s.~%~%"
                      bad-program
                      '*initial-program-fns-with-raw-code*))
            (when bad-logic
              (format t
                      "The following logic-mode functions differ in their~%~
                       #+acl2-loop-only and #-acl2-loop-only code:~%~s~%~
                       They probably should be added to ~s.~%~%"
                      bad-logic
                      '*initial-logic-fns-with-raw-code*))
            (error "Check failed!")))))
    (let* ((wrld (w state))
           (fns (loop for fn in (append (strip-cars *ttag-fns*)
                                        *initial-untouchable-fns*)
                      when

; It is tempting to conjoin (logicp fn wrld) below.  But we want to include
; relevant program mode functions too, if any, in case the user converts them
; to logic mode.  We consider a #+acl2-save-unnormalized-bodies to be a hack,
; for which we include that logicp check in order to avoid an built-time error.

                      (and #+acl2-save-unnormalized-bodies (logicp fn wrld)
                           (getpropc fn 'unnormalized-body nil wrld)
                           (all-nils (stobjs-in fn wrld))
                           (all-nils (stobjs-out fn wrld)))
                      collect fn))
           (bad (set-difference-eq fns
; Avoid undefined constant warning during boot-strap by using symbol-value:
                                   (symbol-value '*blacklisted-apply$-fns*))))
      (when bad
        (interface-er
         "The value of *blacklisted-apply$-fns* fails to include ~&0.  This ~
          is an error because all functions from *ttag-fns* and ~
          *initial-untouchable-fns* must be in *blacklisted-apply$-fns*."
         bad)))

; The following is a start on checking that we don't have superfluous symbols
; in the list values of certain constants.  But in fact there can be such
; symbols: we want the value for each constant must be independent of
; features :hons or :acl2-par, yet some macros and functions are only defined
; when such features are present.  We may think more about this later.

;   (let ((undefined-macros
;          (loop for x in *initial-macros-with-raw-code*
;                when (not (or (macro-function x) (symbol-function x)))
;                collect x))
;         (undefined-program-fns
;          (loop for x in *initial-program-fns-with-raw-code*
;                when (not (fboundp x))
;                collect x))
;         (undefined-logic-fns
;          (loop for x in *initial-logic-fns-with-raw-code*
;                when (not (fboundp x))
;                collect x)))
;     (when undefined-macros
;       (format
;        t
;        "Undefined macros in *initial-macros-with-raw-code*:~%~s~%"
;        undefined-macros))
;     (when undefined-program-fns
;       (format
;        t
;        "Undefined macros in *initial-program-fns-with-raw-code*:~%~s~%"
;        undefined-program-fns))
;     (when undefined-logic-fns
;       (format
;        t
;        "Undefined macros in *initial-logic-fns-with-raw-code*:~%~s~%"
;        undefined-logic-fns))
;     (when (or undefined-macros undefined-program-fns undefined-logic-fns)
;       (error "Check failed!")))
    ))

(defun-one-output check-none-ideal (trips acc &aux (state *the-live-state*))
  (cond
   ((null trips)
    (cond ((null acc) nil)
          (t (er hard 'check-none-ideal
                 "The following are :ideal mode functions that are not ~
                  non-executable.  We rely in oneify-cltl-code on the absence ~
                  of such functions in the boot-strap world (see the comment ~
                  on check-none-ideal there); moreover, we want system ~
                  functions to execute efficiently, which might not be the ~
                  case for an :ideal mode function.  These functions should ~
                  have their guards verified: ~&0."
                 (remove-duplicates-eq acc)))))
   (t
    (let* ((trip (car trips))
           (fn (and (eq (car trip) 'event-landmark)
                    (eq (cadr trip) 'global-value)
                    (case (access-event-tuple-type (cddr trip))
                      (defun (access-event-tuple-namex (cddr trip)))
                      (defuns (car (access-event-tuple-namex (cddr trip))))
                      (otherwise nil)))))
      (cond ((and fn
                  (symbolp fn) ; always true?
                  (eq (symbol-class fn (w state))
                      :ideal)
                  (not (eq (getpropc fn 'non-executablep)
                           t)))
             (check-none-ideal (cdr trips) (cons fn acc)))
            (t (check-none-ideal (cdr trips) acc)))))))

(defun check-state-globals-initialized ()
  (let (bad)
    (do-symbols
     (sym (find-package "ACL2_GLOBAL_ACL2"))
     (when (boundp sym)
       (let ((acl2-sym (intern (symbol-name sym) "ACL2")))
         (when (not
                (or (assoc acl2-sym *initial-global-table* :test 'eq)
                    (assoc acl2-sym *initial-ld-special-bindings* :test 'eq)))
           (push (cons acl2-sym (symbol-value sym))
                 bad)))))
    (when bad
      (error
       "The following symbols, perhaps with the values shown, need to~%~
        be added to *initial-global-table*:~%~s~%"
       bad))))

(defun check-slashable ()

; First check that certain obviously slashable characters are marked as such.

  (let ((bad
         (loop for char in
               '(#\Newline #\Page #\Space #\Tab #\" #\# #\' #\( #\) #\, #\:
                 #\; #\\ #\`
                 #\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m #\n
                 #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z #\|)
               when (not (svref *slashable-array* (char-code char)))
               collect (char-code char))))
    (when bad
      (interface-er
       "The character code~#0~[~/s~] ~&0 must be associated with T in ~
        *slashable-array*."
       bad)))

; Next check that *slashable-chars* and *slashable-array* specify the same set
; of slashable characters.

  (let ((bad ; quadratic below, but 256^2 isn't big
         (loop for i from 0 to 255
               when (not (iff (member (code-char i) *slashable-chars*)
                              (svref *slashable-array* i)))
               collect i)))
    (when bad
      (interface-er
       "Each character code in the list ~x0 is marked as slashable in exactly ~
        one of *slashable-array* and *slashable-chars*; but those two ~
        structures are supposed to represent the same set of slashable ~
        characters."
       bad)))

; Finally, check that the set specified in *slashable-array* is sufficient for
; the current host Lisp.  See *slashable-array* for a comment on why this check
; is appropriate.

  (let ((bad
         (loop for i from 0 to 255
               when (let ((str (coerce (list (code-char i)
                                             #\A #\B
                                             (code-char i)
                                             #\U #\V
                                             (code-char i))
                                       'string)))
                      (and (not (eq (ignore-errors (read-from-string str))
                                    (intern str "ACL2")))
                           (not (svref *slashable-array* i))))
               collect i)))
    (when bad
      (interface-er
       "Each character code in the list ~x0 needs to be marked as slashable ~
        in both *slashable-array* and *slashable-chars*."
       bad))))

(defun check-some-builtins-for-executability ()

; The function logical-defun produces the logical definition of a given
; function symbol if there is one.  It does so by fetching the event for that
; symbol, but if that event is verify-termination-boot-strap, then
; logical-defun uses cltl-def-from-name to fetch the definition.  Now
; cltl-def-from-name generally returns the logical defun form, but for
; non-executable functions it returns a defun form intended for use in raw Lisp
; only (whose body is a call of throw-or-attach).  Here, we make sure that we
; do not hit that case.

; If we run across an error from this check, we can allow an exception for the
; offending function(s) provided we deal with those exceptions in the
; definition of logical-defun.

; This check might be coded more efficiently by walking through the world,, but
; it has taken only 0.06 seconds, which seems fine.

  (let ((wrld (w *the-live-state*)) ans)
    (do-symbols (fn (find-package "ACL2"))
                (when (and (eq (car (get-event fn wrld))
                               'verify-termination-boot-strap)
                           (getpropc fn 'non-executablep nil wrld))
                  (push fn ans)))
    (or (null ans)
        (interface-er
         "The initial ACL2 world has the following non-empty list of ~
          functions for which get-logical-defun will produce the wrong ~
          result:~%~x0.~%See ACL2 function check-executable-builtins for an ~
          explanation, or contact the ACL2 implementors."
         ans))))

(defun-one-output check-acl2-initialization ()
  (check-built-in-constants)
  (check-out-instantiablep (w *the-live-state*))
  (check-none-ideal (w *the-live-state*) nil)
  (check-state-globals-initialized)
  (or (plist-worldp-with-formals (w *the-live-state*))
      (error "The initial ACL2 world does not satisfy ~
              plist-worldp-with-formals!"))
  (check-slashable)
  (check-some-builtins-for-executability)
  nil)

(defun set-initial-cbd ()
  (let ((state *the-live-state*))
    (setq *initial-cbd* (our-pwd))

; In CCL, it seems that *initial-cbd* as computed above could give a string
; not ending in "/".  We fix that here.

    (cond ((and (stringp *initial-cbd*)
                (not (equal *initial-cbd* ""))
                (not (eql (char *initial-cbd*
                                (1- (length *initial-cbd*)))
                          #\/)))
           (setq *initial-cbd*
                 (concatenate 'string *initial-cbd* "/"))))
    (cond ((not (absolute-pathname-string-p
                 *initial-cbd*
                 t
                 (get-os)))
           (error
            "Our guess for the initial setting of cbd, ~x0, which was ~%~
              generated by (our-pwd), is not a legal directory!  Before ~%~
              entering ACL2, please setq *initial-cbd* to a nonempty ~%~
              string that represents an absolute ACL2 (i.e., Unix-style) ~%~
              pathname.  Sorry for the inconvenience."
            *initial-cbd*)))
    (f-put-global 'connected-book-directory *initial-cbd*
                  state)))

(defun initialize-acl2 (&optional (pass-2-ld-skip-proofsp 'include-book)
                                  (acl2-pass-2-files *acl2-pass-2-files*)
                                  system-books-dir
                                  skip-comp-exec
                                  &aux

; We avoid proclaiming types dynamically, instead doing so only via the
; acl2-proclaims.lisp mechanism.  See the Essay on Proclaiming.

                                  (*do-proclaims* nil))

; Note: if system-books-dir is supplied, it should be a Unix-style
; pathname (either absolute or not [doesn't matter which]).

; This function first lds all of the *acl2-files*, except
; boot-strap-pass-2-*.lisp and *-raw.lisp, in default-defun-mode :program
; (which is the default default-defun-mode).  It then loads the files in
; acl2-pass-2-files in :logic mode.

; During the first pass, ld-skip-proofsp is 'initialize-acl2, which is like the
; setting t (doing syntactic checks but skipping proofs and LOCALs) but omits a
; few of the checks so the bootstrapping can be done.  During the second pass,
; ld-skip-proofsp is as specified by the &optional parameter above.  It
; defaults to 'include-book, which means we skip LOCALs, all syntactic checks,
; and proofs.  By calling this function with pass-2-ld-skip-proofsp nil you can
; arrange for it to try to prove its way through the second pass.  However, see
; below.

; Why Two Passes?  By doing things in two passes we make it possible to use all
; system functions in hints and other proof commands.  In the one-pass
; initialization we used to use, it was impossible to use theory expressions in
; the defthms in axioms.lisp because the necessary theory functions were not
; yet defined and so trans-eval balked on them.

  (when (null system-books-dir)
    (let ((dir (getenv$-raw "ACL2_SYSTEM_BOOKS")))
      (when (and dir (not (equal dir "")))
        (setq system-books-dir dir))))

  (with-warnings-suppressed

; Interactive Proofs: Many times, (initialize-acl2 nil) -- which causes the
; system to prove the admissibility of everything done in the second pass --
; will fail because insufficient lemmas are available to handle new functions
; added since the last such proof.  But it will leave you in a state so that
; you can continue to develop proofs.  In particular, if you have changed some
; of the proved code, e.g., axioms.lisp, and you wish to re-verify it, you can
; proceed as follows.  First, fire up akcl.  Then do (acl2::load-acl2).
; Finally do (initialize-acl2 nil) and wait for the first proof to fail.  When
; it fails you will be returned to lisp.  There, in raw lisp, you should
; execute
;   (let ((state *the-live-state*))
;    (reset-ld-specials t)
; ;  (set-ld-redefinition-action '(:doit! . :overwrite) state) ;see below
;    )
; This will set the ld-specials to their conventional post-boot-strap setting,
; except (possibly) for ld-redefinition-action which will allow redefinition.
; (We discuss this more below.)  Then enter the loop with (LP!), which will set
; *features* to include :acl2-loop-only in case read conditionals are present
; in the sources you wish to develop.  Once in the loop, you should be able to
; continue as normal with proof development.

; If the initialization did not get beyond pass one, :q is undefined and the
; only way to exit is to do (mv nil :q state).  You will also note that other
; keyword commands, e.g., :pc, are unavailable.  You can always execute the
; appropriate form in raw lisp, e.g.,

; (let ((state *the-live-state*)) (pc 'fn))

; If you did get beyond pass one, things will be pretty normal looking except
; that inspection will show that both (global-val 'boot-strap-flg (w state))
; and (global-val 'boot-strap-pass-2 (w state)) are t.  This will manifest
; itself in some perhaps surprising ways during interactive proofs, e.g.,
; redundant deflabels are admitted during the second pass.

; Is Redefinition Permission Necessary?  Not always.  If you are re-verifying
; the sources the chances are you've changed something.  Suppose some event is
; no longer admissible.  If you have to change a function definition to admit
; it, i.e., one of your new events is incorrectly written, then redefinition
; permission is necessary because what you are trying to do is NOT just a
; simple reclassifying (you're changing the definition).  If on the other hand
; you are not changing definitions but adding them, you need not perform the
; set-ld-redefinition-action shown above.  A conservative thing to do is to
; leave the redefinition action nil and not set it until necessary.

; How do I Add a New Function Definition?  If you try to add to the sources a
; new function definition while in pass one of the initialization it will fail
; because we insist that all functions defined logically already have raw lisp
; definitions.  You should define the function first in raw lisp (by exiting
; the LP!) and then in the loop.  If you discovered this problem by provoking
; the hard error: ACL2 Error in ACL2-INTERFACE: fn is not fboundp! then you
; must first exit the lisp break with :q.  This will revert the world and throw
; you out of the LP!.  The world is as it was before the offensive definition,
; so you should define the function in raw lisp, reenter LP! and proceed as
; intended.

; The Special State Discussion: We bind state to *the-live-state* below because
; the macro expansion of ld introduces the variable state.  Once upon a time we
; declared state special with (defparameter state *the-live-state*) in this
; file.  But that had the effect of preventing tail-recursion removal in
; situations like (pprogn (princ$ ...) (recursive-call ...)) because pprogn
; macro expands to a binding of state and you can't jump out of a binding of a
; special in tail recursion (it is only allowed if it is lexical).  Thus, we
; got the curious and frustrating problem that if we recompiled system
; functions (like print-doc-string-part1) then they would no longer have tail
; recursions removed, even though the recursion would be so removed when we
; made the system from scratch.  (Reiterating the reason: between the two
; compilations of the function, state became special.  Had we declared state
; special in axioms.lisp instead of here in interface-raw.lisp, none of
; tail-recursion removal on state changing functions would have been done!)  We
; no longer make state special and hence must bind it to *the-live-state*
; lexically when its use is unavoidable.  In point of fact we now evaluate
; (setq state *the-live-state*) in (load-acl2), without making state special,
; and hence state may be used in raw Lisp after the system is loaded as long as
; the form using state is not compiled.

; Finally: another way to prove your way through axioms.lisp is to invoke
; (acl2::load-acl2) and (initialize-acl2), then save the system (e.g., in akcl
; execute (si::save-system "my-saved_acl2")), and now each time you invoke that
; saved image first execute

; (defconst *acl2-pass-2-files* '())

; in raw Lisp (or, execute this before saving the image), and then after
; executing (LP!) submit the form

; (set-w 'extension (global-set 'boot-strap-pass-2 t (w state)) state)

; to ACL2 in order to allow system DEFLABELs to be considered redundant.

; Save perhaps 12K in image.

   (set-initial-cbd)
   (makunbound '*copy-of-common-lisp-symbols-from-main-lisp-package*)
   (let* ((*features* (cons :acl2-loop-only *features*))
          #+akcl

; AKCL compiler note stuff.  We have so many tail recursive functions
; that the notes about tail recursion optimization are just too much
; to take.

          (compiler:*suppress-compiler-notes* t)
          (state *the-live-state*)
          pass-2-alist)
     (enter-boot-strap-mode system-books-dir (get-os))
     (setq pass-2-alist
           (let ((ans nil))
             (dolist
               (fl acl2-pass-2-files)
               (mv-let (erp val state)

; Warning.  Because of the read-file here, we have to be careful not to define
; any packages in the pass-2 files that contain symbols mentioned in those
; files.  The read-file will break in any such case; the DEFPKG in such a file
; must be processed first.

                 (read-file (coerce
                             (append (coerce fl 'list)
                                     (cons #\. (coerce *lisp-extension*
                                                       'list)))
                             'string)
                            *the-live-state*)
                 (declare (ignore state))
                 (cond (erp (interface-er "Unable to read file ~x0!"
                                          fl))
                       (t (push (cons fl val) ans)))))
             ans))
     (dolist
       (fl *acl2-files*)
       (when (not (or (equal fl "boot-strap-pass-2-a")
                      (equal fl "boot-strap-pass-2-b")
                      (raw-source-name-p fl)))
         (mv-let (er val st)
                 (ld-fn
                  (ld-alist-raw (or (cdr (assoc fl pass-2-alist :test #'equal))
                                    (coerce
                                     (append (coerce fl 'list)
                                             (cons #\. (coerce *lisp-extension*
                                                               'list)))
                                     'string))
                                'initialize-acl2
                                :error)
                  *the-live-state*
                  nil)
                 (declare (ignore val st))
                 (cond (er

; The load caused an error.  We abort quietly without doing anything
; else so we are in the same state.

                        (return-from initialize-acl2 nil))))))
     (enter-boot-strap-pass-2)
     (dolist
       (fl acl2-pass-2-files)
       (mv-let (er val st)
         (ld-fn
          (ld-alist-raw (or (cdr (assoc fl pass-2-alist :test #'equal))
                            (interface-er "Did not find ~x0 in pass-2-alist."
                                          fl))
                        pass-2-ld-skip-proofsp
                        :error)
          state
          nil)
         (declare (ignore val st))
         (cond (er

; The load caused an error.  We abort quietly without doing anything
; else so we are in the same state.

                (return-from initialize-acl2 nil)))))

; It is important not to wait to write out TMP1.lisp until after we leave the
; boot-strap.  By doing so before that time, we ensure that the guard-check
; under safe mode is made for primitives (see oneify-cltl-code), and that
; compile-uncompiled-*1*-defuns will not encounter 'exit-boot-strap-mode and
; thus stop finding functions to compile.  We use a call of ld here to make
; possible the subsidiary uses of state-global-let* on behalf of macroexpand1
; (see the comment in comp-fn for more information).

     (unless skip-comp-exec

; Optimization: Skip this compile for generate-acl2-proclaims.

       (ld '((comp-fn :exec nil "1" state))))
     (exit-boot-strap-mode)
     (initialize-pc-acl2 *the-live-state*)

; We now set up the ld specials as we wish them for the user's first
; invocation of LP.  The ld specials were previously initialized (in
; enter-boot-strap-mode) to the same values used below (because the
; LDs above make reference to some of them so they must be bound).
; But the LD above changes them so we now initialize them again.

     (f-put-ld-specials *initial-ld-special-bindings* *the-live-state*)

; We now check certain invariants, for example, that we have defined certain
; built-in constants correctly.

     (or (not acl2-pass-2-files)

; The check for check-built-in-constants in check-acl2-initialization, for one,
; will fail if we do not make a second pass through axioms.lisp.  That is
; because all (or at least most) of the 'level-no properties are still 0 before
; then, so chk-initial-built-in-clauses (called in check-built-in-constants)
; will fail, because its subroutine all-fnnames-subsumer does not behave
; properly until the 'level-no properties are set.

         (check-acl2-initialization))
     (cond
      ((or (not (probe-file *acl2-status-file*))
           (delete-file *acl2-status-file*))
       (with-open-file (str *acl2-status-file*
                            :direction :output)
                       (format str
                               "~s"

; The next token, :INITIALIZED, is used in GNUmakefile; keep in sync.

                               :INITIALIZED))))

     (setq *saved-build-date-lst*

; The call of eval below should avoid a warning in cmucl version 18d.  Note
; that saved-build-date-string is defined in interface-raw.lisp.

           (list (eval '(saved-build-date-string))))

; If you want the final image to have infixp = t (and have feature :acl2-infix
; set), then put the following form here:
;    (f-put-global 'infixp t *the-live-state*)

     t)))


;                                  LP

; Lp is the function that an ACL2 user invokes to get into the ACL2
; read-eval-print loop.

; Essay on Pathnames

; We use Unix-style pathnames everywhere in ACL2 except when interfacing with
; the operating system.  Functions defined in this file, interface-raw.lisp,
; generally use real pathname strings for the host operating system, which we
; call "OS filenames".  (Exceptions are clearly labeled, including
; compile-uncompiled-defuns and compile-uncompiled-*1*-defuns.)  Functions
; defined outside this file (interface-raw.lisp) pass around what we call "ACL2
; filenames", which are Unix-style pathname strings that consist solely of
; legal ACL2 characters, as checked by bad-lisp-stringp.

; Here are some examples of functions that take OS pathnames.

; acl2-compile-file [but see comment there]
; compile-file
; convert-book-name-to-compiled-name [ACL2 pathname is OK too]
; delete-file
; delete-compiled-file
; expansion-filename [ACL2 pathname is OK too]
; load
; probe-file
; proclaim-file

; Before defining lp, we provide support for inhibiting breaks.

#-(and gcl (not cltl2))
(defun our-abort (condition y
                            &aux
                            (state *the-live-state*)
                            (btp (member-eq
                                  (f-get-global 'debugger-enable *the-live-state*)
                                  '(:bt :break-bt :bt-break))))

; Keep this in sync with :doc set-debugger-enable.

  (declare (ignore y))
  #+acl2-par (setq *reset-parallelism-variables* t)
  (print-proof-tree-finish state)
  (when btp (print-call-history))
  (cond ((or (debugger-enabledp state)
             (eql *ld-level* 0)
             (f-get-global 'boot-strap-flg state))
         nil)
        (t
         (let ((*debugger-hook* nil) ; extra care to avoid possible loop
               #+ccl ; as above, for CCL revision 12090 and beyond
               (ccl::*break-hook* nil)
               (*package* (find-package (current-package state)))
               (continue-p

; If *acl2-time-limit-boundp* is true, then we can safely use our approach of
; continuing from the break (if possible) and letting the prover notice that
; *acl2-time-limit* is 0.  That allows the prover to quit sufficiently normally
; such that state global 'redo-flat-fail is bound in support of :redo-flat.
; The reason that *acl2-time-limit-boundp* needs to be true is that ultimately,
; we want *acl2-time-limit* to revert to its default value of nil.

                (and (find-restart 'continue)
                     *acl2-time-limit-boundp*
                     (not (eql *acl2-time-limit* 0)))))
           #+ccl ; for CCL revisions before 12090
           (declare (ignorable ccl::*break-hook*))
           (terpri t)
           (format t
                   "***********************************************")
           (cond
            (continue-p
             (format t
                     "~&Note:  ~A~
                      ~&  Will attempt to exit the proof in progress;~
                      ~&  otherwise, the next interrupt will abort the proof."
                     condition))
            (t
             (format t
                     "~&************ ABORTING from raw Lisp ***********")
             (format t
                     "~&********** (see :DOC raw-lisp-error) **********")

; In CCL we can get information about the function currently being executed.
; Consider for example what happens if, during a computation, the evaluation of
; (ash 1 (expt 2 48)) causes the error "Memory allocation request failed".
; That is not very helpful, but it could be helpful to see the following extra
; information about when this occurred:

; "While executing: CCL::BIGNUM-ASHIFT-LEFT-DIGITS."

; This extra information is a bit dodgy, since it comes from the low-level
; definition of function ccl::%break-message in CCL source file
; level-1/l1-readloop-lds.lisp (circa late 2017).  It is also may be unhelpful
; in many cases, or not ideal; for example, the same function as above,
; CCL::BIGNUM-ASHIFT-LEFT-DIGITS, is reported when attempting to evaluate (expt
; 2 (expt 2 48)).  However, you get what you get with raw Lisp errors, and we
; are happy to make them a bit more useful in some cases.

             (cond
              #+ccl
              ((and (fboundp 'ccl::%real-err-fn-name)
                    (boundp 'ccl::*top-error-frame*))
               (format t
                       "~&Error:  ~A~&While executing: ~S"
                       condition
                       (ccl::%real-err-fn-name ccl::*top-error-frame*)))
              (t
               (format t
                       "~&Error:  ~A"
                       condition)))))
           (when btp (format t "~%NOTE: See above for backtrace.~%"))
           (format t
                   "~&***********************************************~&")
           (when *acl2-error-msg*
             (format t *acl2-error-msg*))
           (when (not (untouchable-fn-p 'set-debugger-enable-fn
                                        (w state)
                                        (f-get-global 'temp-touchable-fns
                                                      state)))
             (format t
                     "~%To enable breaks into the debugger (also see :DOC ~
                      acl2-customization):~&~s~&"
                     '(set-debugger-enable t)))
           (force-output t)
           (cond (continue-p
                  (setq *acl2-time-limit* 0)
                  (invoke-restart 'continue))
                 (t

; Parallelism blemish: as of May 16, 2011, we also reset all parallelism
; variables in Rager's modified version of the source code.  However, that
; strikes Rager as strange, since we went through so much trouble to find out
; where we should reset parallelism variables. So, it is now commented out,
; today, May 16, 2011, and we will wait to see what happens.

;                  #+acl2-par
;                  (reset-all-parallelism-variables)

; Parallelism blemish: after a single proof runs for awhile, at least with
; waterfall parallelism enabled, it can take two interrupts before the abort
; occurs.  It would be nice if the proof could abort after the first interrupt,
; since when two interrupts are required, the summary does not print the
; ACL2(p) checkpoints.

                  (our-ignore-errors ; might not be in scope of catch
                    (throw 'local-top-level :our-abort))))))))

; We formerly set *debugger-hook* here, but now we set it in lp; see the
; comment there.

#+ccl ; for CCL revisions starting with 12090
(when (boundp 'ccl::*break-hook*)
  (setq ccl::*break-hook* 'our-abort))

(defun initial-customization-filename ()

; Every value returned by this function is either :none, nil, or a legal ACL2
; string.

  (let* ((cfb00 (getenv$-raw "ACL2_CUSTOMIZATION")) ; nil or legal ACL2 string
         (cfb0 (if (equal cfb00 "NONE")
                   :none
                 (and cfb00
                      (not (equal cfb00 ""))
                      (extend-pathname (f-get-global 'connected-book-directory
                                                     *the-live-state*)
                                       cfb00
                                       *the-live-state*)))))
    (cond
     ((eq cfb0 :none)
      :none)
     ((and cfb0 (probe-file cfb0))
      cfb0)
     (cfb0 ; but (not (probe-file cfb0))
      (let ((*print-circle* nil))
        (format t
                "~%ERROR: Environment variable ACL2_CUSTOMIZATION has value~%~
                 ~3T~a~%but file~%~3T~a~%does not appear to exist.~%~
                 Now quitting ACL2.  To fix this problem, you may wish~%~
                 to fix the value of that environment variable by setting it~%~
                 to a valid file name, by unsetting it, or by setting it to~%~
                 the empty string.~%~%"
                cfb00
                cfb0))
      (exit-lisp 1))
     (t
      (let* ((cb1 (our-merge-pathnames
                   (f-get-global 'connected-book-directory *the-live-state*)
                   "acl2-customization"))
             (cfb1 (string-append cb1 ".lsp"))
             (cfb1a (string-append cb1 ".lisp")))
        (cond
         ((probe-file (pathname-unix-to-os cfb1 *the-live-state*))
          cfb1)
         ((probe-file (pathname-unix-to-os cfb1a *the-live-state*))
          cfb1a)
         (t
          (let* ((home (our-user-homedir-pathname))
                 (cb2 (and home
                           (our-merge-pathnames

; The call of pathname-os-to-unix below may seem awkward, since later we apply
; pathname-unix-to-os before calling probe-file.  However, our-merge-pathnames
; requires Unix-style pathname arguments, and we prefer not to write an
; analogous function that takes pathnames for the host operating system.

                            (pathname-os-to-unix

; MCL does not seem to handle calls of truename correctly on logical pathnames.
; We should think some more about this, but for now, let's solve this problem
; by brute force.

                             #+(and mcl (not ccl))
                             (our-truename
                              (common-lisp::translate-logical-pathname
                               home)
                              t)
                             #-(and mcl (not ccl))
                             (our-truename home
                                           "Note: Calling OUR-TRUENAME from ~
                                            INITIAL-CUSTOMIZATION-FILENAME")
                             (os (w *the-live-state*))
                             *the-live-state*)
                            "acl2-customization")))
                 (cfb2 (and cb2 (string-append cb2 ".lsp")))
                 (cfb2a (and cb2 (string-append cb2 ".lisp"))))
            (cond (cb2 (cond ((probe-file (pathname-unix-to-os
                                           cfb2 *the-live-state*))
                              cfb2)
                             ((probe-file (pathname-unix-to-os
                                           cfb2a *the-live-state*))
                              cfb2a)
                             (t nil))))))))))))

#+(and acl2-par lispworks)
(setq system:*sg-default-size*

; Keep the below number in sync with the call to hcl:extend-current-stack in
; lp.

      80000)

#+(and acl2-par lispworks)
(defun spawn-extra-lispworks-listener ()

; In Lispworks, we spawn a thread for the listener before we exit lp for the
; first time, so that when we exit lp, multiprocessing does not stop.  This
; strategy is derived from the following quote, from Martin Simmons, of
; Lispworks.
;
; "If you want it to run a normal REPL, then you could call
; lw:start-tty-listener when acl2::lp returns.  That will make a new thread
; running the REPL, which will prevent multiprocessing from stopping."
;
; Another strategy, which was never released, involved following the
; multiprocessing example in section 15.13 of the Lispworks 6.0 manual.  To
; quickly outline that strategy, we (1) renamed "lp" to "lp1", (2) defined "lp"
; to spawn a thread that called "lp1", (3) saved the Lispworks image with the
; ":multiprocessing t" flag, and (4) ensured that the Lispworks image's restart
; function was acl2-default-restart-function, which called "lp".
;
; We feel that Martin's suggested implementation is simpler, and so we
; use that.
;
; We rely on the following property of lw:start-tty-listener: if the tty
; listener is already running, calling lw:start-tty-listener does nothing.

  (lw:start-tty-listener))

(#+allegro

; Builds with Allegro CL warn that this constant is redefined, when using
; defconstant.  We could probably use defparameter in all Lisps, but we really
; want this to be a constant; in particular, there is no reason to let-bind
; it.  In order to avoid the warning in Allegro CL, we conditionalize here.

 defparameter
 #-allegro
 defconstant
 *our-standard-io*

; We bind *debug-io* to this constant inside LP to ensure that when the
; debugger is invoked, it will write to the standard output rather than to the
; terminal (unless *debug-io* is rebound, as in community books file
; books/centaur/vl2014/server/server-raw.lsp).  Formerly we bound *debug-io* to
; *standard-output* in LP, which would cause an infinite loop in the SBCL
; debugger as described below.  We thank Keshav Kini for the current approach,
; and for bringing this problem to our attention.  As described below, this
; approach ensures that debugger output is printed to standard output, not to
; the terminal, but without binding *debug-io* to an output-only stream.

; Below is some discussion showing how we formerly got this wrong and
; progressed towards the current solution.  Before making changes
; related to this constant, be sure to understand the issues raised in
; that discussion.

; (1) Git commit 26013676ec22cd68e29be0a43f9cbf2aeee2114e on Feb 5, 2016
;     provided a fix for problem described in the following quote from :doc
;     note-7-3.

;       It was possible for a backtrace to be printed to the terminal by SBCL
;       and CMUCL, even when output is redirected to a file. This has been
;       fixed.

;     The fix was for ACL2 function print-call-history to print backtraces to
;     *standard-output*, rather than to the default stream, *debug-io*.
;
; BUT that fix caused a problem:
;
; (2) Commit 6d7ad53ecdaaec9dcf3e3d05c19832b97fa7062a on Aug 26, 2016 provided
;     a fix for GitHub Issue 634 (https://github.com/acl2/acl2/issues/634),
;     namely, printing of a backtrace to the terminal.  The problem had been
;     that for SBCL (and CMUCL), print-call-history was sending its output to
;     *standard-output* instead of *debug-io*, so the rebinding of *debug-io*
;     in community books file books/centaur/vl2014/server/server-raw.lsp had no
;     effect on where print-call-history sent its output: that output was going
;     to *standard-output*, hence to a .cert.out file.  The fix was to avoid
;     the use of *standard-output* in print-call-history, instead binding
;     *debug-io* to *standard-output* in LP.  That solution still handles (1)
;     by sending backtraces to *standard-output* by default; but now, the
;     redirection in server-raw.lsp, by rebinding *debug-io*, works as
;     intended.

; BUT that fix caused a problem: with *debug-io* bound to *standard-output*, a
; horrible infinite loop could occur in SBCL when trying to read from
; *debug-io*, as shown in this item, formerly in community books file
; books/system/to-do.txt, for obtaining that infinite loop in ACL2 but not in
; pure SBCL:

; (value :q)
; (LP!) ; only in ACL2
; #+acl2-loop-only (program)
; (defun foo (x) (declare (optimize (safety 0))) (car x))
; #+acl2-loop-only (set-debugger-enable t)
; (foo 3)
;
; So now, in LP we bind *debug-io* to *our-standard-io* instead of
; *standard-output*, thus guaranteeing that debugger output is sent to standard
; output rather than the terminal, without the mistake of binding *debug-io* to
; an output-only stream.

  (make-two-way-stream *standard-input* *standard-output*))

(defun lp (&rest args)

; This function can only be called from within raw lisp, because no ACL2
; function mentions it.  Thus, we assume we are in raw lisp.  This is the
; top-level entry to ACL2.  Note that truename can cause an error in some
; Common Lisps when the given file or directory does not exist, in which case
; our-truename will generally return nil.  Hence, we sometimes call
; our-truename on "" rather than on a file name.

  (when args
    (error "LP takes no arguments."))

  (when (not *acl2-default-restart-complete*)
    (acl2-default-restart t)
    #+gcl
    (save-acl2-in-akcl nil nil nil t))

  (with-more-warnings-suppressed

; Parallelism wart: we currently reset the parallelism variables twice on
; startup.  Removing the below call to reset-all-parallelism-variables should
; be the correct way to remove this double-reset, because we more thoroughly
; determine where to reset parallelism variables elsewhere in the code.

   #+acl2-par
   (reset-all-parallelism-variables)

; Remark for #+acl2-par.  Here we set the gc-threshold to a high number.  If
; the Lisps support it, this threshold could be based off the actual memory in
; the system.  We perform this setting of the threshold in lp, because Lispworks
; doesn't save the GC configuration as part of the Lisp image.

; Parallelism no-fix: the threshold below may cause problems for machines with
; less than that amount of free RAM.  At a first glance, this shouldn't
; realistically be a problem.  However, a user might actually encounter this
; problem when running several memory-intensive ACL2(p) sessions in parallel
; via make -j.

   #+acl2-par
   (when (not *lp-ever-entered-p*) (set-gc-threshold$ (expt 2 30) nil))

   #+(and acl2-par lispworks)
   (when (not *lp-ever-entered-p*)
     (sys:set-default-segment-size 0 :cons 250)
     (sys:set-default-segment-size 1 :cons 250)
     (sys:set-default-segment-size 2 :cons 250)
     (sys:set-default-segment-size 0 :other 250)
     (sys:set-default-segment-size 1 :other 250)
     (sys:set-default-segment-size 2 :other 250))

   #+acl2-par
   (f-put-global 'parallel-execution-enabled t *the-live-state*)
   (let ((state *the-live-state*)
         #+(and gcl (not cltl2))
         (system::*break-enable* (debugger-enabledp *the-live-state*))
         (*debug-io* *our-standard-io*))
     (cond
      ((> *ld-level* 0)
       (when (raw-mode-p *the-live-state*)
         (fms "You have attempted to enter the ACL2 read-eval-print loop from ~
               within raw mode.  However, you appear already to be in that ~
               loop.  If your intention is to leave raw mode, then execute:  ~
               :set-raw-mode nil.~|"
              nil (standard-co *the-live-state*) *the-live-state* nil))
       (return-from lp nil))
      ((not *lp-ever-entered-p*)
       (f-put-global 'saved-output-reversed nil state)
       (push-current-acl2-world 'saved-output-reversed *the-live-state*)
       (set-initial-cbd)
       (eval `(in-package ,*startup-package-name*)) ;only changes raw Lisp pkg

; We formerly set *debugger-hook* at the top level using setq, just below the
; definition of our-abort.  But that didn't work in Lispworks, where that value
; persisted right up to the saving of an image yet *debugger-hook* was nil
; after starting up that image.  Apparently Lispworks 6.0 sets *debugger-hook*
; globally to nil when input comes from a file, which is how ACL2 is built,
; rather than standard-input,

       #-(and gcl (not cltl2))
       (setq *debugger-hook* 'our-abort)

; We have found it necessary to extend the LispWorks stack size, in particular
; for community books books/concurrent-programs/bakery/stutter2 and
; books/unicode/read-utf8.lisp.

       #+lispworks (hcl:extend-current-stack 400)

; David Rager agrees that the following block of code is fine to delete (note
; that as of 11/2017 (hcl:current-stack-length) is 399998 when ACL2 comes up,
; built on 64-bit LispWorks), though he wonders if it is needed for 32-bit
; LispWorks.  We'll leave it as a comment in case something like it is useful
; in the future.

;;;        #+(and lispworks acl2-par)
;;;        (when (< (hcl:current-stack-length)
;;;
;;; ; Keep the below number (currently 80000) in sync with the value given to
;;; ; *sg-default-size* (set elsewhere in our code).
;;;
;;;                 80000)
;;;          (hcl:extend-current-stack
;;;
;;; ; this calculation sets the current stack length to be within 1% of 80000
;;;
;;;           (- (round (* 100 (/ (hcl:current-stack-length) 80000))) 100)))

       #+sbcl
       (define-our-sbcl-putenv) ; see comment on this in acl2-fns.lisp

; Acl2-default-restart isn't enough in Allegro, at least, to get the new prompt
; when we start up:

       (let* ((save-expansion (let ((s (getenv$-raw "ACL2_SAVE_EXPANSION")))
                                (and s
                                     (not (equal s ""))
                                     (not (equal (string-upcase s)
                                                 "NIL")))))
              (book-hash-alistp-env

; A non-nil value of this variable indicates that we are to use the "book-hash"
; mechanism of storing an alist in the .cert file, instead of a numeric
; checksum.  Starting in June 2016, storing such an alist is the default.  That
; default is defeated when the indicated environment variable is empty or (up
; to case) "NIL".

               (let ((s (getenv$-raw "ACL2_BOOK_HASH_ALISTP")))
                 (or (null s) ; default case
                     (not (equal (string-upcase s)
                                 "NIL")))))
              (os-user-home-dir-path (our-user-homedir-pathname))
              (os-user-home-dir0 (and os-user-home-dir-path
                                      (our-truename os-user-home-dir-path
                                                    "Note: Calling OUR-TRUENAME ~
                                                  from LP.")))
              (os-user-home-dir (and os-user-home-dir0
                                     (if (eql (char os-user-home-dir0
                                                    (1- (length os-user-home-dir0)))
                                              *directory-separator*)
                                         (subseq os-user-home-dir0
                                                 0
                                                 (1- (length os-user-home-dir0)))
                                       os-user-home-dir0)))
              (user-home-dir (and os-user-home-dir
                                  (pathname-os-to-unix
                                   os-user-home-dir
                                   (os (w *the-live-state*))
                                   *the-live-state*)))
              (system-dir0 (let ((str (getenv$-raw "ACL2_SYSTEM_BOOKS")))
                             (and str
                                  (maybe-add-separator str)))))
         (when save-expansion
           (f-put-global 'save-expansion-file t *the-live-state*))
         (when book-hash-alistp-env
           (f-put-global 'book-hash-alistp t *the-live-state*))
         (when user-home-dir
           (f-put-global 'user-home-dir user-home-dir *the-live-state*))
         (when system-dir0 ; needs to wait for user-homedir-pathname
           (f-put-global
            'system-books-dir
            (canonical-dirname!
             (unix-full-pathname
              (expand-tilde-to-user-home-dir
               system-dir0 ; from getenv$-raw, hence a legal ACL2 string
               (os (w *the-live-state*))
               'lp
               *the-live-state*))
             'lp
             *the-live-state*)
            *the-live-state*)))
       (set-gag-mode-fn :goals *the-live-state*)
       #-hons
; Hons users are presumably advanced enough to tolerate the lack of a
; "[RAW LISP]" prompt.
       (install-new-raw-prompt)
       #+hons (f-put-global 'serialize-character-system #\Z state)
       #+(and (not acl2-loop-only) acl2-rewrite-meter)
       (setq *rewrite-depth-alist* nil)

; Without the following call, it was impossible to read and write with ACL2 I/O
; functions to *standard-co* in CLISP 2.30.  Apparently the appropriate Lisp
; streams at the time of the build were closed when the ACL2 image was brought
; up.  So we "refresh" the appropriate property lists with the current such
; Lisp streams.

       (setup-standard-io)

; The following applies to CLISP 2.30, where charset:iso-8859-1 is defined, not to
; CLISP 2.27, where charset:utf-8 is not defined.  It apparently has to be
; executed in the current Lisp session.  We tried executing the following form
; before saving an image, but the value of custom:*default-file-encoding* at
; startup was #<ENCODING CHARSET:ASCII :UNIX>.

       #+(and clisp unicode)
       (setq custom:*default-file-encoding* charset:iso-8859-1)
       (let ((customization-full-file-name
              (initial-customization-filename)))
         (cond
          ((or (eq customization-full-file-name :none)
               (f-get-global 'boot-strap-flg state))
           nil)
          (customization-full-file-name

; If the ACL2 customization file exists (and we are not booting) then it hasn't
; been included yet, and we include it now.

           (let ((quietp (let ((s (getenv$-raw "ACL2_CUSTOMIZATION_QUIET")))
                           (and s
                                (not (equal s ""))
                                (not (string-equal s "NIL"))
                                (if (string-equal s "ALL") :all t)))))
             (when (not quietp)
               (fms "Customizing with ~x0.~%"
                    (list (cons #\0 customization-full-file-name))
                    *standard-co*
                    state
                    nil))
             (let ((ld-alist (put-assoc-eq
                              'standard-oi
                              customization-full-file-name
                              (put-assoc-eq
                               'ld-error-action :return
                               (f-get-ld-specials *the-live-state*))))
                   #+acl2-infix (old-infixp
                                 (f-get-global 'infixp *the-live-state*)))
               #+acl2-infix (f-put-global 'infixp nil *the-live-state*)
               (with-suppression ; package locks, not just warnings, for read
                (state-free-global-let*
                 ((connected-book-directory
                   (f-get-global 'connected-book-directory state)))
                 (cond (quietp

; We avoid using with-output!, since it generates a call of state-global-let*,
; which isn't allowed outside the loop -- which we haven't yet entered!

                        (state-free-global-let*
                         ((inhibit-output-lst *valid-output-names*)
                          (gag-mode nil)
                          (print-clause-ids nil))
                         (let ((quiet-alist ld-alist))
                           (loop for pair in
; Warning: Keep quiet-alist in sync with the state-free-global-let* bindings
; below.
                                 '((ld-verbose . nil)
                                   (ld-pre-eval-print . :never)
                                   (ld-post-eval-print . nil)
                                   (ld-prompt . nil))
                                 do (setq quiet-alist
                                          (put-assoc-eq (car pair)
                                                        (cdr pair)
                                                        quiet-alist)))
                           (cond
                            ((eq quietp :all)
                             (ld-fn quiet-alist *the-live-state* nil))
                            (t
                             (state-free-global-let*
; Warning: Keep these bindings in sync with quiet-alist.
                              ((ld-verbose nil)
                               (ld-pre-eval-print :never)
                               (ld-post-eval-print nil)
                               (ld-prompt nil))
                              (ld-fn quiet-alist *the-live-state* nil)))))))
                       (t (ld-fn ld-alist *the-live-state* nil)))))
               #+acl2-infix
               (f-put-global 'infixp old-infixp *the-live-state*))))))
       (let ((val (getenv$-raw "ACL2_CHECK_INVARIANT_RISK")))
         (when (and val (not (equal val "")))
           (let* ((val1 (string-upcase val))
                  (val2 (cond
                         ((equal val1 "NIL") nil)
                         ((equal val1 "T") t)
                         ((member-equal val1 '(":ERROR" "ERROR"))
                          :ERROR)
                         ((member-equal val1 '(":WARNING" "WARNING"))
                          :WARNING)
                         (t (error "Error detected in ~
                                    initialize-state-globals:~%Illegal value, ~
                                    ~s, for environment variable ~
                                    ACL2_CHECK_INVARIANT_RISK.~%See :DOC ~
                                    invariant-risk."
                                   val1)))))
             (ld-fn (put-assoc-eq
                     'standard-oi
                     `((set-check-invariant-risk ,val2))
                     (put-assoc-eq 'ld-pre-eval-print
                                   t
                                   (f-get-ld-specials *the-live-state*)))
                    *the-live-state*
                    t))))
       (f-put-global 'ld-error-action :continue *the-live-state*)))
     (with-suppression ; package locks, not just warnings; to read 'cl::foo
      (cond ((and *return-from-lp*
                  (not *lp-ever-entered-p*))
             (f-put-global 'standard-oi
                           `(,*return-from-lp* (value :q))
                           *the-live-state*)
             (setq *return-from-lp* nil)
             (setq *lp-ever-entered-p* t)
             (state-free-global-let*
              ((ld-verbose nil)
               (ld-prompt nil)
               (ld-post-eval-print nil))
              (ld-fn (f-get-ld-specials *the-live-state*)
                     *the-live-state*
                     nil)))
            (t (setq *lp-ever-entered-p* t)
               (f-put-global 'standard-oi *standard-oi* *the-live-state*)
               (cond
                (*lp-init-forms*
                 (let ((standard-oi (append *lp-init-forms* *standard-oi*)))
                   (setq *lp-init-forms* nil)
                   (ld-fn (put-assoc-eq 'standard-oi
                                        standard-oi
                                        (f-get-ld-specials *the-live-state*))
                          *the-live-state*
                          nil)))
                (t (ld-fn (f-get-ld-specials *the-live-state*)
                          *the-live-state*
                          nil)))
               (fms "Exiting the ACL2 read-eval-print loop.  To re-enter, ~
                     execute (LP)."
                    nil *standard-co* *the-live-state* nil))))
     #+(and acl2-par lispworks)
     (spawn-extra-lispworks-listener)
     (values))))

(defmacro lp! (&rest args)
  `(let ((*features* (add-to-set-eq :acl2-loop-only *features*)))
     (lp ,@args)))

;                   COMPILING, SAVING, AND RESTORING

#+ccl
(defun stack-access-defeat-hook-cert-ht ()

; This function either returns nil or, if ccl::*stack-access-winners* is bound
; to a hash-table, a hash-table whose keys are names of currently-known
; "winners".  Each such name is the name of a function FN that is a key of
; ccl::*stack-access-winners* such that FN is the current symbol-function of
; FN.

  (let ((ccl-ht
         (and (boundp 'ccl::*stack-access-winners*)
              (symbol-value 'ccl::*stack-access-winners*))))
    (and (hash-table-p ccl-ht)
         (let ((ht (make-hash-table :test 'eq)))
           (maphash (lambda (key val)
                      (when (and val
                                 (symbolp val)
                                 (fboundp val)
                                 (eq key (symbol-function val)))
                        (setf (gethash val ht) t)))
                    ccl-ht)
           ht))))

#+ccl
(defvar *stack-access-defeat-hook-cert-ht* nil)

#+ccl
(defun stack-access-defeat-hook-cert (fn)

; This function assumes that *stack-access-defeat-hook-cert-ht* is bound to a
; hash-table of names of "winners"; see function
; stack-access-defeat-hook-cert-ht.

  (and (symbolp fn)
       (not (gethash fn *stack-access-defeat-hook-cert-ht*))))

(defun acl2-compile-file (full-book-name os-expansion-filename)

; Full-book-name is an ACL2 pathname, while os-expansion-filename is an OS
; pathname; see the Essay on Pathnames.  We compile os-expansion-filename but
; into the compiled filename corresponding to full-book-name.

; To compile os-expansion-filename, we need to make sure that uses in the file
; of backquote and comma conform in meaning to those that were in effect during
; certification.

; We assume that this function is called only after forms in the given
; full-book-name have already been evaluated and (if appropriate) proclaimed,
; hence in particular so that macros have been defined.

  (progn
   (chk-book-name full-book-name full-book-name 'acl2-compile-file
                  *the-live-state*)
   (let ((*defeat-slow-alist-action* t)
         (*readtable* *acl2-readtable*)
         (ofile (convert-book-name-to-compiled-name
                 (pathname-unix-to-os full-book-name *the-live-state*)
                 *the-live-state*))
         (stream (get (proofs-co *the-live-state*)
                      *open-output-channel-key*)))

; It is tempting to evaluate (proclaim-file os-expansion-filename).  However,
; all functions in full-book-name were presumably already proclaimed, as
; appropriate, during add-trip.

     (let ((*readtable* *reckless-acl2-readtable*)

; We reduce the compiled file size produced by CCL, even in the #+hons case
; where we may have set ccl::*save-source-locations* to t.  We have seen an
; example where this binding reduced the .dx64fsl size from 13696271 to 24493.

           #+ccl (ccl::*save-source-locations* nil))
       (cond
        #+ccl
        (*stack-access-defeat-hook-cert-ht*
         (let ((ccl::*stack-access-defeat-hook*
                'stack-access-defeat-hook-cert))
           (declare (special ccl::*stack-access-defeat-hook*))
           (compile-file os-expansion-filename :output-file ofile)))
        (t (compile-file os-expansion-filename :output-file ofile))))

; Warning: Keep the following "compile on the fly" readtime conditional in sync
; with the one in initialize-state-globals.  Here, we avoid loading the
; compiled file when compiling a certified book, because all functions are
; already compiled.

     #-(or ccl sbcl)
     (let ((*compiling-certified-file*

; See the comment about an optimization using *compiling-certified-file* in the
; raw Lisp definition of acl2::defconst.

            t)
           (alist (and (hons-enabledp *the-live-state*)
                       (loop for pair in
                             (table-alist 'memoize-table (w *the-live-state*))
                             when (fboundp (car pair)) ; always true?
                             collect (cons (car pair)
                                           (symbol-function (car pair)))))))
       (load-compiled ofile t)
       (loop for pair in alist
             when (not (eq (symbol-function (car pair))
                           (cdr pair)))
             do (setf (symbol-function (car pair))
                      (cdr pair)))
       (terpri stream)
       (prin1 ofile stream))
     (terpri stream)
     (terpri stream))))

(defun-one-output delete-auxiliary-book-files (full-book-name)
  (let* ((file (pathname-unix-to-os full-book-name *the-live-state*))
         (ofile (convert-book-name-to-compiled-name file *the-live-state*))
         (efile (expansion-filename file))
         (err-string "A file created for book ~x0, namely ~x1, exists and ~
                      cannot be deleted with Common Lisp's delete-file.  We ~
                      do not know for sure whether this file was produced by ~
                      ACL2 and we do not even know that it corresponds to the ~
                      book ~x0.  If ~x1 exists at the time of an ~
                      (include-book ~x0), it might be erroneously loaded, ~
                      possibly causing inconsistency."))
    (when (probe-file ofile)
      (cond ((delete-file ofile) nil)
            (t (er hard 'delete-auxiliary-book-files
                   err-string
                   full-book-name ofile))))
    #+clisp
    (let* ((len (length file))
           (lib-file (assert$ (equal (subseq file (- len 5) len) ".lisp")
                              (concatenate 'string
                                           (subseq file 0 (- len 5))
                                           ".lib"))))
      (when (probe-file lib-file)
        (cond ((delete-file lib-file) nil)
              (t (er hard 'delete-auxiliary-book-files
                     err-string
                     full-book-name lib-file)))))
    (when (probe-file efile)
      (cond ((delete-file efile) nil)
            (t (er hard 'delete-auxiliary-book-files
                   err-string
                   full-book-name efile))))))

(defun delete-expansion-file (os-expansion-filename full-book-name state)

; Os-expansion-filename is, as the name suggests, an OS filename; see the Essay
; on Pathnames.  Since that pathname could contain characters that are not ACL2
; characters, we print the message using the ACL2 string for the corresponding
; book, full-book-name.

  (delete-file os-expansion-filename)
  (io? event nil state
       (full-book-name)
       (fms "Note: Deleting expansion file for the book,~%~s0.~|"
            (list (cons #\0 full-book-name))
            (proofs-co state) state nil)))

(defun compile-uncompiled-defuns (file &optional (fns :some) gcl-flg
                                       &aux (state *the-live-state*))

; File should be given in Unix-style syntax.  Hence for example, "TMP" is
; relative to the current directory, even though on a Macintosh this might
; appear to be an absolute pathname for a file.

; Compile-uncompiled-defuns compiles the non-built-in defuns that are not
; currently compiled if FNS is :some.  Otherwise, FNS should be a list of
; functions to compile.

  (when (and (not (symbol-listp fns))
             (not (eq fns :some)))
    (er hard 'compile-uncompiled-defuns
        "The argument to compile-uncompiled-defuns must be either a true list ~
         of symbols or the keyword :some.  The argument ~x0 is thus illegal."
        fns))
  (cond
   ((null fns)
    (warning$ 'compile-uncompiled-defuns nil
              "No functions to compile.")
    (return-from compile-uncompiled-defuns file)))
  (let ((os-file (pathname-unix-to-os file state)))
    (state-global-let*
     ((print-circle (f-get-global 'print-circle-files state))

; The use of with-output-object-channel-sharing below will fail in Lisps that
; allow compilation, like Allegro CL and unlike CCL, when we are inside a
; binding of writes-okp to nil, as within a call of
; protect-system-state-globals (e.g., when inside make-event expansion or
; perhaps evaluation of a clause-processor hint).  It's sad to see an event
; fail for that reason, such as (make-event (er-progn (comp t) (value
; '(value-triple nil)))).  So here we bind writes-okp to t.

      (writes-okp t)
      (serialize-character (f-get-global 'serialize-character-system state)))
     (with-print-controls
      :defaults
      ((*print-circle* (f-get-global 'print-circle state)))
      (let ((seen (make-hash-table :test 'eq))
            (fns (cond ((eq fns :uncompiled)
                        :some)
                       ((eq fns t)
                        :all)
                       (t fns)))
            (fn-file (format nil "~a.lisp" file)))

; (Warning: Do not delete the following comment without considering the pointer
; to it in compile-uncompiled-*1*-defuns.)
; The following use of with-output-object-channel-sharing causes #n= sharing
; notation to be used when printing each defun.  The number of such indices (n)
; starts fresh with each definition.  This should be OK since each defun will
; presumably be read separately -- quoting the CL HyperSpec, Section "2.4.8.15
; Sharpsign Equal-Sign": ... The scope of the label is the expression being
; read by the outermost call to read; within this expression, the same label
; may not appear twice.

        (with-output-object-channel-sharing
         chan fn-file
         (let ((str0
                (get-output-stream-from-channel chan))
               (str1
                "; (ACL2 Note) Attempting separate compilation ~a: ~s.~&"))
           (format str0
                   "; This file is automatically generated, to be ~
                    compiled.~%; Feel free to delete it after compilation.~%")

; We print (in-package "...") but we do it this way to guarantee that the
; symbol 'in-package is printed correctly.

           (print-object$ (list 'in-package (current-package state))
                          chan state)
           (dolist (trip (w state))
             (cond ((and (eq fns :some)
                         (eq (car trip) 'command-landmark)
                         (eq (cadr trip) 'global-value)
                         (equal (access-command-tuple-form (cddr trip))
                                '(exit-boot-strap-mode)))
                    (return))
                   ((and (eq (car trip) 'cltl-command)
                         (eq (cadr trip) 'global-value)
                         (consp (cddr trip))
                         (eq (caddr trip) 'memoize)
                         (not (gethash (cadddr trip) seen))
                         (memoizedp-raw (cadddr trip))
                         (or (eq fns :some)
                             (member-eq (cadddr trip) fns)))
                    (setf (gethash (cadddr trip) seen) t)
                    (when (not (compiled-function-p! (cadddr trip)))
                      (format t str1

; We ignore errors (if possible), since for example, we have seen LispWorks
; complain when (car x) names a function that is a lexical closure.

                              "for memoized function"
                              (cadddr trip))

; We ignore errors (if possible), since for example, we have seen LispWorks
; complain when (car x) names a function that is a lexical closure.

                      (our-ignore-errors (compile (cadddr trip)))))
                   ((and (eq (car trip) 'cltl-command)
                         (eq (cadr trip) 'global-value)
                         (consp (cddr trip))
                         (eq (caddr trip) 'defuns)

; The next test asks whether the ignorep field of the defuns tuple is
; '(defstobj . stobj).  If it is, this triple didn't actually make
; those definitions.

                         (not (and (consp (caddr (cddr trip)))
                                   (eq (car (caddr (cddr trip))) 'defstobj))))
                    (dolist (x (cdddr (cddr trip)))
                      (cond ((and (not (gethash (car x) seen))
                                  (or (eq fns :some)
                                      (member-eq (car x) fns)))
                             (setf (gethash (car x) seen) t)
                             (when (not (compiled-function-p! (car x)))
                               (cond ((or (member-eq
                                           (car x)
                                           (f-get-global
                                            'program-fns-with-raw-code
                                            state))
                                          (member-eq
                                           (car x)
                                           (f-get-global
                                            'logic-fns-with-raw-code
                                            state)))
                                      (format t str1
                                              "due to raw code"
                                              (car x))

; We ignore errors (if possible), since for example, we have seen LispWorks
; complain when (car x) names a function that is a lexical closure.

                                      (our-ignore-errors (compile (car x))))
                                     (t (print-object$ (cons 'defun x)
                                                       chan state))))))))
                   ((and (eq (car trip) 'cltl-command)
                         (eq (cadr trip) 'global-value)
                         (consp (cddr trip))
                         (eq (caddr trip) 'defstobj))
                    (dolist (x (car (cddddr (cddr trip))))

; (cddr trip) is of the form
; (DEFSTOBJ name the-live-name init raw-defs disc axiomatic-defs)
; where disc is the redundant-raw-lisp-discriminator for name.  Note that since
; raw Lisp definitions for defabsstobj are defmacros, we do not deal with
; defabsstobj, just as we skip the defstobj case when defabbrev is used for raw
; Lisp definitions, as determined by (member-equal *stobj-inline-declare* x) as
; shown below.

                      (cond
                       ((and (not (gethash (car x) seen))
                             (not (member-equal *stobj-inline-declare* x))
                             (or (eq fns :some)
                                 (member-eq (car x) fns)))
                        (setf (gethash (car x) seen) t)
                        (when (not (compiled-function-p! (car x)))
                          (print-object$ (cons 'defun x)
                                         chan state))))))
                   ((eq (cadr trip) 'redefined)

; This case avoids redefining a macro back to an overwritten function in the
; following example provided by Eric Smith.

; (defun foo (x) x)
; :redef!
; (defmacro foo (x) x)
; :comp t

                    (setf (gethash (car trip) seen) t))))
           (newline chan state)
           (close-output-channel chan state)))
        (when (not (eq fns :some))
          (let (missing)
            (dolist (fn fns)
              (when (not (gethash fn seen))
                (push fn missing)))
            (when missing
              (format t
                      "~%Warning:  The following functions have not been ~
                       compiled.~%  ~s~%Perhaps you have not defined them ~
                       inside the ACL2 command loop.~%"
                      missing))))
        (cond
         (gcl-flg
          #+gcl
          (compile-file
           (our-truename (pathname-unix-to-os fn-file state)
                         "Note: Calling OUR-TRUENAME from ~
                          COMPILE-UNCOMPILED-DEFUNS (under gcl-flg and #+gcl).")
           :c-file t :h-file t)
          #-gcl
          (er hard 'compile-uncompiled-defuns
              "The gcl-flg argument to compile-uncompiled-defuns is only ~
               legal when running under GCL."))
         (t
          (let ((lisp-file
                 (our-truename (pathname-unix-to-os fn-file state)
                               "Note: Calling OUR-TRUENAME from ~
                                COMPILE-UNCOMPILED-DEFUNS.")))
            (compile-file lisp-file)
            (when (not (keep-tmp-files state))
              (delete-file lisp-file)
              #+clisp
              (delete-file (concatenate 'string os-file ".lib"))))))
        (load-compiled os-file t)
        (if (not (keep-tmp-files state))
            (delete-file (concatenate 'string os-file "."
                                      *compiled-file-extension*))))
      (value nil)))
    os-file))

(defun compile-uncompiled-*1*-defuns (file &optional (fns :some) gcl-flg chan0
                                           &aux
                                           (state *the-live-state*)
                                           (wrld (w *the-live-state*)))

; This is similar to compile-uncompiled-defuns, but for *1* functions.
; However, an optional chan0 may be supplied; if non-nil, then it is an open
; output channel of type :object, which is closed by this function.

; File should be given in Unix-style syntax.  Hence for example, "TMP" is
; relative to the current directory, even though on a Macintosh this might
; appear to be an absolute pathname for a file.

; If chan0 is not nil, then unlike compile-uncompiled-defuns, we write out all
; relevant *1* function definitions, even those that are currently compiled.

  (when (and (not (symbol-listp fns))
             (not (eq fns :some)))
    (er hard 'compile-uncompiled-*1*-defuns
        "The argument to compile-uncompiled-*1*-defuns must be either a true ~
         list of symbols or the keyword :some.  The argument ~x0 is thus ~
         illegal."
        fns))
  (cond
   ((and (null fns) (null chan0))
    (warning$ 'compile-uncompiled-defuns nil
              "No functions to compile.")
    (return-from compile-uncompiled-*1*-defuns file)))
  (let ((os-file (pathname-unix-to-os file state)))
    (state-global-let*
     ((print-circle (f-get-global 'print-circle-files state))
      (writes-okp t) ; see comment on this binding in compile-uncompiled-defuns
      (serialize-character (f-get-global 'serialize-character-system state)))
     (with-print-controls
      :defaults
      ((*print-circle* (f-get-global 'print-circle state)))
      (let ((seen (let ((tbl (make-hash-table :test 'eq)))
                    (when (not (eq fns :some))
                      (dolist (fn fns)
                        (setf (gethash fn tbl) :init)))
                    tbl))
            (fns (cond ((eq fns :uncompiled)
                        :some)
                       ((eq fns t)
                        :all)
                       (t fns)))
            (fn-file (format nil "~a.lisp" file))
            (not-boot-strap-p (null (f-get-global 'boot-strap-flg state))))

; See the comment just above the call of with-output-object-channel-sharing in
; compile-uncompiled-defuns.

        (with-output-object-channel-sharing
         chan fn-file
         (cond
          ((null chan)
           (return-from compile-uncompiled-*1*-defuns
                        (er hard 'compile-uncompiled-*1*-defuns
                            "Unable to open file ~x0 for object output."
                            fn-file)))
          (t
           (let ((defs nil) ; only used in the case chan0 is not nil
                 (str0 (get-output-stream-from-channel chan)))
             (cond ((null chan0) ; new output file
                    (format str0
                            "; This file is automatically generated, to be ~
                             compiled.~%; Feel free to delete it after ~
                             compilation.~%")

; We print (in-package "...") but we do it this way to guarantee that the
; symbol 'in-package is printed correctly.

                    (print-object$ (list 'in-package
                                         (current-package state))
                                   chan state))
                   (t state))
             (dolist (trip wrld)
               (cond ((and (eq fns :some)
                           (eq (car trip) 'command-landmark)
                           (eq (cadr trip) 'global-value)
                           (equal (access-command-tuple-form (cddr trip))
                                  '(exit-boot-strap-mode)))

; If we are compiling while building the system, then we will never see
; 'exit-boot-strap-mode, which allows us to explore the entire world.  But when
; a user executes (comp t), thus calling this function with argument fns equal
; to :some, the exploration should only consider user-defined events.

                      (return))
                     ((and (eq (car trip) 'cltl-command)
                           (eq (cadr trip) 'global-value)
                           (consp (cddr trip))
                           (eq (caddr trip) 'defuns))
                      (dolist
                        (x (cdddr (cddr trip)))
                        (when (not (member-eq
                                    (car x)
                                    `(mv-list return-last wormhole-eval
                                              ,@*defun-overrides*)))
                          (let ((*1*fn (*1*-symbol (car x))))
                            (cond
                             ((and (fboundp *1*fn)
                                   (cond
                                    ((eq fns :some)
                                     (and (not (gethash (car x) seen))

; We have seen during development of v2-9 that in Allegro CL, when compiling
; *1* functions on the fly during boot-strap (because of code in add-trip), the
; image size increases from 29.3M to 36.9M if we instead use the following
; code, which avoids writing *1* definitions to TMP1.lisp for compiled :logic
; mode functions at the end of the boot-strap.
;                                  (and (not (compiled-function-p! *1*fn))
;                                       (or not-boot-strap-p
;                                           (not (eq (cadr (cddr trip))
;                                                    :program))))
; That is, when we wrote out a TMP1.lisp for all :logic mode functions at the
; end of initialization and compiled it, we saved 7.6M.  This result remains a
; mystery, but we prefer the smaller image so we keep the code below.  The
; resulting increase in wall-clock build time was only about 3 seconds.  See
; also the corresponding comment mentioning compile-uncompiled-*1*-defuns in
; add-trip.

                                          (if not-boot-strap-p
                                              (not (compiled-function-p!
                                                    *1*fn))

; We have noticed about a corresponding 0.6% to 1.2% slowdown in the regression
; suite when we avoid compiling :program mode *1* functions for GCL during the
; build and also at the end, when TMP1.lisp is written, as discussed in the
; comment above "boot-strap-flg ; delete for build speed-up (see above)" in
; add-trip.  With that mod, we have tried the following additional mod so that
; for GCL we still compile built-in :program mode *1* functions after all, by
; writing out a huge TMP1.lisp file (8.3 MB instead 0.4 MB).

; #+gcl t #-gcl

; But this made things worse.  Here are examples for v2-9-1 (on the way to
; v2-9-2):
;
; During the build, compile :program mode functions on the fly (as usual):
; 9763.160u 146.760s 2:51:33.10 96.2%   0+0k 0+0io 13673004pf+0w
;
; During the build, do not compile :program mode functions at all:
; 9827.570u 149.730s 2:52:29.27 96.4%   0+0k 0+0io 14549410pf+0w
;
; During the build, do not compile :program mode functions until the end
; (creating very large TMP1.lisp file):
; 9893.870u 150.240s 2:54:22.62 95.9%   0+0k 0+0io 14528555pf+0w
;
; Moreover, the saved_acl2.gcl file went from 43 MB, for the first two, to 104
; MB for the last.  So let's not write :program mode *1* functions to
; TMP1.lisp.  See the long comment about *fast-acl2-gcl-build* in add-trip.

                                            (not (eq (cadr (cddr trip))
                                                     :program)))
                                          (setf (gethash (car x) seen) t)))
                                    ((eq (gethash (car x) seen) :init)
                                     (setf (gethash (car x) seen) t)
                                     (or chan0
                                         (not (compiled-function-p!
                                               *1*fn))))))
                              (let ((*1*def
                                     (cons 'defun
                                           (oneify-cltl-code
                                            (cadr (cddr trip)) ; defun-mode
                                            x
                                            (getpropc (car x) 'stobj-function
                                                      nil wrld)
                                            wrld))))
                                (cond (chan0 (push *1*def defs))
                                      (t (print-object$ *1*def chan
                                                        state))))))))))
                     ((eq (cadr trip) 'redefined)

; This case avoids a hard error message when encountering a macro redefined
; from an earlier defun, in the following example provided by Eric Smith.

; (defun foo (x) x)
; :redef!
; (defmacro foo (x) x)
; :comp t

                      (setf (gethash (car trip) seen) t))))
             (when chan0

; Print all the defs in a single progn, for maximum structure sharing via #n=
; and #n#.

               (print-object$ (cons 'progn (nreverse defs)) chan state))
             (newline chan state)
             (cond (chan0 (return-from compile-uncompiled-*1*-defuns os-file))
                   (t (close-output-channel chan state))))))
         chan0)
        (when (not (eq fns :some))
          (let (missing)
            (dolist (fn fns)
              (when (not (eq (gethash fn seen) t))
                (push fn missing)))
            (when missing
              (format t
                      "~%Warning:  The following executable-counterpart ~
                       functions have not been compiled.~%  ~s~%Perhaps you ~
                       have not defined them inside the ACL2 command loop.~%"
                      missing))))
        (cond
         (gcl-flg
          #+gcl
          (compile-file
           (our-truename (pathname-unix-to-os fn-file state)
                         "Note: Calling OUR-TRUENAME from ~
                          COMPILE-UNCOMPILED-*1*-DEFUNS (under gcl-flg and ~
                          #+gcl).")
           :c-file t :h-file t)
          #-gcl
          (er hard 'compile-uncompiled-defuns
              "The gcl-flg argument to compile-uncompiled-*1*-defuns is only ~
               legal when running under GCL."))
         (t
          (let ((lisp-file
                 (our-truename (pathname-unix-to-os fn-file state)
                               "Note: Calling OUR-TRUENAME from ~
                                COMPILE-UNCOMPILED-*1*-DEFUNS.")))
            (compile-file lisp-file)
            (when (not (keep-tmp-files state))
              (delete-file lisp-file)
              #+clisp
              (delete-file (concatenate 'string os-file ".lib"))))))
        (load-compiled os-file t)
        (if (not (keep-tmp-files state))
            (delete-file (concatenate 'string os-file "."
                                      *compiled-file-extension*)))
        (value nil))))
    os-file))

(defun compile-certified-file (os-expansion-filename full-book-name state)

; Warning: full-book-name should be the full book name of a book that has
; already have been included, so that its macro definitions have been evaluated
; before we compile.  Moreover, os-expansion-filename must already have been
; written.  As the names suggest, os-expansion-filename is an OS pathname and
; full-book-name is an ACL2 pathname; see the Essay on Pathnames.

  (let* ((os-full-book-name (pathname-unix-to-os full-book-name state))
         (os-full-book-name-compiled
          (convert-book-name-to-compiled-name os-full-book-name state))
         #+ccl
         (*stack-access-defeat-hook-cert-ht*
          (stack-access-defeat-hook-cert-ht)))
    (when (probe-file os-full-book-name-compiled)
      (delete-file os-full-book-name-compiled))
    (acl2-compile-file full-book-name os-expansion-filename)
    os-full-book-name-compiled))

(defun compile-for-include-book (full-book-name certified-p ctx state)
  (cond
   ((not certified-p)

; We warn rather than cause an error, since if one is including an uncertified
; book then one is presumably willing to live with the result.  It could be
; annoying if an include-book :load-compiled-file :comp occurs inside another
; book, since one might not want to edit the parent book.

    (pprogn (warning$ ctx "Compiled file"
                      "An include-book form for book ~x0 has specified option ~
                       :load-compiled-file :comp.  But this book is ~
                       uncertified, so compilation is being skipped."
                      full-book-name)
            (value nil)))
   (t
    (let* ((efile (pathname-unix-to-os (expansion-filename full-book-name)
                                       state))
           (entry (and *hcomp-book-ht*
                       (gethash full-book-name *hcomp-book-ht*)))
           (status (and entry
                        (access hcomp-book-ht-entry entry :status))))
      (cond ((eq status 'complete)
             (value nil))
            (t
             (mv-let
              (cfile state)
              (certificate-file full-book-name state)
              (let* ((cfile (and cfile (pathname-unix-to-os cfile state)))
                     (cfile-write-date (and cfile
                                            (file-write-date cfile)))
                     (efile-write-date (and (probe-file efile)
                                            (file-write-date efile)))
                     (reason (cond ((not (probe-file cfile))
                                    "the certificate file does not exist")
                                   ((not (probe-file efile))
                                    "the expansion file does not exist")
                                   ((not (eq status 'to-be-compiled))
                                    "the expansion file or compiled file ~
                                     appears not to have been loaded to ~
                                     completion")
                                   ((and cfile-write-date
                                         efile-write-date
                                         (<= cfile-write-date efile-write-date))
                                    nil)
                                   (t
                                    "the write-date of the expansion file is ~
                                     not greater than the write date of the ~
                                     certificate file"))))
                (cond (reason (er soft ctx
                                  "An include-book event with option ~
                                   :load-compiled-file :comp has failed for ~
                                   book~|~s0,~|because ~@1.  See :DOC ~
                                   include-book and see :DOC ~
                                   book-compiled-file."
                                  full-book-name reason))
                      (t
                       (observation ctx
                                    "Compiling file ~x0, as specified by ~
                                     include-book option :load-compiled-file ~
                                     :comp."
                                    full-book-name)
                       (acl2-compile-file full-book-name efile)
                       (value nil)))))))))))


;                            MISCELLANEOUS

(defun-one-output enabled-structurep (x)

; This function is basically a hack.  We return t if x is probably an
; enable-structure.  This is just part of the test of recognizing
; something we don't want to print out when tracing.  See below.
; Without something like this, it is just too uncomfortable to trace
; many ACL2 functions because too much output is printed since
; enabled-structures typically take hundreds of lines to print.

; WARNING:  Keep this in sync with enabled-structure.

  (case-match x
              (((index-of-last-enabling . theory-array)
                (array-name . array-length)
                array-name-root . array-name-suffix)
               (and (integerp index-of-last-enabling)
                    (symbolp array-name)
                    (array1p array-name theory-array)
                    (integerp array-length)
                    (character-listp array-name-root)
                    (integerp array-name-suffix)))
              (& nil)))

(defun-one-output rcnstp (x)

; This is another function in the spirit of enabled-structurep, above.

; WARNING: Keep this in sync with rewrite-constant.

  (case-match x
              (((current-enabled-structure)
                (& & . &)
                (& . &)
                (& . &)
                .
                &)
               (enabled-structurep current-enabled-structure))
              (& nil)))

(defvar *trace-alist*
  (list (cons 'state '|*the-live-state*|)))

(defun-one-output assoc-eq-trace-alist (val alist)
  (cond
   ((endp alist) nil)
   ((and (boundp (caar alist))
         (eq val (symbol-value (caar alist))))
    (car alist))
   (t (assoc-eq-trace-alist val (cdr alist)))))

(defun-one-output print-list-without-stobj-arrays (lst)
  (loop for x in lst
        collect
        (if (eq x *the-live-state*)
            '|<state>|
          (or (and (arrayp x)
                   (stobj-print-symbol x *user-stobj-alist*))
              x))))

(defun-one-output stobj-print-symbol (x user-stobj-alist-tail)
  (and (live-stobjp x)
       (loop for pair in user-stobj-alist-tail
             when (eq x (cdr pair))
             do (return (intern-in-package-of-symbol
                         (stobj-print-name (car pair))
                         (car pair)))
             finally (return (intern "<some-stobj>"
                                     (find-package-fast
                                      (current-package *the-live-state*)))))))

(defun-one-output trace-hide-world-and-state (l)

; This function intuitively belongs over in init.lisp but it is here so
; that it will get compiled so we won't get stack overflow when
; tracing large objects.  It is used to replace certain offensive
; objects by less offensive ones before trace prints the args and
; results of traced functions.  It may not work well with local stobjs.

; In some functions, notably trace-fix-exit-raw and trace-fix-exit for GCL, we
; assume that trace-hide-world-and-state and its subroutines do not call mv.
; If that changes then we should use protect-mv there as we do in some other
; places.

  (let* ((stobj-pair (rassoc l *user-stobj-alist*))
         (l (cond
             (stobj-pair
              (intern-in-package-of-symbol
               (stobj-print-name (car stobj-pair))
               (car stobj-pair)))
             (t ; consider local stobjs
              (or (and (arrayp l)
                       (stobj-print-symbol l *user-stobj-alist*))
                  l))))
         (pair (assoc-eq-trace-alist l *trace-alist*)))
    (cond (pair (cdr pair))
          ((atom l) l)
          ((eq l (w *the-live-state*))
           '|current-acl2-world|)
          ((rcnstp l) '|some-rcnst|)
          ((enabled-structurep l) '|some-enabled-structure|)
          ((and (consp l)
                (or (eq (car l) 'event-index)
                    (eq (car l) 'command-index))
                (consp (cdr l))
                (eq (car (cdr l)) 'global-value))
           (list* (car l) 'global-value '|some-index|))

; I have been known to put this in here

;           ((and (consp l)
;                 (consp (car l))
;                 (symbolp (car (car l)))
;                 (consp (cdr (car l)))
;                 (eq (car (cdr (car l))) 'global-value))
;            '|some-other-world-perhaps|)

          (t (cons (trace-hide-world-and-state (car l))
                   (trace-hide-world-and-state (cdr l)))))))

(defun-one-output get-stobjs-out-for-declare-form (fn)

; Warning: Keep this in sync with stobjs-out.

; This function is used in acl2-fns.lisp.

; Here we essentially open-code stobjs-out, except that we allow for the
; possibility that fn is defined in raw Lisp.

  (cond ((eq fn 'cons)
; We call this function on cons so often we optimize it.
         '(nil))
        ((member-eq fn *stobjs-out-invalid*)
         (interface-er "Implementation error in ~
                        get-stobjs-out-for-declare-form: Attempted to find ~
                        stobjs-out for ~x0."
                       fn))
        (t (let ((w (w *the-live-state*)))
             (or (getpropc fn 'stobjs-out nil w)
                 (and (getpropc fn 'symbol-class nil w)
                      '(nil)))))))

; The definition of fix-trace and its subfunction fix-trace-untrace can go
; anywhere, but since they are raw Lisp, we will put them in this file.

(defun fix-trace-untrace (new-trace-specs old-trace-specs)

; Collect functions traced in new-trace-specs that are not traced in
; old-trace-specs.

  (cond ((endp new-trace-specs) nil)
        ((assoc-eq (caar new-trace-specs) old-trace-specs)
         (fix-trace-untrace (cdr new-trace-specs) old-trace-specs))
        (t
         (cons (caar new-trace-specs)
               (fix-trace-untrace (cdr new-trace-specs) old-trace-specs)))))

(defun fix-trace (old-trace-specs)
  (let* ((new-trace-specs (f-get-global 'trace-specs *the-live-state*))
         (to-untrace (fix-trace-untrace new-trace-specs old-trace-specs))
         (to-retrace (set-difference-equal old-trace-specs new-trace-specs)))
    (when to-untrace
      (eval `(untrace$ ,@to-untrace)))
    (when to-retrace
      (eval `(trace$ ,@to-retrace)))))

;;;;;;;;;;
;;; Start memory management code (formerly called start-sol-gc)
;;;;;;;;;;

; This section of code was suggested by Jared Davis as a way to regain
; performance of ACL2(h) on regressions at UT CS.  Initially, these regressions
; showed significant slowdown upon including new memoization code from Centaur
; on 3/28/2013:
; ; old:
; 24338.570u 1357.200s 1:19:02.75 541.7%	0+0k 0+1918864io 0pf+0w
; ; new:
; 33931.460u 1017.070s 1:43:24.28 563.2%	0+0k 392+1931656io 0pf+0w
; After restoring (start-sol-gc) in function acl2h-init, we regained the old
; level of performance for a UT CS ACL2(h) regression, with the new memoization
; code.

(defun mf-looking-at (str1 str2 &key (start1 0) (start2 0))

; (Mf-looking-at str1 str2 :start1 s1 :start2 s2) is non-nil if and only if
; string str1, from location s1 to its end, is an initial segment of string
; str2, from location s2 to its end.

   (unless (typep str1 'simple-base-string)
     (error "looking at:  ~a is not a string." str1))
   (unless (typep str2 'simple-base-string)
     (error "looking at:  ~a is not a string." str2))
   (unless (typep start1 'fixnum)
     (error "looking at:  ~a is not a fixnum." start1))
   (unless (typep start2 'fixnum)
     (error "looking at:  ~a is not a fixnum." start2))
   (locally
     (declare (simple-base-string str1 str2)
              (fixnum start1 start2))
     (let ((l1 (length str1)) (l2 (length str2)))
       (declare (fixnum l1 l2))
       (loop
        (when (>= start1 l1) (return t))
        (when (or (>= start2 l2)
                  (not (eql (char str1 start1)
                            (char str2 start2))))
          (return nil))
        (incf start1)
        (incf start2)))))

(defun our-uname ()

; Returns nil or else a keyword -- currently :darwin, :linux, or :freebsd -- to
; indicate the result of shell command "uname".

  (multiple-value-bind
   (exit-code val)
   (system-call+ "uname" nil)
   (and (eql exit-code 0)
        (stringp val)
        (<= 6 (length val))
        (cond ((string-equal (subseq val 0 6) "Darwin") :darwin)
              ((string-equal (subseq val 0 5) "Linux") :linux)
              ((string-equal (subseq val 0 7) "FreeBSD") :freebsd)))))

(defun meminfo (&optional arg)

; With arg = nil, this function either returns 0 or else the size of the
; physical memory.  See the code below to understand what information might be
; returned for non-nil values of arg.

  (assert (or (null arg)
              (stringp arg)))
  (or
   (with-standard-io-syntax
    (case (our-uname)
      (:linux
       (let ((arg (or arg  "MemTotal:")))
         (and
          (our-ignore-errors (probe-file "/proc/meminfo"))
          (with-open-file
           (stream "/proc/meminfo")
           (let (line)
             (loop while (setq line (read-line stream nil nil)) do
                   (when (mf-looking-at arg line)
                     (return
                      (values
                       (read-from-string line nil nil
                                         :start (length arg)))))))))))
      (:darwin
       (let* ((arg (or arg "hw.memsize"))
              (len (length arg)))
         (multiple-value-bind
          (exit-code val)
          (system-call+ "sysctl" (list arg))
          (and (eql exit-code 0)
               (mf-looking-at arg val)
               (mf-looking-at arg ": " :start1 len)
               (let ((ans (read-from-string val nil nil :start (+ 2 len))))
                 (and (integerp ans)
                      (equal (mod ans 1024) 0)
                      (/ ans 1024)))))))
      (:freebsd
       (let* ((arg (or arg

; Gary Byers suggests hw.usermem instead of hw.physmem, to avoid including
; memory that seems to be reserved for kernel drivers.

                       "hw.usermem"))
              (len (length arg)))
         (multiple-value-bind
          (exit-code val)
          (system-call+ "sysctl" (list arg))
          (and (eql exit-code 0)
               (mf-looking-at arg val)
               (mf-looking-at arg ": " :start1 len)
               (let ((ans (read-from-string val nil nil :start (+ 2 len))))
                 (and (integerp ans)
                      (equal (mod ans 1024) 0)
                      (/ ans 1024)))))))
      (t nil)))
   0))

(defg *max-mem-usage*

; This global is set in ccl-initialize-gc-strategy.  It is an upper bound, in
; bytes of memory used, that when exceeded results in certain garbage
; collection actions.

; See also the centaur/misc/memory-mgmt books.

  (expt 2 32))

(defg *gc-min-threshold*

; This is set in ccl-initialize-gc-strategy.

; See also the centaur/misc/memory-mgmt books.

  (min (expt 2 30)

 ; CCL requires a fixnum for ccl::lisp-heap-gc-threshold.

       most-positive-fixnum))

(let ((physical-memory-cached-answer nil))
(defun physical-memory () ; in KB
  (or physical-memory-cached-answer
      (setq physical-memory-cached-answer
            (meminfo))))
)

#+ccl
(defun set-and-reset-gc-thresholds ()

; See set-gc-strategy-builtin-delay (formerly start-sol-gc) for a full
; discussion.  The comments here summarize how that works out if, for example,
; there are 8G bytes of physical memory, just to make the concepts concrete --
; so it might be helpful to read the comments in this function before reading
; the more general discussion in set-gc-strategy-builtin-delay.

  (let ((n

; E.g., with 8G bytes of physical memory, *max-mem-usage* is 1/8 of that --
; i.e., 1G -- and *gc-min-threshold* is 1/4 of that -- i.e., (1/4)G.  Then here
; we arrange to allocate enough memory after a GC to reach *max-mem-usage* = 1G
; bytes before the next GC, unless the current memory usage is more than
; (3/4)G, in which case we allocate the minimum of (1/4)G.

         (min (max (- *max-mem-usage* (ccl::%usedbytes))
                   *gc-min-threshold*)

; CCL requires a fixnum for ccl::lisp-heap-gc-threshold.

              most-positive-fixnum)))

; Now set the "threshold" to the number of bytes computed above (unless that
; would be a no-op).

    (unless (eql n (ccl::lisp-heap-gc-threshold))
      (ccl::set-lisp-heap-gc-threshold n)))

; The above setting won't take effect until the next GC unless we take action.
; Here is that action, which actually allocates the bytes computed above as
; free memory.

  (ccl::use-lisp-heap-gc-threshold)

; Finally, still assuming 8G bytes of physical memory, set the "threshold" to
; (1/4)G.  This is how much the next GC will set aside as free memory -- at
; least initially, but then the post-gc hook will call this function.  As
; explained above, in the case that the current memory usage is less than
; (3/4)G, enough free memory will be allocated so that the next GC is triggered
; after *max-mem-usage* = 1G bytes are in use.

  (unless (eql *gc-min-threshold* (ccl::lisp-heap-gc-threshold))
    (ccl::set-lisp-heap-gc-threshold *gc-min-threshold*)))

#+ccl
(defun ccl-initialize-gc-strategy (&optional threshold)
  (let* ((phys (physical-memory))                   ; in KB
         (memsize (cond ((> phys 0) (* phys 1024))  ; to bytes
                        (t (expt 2 32)))))
    (setq *max-mem-usage* ; no change if we were here already
          (min (floor memsize 8)
               (expt 2 31)))
    (setq *gc-min-threshold* ; no change if we were here already
          (min (cond ((null threshold)
                      (floor *max-mem-usage* 4))
                     ((posp threshold) threshold)
                     (t (error "The GC threshold must be a positive integer, ~
                                but ~s is not!"
                               threshold)))

 ; CCL requires a fixnum for ccl::lisp-heap-gc-threshold.

               most-positive-fixnum))
    (ccl::set-lisp-heap-gc-threshold *gc-min-threshold*)
    (ccl::use-lisp-heap-gc-threshold)
    nil))

#+ccl
(defun set-gc-strategy-builtin-delay ()

; This function was called start-sol-gc through ACL2 Version_7.1.  It should
; undo the effects of set-gc-strategy-builtin-egc, by turning off EGC and
; enabling the delay strategy.  The list ccl::*post-gc-hook-list* should
; contain the symbol set-and-reset-gc-thresholds after this call succeeds.

; The function ccl-initialize-gc-strategy should be called before this function
; is called.

; This function should probably not be invoked in recent versions of CCL,
; instead relying on EGC for memory management, except perhaps in
; static-hons-intensive applications.  See *acl2-egc-on*.

;          Sol Swords's scheme to control GC in CCL
;
; The goal is to get CCL to perform a GC whenever we're using almost
; all the physical memory, but not otherwise.
;
; The discussion below is self-contained, but for more discussion, relevant CCL
; documentation is at http://ccl.clozure.com/ccl-documentation.html, Chapter
; 16: "Understanding and Configuring the Garbage Collector".  Note that it
; might be easier to read the comment in source function
; set-and-reset-gc-thresholds before reading below.

; The usual way of controlling GC on CCL is via LISP-HEAP-GC-THRESHOLD.  This
; value is approximately the amount of free memory that will be allocated
; immediately after GC.  This means that the next GC will occur after
; LISP-HEAP-GC-THRESHOLD more bytes are used (by consing or array allocation or
; whatever).  But this means the total memory used by the time the next GC
; comes around is the threshold plus the amount that remained in use at the end
; of the previous GC.  This is a problem because of the following scenario:
;
;  - We set the LISP-HEAP-GC-THRESHOLD to 3GB since we'd like to be able
;    to use most of the 4GB physical memory available.
;
;  - A GC runs or we say USE-LISP-HEAP-GC-THRESHOLD to ensure that 3GB
;    is available to us.
;
;  - We run a computation until we've exhausted this 3GB, at which point
;    a GC occurs.
;
;  - The GC reclaims 1.2 GB out of the 3GB used, so there is 1.8 GB
;    still in use.
;
;  - After GC, 3GB more is automatically allocated -- but this means we
;    won't GC again until we have 4.8 GB in use, meaning we've gone to
;    swap.
;
; What we really want is, instead of allocating a constant additional
; amount after each GC, to allocate up to a fixed total amount including
; what's already in use.  To emulate that behavior, we use the hack
; below.  This operates as follows, assuming the same 4GB total physical
; memory as in the above example (or, unknown physical memory that defaults to
; 4GB as shown below, i.e., when function meminfo returns 0).
;
; 1. We set the LISP-HEAP-GC-THRESHOLD to (0.5G minus used bytes) and call
; USE-LISP-HEAP-GC-THRESHOLD so that our next GC will occur when we've used a
; total of 0.5G.
;
; 2. We set the threshold back to *gc-min-threshold*= 0.125GB without calling
; USE-LISP-HEAP-GC-THRESHOLD.
;
; 3. Run a computation until we use up the 0.5G and the GC is called.  Say the
; GC reclaims 0.3GB so there's 0.2GB in use.  0.125GB more (the current
; LISP-HEAP-GC-THRESHOLD) is allocated so the ceiling is temporarily 0.325GB.
;
; 4. A post-GC hook runs which again sets the threshold to (0.5G minus used
; bytes), calls USE-LISP-HEAP-GC-THRESHOLD to raise the ceiling to 0.5G, then
; sets the threshold back to 0.125GB, and the process repeats.
;
; A subtlety about this scheme is that post-GC hooks runs in a separate
; thread from the main execution.  A possible bug is that in step 4,
; between checking the amount of memory in use and calling
; USE-LISP-HEAP-GC-THRESHOLD, more memory might be used up by the main
; execution, which would set the ceiling higher than we intended.  To
; prevent this, we initially interrupted the main thread to run step 4.
; However, discussions with Gary Byers led us to avoid calling
; process-interrupt, which seemed to be leading to errors.

; The following settings are highly heuristic.  We arrange that gc
; occurs at 1/8 of the physical memory size in bytes, in order to
; leave room for the gc point to grow (as per
; set-and-reset-gc-thresholds).  If we can determine the physical
; memory; great; otherwise we assume that it it contains at least 4GB,
; a reasonable assumption we think for anyone using ACL2 in 2015 or beyond.

  (without-interrupts ; leave us in a sane state
   (ccl:egc nil)
   (ccl::add-gc-hook

; We use 'set-and-reset-gc-thresholds rather than #'set-and-reset-gc-thresholds
; to ensure that ccl::remove-gc-hook will remove the hook, since an EQ test is
; used -- though it appears that #' would also be suitable for that purpose.

    'set-and-reset-gc-thresholds
    :post-gc)
   (set-and-reset-gc-thresholds)))

#+ccl
(defun set-gc-strategy-builtin-egc ()

; This function should undo the effects of set-gc-strategy-builtin-delay, by
; turning on EGC and disabling the delay strategy.  The list
; ccl::*post-gc-hook-list* should not contain the symbol
; set-and-reset-gc-thresholds after this call succeeds.

  (without-interrupts ; leave us in a sane state
   (ccl:egc t)
   (ccl::remove-gc-hook

; It appears that remove-gc-hook is simply a no-op, rather than causing an
; error, when the argument isn't installed as a :post-gc hook.

    'set-and-reset-gc-thresholds
    :post-gc)))

#+ccl
(defvar *gc-strategy*
  #-hons ; else initialized with set-gc-strategy in acl2h-init
  (progn (ccl::egc nil) t))

#+ccl
(defun start-sol-gc ()
  (error "Start-sol-gc has been replaced by set-gc-strategy (more ~%~
          specifically, by set-gc-strategy-builtin-delay).  See :DOC ~%~
          set-gc-strategy."))
