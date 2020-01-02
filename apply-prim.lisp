; ACL2 Version 8.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

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

; Essay on the APPLY$ Integration

; For an explanation of the logical foundations of apply$, see the paper
; ``Limited Second Order Functionality in a First Order Setting''.  We assume
; here that you are familiar with that paper and the terminology it uses.

; The basic logical development of apply$ proceeds in three steps: (i) defining
; apply$-prim, etc., to interpret built-in symbols like CONS and BINARY-+, (ii)
; constraining badge-userfn and apply$-userfn which will be connected to
; user-defined functions via warrants, and (iii) defining badge, tamep, apply$,
; and defwarrant in terms of the functions in (i) and (ii).

; The paper above explains how an ordinary certified book could be used to
; introduce apply$ into an ACL2 without native support for apply$ -- with one
; ``minor'' exception.  Indeed, that is how apply$ was developed (during the
; period 2015-2017 with ACL2 Versions 7.2 through 7.4).  Each of the three
; steps was carried out in its own certified book, appropriately named
; apply-prim, apply-constraints (aka ``constraints''), and apply.  We preserved
; that file basic structure when we integrated apply$ into the ACL2 source
; code.

; The ``minor'' exception noted above is that without native support it is
; impossible to execute apply$: apply$-userfn is constrained.  Only by
; implicitly assuming warrants can apply$ run a user-defined function, and the
; implicit extension of the ``evaluation theory'' to include all warrants
; required changes to ACL2 itself.  Our desire to support execution naturally
; meant we had to make those changes and upon completion of that integration
; task we named the resulting ACL2 Version_8.0.

; Ground apply$ terms can only be executed at the top-level because execution
; implicitly assumes warrants.  Conservativity forces us to require that
; warrants be explicit in proofs.  Thus, execution of apply$ is via attachments
; to badge-userfn and apply$-userfn and the concrete functions used must be
; built into ACL2's sources since they must ``magically'' determine whether the
; corresponding function symbols have warrants in the current world.

; Below is a guide to the files primarily related to the integration of apply$
; into our source code.  Of course, the name ``APPLY$'' and related symbols are
; sprinkled throughout the ACL2 source files now, e.g., in
; *initial-logic-fns-with-raw-code*, but these are the main files and books
; and we list them in four groups explained below.

; Foundations:
;  books/projects/apply-model/
;    apply-prim.lisp
;    apply-constraints.lisp
;    apply.lisp
;    ex1/*
;    ex2/*

; Source Code:
;  other-events.lisp
;  apply-prim.lisp
;  apply-constraints.lisp
;  apply.lisp
;  apply-raw.lisp

; Bootstrapping:
;  books/system/apply/apply-prim.lisp
;  books/system/apply/apply-constraints.lisp
;  books/system/apply/apply.lisp

; User:
;  books/projects/apply/base.lisp
;  books/projects/apply/report.lisp

; * The Foundations Group preserves the original construction of apply$ by
; defining it exactly as in the paper ``Limited Second Order Functionality in a
; First Order Setting'' but in a different symbol package (since functions of
; those names are now defined in ACL2).  The subdirectories ex1/ and ex2/
; illustrate the claim (proved in the paper) that for any set of functions
; accepted by defwarrant it is possible to define badge-userfn and
; apply$-userfn so that all warrants are valid.  We regard the Foundation books
; as a historic record and thus static; the books correspond to the paper.

; * The Source Code Group contains the five files that introduce apply$, et al,
; into the source code.  The first one listed above, other-events.lisp, just
; introduces two partially constrained functions, doppelganger-badge-userfn and
; doppelganger-apply$-userfn, that play a role in the implementation of the
; evaluation theory for apply$.  We do not discuss that file further here since
; it is overwhelmingly concerned with events not related to apply$, but we
; discuss the concrete functions extensively in apply-raw.lisp.

; The next three files, apply-prim, apply-constraints, and apply, correspond to
; their Foundations counterparts except they only contain the defuns and
; constraints but not the machinery needed to prove termination and guards.

; The fourth, apply-raw, defines the ``magic'' concrete functions that will be
; attached to badge-userfn and apply$-userfn to enable top-level execution of
; apply$.  It also implements a fast version of apply$-lambda that involves
; compilation and a cache.  And finally, perhaps incongruously, it includes, at
; the very end, a 1500 line Essay on Admitting a Model for Apply$ and the
; Functions that Use It.  That essay is mentioned in the above cited paper,
; ``Limited Second Order Functionality in a First Order Setting,'' which
; explains that we can can build a model of apply$ and all warranted functions
; so that all warrants are valid, but the paper only sketches the proof that
; the model can be admitted.  The essay contains the full proof.

; At the time apply$ was integrated (Version_8.0) the relevant definitions in
; the Source Code Group files were the same (modulo some bootstrapping issues
; noted below) as their counterparts in the Foundations files.  However, over
; time we imagine the support for apply$ in ACL2 will go beyond what is
; described in the paper, e.g., we might enlarge or shrink the set of
; primitives, extend the syntactic class of tame expressions, or make
; defwarrant able to handle mutual recursion.

; * The Bootstrapping Group contains the definitions of the Source Code group
; but also contains the measures and other machinery needed to prove
; termination and guards.  For example, the apply$ clique in the Foundations
; group is justified by a well-founded lexicographic relation, but such
; relations are not available in ACL2 until after the ordinals/ books have been
; certified.  So apply$ cannot be admitted in the Source Code group the way it
; was in the Foundations group.  Similar problems are encountered several times
; during the build of ACL2, specifically when the :acl2-devel feature is set.
; For documentation of the acl2-devel process, see :DOC
; verify-guards-for-system-functions, or see the comment in source constant
; *system-verify-guards-alist* in boot-strap-pass-2-b.lisp.

; (The basic story is that we first introduce such functions in :program
; mode, build an ``:acl2-devel'' image of the system, redundantly define the
; functions we wish to upgrade in various systems/ books, certify all those
; systems/ books with the :acl2-devel image, check that the data in
; *system-verify-guards-alist* is justified by the books just certified, and
; then build the public image of ACL2 in which we trustingly use
; *system-verify-guards-alist* to assert that the functions terminate and are
; guard verified.  The books in the Bootstrapping group must track the
; definitions in the Source Code group: changing one without the changing the
; other will probably result in the failure of the :acl2-devel certification of
; the system/ books.)

; * The User Group contains lemmas and examples that will probably be of value
; to ACL2 users wishing to prove things about functions that use apply$.

; End of Essay on the APPLY$ Integration

; The Maximal Defun of Apply$-Prim

; We define *apply$-primitives*, apply$-primp, and apply$-prim to include
; almost all functions in the bootstrap world that could have badges.  We
; intentionally skip a few problematic or silly primitives, like wormhole1
; which has some syntactic restrictions on how it can be called -- restrictions
; that would complicate or confuse any attempt to apply$ 'wormhole1.

; Historical Note: Before apply$ was integrated over 800 symbols satisfied
; apply$-primp.  After integration, that number dropped to slightly fewer than
; 800 because at the time this file is processed as part of the build not quite
; all primitives have been introduced.  (Indeed, this is one of the reasons we
; process this file rather late in the build.)  As a consequence, we have
; changed occurrences of ``800+'' to ``~800'' and recognize that the exact
; number may vary as the sources and build process change.

(in-package "ACL2")

; Handling the Primitives

(defun first-order-like-terms-and-out-arities1 (runes avoid-fns wrld ans)
  (declare (xargs :mode :program))

; We return a list of the form (... ((fn . formals) . output-arity) ...).  See
; first-order-like-terms-and-out-arities for details.

  (cond
   ((endp runes) ans)
   (t (let ((fn (base-symbol (car runes))))
        (cond
         ((and (acl2-system-namep fn wrld)

; In ACL2(r), we avoid non-classical functions, to avoid failure of the
; defevaluator event in the book version of apply-prim.lisp.

; But there's a deeper reason to avoid non-classical functions.  The logical
; story behind apply$ involves introducing a single mutual-recursion that
; defines apply$ and all functions.  See for example
; books/projects/apply-model/ex1/doppelgangers.lisp.  But ACL2(r) does not
; permit recursive definitions of non-classical functions.

; Even if we could work through that concern, it may well be wrong to give a
; badge to a non-classical function, because the usual test for non-classical
; functions in a body would not notice the first argument of a call, (apply
; 'non-classical-function ...).

               #+:non-standard-analysis
               (classicalp fn wrld)

               (not (member-eq fn avoid-fns))
               (all-nils (getpropc fn 'stobjs-in nil wrld))

; Note that even functions taking state like state-p and global-table-cars,
; i.e., that take a STATE-STATE input, will have STATE in their stobjs-in and
; hence will fail the test just above.  So we don't need to give special
; treatment to such functions.

               (all-nils (getpropc fn 'stobjs-out nil wrld)))

; Note that stobj creators take no stobjs in but return stobjs.  We don't want
; any such functions in our answer!  Also, we don't want to think about
; functions like BOUNDP-GLOBAL1 and 32-BIT-INTEGER-STACK-LENGTH1 that use
; STATE-STATE as a formal preventing their execution.

          (first-order-like-terms-and-out-arities1
           (cdr runes)
           avoid-fns wrld
           (cons (cons (cons fn (formals fn wrld))
                       (length (getpropc fn 'stobjs-out nil wrld)))
                 ans)))
         (t (first-order-like-terms-and-out-arities1
             (cdr runes)
             avoid-fns wrld
             ans)))))))

; Note: The following list is used to determine ancestral dependence on
; apply$-userfn.  But because apply$ calls apply$-userfn, we think it is
; probably most efficient to look for apply$ and ev$ instead of just
; apply$-userfn.  Would it be more efficient still to include the loop$ scions
; in this list?  On the one hand it would save us from exploring them.  On the
; other, we'd the list would be longer and more often than not we wouldn't find
; fn on it anyway.  We opt not to include the loop$ scions.

(defconst *apply$-userfn-callers*
  '(apply$ ev$ apply$-userfn))

(defconst *blacklisted-apply$-fns*

; The functions listed here are not safe to apply, primarily because their
; behavior differs from their logical definitions.

   '(SYNP                                      ; bad
     HIDE                                      ; stupid
     WORMHOLE1                                 ; restricts arguments
     WORMHOLE-EVAL                             ; restricts arguments
     SYS-CALL                                  ; bad -- requires trust tag
     HONS-CLEAR!                               ; bad -- requires trust tag
     HONS-WASH!                                ; bad -- requires trust tag
     UNTOUCHABLE-MARKER                        ; bad -- untouchable
     ))

; At one time we considered disallowing these functions but we now allow them.
; We list them here just to document that we considered them and concluded that
; it is ok to apply$ them.

;    MV-LIST                                   ; we now handle multiple values
;    MAKE-WORMHOLE-STATUS
;    SET-WORMHOLE-DATA
;    SET-WORMHOLE-ENTRY-CODE
;    WORMHOLE-DATA
;    WORMHOLE-ENTRY-CODE
;    WORMHOLE-STATUSP
;    BREAK$
;    PRINT-CALL-HISTORY
;    NEVER-MEMOIZE-FN
;    MEMOIZE-FORM
;    CLEAR-MEMOIZE-STATISTICS
;    MEMOIZE-SUMMARY
;    CLEAR-MEMOIZE-TABLES
;    CLEAR-MEMOIZE-TABLE

(defun first-order-like-terms-and-out-arities (world)

; Search the world for every ACL2 primitive function that does not traffic (in
; or out) in stobjs or state and that are not among a select few (named below)
; that require trust tags or have syntactic restrictions on their calls.  Note
; that our final list includes functions that return multiple values, which are
; not warranted but will have badges: they are first-order-like and could be
; used in the subsequent definitions of warranted functions provided their
; multiple values are ultimately turned into a single returned value.

; Return (... ((fn . formals) . output-arity) ...), that for each identified
; fn, pairs a term, (fn . formals), with its output arity.  We will ultimately
; need those terms to generate the defevaluator event that will define
; apply$-prim and to generate the :meta theorem we need.  We need the output
; arity in computing the badges of the functions; see
; compute-badge-of-primitives.

; We accumulate the pairs in reverse order, which (it turns out) puts the most
; basic, familiar ACL2 primitives first.

; The ``select few'' we do not collect are prohibited as per the comments
; below.  Note: Many functions that we do include actually have no utility in
; this setting.  The symbols commented out below were once so identified (by
; manual inspection).  E.g., does any user really want to call
; make-wormhole-status via apply$?  But if all calls are legal without a trust
; tag, we now include it, just to live up to the name "Maximal".

  (declare (xargs :mode :program))
  (first-order-like-terms-and-out-arities1
   (function-theory :here)
   *blacklisted-apply$-fns*
   world
   nil))

; We need to know the names, formals, and output arities of the primitives in
; order to generate the defevaluator form, meta theorem, and badges below.  So
; we save them in *first-order-like-terms-and-out-arities*, which looks like:

; (defconst *first-order-like-terms-and-out-arities*
;   '(((ACL2-NUMBERP X) . 1)
;     ((BAD-ATOM<= X Y) . 1)
;     ((BINARY-* X Y) . 1)
;     ...))

; But in apply.lisp and in the support for the execution of the stubs
; badge-userfn and apply$-userfn we do not need the formals and we sometimes
; need the arities.  So we define another constant which is used in those
; places.  That constant, *badge-prim-falist*, is a fast alist.

(when-pass-2

; There is a bit of a boot-strap problem in defining the constant
; *first-order-like-terms-and-out-arities*.  ACL2 rightly complains about
; compiling make-event forms, so we mark this event with when-pass-2, along
; with those below that depend on it, in order to avoid compiling such forms.
; They will be evaluated during pass-2 of initialization.

(make-event ` ; backquote here so that the next line can assist tags
(defconst *first-order-like-terms-and-out-arities*
  ',(first-order-like-terms-and-out-arities (w state)))
))

; We originally defined the apply$-badge record here.  But it is needed in
; warrantp, which is needed in defattach-constraint-rec.
; (defrec apply$-badge (arity out-arity . ilks) nil)

(defun compute-badge-of-primitives (terms-and-out-arities)
  (declare (xargs :mode :program))
  (cond ((endp terms-and-out-arities) nil)
        (t (let* ((term (car (car terms-and-out-arities)))
                  (fn (ffn-symb term))
                  (formals (fargs term))
                  (output-arity (cdr (car terms-and-out-arities))))
             (hons-acons fn
                         (make apply$-badge
                               :arity (length formals)
                               :out-arity output-arity
                               :ilks t)
                         (compute-badge-of-primitives
                          (cdr terms-and-out-arities)))))))

; Much of the rest of the file depends on the make-event above that generates
; (defconst *first-order-like-terms-and-out-arities* ...).  So we wrap the next
; several forms in when-pass-2; see the comment at the make-event above.

(when-pass-2 ; See comment above regarding "depends on the make-event above."

(defconst *badge-prim-falist* ; this is a fast-alist!
  (compute-badge-of-primitives *first-order-like-terms-and-out-arities*))

(defun apply$-primp (fn)
  (declare (xargs :mode :logic :guard t))
  (and (hons-get fn *badge-prim-falist*) t))

(defun badge-prim (fn)
  (declare (xargs :mode :logic :guard t))
  (cdr (hons-get fn *badge-prim-falist*)))

)

(defun apply$-badgep (x)
  (declare (xargs :guard t))
  (and (weak-apply$-badge-p x)
       (natp (access apply$-badge x :arity))
       (natp (access apply$-badge x :out-arity))
       (or (eq (access apply$-badge x :ilks) t)
           (and (true-listp (access apply$-badge x :ilks))
                (equal (len (access apply$-badge x :ilks))
                       (access apply$-badge x :arity))
                (not (all-nils (access apply$-badge x :ilks)))
                (subsetp (access apply$-badge x :ilks) '(nil :fn :expr))))))

(defun n-car-cadr-caddr-etc (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
      (cons `(CAR ,x)
            (n-car-cadr-caddr-etc (- n 1) `(CDR ,x)))))

(defun make-apply$-prim-body-fn (falist acc)

; WARNING: Keep this in sync with make-apply$-prim-body-fn-raw.

; Falist = ((fn . badge) ...) and is a fast alist although we do not actually
; use it as an alist here; we just cdr down it.

; We produce the guts of the body used in the defun of APPLY$-PRIM.  That
; function will be defined as:

; (defun apply$-prim (fn args)
;   (declare (xargs :guard (true-listp args)))
;   (case fn
;    (ACL2-NUMBERP (ACL2-NUMBERP (CAR ARGS)))
;    (BAD-ATOM<=   (EC-CALL (BAD-ATOM<= (CAR ARGS)
;                                       (CAR (CDR ARGS)))))
;    ...
;    (otherwise nil))

; and this function constructs the part in all-caps above.  The EC-CALLs
; surround every call of each apply$ primitive except the ones where we know it
; is not necessary.

  (declare (xargs :mode :program))
  (cond
   ((endp falist) (reverse acc)) ; reversing might be unnecessary
   (t (let* ((fn (car (car falist)))
             (badge (cdr (car falist)))
             (call1 `(,fn ,@(n-car-cadr-caddr-etc
                             (access apply$-badge badge :arity)
                             'ARGS)))
             (call2 (if (member-eq fn *EC-CALL-BAD-OPS*)
                        (cond ((eq fn 'return-last)
                               '(caddr args))
                              ((eq fn 'mv-list)
                               '(cadr args))
                              (t call1))
                        `(ec-call ,call1)))
             (call3 (if (int= (access apply$-badge badge :out-arity) 1)
                        call2
                        `(mv-list ',(access apply$-badge badge :out-arity)
                                  ,call2))))
        (make-apply$-prim-body-fn
         (cdr falist)
         (cons `(,fn ,call3) acc))))))

; It will be necessary to disable the executable-counterpart of break$ when
; verifying the guards for apply$-prim, as is done by "make proofs".  It seems
; reasonable actually to disable that rune globally, to avoid breaks during
; proofs; so we do that.  We also disable the executable-counterpart of
; good-bye-fn; otherwise ACL2 can quit during a proof!
(in-theory (disable (:e break$) (:e good-bye-fn)))

#-acl2-loop-only
(progn

(defvar *apply$-prim-ht* (make-hash-table :test 'eq))

(defun make-apply$-prim-body-fn-raw (falist ht)

; WARNING: Keep this in sync with make-apply$-prim-body-fn.

; The present function's name is perhaps a bit misleading, since it doesn't
; create a function body, but rather, it populates the given hash-table, which
; will actually be *apply$-prim-ht*.

; See make-apply$-prim-body-fn.  Note that we do not handle return-last
; specially here, unlike make-apply$-prim-body-fn.

  (cond
   ((endp falist) nil) ; reversing might be unnecessary
   (t (let* ((fn (car (car falist)))
             (badge (cdr (car falist)))
             (fn-to-call

; Fn-to-call is the name of the function we're to call when fn is applied.  It
; is typically fn itself but maybe *1*fn.

              (cond ((member fn *ec-call-bad-ops*
                             :test 'eq)
                     fn)
                    (t (let ((*1*fn (*1*-symbol fn)))
                         (assert (fboundp *1*fn))
                         *1*fn)))))
        (setf (gethash fn ht)
              (list* fn-to-call
                     (access apply$-badge badge :arity)
                     (access apply$-badge badge :out-arity)))
        (make-apply$-prim-body-fn-raw (cdr falist) ht)))))

(defun apply$-prim (fn args)
  (cond ((eq fn 'return-last)
         (caddr args))
        ((eq fn 'mv-list)
         (cadr args))
        (t (let ((trip (gethash fn *apply$-prim-ht*)))
             (and trip
                  (let ((fn2 (car trip))
                        (arity (cadr trip))
                        (out-arity (cddr trip)))
                    (let ((args (if (int= arity (length args))
                                    args
                                    (take arity args))))
                      (if (int= out-arity 1)
                          (apply fn2 args)
                          (multiple-value-list (apply fn2 args))))))))))

(defun-*1* apply$-prim (fn args)
  (if (true-listp args) ; guard
      (apply$-prim fn args)
    (gv apply$-prim (fn args) (apply$-prim fn (fix-true-list args)))))

)

(when-pass-2

; We use when-pass-2 because of dependence on *badge-prim-falist*.  See comment
; above regarding "depends on the make-event above."

(set-raw-mode t)

(make-apply$-prim-body-fn-raw *badge-prim-falist* *apply$-prim-ht*)

(set-raw-mode nil)

(defmacro make-apply$-prim-body ()
  `(case fn
     ,@(make-apply$-prim-body-fn *badge-prim-falist* nil)
     (otherwise nil)))

#+acl2-loop-only
(defun apply$-prim (fn args)
  (declare (xargs :guard (true-listp args)))
  (make-apply$-prim-body))

)

