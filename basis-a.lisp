; ACL2 Version 8.6 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2025, Regents of the University of Texas

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

; The code in this file was originally placed in several different source
; files, but was moved here in order to support the creation of "toothbrush"
; applications -- that is, so that fewer ACL2 source files need to be loaded in
; order to support ACL2 applications.  See community books file
; books/system/toothbrush/README.

(in-package "ACL2")

; Start definitions related to defun-inline.

(defun-inline +f!-fn2 (x y)

; The form (add-macro-alias +f!-fn2 +f!-fn2$inline) in boot-strap-pass-2-b.lisp
; is explained there.

; See +f!.

  (declare (type #.*fixnat-type* x y))
  (the-fixnat
   (min (the (unsigned-byte #.*fixnat-bits+1*)
             (+ x y))
        (fixnum-bound))))

(defun-inline +f!-fn3 (x y z)

; The form (add-macro-alias +f!-fn3 +f!-fn3$inline) in boot-strap-pass-2-b.lisp
; is explained there.

; See +f!.

  (declare (type #.*fixnat-type* x y z))
  (the-fixnat
   (min (the (unsigned-byte #.*fixnat-bits+2*)
             (+ x y z))
        (fixnum-bound))))

(defmacro +f! (x y &optional z)

; For fixnats x and y, and optionally z, we return the minimum of (+ x y) and
; (fixnum-bound), using only actual Lisp fixnum arithmetic (for virtually all
; Lisps).  No error takes place due to (fixnum-bound) being exceeded by (+ x
; y).

  (if z
      `(+f!-fn3 ,x ,y ,z)
    `(+f!-fn2 ,x ,y)))

; Case-match

(defun equal-x-constant (x const)

; x is an arbitrary term, const is a quoted constant, e.g., a list of
; the form (QUOTE guts).  We return a term equivalent to (equal x
; const).

  (declare (xargs :guard (and (consp const)
                              (eq (car const) 'quote)
                              (consp (cdr const)))))
  (let ((guts (cadr const)))
    (cond ((symbolp guts)
           (list 'eq x const))
          ((or (acl2-numberp guts)
               (characterp guts))
           (list 'eql x guts))
          ((stringp guts)
           (list 'equal x guts))
          (t (list 'equal x const)))))

(defun match-tests-and-bindings (x pat tests bindings dups)

; We return three results.  The first is a list of tests, in reverse order,
; that determine whether x matches the structure pat.  We describe the language
; of pat below.  The tests are accumulated onto tests, which should be nil
; initially.  The second result is an alist, accumulated into bindings in
; reverse order (though the order is irrelevant), containing entries of the
; form (sym expr), suitable for use as the bindings in the let we generate if
; the tests are satisfied.  The third is a list of variables, accumulated into
; dups, that are bound more than once in the constructed alist; these will be
; used for generating ignore declarations.

; For example, the pattern
;   ('equal ('car ('cons u v)) u)
; matches only first order instances of (EQUAL (CAR (CONS u v)) u).

; The pattern
;   ('equal (ev (simp x) a) (ev x a))
; matches only second order instances of (EQUAL (ev (simp x) a) (ev x a)),
; i.e., ev, simp, x, and a are all bound in the match.

; In general, the match requires that the cons structure of x be isomorphic to
; that of pat, down to the atoms in pat.  Symbols in the pat denote variables
; that match anything and get bound to the structure matched.  Occurrences of a
; symbol after the first match only structures equal to the binding.
; Non-symbolp atoms match themselves.

; There are some exceptions to the general scheme described above.  A cons
; structure starting with QUOTE matches only itself.  A cons structure of the
; form (QUOTE~ sym), where sym is a symbol, is like (QUOTE sym) except it
; matches any symbol with the same symbol-name as sym.  The symbols nil and t,
; and all symbols whose symbol-name starts with #\* match only structures equal
; to their values.  (These symbols cannot be legally bound in ACL2 anyway, so
; this exceptional treatment does not restrict us further.)  Any symbol
; starting with #\! matches only the value of the symbol whose name is obtained
; by dropping the #\!.  This is a way of referring in the pattern to already
; bound variables.  Finally, the symbol & matches anything and causes no
; binding.

  (declare (xargs :guard (and (symbol-doublet-listp bindings)
                              (true-listp dups))))
  (cond
   ((symbolp pat)
    (cond
     ((or (eq pat t)
          (eq pat nil)
          (keywordp pat))
      (mv (cons (list 'eq x pat) tests) bindings dups))
     ((let ((len (length (symbol-name pat))))
        (and (> len 0)
             (eql #\* (char (symbol-name pat) 0))
             (eql #\* (char (symbol-name pat) (1- len)))))
      (mv (cons (list 'equal x pat) tests) bindings dups))
     ((and (> (length (symbol-name pat)) 0)
           (eql #\! (char (symbol-name pat) 0)))
      (mv (cons (list 'equal x
                      (intern-in-package-of-symbol
                       (subseq (symbol-name pat)
                               1
                               (length (symbol-name pat)))
                       pat))
                tests)
          bindings
          dups))
     ((eq pat '&) (mv tests bindings dups))
     (t (let ((binding (assoc-eq pat bindings)))
          (cond ((null binding)
                 (mv tests (cons (list pat x) bindings) dups))
                (t (mv (cons (list 'equal x (cadr binding)) tests)
                       bindings
                       (add-to-set-eq pat dups))))))))
   ((atom pat)
    (mv (cons (equal-x-constant x (list 'quote pat)) tests)
        bindings
        dups))
   ((and (eq (car pat) 'quote)
         (consp (cdr pat))
         (null (cddr pat)))
    (mv (cons (equal-x-constant x pat) tests)
        bindings
        dups))
   ((and (eq (car pat) 'quote~)
         (consp (cdr pat))
         (symbolp (cadr pat))
         (null (cddr pat)))
    (mv (cons (list 'symbol-name-equal x (symbol-name (cadr pat))) tests)
        bindings
        dups))
   (t (mv-let (tests1 bindings1 dups1)
        (match-tests-and-bindings (list 'car x) (car pat)
                                  (cons (list 'consp x) tests)
                                  bindings dups)
        (match-tests-and-bindings (list 'cdr x) (cdr pat)
                                  tests1 bindings1 dups1)))))

(defun match-clause (x pat forms)
  (declare (xargs :guard t))
  (mv-let (tests bindings dups)
    (match-tests-and-bindings x pat nil nil nil)
    (list (if (null tests)
              t
            (cons 'and (reverse tests)))
          `(let ,(reverse bindings)
             ,@(and dups `((declare (ignorable ,@dups))))
             ,@forms))))

(defun match-clause-list (x clauses)
  (declare (xargs :guard (alistp clauses)))
  (cond ((consp clauses)
         (if (eq (caar clauses) '&)
             (list (match-clause x (caar clauses) (cdar clauses)))
           (cons (match-clause x (caar clauses) (cdar clauses))
                 (match-clause-list x (cdr clauses)))))
        (t '((t nil)))))

(defmacro case-match (&rest args)
  (declare (xargs :guard (and (consp args)
                              (symbolp (car args))
                              (alistp (cdr args))
                              (null (cdr (member-equal (assoc-eq '& (cdr args))
                                                       (cdr args)))))))
  (cons 'cond (match-clause-list (car args) (cdr args))))

; Essay on Wormholes

; See :doc wormhole for the basic idea.  Wormholes provide access to state from
; places without access to state.  Their main purpose is to allow the
; collection and display of data, and to allow user interaction, without
; changing state.  Associated with every wormhole is an ACL2 object called its
; ``persistent wormhole status'' or ``persistent-whs.''  The shape of these
; status objects varies with the wormhole and is determined by the author of
; the wormhole (though the car of each status object is always supposed to be
; :SKIP or :ENTER).  The persistent-whs is accessible to ACL2 terms only via
; the ACL2 oracle.  That is, we think of the persistent-whs as outside of the
; ACL2 state or hidden.

; To get the persistent-whs of a wormhole one can use (get-persistent-whs name
; state) => (mv whs state').  Note that it changes state by using
; read-acl2-oracle to get the whs.  Thus, this is not a very convenient
; interface to wormholes since one of the main purposes is to not change state!

; However, the function wormhole-eval allows the caller to change the
; persistent-whs as a function of the current status without ever exporting it.
; Roughly speaking, wormhole-eval takes a wormhole name and a lambda
; expression, applies the lambda expression to the persistent-whs of the named
; wormhole, and stores the result back into the persistent-whs.  Wormhole-eval
; does not take state as an argument and always returns nil.  So, for example,
; you can accumulate data into the persistent-whs with wormhole-eval, without
; ever making the status available outside.  You can also print from within
; wormhole-eval to display the accumulated data.  You now know how
; accumulated-persistence and fc-report are implemented.

; In order to allow user interaction with a wormhole, e.g., as provided by
; break-rewrite, the function wormhole is provided.  Roughly speaking, it takes
; a wormhole name, a lambda expression, an arbitrary object, input, and a
; quoted untranslated term, first-form.  Wormhole does not take state.  It
; applies the lambda expression to the persistent-whs of the named wormhole and
; if the resulting persistent-whs has car :ENTER (actually, if the car is not
; :SKIP),

; (a) provisions are made so that all allowed state changes are undone upon
;     exit,

; (b) the wormhole name, input, and the persistent-whs are (undoably) assigned
;     to the state global variables wormhole-name, wormhole-input, and
;     wormhole-status,

; (c) LD is invoked on *the-live-state* so that the first form read and eval'd
;     by LD is first-form,

; (d) when that LD is exited the value of the state global wormhole-status is
;     stored as the new persistent-whs for the wormhole,

; (e) all state changes are undone, and

; (f) wormhole returns nil.

; Entering a wormhole is thus expensive, which is why it's gated by the lambda
; expression and wormhole-eval (which are implemented efficiently).

; Historical Note: Once upon a time (Version 3.6 and earlier) the wormhole
; function had a pseudo-flg argument which allowed the user a quick way to
; determine whether it was appropriate to incur the expense of going into the
; wormhole.  The idea was that the form could have one a free var in it,
; wormhole-output, and that when it was evaluated in raw Lisp that variable was
; bound to the last value returned by the wormhole.  Since wormhole always
; returned nil anyway, this screwy semantics didn't matter.  However, it was
; implemented in such a way that a poorly constructed pseudo-flg could survive
; guard verification and yet cause a hard error at runtime because during guard
; verification wormhole-output was bound to NIL but in actual evaluation it was
; entirely under the control of the wormhole forms.  End of Historical Note.

; While in the wormhole, forms evaluated by the LD can access the wormhole
; status with (f-get-global 'wormhole-status state).  But that status will
; ``disappear'' when the wormhole is exited.  So we call that the
; ``ephemeral-whs.''

; Thus, from within the wormhole the ephemeral-whs can be inspected, computed
; with, printed, etc.  This is very handy because it means code executed in the
; wormhole can easily access the previously inaccessible status.

; But the emphemeral whs cannot be directly changed.  That is: wormhole-status
; is untouchable, even from within the wormhole: (f-put-global 'wormhole-status
; new-whs state) will cause an error.  This is necessary to prevent the
; interactive user from violating invariants we maintain on system wormholes.

; While in a user wormhole (not a system wormhole), the user can call
; wormhole-eval to change the persistent-whs.  An example of why this might
; happen is provided by the :monitor command of break-rewrite.  At the
; top-level of ACL2 the user will use :monitor to install a monitor on a rune.
; The list of monitored runes is maintained inside the brr wormhole to allow
; the user to add new monitors during a proof attempt, without changing state.
; So :monitor is defined in terms of wormhole-eval.  So if the user adds a new
; :monitor while inside brr, the persistent-whs of the brr wormhole is changed.

; ``Wormhole coherence'' is the concept that the persistent-whs and the
; ephemeral-whs are equal.  Think of the persistent-whs as the value of a
; remote memory location and the ephemeral-whs as a nearby cache.

; Note that the use of wormhole-eval from within a wormhole can make the
; persistent-whs and the ephemeral-whs unequal.  We say such a wormhole is
; ``incoherent.''

; The function sync-ephemeral-whs-with-persistent-whs does what its name
; suggests and restores coherence.  The code for system wormholes like brr is
; careful to maintain coherence, e.g., :monitor uses wormhole-eval to change
; the persistent-whs and then sync-ephemeral-whs-with-persistent-whs to to
; restore coherence.  But users implementing wormholes of their own have to
; decide whether they care about coherence or not.  (Note: if all reads and
; writes to a wormhole's status are done with wormhole-eval, you needn't even
; think about coherence.  There is never an ephemeral-whs; all operations are
; done at a single location, the persistent-whs.  It's only when interaction is
; allowed that one might need to worry about two copies of ``the'' status.)

; A better way, from within a wormhole, to change the status is to change both,
; using set-persistent-whs-and-ephemeral-whs.

; See :doc wormhole-programming-tips.

; Now for a few more implementation-level details.

; The persistent-whs of each wormhole is stored in an alist in raw Lisp.  The
; alist is named *wormhole-status-alist*.

; Wormhole-eval takes two important arguments, the name of the wormhole and a
; lambda expression.  Both must be quoted in user input.  (Translate allows
; developers to use variables in the name position during boot-strap.)  The
; lambda may have at most one argument but the body may contain any variables
; available in the environment of the wormhole-eval call.  (A third argument to
; wormhole-eval is an arbitrary form that uses all the free vars of the lambda,
; thus insuring that translate will cause an error if the lambda uses variables
; unavailable in the context.)  The body of the lambda must be a single-valued,
; non-state, non-stobj term.

; Translation of a wormhole-eval call enforces these restrictions.
; Furthermore, it translates the body of the lambda (even though the lambda is
; quoted).  This is irrelevant since the wormhole-eval returns nil regardless
; of the lambda expression supplied.  Similarly, translation computes an
; appropriate third argument to use all the free vars, so the user may just
; write nil there and a suitable form is inserted by translate.

; We arrange for wormhole-eval to be a macro in raw lisp that really does what
; is said above, so it is as efficient as we can make.  I.e., the lambda
; expression is not applied, it is compiled in place.

; To make it bullet-proof, when we generate guard clauses we go inside the
; lambda, generating a new variable symbol to use in place of the lambda formal
; denoting the last value of the wormhole output.  Thus, if guard clauses can be
; verified, it doesn't matter what the wormhole actually returns as its value.

; Ev-rec, the interpreter for terms, treats wormhole-eval specially in the
; expected way, as does oneify.  Thus, both interpreted and compiled calls of
; wormhole-eval are handled, and guard violations are handled politely.  So if
; you change wormholes you must also look at translate, ev-rec, oneify, and
; guard-clauses, at least!

; It is possible to enter a wormhole from within another wormhole.  It happens
; all the time when a wormhole prints using cw, which is implemented by the
; comment-window-io wormhole.

; If we wanted to convert our system code to logic mode we would want to verify
; the guards of the lambda bodies and the wormhole-status after ld.  See the
; comment in push-accp.  Here is a proposal for how to do that.  First, insist
; that wormhole names are symbols.  Indeed, they must be one argument,
; guard-verified Boolean functions.  The guard for a call of wormhole-eval on a
; wormhole named foo should include the conjunct (foo nil) to ensure that the
; initial value of the status is acceptable.  The guard on the body of (lambda
; (whs) body) should be extended to include the hypothesis that (foo whs) is
; true and that (foo whs) --> (foo body) is true.  We should then change
; wormhole so that if it calls ld it tests foo at runtime after the ld returns
; so we know that the final status satisfies foo.  If we do this we can safely
; assume that every status seen by a lambda body in wormhole-eval will satisfy
; the foo invariant.

; End of the Essay on Wormholes

(defun wormhole-statusp (whs)
  (declare (xargs :mode :logic :guard t))
  (or (equal whs nil)
      (and (consp whs)
           (or (eq (car whs) :ENTER)
               (eq (car whs) :SKIP)))))

(defun wormhole-entry-code (whs)

; Keep this function in sync with the inline code in wormhole1.

  (declare (xargs :mode :logic :guard t))
  (if (and (consp whs)
           (eq (car whs) :SKIP))
      :SKIP
      :ENTER))

(defun wormhole-data (whs)
  (declare (xargs :mode :logic :guard t))
  (if (consp whs)
      (cdr whs)
      nil))

(defun set-wormhole-entry-code (whs code)
  (declare (xargs :mode :logic
                  :guard (or (eq code :ENTER)
                             (eq code :SKIP))))
  (if (consp whs)
      (if (eq (car whs) code)
          whs
          (cons code (cdr whs)))
      (if (eq code :enter)
          whs
          (cons :skip whs))))

(defun set-wormhole-data (whs data)
  (declare (xargs :mode :logic :guard t))
  (if (consp whs)
      (if (equal (cdr whs) data)
          whs
          (cons (car whs) data))
      (cons :enter data)))

(defun make-wormhole-status (old-status new-code new-data)
  (declare (xargs :mode :logic
                  :guard (or (eq new-code :ENTER)
                             (eq new-code :SKIP))))
  (if (consp old-status)
      (if (and (eq new-code (car old-status))
               (equal new-data (cdr old-status)))
          old-status
          (cons new-code new-data))
      (cons new-code new-data)))

; (defthm wormhole-status-guarantees
;   (if (or (eq code :enter)
;           (eq code :skip))
;       (and (implies (wormhole-statusp whs)
;                     (wormhole-statusp (set-wormhole-entry-code whs code)))
;            (implies (wormhole-statusp whs)
;                     (wormhole-statusp (set-wormhole-data whs data)))
;            (equal (wormhole-entry-code (set-wormhole-entry-code whs code))
;                   code)
;            (equal (wormhole-data (set-wormhole-data whs data))
;                   data)
;            (implies (wormhole-statusp whs)
;                     (equal (wormhole-data (set-wormhole-entry-code whs code))
;                            (wormhole-data whs)))
;            (implies (wormhole-statusp whs)
;                     (equal (wormhole-entry-code
;                             (set-wormhole-data whs data))
;                            (wormhole-entry-code whs)))
;            (implies (wormhole-statusp whs)
;                     (wormhole-statusp (make-wormhole-status whs code data)))
;            (equal (wormhole-entry-code (make-wormhole-status whs code data))
;                   code)
;            (equal (wormhole-data (make-wormhole-status whs code data))
;                   data))
;       t)
;   :rule-classes nil)
;
; (verify-guards wormhole-status-guarantees)

; In particular, given a legal code, set-wormhole-entry-code preserves
; wormhole-statusp and always returns an object with the given entry code
; (whether the status was well-formed or not).  Furthermore, the guards on
; these functions are verified.  Thus, they can be called safely even if the
; user has messed up our wormhole status.  Of course, if the user has messed up
; the status, there is no guarantee about what happens inside the wormhole.

(defun tree-occur-eq (x y)

; Does symbol x occur in the cons tree y?

  (declare (xargs :guard (symbolp x)))
  (cond ((consp y)
         (or (tree-occur-eq x (car y))
             (tree-occur-eq x (cdr y))))
        (t (eq x y))))

#+acl2-loop-only
(defun wormhole-eval (qname qlambda free-vars)

; Warning: Keep this function in sync with the other functions listed in the
; Essay on the Wormhole Implementation Nexus in axioms.lisp.

; A typical call of this function is
; (wormhole-eval 'my-wormhole
;                '(lambda (output) (p x y output))
;                (list x y))

; And the pragmatic semantics is that the lambda expression is applied to the
; persistent-whs of the wormhole my-wormhole, the result of the application is
; stuffed back in as the persistent-whs, and the function logically returns
; nil.  Note that free vars in the lambda must be listed.  This is so that the
; free vars of this wormhole-eval expression consists of the free vars of the
; lambda, even though the lambda appears quoted.  Translate automatically
; replaces the lambda expression constant by the translated version of that
; same constant, and it replaces the supposed list of free vars by the actual
; free vars.  So in fact the user calling wormhole-eval can just put nil in the
; free-vars arg and let translate fill it in.  Translate can mangle the
; arguments of wormhole-eval because it always returns nil, regardless of its
; arguments.

; The guard is declared below to be t but actually we compute the guard for the
; body of the quoted lambda, with some fiddling about the bound variable.

; (Remember: the quoted lambda of wormhole-eval is unrelated to apply$.)

  (declare (xargs :mode :logic
                  :guard t)
           (ignore qname qlambda free-vars))


  nil)

(deflock *wormhole-lock*)

#-acl2-loop-only
(defun put-assoc-equal-destructive (key val alist)
  (let ((pair (assoc-equal key alist)))
    (cond (pair (setf (cdr pair) val)
                alist)
          (t (acons key val alist)))))

(defun wormhole-eval-early-null-exit-p (qlambda)

; This function recognizes quoted lambdas that are subject to the wormhole-eval
; optimization of returning immediately when the wormhole-data is nil, which is
; reasonable since the old and new status are then equal.

  (case-match qlambda
    (('quote ('lambda (whs)
               ('let ((info ('wormhole-data whs)))
                 ('cond (('null info) whs) . &))))
     (declare (ignore info whs))
     t)
    (& nil)))

#-acl2-loop-only
(defmacro wormhole-eval (namex qlambda free-vars)
  (declare (xargs :guard t))

; Warning: Keep this function in sync with the other functions listed in the
; Essay on the Wormhole Implementation Nexus in axioms.lisp.

; All calls of wormhole-eval that have survived translation are of a special
; form.  Namex is a term that evaluates to the name of a wormhole, and qlambda
; is of one of the two forms:

; (i)  (quote (lambda (whs) body)), or
; (ii) (quote (lambda ()    body))

; where whs (``wormhole status'') is a legal variable symbol, body is a fully
; translated term that may involve whs and other variables which returns one
; result.  We furthermore know that the free vars in the lambda are the free
; vars of the term free-vars, which is typically just a list-expression of
; variable names supplied by translate.  Finally, we know that whs appears as
; the lambda formal iff it is used in body.

; Wormholes may have arbitrary objects for names, so namex does not necessarily
; evaluate to a symbol.  This may be the first entry into the wormhole of that
; name, in which case the most recent output of the wormhole is understood to
; be nil.

; Logically this function always returns nil.  Actually, it applies the lambda
; expression to either (i) persistent-whs of the named wormhole or (ii) no
; arguments, appropriately, and stores the result as the persistent-whs, and
; then returns nil.

; For efficiency we use put-assoc-equal-destructive below instead of put-assoc.
; When considering a similar use of put-assoc-equal-destructive elsewhere --
; specifically, in ev-rec and in a cleanup form in wormhole1 -- then we should
; think about whether locks might be needed for ACL2(p).  We do have a lock
; here, by default.

  (let* ((whs (car (cadr (cadr qlambda)))) ; non-nil in Case (i) only
         (early-null-exit-p (and whs
                                 (wormhole-eval-early-null-exit-p qlambda)))
         (name (gensym)) ; name will be bound to the value of namex
         (val (gensym))  ; val will be bound to the value of the lambda body
         (form1
          `(let* ((*wormholep* t)
                  ,@(and whs                       ; Case (i)
                         (not early-null-exit-p)   ; otherwise bind whs later
                         `((,whs
                            (cdr (assoc-equal ,name
                                              *wormhole-status-alist*)))))
                  (,val ,(caddr (cadr qlambda))))

; At one time we skipped the following setq in the case that (equal ,whs ,val),
; where ,whs was unconditionally bound above.  However, that equality test can
; be expensive, so we avoid it.

             (setq *wormhole-status-alist*
                   (put-assoc-equal-destructive ,name
                                                ,val
                                                *wormhole-status-alist*))
             nil))
         (form2 (cond ((tree-occur-eq :no-wormhole-lock free-vars)
                       form1)
                      (t `(with-wormhole-lock ,form1)))))
    (cond (early-null-exit-p ; hence whs is non-nil
           `(let* ((,name ,namex)
                   (,whs (cdr (assoc-equal ,name
                                          *wormhole-status-alist*))))
              (cond ((null (wormhole-data ,whs))

; Wormhole-data doesn't change (see wormhole-eval-early-null-exit-p), so we
; simply return.

                     nil)
                    (t ,form2))))
          (t `(let ((,name ,namex)) ,form2)))))

(defun sync-ephemeral-whs-with-persistent-whs (name state)

; If you are in the named wormhole, this function updates ephemeral-whs to be
; the persistent-whs, achieving Wormhole Coherence.  If you are not in the
; named wormhole, this function is a no-op returning state and the wormhole is
; coherent since there is no ephemeral-whs.

  (declare (xargs :stobjs state))
  (if (and name
           (equal (f-get-global 'wormhole-name state) name))
      #+acl2-loop-only
      (mv-let (erp val state)
        (read-acl2-oracle state)
        (declare (ignore erp))
        (f-put-global 'wormhole-status val state))
      #-acl2-loop-only
      (if (and *wormholep*
               (live-state-p state))
          (f-put-global 'wormhole-status
                        (cdr (assoc-equal name *wormhole-status-alist*))
                        state)
          state)
      state))

(defun set-persistent-whs-and-ephemeral-whs (name new-status state)

; Update the persistent-whs for name to be new-status and then, if you're in
; the wormhole, also update the ephemeral-whs.  Thus, you can establish and
; maintain Wormhole Coherence if you use this function to update your wormhole
; status.

  (declare (xargs :stobjs state))
  (prog2$
   (wormhole-eval name ; set persistent-whs
                  '(lambda nil new-status)
                  new-status)
   (sync-ephemeral-whs-with-persistent-whs name state)))

(defmacro wormhole (name entry-lambda input form
                         &key
                         (current-package 'same current-packagep)
                         (useless-runes 'same useless-runesp)
                         (ld-skip-proofsp 'same ld-skip-proofspp)
                         (ld-redefinition-action 'save ld-redefinition-actionp)
                         (ld-prompt ''wormhole-prompt)
                         (ld-missing-input-ok 'same ld-missing-input-okp)
                         (ld-always-skip-top-level-locals
                          'same
                          ld-always-skip-top-level-localsp)
                         (ld-pre-eval-filter 'same ld-pre-eval-filterp)
                         (ld-pre-eval-print 'same ld-pre-eval-printp)
                         (ld-post-eval-print 'same ld-post-eval-printp)
                         (ld-evisc-tuple 'same ld-evisc-tuplep)
                         (ld-error-triples 'same ld-error-triplesp)
                         (ld-error-action 'same ld-error-actionp)
                         (ld-query-control-alist 'same ld-query-control-alistp)
                         (ld-verbose 'same ld-verbosep)
                         (ld-user-stobjs-modified-warning ':same))

; Warning: Keep this function in sync with the other functions listed in the
; Essay on the Wormhole Implementation Nexus in axioms.lisp.

; Warning: Also, keep this in sync with f-get-ld-specials, f-put-ld-specials,
; *initial-ld-special-bindings*, ld-alist-raw, chk-acceptable-ld-fn1-pair, and
; ld.

  `(with-wormhole-lock
    (prog2$
     (wormhole-eval ,name ,entry-lambda

; It is probably harmless to allow a second lock under the one above, but there
; is no need, so we avoid it.

                    :no-wormhole-lock)
     (wormhole1
      ,name
      ,input
      ,form
      (list
       ,@(append
          (if current-packagep
              (list `(cons 'current-package ,current-package))
            nil)
          (if useless-runesp
              (list `(cons 'useless-runes ,useless-runes))
            nil)
          (if ld-skip-proofspp
              (list `(cons 'ld-skip-proofsp ,ld-skip-proofsp))
            nil)
          (if ld-redefinition-actionp
              (list `(cons 'ld-redefinition-action
                           ,ld-redefinition-action))
            nil)
          (list `(cons 'ld-prompt ,ld-prompt))
          (if ld-missing-input-okp
              (list `(cons 'ld-missing-input-ok ,ld-missing-input-ok))
            nil)
          (if ld-always-skip-top-level-localsp
              (list `(cons 'ld-always-skip-top-level-locals
                           ,ld-always-skip-top-level-locals))
            nil)
          (if ld-pre-eval-filterp
              (list `(cons 'ld-pre-eval-filter ,ld-pre-eval-filter))
            nil)
          (if ld-pre-eval-printp
              (list `(cons 'ld-pre-eval-print ,ld-pre-eval-print))
            nil)
          (if ld-post-eval-printp
              (list `(cons 'ld-post-eval-print ,ld-post-eval-print))
            nil)
          (if ld-evisc-tuplep
              (list `(cons 'ld-evisc-tuple ,ld-evisc-tuple))
            nil)
          (if ld-error-triplesp
              (list `(cons 'ld-error-triples ,ld-error-triples))
            nil)
          (if ld-error-actionp
              (list `(cons 'ld-error-action ,ld-error-action))
            nil)
          (if ld-query-control-alistp
              (list `(cons 'ld-query-control-alist ,ld-query-control-alist))
            nil)
          (if ld-verbosep
              (list `(cons 'ld-verbose ,ld-verbose))
            nil)
          (if (eq ld-user-stobjs-modified-warning :same)
              (list `(cons 'ld-user-stobjs-modified-warning
                           ,ld-user-stobjs-modified-warning))
            nil)))))))

(defun lambda-keywordp (x)
  (and (symbolp x)
       (eql 1 (string<= "&" (symbol-name x)))))

(defun legal-variable-or-constant-namep (name)

; This function checks the syntax of variable or constant name
; symbols.  In all cases, name must be a symbol that is not in the
; keyword package or among *common-lisp-specials-and-constants*
; (except t and nil), or in the main Lisp package but outside
; *common-lisp-symbols-from-main-lisp-package*, and that does not
; start with an ampersand.  The function returns 'constant, 'variable,
; or nil.

; WARNING: T and nil are legal-variable-or-constant-nameps
; because we want to allow their use as constants.

; We now allow some variables (but still no constants) from the main Lisp
; package.  See *common-lisp-specials-and-constants*.  The following note
; explains why we have been cautious here.

; Historical Note

; This package restriction prohibits using some very common names as
; variables or constants, e.g., MAX and REST.  Why do we do this?  The
; reason is that there are a few such symbols, such as
; LAMBDA-LIST-KEYWORDS, which if bound or set could cause real
; trouble.  Rather than attempt to identify all of the specials of
; CLTL that are prohibited as ACL2 variables, we just prohibit them
; all.  One might be reminded of Alexander cutting the Gordian Knot.
; We could spend a lot of time unraveling complex questions about
; specials in CLTL or we can get on with it.  When ACL2 prevents you
; from using REST as an argument, you should see the severed end of a
; once tangled rope.

; For example, gcl and lucid (and others perhaps) allow you to define
; (defun foo (boole-c2) boole-c2) but then (foo 3) causes an error.
; Note that boole-c2 is recognized as special (by
; system::proclaimed-special-p) in lucid, but not in gcl (by
; si::specialp); in fact it's a constant in both.  Ugh.

; End of Historical Note.

  (and (symbolp name)
       (cond
        ((or (eq name t) (eq name nil))
         'constant)
        (t (let ((p (symbol-package-name name)))
             (and (not (equal p "KEYWORD"))
                  (let ((s (symbol-name name)))
                    (cond
                     ((and (not (= (length s) 0))
                           (eql (char s 0) #\*)
                           (eql (char s (1- (length s))) #\*))

; It was an oversight that a symbol with a symbol-name of "*" has always been
; considered a constant rather than a variable.  The intention was to view "*"
; as a delimiter -- thus, even "**" is probably OK for a constant since the
; empty string is delimited.  But it doesn't seem important to change this
; now.  If we do make such a change, consider the following (at least).

; - Be sure to rule out * in any package as a stobj name, since in a signature,
;   such a symbol denotes a non-stobj (see for example collect-non-* and see
;   mentions of "*" in functions that involve signatures).

; - It will be necessary to update :doc defconst.

; - Fix the error message for, e.g., (defconst foo::* 17), so that it doesn't
;   say "does not begin and end with the character *".

; - Make sure the error message is correct for (defun foo (*) *).  It should
;   probably complain about the main Lisp package, not about "the syntax of a
;   constant".

                      (if (equal p *main-lisp-package-name*)
                          nil
                        'constant))
                     ((and (not (= (length s) 0))
                           (eql (char s 0) #\&))
                      nil)
                     ((equal p *main-lisp-package-name*)
                      (and (not (member-eq
                                 name
                                 *common-lisp-specials-and-constants*))
                           (member-eq
                            name
                            *common-lisp-symbols-from-main-lisp-package*)
                           'variable))
                     (t 'variable)))))))))

(defun legal-variablep (name)

; Name may be used as a variable if it has the syntax of a variable
; (see legal-variable-or-constant-namep) and does not have the syntax of
; a constant, i.e., does not start and end with a *.

  (eq (legal-variable-or-constant-namep name) 'variable))

(defun arglistp1 (lst)

; Every element of lst is a legal-variablep.

  (cond ((atom lst) (null lst))
        (t (and (legal-variablep (car lst))
                (arglistp1 (cdr lst))))))

(defun arglistp (lst)
  (and (arglistp1 lst)
       (no-duplicatesp-eq lst)))

(defun find-first-bad-arg (args)

; This function is only called when args is known to be a non-arglistp
; that is a true list.  It returns the first bad argument and a string
; that completes the phrase "... violates the rules because it ...".

  (declare (xargs :guard (and (true-listp args)
                              (not (arglistp args)))))
  (cond
   ;;((null args) (mv nil nil)) -- can't happen, given the guard!
   ((not (symbolp (car args))) (mv (car args) "is not a symbol"))
   ((legal-constantp1 (car args))
    (mv (car args) "has the syntax of a constant"))
   ((lambda-keywordp (car args))
    (mv (car args) "is a lambda keyword"))
   ((keywordp (car args))
    (mv (car args) "is in the KEYWORD package"))
   ((member-eq (car args) *common-lisp-specials-and-constants*)
    (mv (car args) "belongs to the list *common-lisp-specials-and-constants* ~
                    of symbols from the main Lisp package"))
   ((member-eq (car args) (cdr args))
    (mv (car args) "occurs more than once in the list"))
   ((and (equal (symbol-package-name (car args)) *main-lisp-package-name*)
         (not (member-eq (car args)
                         *common-lisp-symbols-from-main-lisp-package*)))
    (mv (car args) "belongs to the main Lisp package but not to the list ~
                    *common-lisp-symbols-from-main-lisp-package*"))
   (t (find-first-bad-arg (cdr args)))))

(defun process-defabbrev-declares (decls)
  (cond ((endp decls) ())

; Here we do a cheap check that the declare form is illegal.  It is tempting to
; use collect-declarations, but it take state.  Anyhow, there is no soundness
; issue; the user will just be a bit surprised when the error shows up later as
; the macro defined by the defabbrev is applied.

        ((not (and (consp (car decls))
                   (eq (caar decls) 'DECLARE)
                   (true-list-listp (cdar decls))
                   (subsetp-eq (strip-cars (cdar decls))
                               '(IGNORE IGNORABLE TYPE))))
         (er hard 'process-defabbrev-declares
             "In a DEFABBREV form, each expression after the argument list ~
              but before the body must be of the form (DECLARE decl1 .. ~
              declk), where each dcli is of the form (IGNORE ..), (IGNORABLE ~
              ..), or (TYPE ..).  The form ~x0 is thus illegal."
             (car decls)))
        (t
         (cons (kwote (car decls))
               (process-defabbrev-declares (cdr decls))))))

(defun defabbrev1 (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((null lst) nil)
        (t (cons (list 'list (list 'quote (car lst)) (car lst))
                 (defabbrev1 (cdr lst))))))

(defmacro defabbrev (fn args &rest body)
  (cond ((null body)
         (er hard (cons 'defabbrev fn)
             "The body of this DEFABBREV form is missing."))
        ((not (true-listp args))
         (er hard (cons 'defabbrev fn)
             "The formal parameter list for a DEFABBREV must be a true list.  ~
              The argument list ~x0 is thus illegal."
             args))
        ((not (arglistp args))
         (mv-let (culprit explan)
                 (find-first-bad-arg args)
                 (er hard (cons 'defabbrev fn)
                     "The formal parameter list for a DEFABBREV must be a ~
                      list of distinct variables, but ~x0 does not meet these ~
                      conditions.  The element ~x1 ~@2."
                     args culprit explan)))
        (t
         (mv-let (doc-string-list body)
                 (if (and (stringp (car body))
                          (cdr body))
                     (mv (list (car body)) (cdr body))
                   (mv nil body))
                 (cond ((null body)
                        (er hard (cons 'defabbrev fn)
                            "This DEFABBREV form has a doc string but no ~
                             body."))
                       ((and (consp (car (last body)))
                             (eq (caar (last body)) 'declare))
                        (er hard (cons 'defabbrev fn)
                            "The body of this DEFABBREV form is a DECLARE ~
                             form, namely ~x0.  This is illegal and probably ~
                             is not what was intended."
                            (car (last body))))
                       (t
                        `(defmacro ,fn ,args
                           ,@doc-string-list
                           (list 'let
                                 (list ,@(defabbrev1 args))
                                 ,@(process-defabbrev-declares
                                    (butlast body 1))
                                 ',(car (last body))))))))))

; Essay on Evisceration

; We have designed the pretty printer so that it can print an
; "eviscerated" object, that is, an object that has had certain
; substructures removed.  We discuss the prettyprinter in the Essay on
; the ACL2 Prettyprinter.  The pretty printer has a flag, eviscp,
; which indicates whether the object has been eviscerated or not.  If
; not, then the full object is printed as it stands.  If so, then
; certain substructures of it are given special interpretation by the
; printer.  In particular, when the printer encounters a cons of the
; form (:evisceration-mark . x) then x is a string and the cons is
; printed by printing the characters in x (without the double
; gritches).

;     object                            pretty printed output
; (:evisceration-mark . "#")                     #
; (:evisceration-mark . "...")                   ...
; (:evisceration-mark . "<state>")               <state>
; (:evisceration-mark . ":EVISCERATION-MARK")    :EVISCERATION-MARK

; So suppose you have some object and you want to print it, implementing
; the CLTL conventions for *print-level* and *print-length*.  Then you
; must first scan it, inserting :evisceration-mark forms where
; appropriate.  But what if it contains some occurrences of
; :evisceration-mark?  Then you must use evisceration mechanism to print
; them correctly!  Once you have properly eviscerated the object, you can
; call the prettyprinter on it, telling it that the object has been
; eviscerated.  If, on the other hand, you don't want to eviscerate it,
; then you needn't sweep it to protect the native :evisceration-marks:
; just call the prettyprinter with the eviscp flag off.

(defconst *evisceration-mark* :evisceration-mark)

; Note: It is important that the evisceration-mark be a keyword.
; One reason is that (:evisceration-mark . ":EVISCERATION-MARK")
; couldn't be used to print a non-keyword because the package might
; need to be printed.  Another is that we exploit the fact that no
; event name nor any formal is *evisceration-mark*.  See
; print-ldd-full-or-sketch.  Furthermore, if the particular keyword
; chosen is changed, alter *anti-evisceration-mark* below!

(defconst *evisceration-hash-mark* (cons *evisceration-mark* "#"))
(defconst *evisceration-ellipsis-mark* (cons *evisceration-mark* "..."))
(defconst *evisceration-world-mark*
  (cons *evisceration-mark* "<world>"))
(defconst *evisceration-state-mark*
  (cons *evisceration-mark* "<state>"))
(defconst *evisceration-error-triple-marks*
  (list nil nil *evisceration-state-mark*))
(defconst *evisceration-error-triple-df-marks*
  (list nil :df *evisceration-state-mark*))
(defconst *evisceration-hiding-mark*
  (cons *evisceration-mark* "<hidden>"))

(defconst *anti-evisceration-mark*
  (cons *evisceration-mark* ":EVISCERATION-MARK"))

(defmacro evisceratedp (eviscp x)
; Warning:  The value of x should be a consp.
  `(and ,eviscp (eq (car ,x) *evisceration-mark*)))

; Essay on Iprinting

; Through Version_3.4, when ACL2 eviscerated a form using a print-level or
; print-length from an evisc-tuple, the resulting # and ... made it impossible
; to read the form back in.  We have implemented "iprinting" (think
; "interactive printing") to deal with this problem.  Our implementation uses
; an "iprint array", or "iprint-ar" for short, as described below.  Now, when
; iprinting is enabled, then instead of # or ... we will see #@i# for i = 1, 2,
; etc.  See :doc set-iprint for more information at the user level.  In brief,
; the idea is to maintain a state global 'iprint-ar whose value is an ACL2
; array that associates each such i with its hidden value.  (This use of #@i#
; allows us also to think of "iprinting" as standing for "index printing" or "i
; printing".)

; We implement this idea by modifying the recursive subroutines of eviscerate
; to accumulate each association of a positive i with its hidden value. When
; fmt (or fms, etc.) is called, eviscerate-top or eviscerate-stobjs-top will be
; called in order to update the existing 'iprint-ar with those new
; associations.

; We use index 0 to store the most recent i for which #@i# has been printed,
; assuming iprinting is enabled, or else (list i) if iprinting is disabled.  We
; call such i the last-index, and it is initially 0.  Note that state global
; 'iprint-ar is thus always bound to an installed ACL2 array.

; When state global 'iprint-fal has a non-nil value (which is exactly when
; set-iprint was last called with a non-nil value of :share), it is a
; fast-alist that inverts iprint-ar in the following sense: for every pair (i
; . v) in iprint-ar with 1 <= i <= last-index, (v . i) is in the value of
; 'iprint-fal.  See :doc set-iprint for more about :share.

; We have to face a fundamental question: Do we use acons or aset1 as we
; encounter a new form to assign to some #@i# during those recursive
; subroutines?  The latter is dangerous in case we interrupt before installing
; the result in the state global.  So it's tempting to use acons -- but it
; could be inefficient to compress the iprint-ar on each top-level call.  So
; instead we use acons to build up a new alist from scratch.  Then at the
; top level, we apply aset1 for each entry if we can do so without needing to
; ``rollover'', i.e., set the last-index back to 0; otherwise we call compress1
; rather than making a series of aset1 calls.  With luck this final step will
; be fast and unlikely to be interrupted from the time the first aset1 or
; compress1 is applied until the state global 'iprint-ar is updated.

; Let's also comment on why we have a soft and a hard bound (as described in
; :doc set-iprint).  In general we allow indices to increase between successive
; top-level invocations, so that the user can read back in any forms that were
; printed. But the soft bound forces a rollover at the top level of LD when the
; last-index exceeds that bound, so that we don't hold on to a potentially
; unbounded amount of space for the objects in the iprint-ar. The hard bound
; (which generally exceeds the soft bound) steps in if the last-index exceeds
; it after pretty-printing a single form.  Thus, if there are large objects and
; very long runs between successive top-level forms, space can be
; reclaimed. The hard bound is therefore probably less likely to be of use.

; We maintain the invariant that the dimension of state global 'iprint-ar
; exceeds the hard bound.  Thus, when we update the 'iprint-ar in the normal
; case that the hard bound is not exceeded, then the dimension will not be
; exceeded either; that is, every update will be with an index that is in
; bounds.  In order to maintain this invariant, the hard bound is untouchable,
; and its setter function compresses the global iprint-ar with a new dimension
; that exceeds the specified hard bound.  Therefore the hard bound must be a
; number, not nil.  Notice that with this invariant, we can avoid compressing
; twice when we roll over upon exceeding the hard or soft bound: we first reset
; the last-index to 0 and then do the compression, rather than compressing once
; for the increased dimension and once for the rollover.

; We also maintain the invariant that the maximum-length of the 'iprint-ar is
; always at least four times its dimension.  See the comment about this in
; rollover-iprint-ar.

; It is tempting to cause an error when the user submits a form containing some
; #@j# and #@k# such that j <= last-index < k.  In such a case, k is from
; before the rollover and j is from after the rollover, so these couldn't have
; been stored during a prettyprint of the same form.  By default we avoid this
; restriction, because the user might want to read a list that includes some
; forms prettyprinted before the last rollover and other forms printed after
; the last rollover.  But if iprint sharing is on, then a subform that had been
; printed before rollover might include iprint indices that have since changed,
; which might be highly confusing.  So we make the above restriction on indices
; when iprint sharing is on, as documented in :doc set-iprint.

; We ensure that the global iprint-ar is installed as an ACL2 array, in order
; to avoid slow-array-warnings.

; Wormholes present a potential problem, because information about iprinting is
; kept in state globals, but those are reverted when exiting a wormhole.  For
; example, if #@3# is printed inside a wormhole as an abbreviation for a value
; V, it would be unfortunate if an input of #@3# after exiting that wormhole
; causes an error or, perhaps worse yet, refers to a different value than V.
; We have implemented a two-step solution to this problem.  Step 1 takes
; advantage of the use of push-wormhole-undo-formi, which is mainly for
; restoring state globals when exiting a wormhole, by having that function save
; iprinting state globals from the wormhole into corresponding Lisp specials;
; for example, the value of state global iprint-ar is saved into special
; variable *wormhole-iprint-ar*.  Step 2 is to insert calls of
; iprint-oracle-updates, which magically -- using the acl2-oracle field of the
; state -- transfers those values back to the state, e.g., assigns state global
; iprint-ar the (compressed) value of special variable *wormhole-iprint-ar*.
; Calls of iprint-oracle-updates are needed at the entry points to eviscerating
; using iprinting, namely, eviscerate-top and eviscerate-stobjs-top, and also
; in the top-level loop (see read-object) so that #@n# expressions printed in a
; wormhole or by cw can be read at the top level.

; End of Essay on Iprinting

(defconst *sharp-atsign-ar* ; see get-sharp-atsign
  (let ((dim (1+ *iprint-hard-bound-default*)))
    (compress1
     'sharp-atsign-ar
     (cons `(:HEADER :DIMENSIONS     (,dim)
                     :MAXIMUM-LENGTH ,(1+ dim) ; no duplicates expected
                     :NAME           sharp-atsign-ar)
           (sharp-atsign-alist *iprint-hard-bound-default* nil)))))

(defun get-sharp-atsign (i)

; If i is below the hard bound, then we get the string #@i# from a fixed array,
; so that we don't have to keep consing up that string.

  (declare (xargs :guard (posp i)))
  (cond ((<= i *iprint-hard-bound-default*)
         (aref1 'sharp-atsign-ar *sharp-atsign-ar* i))
        (t (make-sharp-atsign i))))

(defun iprint-alistp1 (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        ((atom (cdr x))
         (and (consp (car x))
              (posp (caar x))
              (null (cdr x))))
        (t (and (consp (car x))
                (posp (caar x))
                (consp (car (cdr x)))
                (integerp (caar (cdr x)))
                (< (caar (cdr x)) (caar x))
                (iprint-alistp1 (cdr x))))))

(defun iprint-alistp (x)
  (declare (xargs :guard t))
  (or (eq x t)
      (natp x)
      (iprint-alistp1 x)))

(defun update-iprint-alist-fal (iprint-alist iprint-fal-new iprint-fal-old val)

; We are doing iprinting.  Iprint-alist is either a positive integer,
; representing the last-index but no accumulated iprint-alist, or else is a
; non-empty alist of entries (i . val_i).  See the Essay on Iprinting.

  (declare (xargs :guard (and (iprint-alistp iprint-alist)
                              (not (symbolp iprint-alist)))))
  (let ((pair (and iprint-fal-old
                   (or (hons-get val iprint-fal-new)
                       (hons-get val iprint-fal-old)))))
    (cond (pair
           (mv (cdr pair) iprint-alist iprint-fal-new))
          ((consp iprint-alist)
           (let ((index (1+ (caar iprint-alist))))
             (mv index
                 (acons index val iprint-alist)
                 (and iprint-fal-old
                      (hons-acons val index iprint-fal-new)))))
          (t
           (let ((index (1+ iprint-alist)))
             (mv index
                 (acons index val nil)
                 (and iprint-fal-old
                      (hons-acons val index iprint-fal-new))))))))

; We now define the most elementary eviscerator, the one that implements
; *print-level* and *print-length*.  In this same pass we also arrange to
; hide any object in alist, where alist pairs objects with their
; evisceration strings -- or if not a string, with the appropriate
; evisceration pair.

(mutual-recursion

(defun eviscerate1 (x v max-v max-n alist evisc-table hiding-cars
                      iprint-alist iprint-fal-new iprint-fal-old eager-p)

; Iprint-alist is either a symbol, indicating that we are not doing iprinting; a
; positive integer, representing the last-index but no accumulated iprint-alist;
; or an accumulated alist of entries (i . val_i).  See the Essay on Iprinting.
; Note that if iprint-alist is a symbol, then it is nil if no evisceration has
; been done based on print-length or print-level, else t.

; If iprint-fal-old is nil (i.e., if iprinting is off), then eager-p is
; essentially irrelevant; but as a sanity check, we insist that eager-p is nil
; in that case (as enforced by the assert$ call below).

  (declare (xargs :guard (and (integerp v)
                              (integerp max-v)
                              (integerp max-n)
                              (alistp alist)
                              (symbol-listp hiding-cars)
                              (iprint-alistp iprint-alist)
                              (iprint-falp iprint-fal-new)
                              (iprint-falp iprint-fal-old))
                  :measure (1+ (* 2 (acl2-count x)))))
  (let* ((temp (or (hons-assoc-equal x alist)
                   (hons-assoc-equal x evisc-table)))
         (eager-pair (and eager-p
                          (null (cdr temp))
                          (consp x)
                          (assert$?
                           iprint-fal-old
                           (or (hons-get x iprint-fal-new)
                               (hons-get x iprint-fal-old))))))
    (cond ((cdr temp)
           (mv (cond ((stringp (cdr temp))
                      (cons *evisceration-mark* (cdr temp)))
                     (t (cdr temp)))
               iprint-alist
               iprint-fal-new))
          ((atom x)
           (mv (cond ((eq x *evisceration-mark*) *anti-evisceration-mark*)
                     (t x))
               iprint-alist
               iprint-fal-new))
          (eager-pair
           (mv (cons *evisceration-mark*
                     (get-sharp-atsign (cdr eager-pair)))
               iprint-alist
               iprint-fal-new))
          ((= v max-v)
           (cond ((symbolp iprint-alist)
                  (mv *evisceration-hash-mark* t iprint-fal-new))
                 (t
                  (mv-let (index iprint-alist iprint-fal-new)
                    (update-iprint-alist-fal iprint-alist
                                             iprint-fal-new
                                             iprint-fal-old
                                             x)
                    (mv (cons *evisceration-mark*
                              (get-sharp-atsign index))
                        iprint-alist
                        iprint-fal-new)))))
          ((member-eq (car x) hiding-cars)
           (mv *evisceration-hiding-mark* iprint-alist iprint-fal-new))
          (t (eviscerate1-lst x (1+ v) 0 max-v max-n alist evisc-table
                              hiding-cars iprint-alist
                              iprint-fal-new iprint-fal-old eager-p)))))

(defun eviscerate1-lst (lst v n max-v max-n alist evisc-table hiding-cars
                            iprint-alist iprint-fal-new iprint-fal-old eager-p)
  (declare (xargs :guard (and (integerp v)
                              (natp n)
                              (integerp max-v)
                              (integerp max-n)
                              (alistp alist)
                              (symbol-listp hiding-cars)
                              (iprint-alistp iprint-alist)
                              (iprint-falp iprint-fal-new)
                              (iprint-falp iprint-fal-old))
                  :measure (* 2 (acl2-count lst))))
  (let* ((temp (or (hons-assoc-equal lst alist)
                   (hons-assoc-equal lst evisc-table)))
         (eager-pair (and eager-p
                          (null (cdr temp))
                          (consp lst)
                          (assert$?
                           iprint-fal-old
                           (or (hons-get lst iprint-fal-new)
                               (hons-get lst iprint-fal-old))))))
    (cond
     ((cdr temp)
      (mv (cond ((stringp (cdr temp))
                 (cons *evisceration-mark* (cdr temp)))
                (t (cdr temp)))
          iprint-alist
          iprint-fal-new))
     ((atom lst)
      (mv (cond ((eq lst *evisceration-mark*) *anti-evisceration-mark*)
                (t lst))
          iprint-alist
          iprint-fal-new))
     (eager-pair
      (mv (cons *evisceration-mark*
                (get-sharp-atsign (cdr eager-pair)))
          iprint-alist
          iprint-fal-new))
     ((= n max-n)
      (cond ((symbolp iprint-alist)
             (mv (list *evisceration-ellipsis-mark*) t iprint-fal-new))
            (t (mv-let (index iprint-alist iprint-fal-new)
                 (update-iprint-alist-fal iprint-alist
                                          iprint-fal-new
                                          iprint-fal-old
                                          lst)
                 (mv (cons *evisceration-mark*
                           (get-sharp-atsign index))
                     iprint-alist
                     iprint-fal-new)))))
     (t (mv-let (first iprint-alist iprint-fal-new)
          (eviscerate1 (car lst) v max-v max-n alist evisc-table
                       hiding-cars iprint-alist
                       iprint-fal-new iprint-fal-old eager-p)
          (mv-let (rest iprint-alist iprint-fal-new)
            (eviscerate1-lst (cdr lst) v (1+ n)
                             max-v max-n alist evisc-table
                             hiding-cars iprint-alist
                             iprint-fal-new iprint-fal-old eager-p)
            (mv (cons first rest) iprint-alist iprint-fal-new)))))))
)

(mutual-recursion

(defun eviscerate1p (x alist evisc-table hiding-cars)

; This function returns t iff (eviscerate1 x 0 -1 -1 alist evisc-table hidep)
; returns something other than x.  That is, iff the evisceration of x either
; uses alist, evisc-table, hiding or the *anti-evisceration-mark* (assuming
; that print-level and print-length never max out).

  (declare (xargs :guard (symbol-listp hiding-cars)
                  :measure (1+ (* 2 (acl2-count x)))))
  (let ((temp (or (hons-assoc-equal x alist)
                  (hons-assoc-equal x evisc-table))))
    (cond ((cdr temp) t)
          ((atom x)
           (cond ((eq x *evisceration-mark*) t)
                 (t nil)))
          ((member-eq (car x) hiding-cars) t)
          (t (eviscerate1p-lst x alist evisc-table hiding-cars)))))

(defun eviscerate1p-lst (lst alist evisc-table hiding-cars)
  (declare (xargs :guard (symbol-listp hiding-cars)
                  :measure (* 2 (acl2-count lst))))
  (let ((temp (or (hons-assoc-equal lst alist)
                  (hons-assoc-equal lst evisc-table))))
    (cond ((cdr temp) t)
          ((atom lst)
           (cond ((eq lst *evisceration-mark*) t)
                 (t nil)))
          (t (or (eviscerate1p (car lst) alist evisc-table hiding-cars)
                 (eviscerate1p-lst (cdr lst) alist evisc-table
                                   hiding-cars))))))
)

(defun eviscerate (x print-level print-length alist evisc-table hiding-cars
                     iprint-alist iprint-fal-new iprint-fal-old eager-p)

; See also eviscerate-top, which takes iprint-ar from the state and installs a
; new iprint-ar in the state, and update-iprint-alist, which describes the role
; of a non-symbol iprint-alist as per the Essay on Iprinting.

; Print-level and print-length should either be non-negative integers or nil.
; Alist and evisc-table are alists pairing arbitrary objects to strings or
; other objects.  Hiding-cars is a list of symbols.  Any x that starts with one
; of these symbols is printed as <hidden>.  If alist or evisc-table pairs an
; object with a string, the string is printed in place of the object.  If alist
; or evisc-table pairs an object with anything else, x, then x is substituted
; for the object and is treated as eviscerated.  In general, alist will
; come from an evisceration tuple and evisc-table will be the value of the
; 'evisc-table table in the current ACL2 world.  We give priority to the former
; because the user may want to override the evisc-table, for example using ~P
; in a call of fmt.

; This function copies the structure x and replaces certain deep substructures
; with evisceration marks.  The determination of which substructures to so
; abbreviate is based on the same algorithm used to define *print-level* and
; *print-length* in CLTL, with the additional identification of all occurrences
; of any object in alist or evisc-table.

; For example, if x is '(if (member x y) (+ (car x) 3) '(foo . b)) and
; print-level is 2 and print-length is 3 then the output is:

; (IF (MEMBER X Y)
;     (+ (*evisceration-mark* . "#") 3)
;     (*evisceration-mark* . "..."))

; See pg 373 of CLTL.

; Of course we are supposed to print this as:

; (IF (MEMBER X Y) (+ # 3) ...)

; We consider a couple of special cases to reduce unnecessary consing
; of eviscerated values.

  (declare (xargs :guard (and (or (null print-level)
                                  (integerp print-level))
                              (or (null print-length)
                                  (integerp print-length))
                              (alistp alist)
                              (symbol-listp hiding-cars)
                              (iprint-alistp iprint-alist)
                              (iprint-falp iprint-fal-new)
                              (iprint-falp iprint-fal-old))))
  (cond ((and (null print-level)
              (null print-length))

; Warning: Observe that even if alist is nil, x might contain the
; *evisceration-mark* or hiding expressions and hence have a
; non-trivial evisceration

         (cond ((eviscerate1p x alist evisc-table hiding-cars)
                (eviscerate1 x 0 -1 -1 alist evisc-table hiding-cars

; Since we are not eviscerating based on print-level or print-length, there is
; no involvement of iprinting, so we pass nil for the remaining arguments.

                             nil nil nil nil))
               (t (mv x iprint-alist iprint-fal-new))))
        (t (eviscerate1 (if eager-p (hons-copy x) x)
                        0
                        (or print-level -1)
                        (or print-length -1)
                        alist
                        evisc-table
                        hiding-cars
                        iprint-alist
                        iprint-fal-new
                        iprint-fal-old
                        eager-p))))

(defun eviscerate-simple (x print-level print-length alist evisc-table
                            hiding-cars)

; This wrapper for eviscerate avoids the need to pass back multiple values when
; the iprint-alist is nil and we don't care if evisceration has occurred.

  (declare (xargs :guard (and (or (null print-level)
                                  (integerp print-level))
                              (or (null print-length)
                                  (integerp print-length))
                              (alistp alist)
                              (symbol-listp hiding-cars))))
  (mv-let (result null-iprint-alist null-iprint-fal)
    (eviscerate x print-level print-length alist evisc-table hiding-cars
                nil nil

; We normally pass in the current value of state global 'iprint-fal for the
; last argument, iprint-fal-old, of eviscerate.  However, since iprint-alist is
; nil, we know that it's fine to pass in nil for iprint-fal-old, and similarly
; for eager-p.

                nil nil)

; We use assert* instead of assert$ to avoid a runtime check, now that
; eviscerate-simple is common-lisp-compliant.

    (declare (ignorable null-iprint-alist null-iprint-fal)) ; for raw Lisp
    (assert* (and (booleanp null-iprint-alist)
                  (null null-iprint-fal))
             result)))

(defun bounded-integer-listp (i j lst)
  (declare (xargs :guard (and (integerp i)
                              (or (integerp j)
                                  (eq j 'infinity)))))
  (cond
   ((consp lst)
    (and (integerp (car lst))
         (<= i (car lst))
         (or (eq j 'infinity)
             (<= (car lst) j))
         (bounded-integer-listp i j (cdr lst))))
   (t (null lst))))

(defun aset1-lst (name alist ar)
  (declare (xargs :guard (eqlable-alistp alist))) ; really nat-alistp
  (declare (xargs :guard
                  (and (alistp alist)
                       (array1p name ar)
                       (bounded-integer-listp 0
                                              (- (car (dimensions name ar)) 1)
                                              (strip-cars alist)))))
  (cond ((endp alist)
         ar)
        (t (aset1-lst name
                      (cdr alist)
                      (aset1 name ar (caar alist) (cdar alist))))))

; Next we define accessors for iprint arrays.

(defun iprint-hard-bound (state)
  (f-get-global 'iprint-hard-bound state))

(defun iprint-soft-bound (state)
  (f-get-global 'iprint-soft-bound state))

(defun iprint-last-index (state)
  (declare (xargs :guard (array1p 'iprint-ar (f-get-global 'iprint-ar state))))
  (iprint-last-index* (f-get-global 'iprint-ar state)))

(defun iprint-ar-illegal-index (index state)
  (declare (xargs :guard
                  (and (natp index)
                       (array1p 'iprint-ar
                                (f-get-global 'iprint-ar state))
                       (natp (iprint-last-index state))
                       (or (null (default 'iprint-ar
                                   (f-get-global 'iprint-ar state)))
                           (integerp (default 'iprint-ar
                                       (f-get-global 'iprint-ar state)))))))
  (or (zp index)
      (let* ((iprint-ar (f-get-global 'iprint-ar state))
             (bound (default 'iprint-ar iprint-ar)))
        (if (null bound)
            (> index (iprint-last-index* iprint-ar))
          (> index bound)))))

(defun iprint-enabledp (state)
  (declare (xargs :guard (array1p 'iprint-ar (f-get-global 'iprint-ar state))))
  (natp (aref1 'iprint-ar (f-get-global 'iprint-ar state) 0)))

(defun iprint-blockedp (state)

; Check for the effect off block-iprint-ar.

  (declare (xargs :guard (array1p 'iprint-ar (f-get-global 'iprint-ar state))))
  (let ((x (aref1 'iprint-ar (f-get-global 'iprint-ar state) 0)))
    (and (consp x)
         (cdr x))))

(defun iprint-ar-aref1 (index state)

; We do not try to determine if the index is appropriate, other than to avoid a
; guard violation on the aref1 call.  See the Essay on Iprinting.

  (declare (xargs :guard
                  (and (posp index)
                       (array1p 'iprint-ar (f-get-global 'iprint-ar state))
                       (< index
                          (car (dimensions 'iprint-ar
                                           (f-get-global 'iprint-ar state)))))))
  (let ((iprint-ar (f-get-global 'iprint-ar state)))

;; PAPER:
; We use a raw Lisp error since otherwise we get an error such as "Can't throw
; to tag RAW-EV-FNCALL".

    #-acl2-loop-only
    (cond ((>= index (car (dimensions 'iprint-ar iprint-ar)))

; The following error probably never occurs, since we have already done a
; bounds check with iprint-ar-illegal-index.

           (error
            "Out of range index for iprinting: ~s.~%See :DOC set-iprint."
            index)))
    (aref1 'iprint-ar iprint-ar index)))

(defun iprint-alistp1-weak (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (posp (caar x))
                (iprint-alistp1-weak (cdr x))))))

(defun collect-posp-indices-to-header (ar acc)

; Accumulates the reverse of ar onto acc, skipping entries with index 0 and
; stopping just before the :header.

  (declare (xargs :guard (and (array1p 'iprint-ar ar)
                              (iprint-alistp1-weak acc))))
  (cond ((endp ar)
         (er hard 'collect-posp-indices-to-header
             "Implementation error: Failed to find :HEADER as expected!"))
        ((eq (caar ar) :HEADER)
         acc)
        (t
         (collect-posp-indices-to-header (cdr ar)
                                         (if (eql (caar ar) 0)
                                             acc
                                           (cons (car ar) acc))))))

(defun iprint-fal-name (iprint-fal)
  (declare (xargs :guard (iprint-falp iprint-fal)))
  (if (consp iprint-fal)
      (cdr (last iprint-fal))
    iprint-fal))

(defun iprint-eager-p (iprint-fal)
  (declare (xargs :guard (iprint-falp iprint-fal)))
  (eq (iprint-fal-name iprint-fal)
      :eager))

(defun init-iprint-fal (sym state)

; Warning: Consider also calling init-iprint-ar when calling this function.

; The initial value of state global 'iprint-fal is nil if we are not to re-use
; indices, and otherwise is the atom, :iprint-fal.  We choose a keyword so that
; fast-alist-summary can print that name nicely in any package.

  (declare (xargs :guard (and (symbolp sym)
                              (iprint-falp (f-get-global 'iprint-fal state)))))
  (let* ((old-iprint-fal (f-get-global 'iprint-fal state))
         (old-iprint-name (iprint-fal-name old-iprint-fal))
         (new-iprint-fal (cond ((null sym) nil)
                               ((eq sym t)
                                :iprint-fal)
                               ((eq sym :same)
                                old-iprint-name)
                               (t sym))))
    (prog2$ (and (consp old-iprint-fal) ; optimization
                 (fast-alist-free old-iprint-fal))
            (pprogn (f-put-global 'iprint-fal new-iprint-fal state)
                    (mv (cond
                         ((eq old-iprint-name new-iprint-fal)
                          nil)
                         (new-iprint-fal
                          (msg "Iprinting is enabled with~@0 sharing, with a ~
                                fast-alist whose name is ~x1."
                               (if (iprint-eager-p new-iprint-fal)
                                   " eager"
                                 "")
                               new-iprint-fal))
                         (t
                          (msg "Iprinting is enabled without sharing.")))
                        state)))))

(defun rollover-iprint-ar (iprint-alist last-index state)

; We assume that iprinting is enabled.  Install a new iprint-ar, whose last
; index before rollover is intended to be last-index and whose alist is
; intended to extend state global 'iprint-ar, as the new (and compressed) value
; of state global 'iprint-ar.

  (declare (xargs :guard
                  (and (iprint-alistp1 iprint-alist)
                       (consp iprint-alist)
                       (iprint-falp (f-get-global 'iprint-fal state))
                       (array1p 'iprint-ar (f-get-global 'iprint-ar state))
                       (posp last-index)
                       (equal last-index (caar iprint-alist))
                       (iprint-array-p (f-get-global 'iprint-ar state)
                                       last-index)
                       (natp (f-get-global 'iprint-hard-bound state))
                       (<= (* 4 (1+ (f-get-global 'iprint-hard-bound
                                                  state)))
; See init-iprint-ar; this is necessary for array1p to hold of the new array.
                           (array-maximum-length-bound)))))
  (let* ((old-iprint-ar (f-get-global 'iprint-ar state))
         (new-dim

; Clearly last-index exceeds the iprint-hard-bound, as required by one of our
; invariants (see the Essay on Iprinting), if we are rolling over because
; last-index exceeds that hard bound.  But we can also call rollover-iprint-ar
; when exceeding the soft bound, which may be smaller than the hard bound (it
; probably is smaller, typically).  The taking of this max is cheap so we
; always do it, so that rollover-iprint-ar will always preserve the above
; invariant.

; To illustrate the above point, evaluate the following forms in a fresh ACL2
; session and see the error if we bind new-dim to (1+ last-index).

; (set-ld-evisc-tuple (evisc-tuple 2 3 nil nil) state)
; (set-iprint t :soft-bound 2 :hard-bound 7)
; '((a b c d e) (a b c d e) (a b c d e))
; '((a b c d e) (a b c d e) (a b c d e) (a b c d e) (a b c d e))

          (1+ (max (iprint-hard-bound state) last-index)))
         (new-max-len

; A multiplier of 4 allows us to maintain the invariant that the maximum-length
; is always at least four times the dimension.  This guarantees that the
; 'iprint-ar alist never reaches the maximum-length because it never reaches
; 4*d, where d is the dimension, as this alist has at most:
; - up to d-2 values for index >= 1 since the latest rollover;
; - up to d-2 values for index >= 1 before the latest rollover;
; - at most two headers (the 2nd is just before a new compression at rollover)
; - no two successive bindings of index 0
; So without considering index 0, the maximum is (d-2 + d-2 + 2) = 2d-1.  Now
; for the bindings of index 0, double that and add one to get 4d-1.

; Thus, since the dimension never decreases (except when we reinitialize), we
; are assured that our use of aset1-lst in update-iprint-ar will never cause a
; recompression.  See also corresponding comments in disable-iprint-ar and
; enable-iprint-ar.

          (* 4 new-dim)))
    (cond
     ((< (array-maximum-length-bound) new-max-len)
      (prog2$
       (er hard? 'rollover-iprint-ar
           "Attempted to expand iprint-ar to a maximum-length of ~x0, ~
            exceeding (array-maximum-length-bound), which is ~x1."
           new-max-len
           (array-maximum-length-bound))
       state))
     (t
      (let* ((new-header
              `(:HEADER :DIMENSIONS     (,new-dim)
                        :MAXIMUM-LENGTH ,new-max-len
                        :DEFAULT        ,last-index
                        :NAME           iprint-ar
                        :ORDER          :none))
             (new-iprint-ar
              (compress1 'iprint-ar
                         (cons new-header
                               (acons 0 0
                                      (collect-posp-indices-to-header
                                       old-iprint-ar

; If we change the :order to < from :none, then we need to reverse iprint-alist
; just below.  But first read the comment in disable-iprint-ar to see why
; changing the :order from :none requires some thought.

                                       iprint-alist))))))
      (mv-let (msg state)
        (init-iprint-fal :same state)
        (declare (ignore msg))
        (f-put-global 'iprint-ar new-iprint-ar state)))))))

(defun update-iprint-fal-rec (iprint-fal-new iprint-fal-old)
  (declare (xargs :guard (iprint-falp iprint-fal-new)))
  (cond ((atom iprint-fal-new) iprint-fal-old)
        (t (update-iprint-fal-rec (cdr iprint-fal-new)
                                  (hons-acons (caar iprint-fal-new)
                                              (cdar iprint-fal-new)
                                              iprint-fal-old)))))

(defun update-iprint-fal (iprint-fal-new state)
  (declare (xargs :guard (iprint-falp iprint-fal-new)))
  (cond
   ((atom iprint-fal-new) state) ; optimization
   (t (f-put-global 'iprint-fal
                    (update-iprint-fal-rec iprint-fal-new
                                           (f-get-global 'iprint-fal state))
                    state))))

(defun update-iprint-ar-fal (iprint-alist iprint-fal-new iprint-fal-old state)

; We assume that iprinting is enabled.  Iprint-alist is known to be a consp.
; We update state globals 'iprint-ar and 'iprint-fal by updating them with the
; pairs in iprint-alist and iprint-fal-new, respectively.

  (declare (xargs :guard
                  (and (iprint-alistp1 iprint-alist)
                       (consp iprint-alist)
                       (equal iprint-fal-old (f-get-global 'iprint-fal state))
                       (iprint-falp iprint-fal-old)
                       (array1p 'iprint-ar (f-get-global 'iprint-ar state))
                       (iprint-array-p (f-get-global 'iprint-ar state)
                                       (caar iprint-alist))
                       (natp (f-get-global 'iprint-hard-bound state))
                       (< (f-get-global 'iprint-hard-bound state)

; Quoting the Essay on Iprinting:
; "We maintain the invariant that the dimension of state global 'iprint-ar
; exceeds the hard bound."

                          (car (dimensions 'iprint-ar
                                           (f-get-global 'iprint-ar state))))
                       (<= (* 4 (1+ (f-get-global 'iprint-hard-bound
                                                  state)))
; See init-iprint-ar; this is necessary for array1p to hold of the new array.
                           (array-maximum-length-bound))
                       (iprint-falp iprint-fal-new))))
  (let ((last-index (caar iprint-alist)))
    (cond ((> last-index (iprint-hard-bound state))

; We throw away iprint-fal-new, because we only want to re-use indices below
; last-index -- re-use of larger indices could quickly leave us pointing to
; stale values when re-printing (say, using without-evisc) recently-printed
; values.

           (rollover-iprint-ar iprint-alist last-index state))
          (t
           (assert$
            (or (null iprint-fal-old) ; might have passed in nil at top level
                (equal (f-get-global 'iprint-fal state)
                       iprint-fal-old))
            (pprogn
             (update-iprint-fal iprint-fal-new state)
             (f-put-global 'iprint-ar

; We know last-index <= (iprint-hard-bound state), and it is an invariant that
; this hard bound is less than the dimension of (@ iprint-ar).  See the
; discussion of this invariant in the Essay on Iprinting.  So last-index is
; less than that dimension, hence we can update with aset1 without encountering
; out-of-bounds indices.

                           (aset1-lst 'iprint-ar
                                      (acons 0 last-index iprint-alist)
                                      (f-get-global 'iprint-ar state))
                           state)))))))

(defun brr-evisc-tuple-oracle-update@par ()
  #-acl2-loop-only
  (brr-evisc-tuple-oracle-update *the-live-state*)
  nil)

(defun iprint-oracle-updates@par ()
  #-acl2-loop-only
  (iprint-oracle-updates-raw *the-live-state*)
  nil)

(defun iprint-oracle-updates? (state)

; This is like iprint-oracle-updates, except that it returns state unchanged if
; iprinting is blocked.  As of this writing, that would be due to a call of
; iprint-blockedp from channel-to-string on behalf of fmt-to-string or the
; like.  We use this notion of "blocked" to avoid calling iprint-oracle-updates
; from fmt-to-string etc., so that such utilities can be used in macros and
; defconst forms, where otherwise safe-mode would cause a program-only error,
; as in the following example.

;   (defconst *c*
;     (fms-to-string "~x0"
;                    (list (cons #\0 (make-list 10)))
;                    :evisc-tuple (evisc-tuple 5 6 nil nil)))

  (declare (xargs :guard (array1p 'iprint-ar (f-get-global 'iprint-ar state))))
  (cond ((iprint-blockedp state) state)
        (t (iprint-oracle-updates state))))

(defun eviscerate-top-state-p (state)
  (declare (xargs :stobjs state))
  (and (natp (f-get-global 'iprint-hard-bound state))
       (iprint-falp (f-get-global 'iprint-fal state))
       (array1p 'iprint-ar
                (f-get-global 'iprint-ar state))
       (consp (f-get-global 'iprint-ar state))
       (natp (iprint-last-index state))
       (iprint-array-p (f-get-global 'iprint-ar state)
                       (1+ (iprint-last-index state)))
       (<= (* 4 (1+ (f-get-global 'iprint-hard-bound
                                  state)))
; See init-iprint-ar; this is necessary for array1p to hold of the new array.
           (array-maximum-length-bound))
       (< (f-get-global 'iprint-hard-bound state)

; Quoting the Essay on Iprinting:
; "We maintain the invariant that the dimension of state global 'iprint-ar
; exceeds the hard bound."

          (car (dimensions 'iprint-ar
                           (f-get-global 'iprint-ar
                                         state))))
       (= (maximum-length 'iprint-ar
                          (f-get-global 'iprint-ar
                                        state))
          (* 4 (car (dimensions
                     'iprint-ar
                     (f-get-global 'iprint-ar
                                   state)))))))

(defun eviscerate-top (x print-level print-length alist evisc-table hiding-cars
                         state)

; We update iprint and brr-evisc-tuple information from wormholes and then
; install a new iprint-ar in the state, in addition to returning the
; evisceration of x.  See eviscerate and the Essay on Iprinting for more
; details.

  (declare (xargs :guard (and (or (null print-level)
                                  (integerp print-level))
                              (or (null print-length)
                                  (integerp print-length))
                              (alistp alist)
                              (symbol-listp hiding-cars)
                              (eviscerate-top-state-p state))))
  (pprogn

; First we ensure that the result will reflect iprint and brr-evisc-tuple
; updates made during brr.

   (iprint-oracle-updates? state)
   (brr-evisc-tuple-oracle-update state)
   (let ((iprint-fal-old (f-get-global 'iprint-fal state)))
     (mv-let (result iprint-alist iprint-fal-new)
       (eviscerate x print-level print-length alist evisc-table hiding-cars
                   (and (iprint-enabledp state)
                        (iprint-last-index state))
                   nil iprint-fal-old (iprint-eager-p iprint-fal-old))
       (fast-alist-free-on-exit
        iprint-fal-new
        (let ((state
               (cond
                ((eq iprint-alist t)
                 (f-put-global 'evisc-hitp-without-iprint t state))
                ((atom iprint-alist) state)
                (t (update-iprint-ar-fal iprint-alist
                                         iprint-fal-new
                                         iprint-fal-old
                                         state)))))
          (mv result state)))))))

; Essay on the ACL2 Prettyprinter

; The ACL2 prettyprinter is a two pass, linear time, exact prettyprinter.  By
; "exact" we mean that if it has a page of width w and a big enough form, it
; will guarantee to use all the columns, i.e., the widest line will end in
; column w.  The algorithm dates from about 1971 -- virtually the same code was
; in the earliest Edinburgh Pure Lisp Theorem Prover.  This approach to
; prettyprinting was invented by Bob Boyer; see
; http://www.cs.utexas.edu/~boyer/pretty-print.pdf.  Most prettyprinters are
; quadratic and inexact.

; The secret to this method is to make two linear passes, ppr1 and ppr2.  The
; first pass builds a data structure, called a ``ppr tuple,'' that tells the
; second pass how to print.

; Some additional general principles of our prettyprinter are
; (i)    Print flat whenever possible.

; (ii)   However, don't print flat argument lists of length over 40; they're
;        too hard to parse.  (But this can be overridden by state global
;        ppr-flat-right-margin.)

; (iii)  Atoms and eviscerated things (which print like atoms, e.g., `<world>')
;        may be printed on a single line.

; (iv)   But parenthesized expressions should not be printed on a line with any
;        other argument (unless the whole form fits on the line).  Thus we may
;        produce:
;        `(foo (bar a) b c d)'
;        and
;        `(foo a b
;              c d)'
;        But we never produce
;        `(foo (bar a) b
;              c d)'
;        preferring instead
;        `(foo (bar a)
;              b c d)'
;        It is our belief that parenthesized expressions are hard to parse and
;        after doing so the eye tends to miss little atoms (like b above)
;        hiding in their shadows.

; See :DOC ppr-special-syms for a discussion of the special-term-num feature.

; To play with ppr we recommend executing this form:

; (ppr2 (ppr1 x (print-base) (print-radix) 30 0 state t)
;       0 *standard-co* state t)

; This will prettyprint x on a page of width 30, assuming that printing starts
; in column 0.  To see the ppr tuple that drives the printer, just evaluate the
; inner ppr1 form,
; (ppr1 x (print-base) (print-radix) 30 0 state nil).

; The following test macro is handy.  A typical call of the macro is

; (test 15 (foo (bar x) (mum :key1 val1 :key2 :val2)))

; Note that x is not evaluated.  If you want to evaluate x and ppr the value,
; use

;   (testfn 10
;           (eviscerate-simple `(foo (bar x)
;                             (mum :key1 :val1 :key2 :val2)
;                             ',(w state))
;                       nil nil ; print-level and print-length
;                       (world-evisceration-alist state nil)
;                       nil
;                       nil)
;           state)

; Note that x may be eviscerated, i.e., eviscerated objects in x are printed in
; their short form, not literally.

;   (defun testfn (d x state)
;     (declare (xargs :mode :program :stobjs (state)))
;     (let ((tuple (ppr1 x (print-base) (print-radix) d 0 state t)))
;       (pprogn
;        (fms "~%Tuple: ~x0~%Output:~%" (list (cons #\0 tuple))
;             *standard-co* state nil)
;        (ppr2 tuple 0 *standard-co* state t)
;        (fms "~%" nil *standard-co* state nil))))
;
;   (defmacro test (d x) `(testfn ',d ',x state))

; Ppr tuples record enough information about the widths of various forms so
; that it can be computed without having to recompute any part of it and so
; that the second pass can print without having to count characters.

; A ppr tuple has the form (token n . z).  In the display below, the variables
; ti represent ppr tuples and the variables xi represent objects to be printed
; directly.  Any xi could an eviscerated object, a list whose car is the
; evisceration mark.

; (FLAT n x1 ... xk) - Print the xi, separated by spaces, all on one
;                      line. The total width of output will be n.
;                      Note that k >= 1.  Note also that such a FLAT
;                      represents k objects.  A special case is (FLAT
;                      n x1), which represents one object.  We make
;                      this observation because sometimes (in
;                      cons-ppr1) we `just know' that k=1 and the
;                      reason is: we know the FLAT we're holding
;                      represents a single object.

; (FLAT n x1... . xk)- Print the xi, separated by spaces, with xk
;                      separated by `. ', all on one line.  Here xk
;                      is at atom or an eviscerated object.

; (FLAT n . xk)      - Here, xk is an atom (or an eviscerated object).
;                      Print a dot, a space, and xk.  The width will
;                      be n.  Note that this FLAT does not actually
;                      represent an object.  That is, no Lisp object
;                      prints as `. xk'.

; Note: All three forms of FLAT are really just (FLAT n . x) where x is a
; possibly improper list and the elements of x (and its final cdr) are printed,
; separated appropriately by spaces or dot.

; (MATCHED-KEYWORD n x1)
;                    - Exactly like (FLAT n x1), i.e., prints x1,
;                      but by virtue of being different from FLAT
;                      no other xi's are ever added.  In this tuple,
;                      x1 is always a keyword and it will appear on
;                      a line by itself.  Its associated value will
;                      appear below it in the column because we tried
;                      to put them on the same line but we did not have
;                      room.

; (DOT 1)            - Print a dot.

; (QUOTE n . t1)     - Print a single-quote followed by pretty-
;                      printing the ppr tuple t1.

; (WIDE n t1 t2 ...) - Here, t1 is a FLAT tuple of width j.  We
;                      print an open paren, the contents of t1, a
;                      space, and then we prettyprint each of the
;                      remaining ti in a column.  When we're done, we
;                      print a close paren.  The width of the longest
;                      line we will print is n.

; (i n t1 ...)       - We print an open paren, prettyprint t1, then
;                      do a newline.  Then we prettyprint the
;                      remaining ti in the column that is i to the
;                      right of the paren.  We conclude with a close
;                      paren.  The width of the longest line we will
;                      print is n.  We call this an `indent tuple'.

; (KEYPAIR n t1 . t2)- Here, t1 is a FLAT tuple of width j.  We print
;                      t1, a space, and then prettyprint t2.  The
;                      length of the longest line we will print is n.

; Supporting the extension by Stephen Westfold described in :DOC
; ppr-special-syms:
; (SPECIAL-TERM n t1 (i-ind i1 ...) r-ind r1 ...)
;                    - Here, t1 is a FLAT tuple of width j.
;                      o-nm is NIL or a FLAT tuple that fits on the same
;                        line as t1.
;                      i-ind is NIL or a natural number.
;                      i1 ... are prettyprinted on the same line as t1 if
;                        i-ind is NIL, otherwise on the next line with
;                        relative indentation i-ind.
;                      r-ind is a natural number.
;                      r1 ... are prettyprinted with relative indentation
;                        r-ind.

; The sentence "The length of the longest line we will print is n."
; bears explanation.  Consider

; (FOO (BAR X)
;      (MUMBLE Y)
;      Z)
;|<- 15 chars  ->|
; 123456789012345

; The length of the longest line, n, is 15.  That is, the length of the longest
; line counts the spaces from the start of the printing.  In the case of a
; KEYPAIR tuple:

; :KEY (FOO
;       (BAR X)
;       Y)
;|<- 13      ->|

; we count the spaces from the beginning of the keyword.  That is, we consider
; the whole block of text.

; Below we print test-term in two different widths, and display the ppr tuple
; that drives each of the two printings.

; (assign test-term
;         '(FFF (GGG (HHH (QUOTE (A . B))))
;               (III YYY ZZZ)))
;
;
; (ppr2 (ppr1 (@ test-term) (print-base) (print-radix) 30 0 state nil) 0
;       *standard-co* state nil)
; ; =>
; (FFF (GGG (HHH '(A . B)))          (WIDE 25 (FLAT 3 FFF)
;      (III YYY ZZZ))                         (FLAT 20 (GGG (HHH '(A . B))))
;                                             (FLAT 14 (III YYY ZZZ)))
; <-          25         ->|
;
; (ppr2 (ppr1 (@ test-term) (print-base) (print-radix) 20 0 state nil) 0
;       *standard-co* state nil)
; ; =>
; (FFF                               (1 20 (FLAT 3 FFF)
;  (GGG                                    (4 19 (FLAT 3 GGG)
;      (HHH '(A . B)))                           (FLAT 15 (HHH '(A . B))))
;  (III YYY ZZZ))                          (FLAT 14 (III YYY ZZZ)))
;
; <-       20       ->|

; The function cons-ppr1, below, is the first interesting function in the nest.
; We want to build a tuple to print a given list form, like a function call.
; We basically get the tuple for the car and a list of tuples for the cdr and
; then use cons-ppr1 to combine them.  The resulting list of tuples will be
; embedded in either a WIDE or an indent tuple.  Thus, this list of tuples we
; will create describes a column of forms.  The number of items in that column
; is not necessarily the same as the number of arguments of the function call.
; For example, the term (f a b c) might be prettyprinted as
; (f a
;    b c)
; where b and c are printed flat on a single line.  Thus, the three arguments
; of f end up being described by a list of two tuples, one for a and another
; for b and c.

; To form lists of tuples we just use cons-ppr1 to combine the tuples we get
; for each element.

; Let x and lst be, respectively, a ppr tuple for an element and a list of
; tuples for list of elements.  Think of lst as describing a column of forms.
; Either x can become another item that column, or else x can be incorporated
; into the first item in that column.  For example, suppose x will print as X
; and lst will print as a column containing y1, y2, etc.  Then we have this
; choice for printing x and lst:

; lengthened column          lengthened first row
; x                          x y1
; y1                         y2
; ...                        ...

; We get the `lengthened column' behavior if we just cons x onto lst.  We get
; the `lengthened row' behavior if we merge the tuples for x and y1.  But we
; only merge if they both print flat.

; Now we lay down some macros that help with the efficiency of the FMT
; functions, by making it easy to declare various formals and function values
; to be nonnegative fixnums.  See the Essay on Fixnum Declarations.

(defmacro mv-letc (vars form body)
  `(mv-let ,vars ,form
     (declare (type #.*fixnat-type* col))
     ,body))

(defmacro er-hard-val (val &rest args)

; Use (er-hard-val val ctx str ...) instead of (er hard? ctx str ...)
; when there is an expectation on the return type, which should be the
; type of val.  Compilation with the cmulisp compiler produces many
; warnings if we do not use some such device.

  `(prog2$ (er hard? ,@args)
           ,val))

(defmacro er-hard?-val? (val quiet &rest args)

; We use er-hard?-val to signal an error unless quiet is true,

  `(if ,quiet
       ,val
     (er-hard-val ,val ,@args)))

(defmacro the-fixnum! (n ctx)
  `(the-fixnum
    (let ((n ,n))
      (if (and (<= n ,(fixnum-bound))
               (>= n ,(- (1+ (fixnum-bound)))))
          n
        (er-hard-val 0 ,ctx
                     "The object ~x0 is not a fixnum (precisely:  not a ~
                      ~x1)."
                     n *fixnum-type*)))))

(defmacro the-fixnat! (n ctx)
  `(the-fixnum
    (let ((n ,n))
      (if (and (<= n ,(fixnum-bound))
               (>= n 0))
          n
        (er-hard-val 0 ,ctx
                     "The object ~x0 is not a nonnagative fixnum (precisely:  ~
                      not a ~x1)."
                     n *fixnat-type*)))))

(defmacro the-unsigned-byte! (bits n ctx)
  `(the (unsigned-byte ,bits)
        (let ((n ,n) (bits ,bits))
          (if (unsigned-byte-p bits n)
              n
            (er-hard-val 0 ,ctx
                         "The object ~x0 is not an (unsigned-byte ~x1)."
                         n bits)))))

(defmacro the-string! (s ctx)
  `(if (stringp ,s)
       (the string ,s)
     (er-hard-val "" ,ctx
                  "Not a string:  ~x0."
                  ,s)))

(defun xxxjoin-fixnum (fn args root)

; This is rather like xxxjoin, but we wrap the-fixnum around all
; arguments.

  (declare (xargs :guard (true-listp args)))
  (if (cdr args)
      (list 'the-fixnum
            (list fn
                  (list 'the-fixnum (car args))
                  (xxxjoin-fixnum fn (cdr args) root)))
    (if args ; one arg
        (list 'the-fixnum (car args))
      root)))

(defmacro +f (&rest args)
  (xxxjoin-fixnum '+ args 0))

(defmacro -f (arg1 &optional arg2)
  (if arg2
      `(the-fixnum (- (the-fixnum ,arg1)
                      (the-fixnum ,arg2)))
    `(the-fixnum (- (the-fixnum ,arg1)))))

(defmacro 1-f (x)
  (list 'the-fixnum
        (list '1- (list 'the-fixnum x))))

(defmacro 1+f (x)
  (list 'the-fixnum
        (list '1+ (list 'the-fixnum x))))

(defmacro charf (s i)
  (list 'the 'character
        (list 'char s i)))

(defmacro *f (&rest args)
  (xxxjoin-fixnum '* args 1))

; Essay on the Printing of Dotted Pairs and

; It is instructive to realize that we print a dotted pair as though it were a
; list of length 3 and the dot was just a normal argument.

; In the little table below I show, for various values of d, two things: the
; characters output by

; (ppr2 (ppr1 `(xx . yy) (print-base) (print-radix) d 0 state nil)
;       0 *standard-co* state nil)

; and the ppr tuple produced by the ppr1 call.
;
; d         output                 ppr tuple

;        |<-  9  ->|

; 9       (XX . YY)              (FLAT 9 (XX . YY))

; 8       (XX                    (3 8 (FLAT 2 XX) (FLAT 5 . YY))
;            . YY)

; 7       (XX                    (2 7 (FLAT 2 XX) (FLAT 5 . YY))
;           . YY)

; 6       (XX                    (1 6 (FLAT 2 XX) (FLAT 5 . YY))
;          . YY)

; 5       (XX                    (2 5 (FLAT 2 XX) (DOT 1) (FLAT 3 YY))
;           .
;           YY)

; 4       (XX                    (1 4 (FLAT 2 XX) (DOT 1) (FLAT 3 YY))
;          .
;          YY)

; The fact that the dot is not necessarily connected to (on the same line as)
; the atom following it is the reason we have the (DOT 1) tuple.  We have to
; represent the dot so that its placement is first class.  So when we're
; assembling the tuple for a list, we cdr down the list using cons-ppr1 to put
; together the tuple for the car with the tuple for the cdr.  If we reach a
; non-nil cdr, atm, we call cons-ppr1 on the dot tuple and the tuple
; representing the atm.  Depending on the width we have, this may produce (FLAT
; n . atm) which attaches the dot to the atm, or ((DOT 1) (FLAT n atm)) which
; leaves the dot on a line by itself.

; We want keywords to appear on new lines.  That means if the first element of
; lst is a keyword, don't merge (unless x is one too).

; BUG
; ACL2 p!>(let ((x '(foo bigggggggggggggggg . :littlllllllllllllle)))
;          (ppr2 (ppr1 x (print-base) (print-radix) 40 0 state nil)
;                0 *standard-co* state nil))
; (x   = (DOT 1)
; lst = ((FLAT 21 :LITTLLLLLLLLLLLLLLE))
; val = ((FLAT 23 . :LITTLLLLLLLLLLLLLLE)))
;
; HARD ACL2 ERROR in CONS-PPR1:  I thought I could force it!

(defmacro ppr-flat-right-margin ()
  '(f-get-global 'ppr-flat-right-margin state))

(defconst *ppr-special-syms*

; The values in the following alist must all satisfy natp.  We keep this alist
; sorted by key (for readability only).

  '((case . 1)
    (case-match . 1)
    (defabsstobj . 1)
    (defaxiom . 1)
    (defchoose . 3)
    (defcong . 2)
    (defconst . 1)
    (defmacro . 2)
    (defstobj . 1)
    (defthm . 1)
    (defthmd . 1)
    (defun . 2)
    (defun-inline . 2)
    (defun-sk . 2)
    (defund . 2)
    (encapsulate . 1)
    (if . 2)
    (lambda . 1)
    (lambda$ . 1)
    (let . 1)
    (let* . 1)
    (mutual-recursion . 0)
    (mv-let . 2)
    (table . 1)))

(set-table-guard ppr-special-syms
                 (and (symbolp key)
                      (natp val)))

(table ppr-special-syms nil *ppr-special-syms* :clear)

(defun symbol-to-fixnat-alistp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (eq x nil))
        (t (and (consp (car x))
                (symbolp (car (car x)))
                (fixnat-guard (cdr (car x)))
                (symbol-to-fixnat-alistp (cdr x))))))

(defun special-term-num (sym state)
  (declare (xargs :guard (and (symbolp sym)
                              (symbol-to-fixnat-alistp
                               (table-alist 'ppr-special-syms (w state))))))
  (let ((pair (assoc-eq sym (table-alist 'ppr-special-syms (w state)))))

; Because of the table guard on ppr-special-syms, we know that all values in the
; table satisfy natp.  So this function is guaranteed to return either nil or a
; natp.

    (and pair
         (cdr pair))))

(defun set-ppr-flat-right-margin (val state)
  (if (posp val)
      (f-put-global 'ppr-flat-right-margin val state)
    (prog2$ (illegal 'set-ppr-flat-right-margin
                     "Set-ppr-flat-right-margin takes a positive integer ~
                      argument, unlike ~x0."
                     (list (cons #\0 val)))
            state)))

(mutual-recursion

(defun ppr-tuple-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (consp (cdr x))
       (unsigned-byte-p #.*small-nat-bits* (cadr x))
       (case (car x)
         (FLAT

; Note that there are no constraints on (cddr x).  It might be an atom, an
; eviscerated object, or a proper or improper list.

           t)
         (MATCHED-KEYWORD
          (and (consp (cddr x))
               (keywordp (caddr x))))
         (DOT t)
         (QUOTE (ppr-tuple-p (cddr x)))
         (KEYPAIR (and (consp (cddr x))
                       (ppr-tuple-p (car (cddr x)))
                       (ppr-tuple-p (cdr (cddr x)))))
         (WIDE (and (consp (cddr x))
                    (ppr-tuple-lst-p (cddr x))))
         (SPECIAL-TERM
          (and (consp (cddr x))
               (consp (cdddr x))
               (consp (car (cdddr x)))
               (consp (cddddr x))
               (ppr-tuple-p (caddr x))
               (or (null (car (cadr (cddr x))))
                   (unsigned-byte-p #.*small-nat-bits* (car (cadr (cddr x)))))
               (ppr-tuple-lst-p (cdr (cadr (cddr x))))
               (unsigned-byte-p #.*small-nat-bits* (car (cddr (cddr x))))
               (ppr-tuple-lst-p (cdr (cddr (cddr x))))))
         (otherwise
          (and (unsigned-byte-p #.*small-nat-bits* (car x))
               (consp (cddr x))
               (ppr-tuple-lst-p (cddr x)))))))

(defun ppr-tuple-lst-p (lst)
  (declare (xargs :guard t))
  (cond
   ((atom lst) (null lst))
   (t (and (ppr-tuple-p (car lst))
           (ppr-tuple-lst-p (cdr lst))))))
)

(defun keyword-param-valuep (tuple eviscp)

; We return t iff tuple represents a single object that could plausibly be the
; value of a keyword parameter.  The (or i ii iii iv) below checks that tuple
; represents a single object, either by being (i) a FLAT tuple listing exactly
; one object (ii) a QUOTE tuple, (iii) a WIDE tuple, or (iv) an indent tuple.
; The only other kinds of tuples are KEYPAIR tuples, FLAT tuples representing
; dotted objects `. atm', FLAT tuples representing several objects `a b c', and
; MATCHED-KEYWORD tuples representing keywords whose associated values are on
; the next line.  These wouldn't be provided as the value of a keyword
; argument.

  (declare (type cons tuple)
           (xargs :guard (ppr-tuple-p tuple)))

  (or (and (eq (car tuple) 'flat)
           (not (or (atom (cddr tuple)) ; tuple is `. atm'
                    (evisceratedp eviscp (cddr tuple))))
           (null (cdr (cddr tuple))))
      (eq (car tuple) 'quote)
      (eq (car tuple) 'wide)
      (integerp (car tuple))))

; Note: In the functions cons-ppr1-guardp and cons-ppr1 below, column is NOT a
; number!  Often in this code, ``col'' is used to represent the position of the
; character column into which we are printing.  But ``column'' is a list of ppr
; tuples.

(defun cons-ppr1-guardp (x column width ppr-flat-right-margin)
  (declare (xargs :guard t))
  (and (ppr-tuple-p x)
       (ppr-tuple-lst-p column)
       (unsigned-byte-p #.*small-nat-bits* width)
       (unsigned-byte-p #.*small-nat-bits* ppr-flat-right-margin)

; The following test formalizes the comment in cons-ppr1: ``Thus, (cddr x) is a
; list of length 1...''.

       (cond ((eq (car x) 'flat)
              (and (consp (cddr x))
                   (null (cdddr x))))
             (t t))
       (cond ((eq (car x) 'dot)
              (and (consp column)
                   (consp (car column))
                   (implies (eq (car (car column)) 'flat)
                            (consp (cddr (car column))))))
             (t t))))

(defun cons-ppr1 (x column width ppr-flat-right-margin pair-keywords-p eviscp)

; Here, x is a ppr tuple representing either a dot or a single object and
; column is a list of tuples corresponding to a list of objects (possibly a
; list of length greater than that of column).  Intuitively, column will print
; as a column of objects and we want to add x to that column, either by
; extending the top row or adding a new row.  In the most typical case, x might
; be (FLAT 3 ABC) and column is ((FLAT 7 DEF GHI) (...)).  Thus our choices
; would be to produce

; lengthened column          lengthened first row
; ABC                        ABC DEF GHI
; DEF GHI                    (...)
; (...)

; It is also here that we deal specially with keywords.  If x is
; (FLAT 3 :ABC) and column is ((...) (...)) then we have the choice:

; lengthened column          lengthened first row
; :ABC                       :ABC (...)
; (...)                      (...)
; (...)

; The default behavior is always to lengthen the column, which is just to cons
; x onto column.

  (declare (type cons x)
           (type #.*small-nat-type* width ppr-flat-right-margin)
           (xargs :guard
                  (cons-ppr1-guardp x column width ppr-flat-right-margin)
                  :split-types t))
  (cond
   ((and (eq (car x) 'flat)

; Note: Since x represents a dot or an object, we know that it is not of the
; form (FLAT n . atm).  Thus, (cddr x) is a list of length 1 containing a
; single (possibly eviscerated) object, x1.  If that object is an atom (or
; prints like one) we'll consider merging it with whatever else is on the first
; row.

         (or (atom (car (cddr x)))
             (evisceratedp eviscp (car (cddr x))))
         (consp column))

    (let ((x1 (car (cddr x)))
          (row1 (car column)))

; We know x represents the atom x1 (actually, x1 may be an eviscerated object,
; but if so it prints flat like an atom, e.g., `<world>').  Furthermore, we
; know column is non-empty and so has a first element, e.g., row1.

      (cond
       ((keywordp x1)

; So x1 is a keyword.  Are we looking at a keypair?  We are if row1 represents
; a single value.  By a ``single value'' we mean a single object that can be
; taken as the value of the keyword x1.  If row1 represents a sequence of more
; than one object, e.g., (FLAT 5 a b c), then we are not in a keypair situation
; because keyword argument lists must be keyword/value pairs all the way down
; and we form these columns bottom up, so if b were a keyword in the proper
; context, we would have paired it with c as keypair, not merged it, or we
; would have put it in a MATCHED-KEYWORD, indicating that its associated value
; is below it in the column.  If row1 does not represent a single value we act
; just like x1 had not been a keyword, i.e., we try to merge it with row1.
; This will shut down subsequent attempts to create keypairs above us.

        (cond
         ((and (keyword-param-valuep row1 eviscp)
               (or pair-keywords-p
                   (null (cdr column))
                   (eq (car (cadr column)) 'keypair)
                   (eq (car (cadr column)) 'matched-keyword)))

; So x1 is a keyword, row1 represents a keyword parameter value, and
; the rest of the column represents keyword/value pairs.  The last
; test is made by just checking the item on the column below row1.  It
; would only be a keyword/value pair if the whole column consisted of
; those.  We consider making a keypair of width n = width of key, plus
; space, plus width of widest line in row1.  Note that we don't mind
; this running over the standard 40 character max line length because
; it is so iconic.

          (let ((n (+g! (cadr x) 1 (cadr row1))))
            (declare (type #.*small-nat-type* n))
            (cond ((<= n width)
                   (cons
                    (cons 'keypair (cons n (cons x row1)))
                    (cdr column)))

; Otherwise, we put x on a newline and leave the column as it was.  Note that
; we convert x from a FLAT to a MATCHED-KEYWORD, to ensure that it stays on a
; line by itself and to ensure keyword/value pairs encountered above us in the
; bottom-up processing to be paired with KEYPAIR.

                  (t (cons (cons 'MATCHED-KEYWORD (cdr x))
                           column)))))

; In this case, we are not in the context of a keyword/value argument even
; though x is a keyword.  So we act just like x is not a keyword and see
; whether we can merge it with row1.  We merge only if row1 is FLAT already and
; the width of the merged row is acceptable.  Even if row1 prints as `. atm' we
; will merge, giving rise to such displays as

; (foo a b c
;      d e f . atm)

         ((eq (car row1) 'flat)
          (let ((n (+g! (cadr x) 1 (cadr row1))))
            (declare (type #.*small-nat-type* n))
            (cond ((and (<= n ppr-flat-right-margin) (<= n width))
                   (cons
                    (cons 'flat (cons n (cons x1 (cddr row1))))
                    (cdr column)))
                  (t (cons x column)))))
         (t (cons x column))))

; In this case, x1 is not a keyword.  But it is known to print in atom-like
; way, e.g., `ABC' or `<world>'.  So we try a simple merge following the same
; scheme as above.

       ((eq (car row1) 'flat)
        (let ((n (+g! (cadr x) 1 (cadr row1))))
          (declare (type #.*small-nat-type* n))
          (cond ((and (<= n ppr-flat-right-margin) (<= n width))
                 (cons
                  (cons 'flat (cons n (cons x1 (cddr row1))))
                  (cdr column)))
                (t (cons x column)))))
       (t (cons x column)))))
   ((and (eq (car x) 'dot)
         (consp column))
    (let ((row1 (car column)))
      (cond ((eq (car row1) 'flat)

; In this case we know (car (cddr row1)) is an atom (or an eviscerated object)
; and it becomes the cddr of the car of the answer, which puts the dot on the
; same line as the terminal cdr.

             (let ((n (+g! (cadr x) 1 (cadr row1))))
               (declare (type #.*small-nat-type* n))
               (cond ((and (<= n ppr-flat-right-margin) (<= n width))
                      (cons
                       (cons 'flat
                             (cons n (car (cddr row1))))
                       (cdr column)))
                     (t (cons x column)))))
            (t (cons x column)))))

; In this case, x1 does not print flat.  So we add a new row.

   (t (cons x column))))

(defun flsz-integer (x print-base acc)
  (declare (type integer x)
           (type (unsigned-byte 5) print-base)
           (type #.*fixnat-type* acc)
           (xargs :guard (print-base-p print-base)
                  :ruler-extenders :lambdas
                  :measure (cond ((not (and (integerp x)
                                            (natp acc)
                                            (< acc (fixnum-bound))
                                            (print-base-p print-base)))
                                  0)
                                 ((< x 0)
                                  (+ 1 (- x)))
                                 ((< x print-base) 0)
                                 (t x))))
  (the-fixnat
   (cond ((not (mbt (and (integerp x)
                         (natp acc)
                         (print-base-p print-base))))
          0) ; impossible case; any legal value will do
         ((mbe :logic (>= acc (fixnum-bound))
               :exec (= acc (fixnum-bound)))

; How could a number be big enough to have 2^29 digits?  Even in base 2, for
; example, the flsz of 2^n is n+1; so the size of any natural less than 2^(2^29
; - 1) is less than 2^29 - 1 = (fixnum-bound).  It's difficult to imagine
; computing with a number as large as 2^(2^29 - 1).  But in the spirit of other
; flsz computations, we just return the maximum possible value in this case.

          (fixnum-bound))
         ((< x 0)
          (flsz-integer (- x) print-base (1+f acc)))
         ((< x print-base) (1+f acc))
         (t (flsz-integer (truncate x print-base) print-base (1+f acc))))))

(defun flsz-atom (x print-base print-radix acc state)
  (declare (type (unsigned-byte 5) print-base)
           (type #.*fixnat-type* acc)
           (xargs :guard (print-base-p print-base)
                  :ruler-extenders :lambdas
                  :measure (cond ((not (fixnat-guard acc))
                                  0)
                                 (t (acl2-count x)))))

  (the-fixnat
   (cond ((not (mbt (fixnat-guard acc)))
          0)
         ((integerp x)
          (flsz-integer x
                        print-base
                        (cond ((null print-radix)
                               acc)
                              ((int= print-base 10) ; `.' suffix
                               (+f! 1 acc))
                              (t ; #b, #o, or #x prefix
                               (+f! 2 acc)))))
         ((symbolp x)

; For symbols we add together the length of the "package part" and the symbol
; name part.  We include the colons in the package part.

          (the-fixnat
           (let* ((s (symbol-name x))
                  (len (min (fixnum-bound) (length s)))
                  (s-sz (cond ((needs-slashes s state)
                               (+f! 2 len))
                              (t len)))
                  (acc (+f! acc s-sz)))
             (declare (type string s)
                      (type #.*fixnat-type* len s-sz acc))
             (the-fixnat
              (cond
               ((keywordp x) (+f! 1 acc))
               ((symbol-in-current-package-p x state)
                acc)
               (t
                (let* ((p (symbol-package-name x))
                       (p-len (min (fixnum-bound) (length p))))
                  (declare (type string p)
                           (type #.*fixnat-type* p-len))
                  (cond ((needs-slashes p state)
                         (+f! 4 acc p-len))
                        (t (+f! 2 acc p-len))))))))))
         ((rationalp x)
          (flsz-integer (numerator x)
                        print-base
                        (flsz-integer (denominator x)
                                      print-base
                                      (cond ((null print-radix)
                                             (+f! 1 acc))
                                            ((= print-base 10) ; #10r prefix
                                             (+f! 5 acc))
                                            (t ; #b, #o, or #x prefix
                                             (+f! 3 acc))))))
         ((complex-rationalp x)
          (flsz-atom (realpart x)
                     print-base
                     print-radix
                     (mbe :logic
                          (min (fixnum-bound)
                               (max 0
                                    (flsz-atom (imagpart x) print-base
                                               print-radix acc state)))
                          :exec
                          (flsz-atom (imagpart x) print-base print-radix acc
                                     state))
                     state))
         ((stringp x)
          (+f! 2 acc (min (fixnum-bound) (length x))))
         ((characterp x)
          (cond ((eql x #\Newline) (+f! 9 acc))
                ((eql x #\Rubout) (+f! 8 acc))
                ((eql x #\Return) (+f! 8 acc))
                ((eql x #\Space) (+f! 7 acc))
                ((eql x #\Page) (+f! 6 acc))
                ((eql x #\Tab) (+f! 5 acc))
                (t (+f! 3 acc))))
         (t 0))))

(defconst *newline-string*
  (string #\Newline))

(defun flsz1 (x print-base print-radix j maximum state eviscp)
  (declare (type (unsigned-byte 5) print-base)
           (type #.*small-nat-type* j maximum)
           (xargs :guard (print-base-p print-base)
                  :measure (acl2-count x)
                  :ruler-extenders :lambdas
                  :verify-guards nil))
  (the-small
   t
   (cond ((> j maximum) j)
         ((atom x)
          (round-to-small t (flsz-atom x print-base print-radix j state)))
         ((evisceratedp eviscp x)
          (if (stringp (cdr x))
              (let ((p (search *newline-string* (cdr x) :from-end t)))
                (cond (p (+g! 1 maximum)) ; pretending width is exceeded
                      (t (+g! j (min (length (cdr x)) *small-hi*))))) ; limit length!
              (+g! 1 maximum))) ; pretending width is exceeded
         ((atom (cdr x))
          (cond ((null (cdr x))
                 (flsz1 (car x) print-base print-radix (+g! 2 j) maximum state
                        eviscp))
                (t (flsz1 (cdr x)
                          print-base
                          print-radix
                          (flsz1 (car x) print-base print-radix (+g! 5 j)
                                 maximum state eviscp)
                          maximum state eviscp))))
         ((and (eq (car x) 'quote)
               (consp (cdr x))
               (null (cddr x)))
          (flsz1 (cadr x) print-base print-radix (+g! 1 j) maximum state
                 eviscp))
         (t (flsz1 (cdr x)
                   print-base
                   print-radix
                   (flsz1 (car x) print-base print-radix (+g! 1 j) maximum state
                          eviscp)
                   maximum state eviscp)))))

; Historical Plaque on Infix Printing

; Once upon a time ACL2 supported the option of reading and printing in
; traditional infix notation.  E.g., ``x * expt(x,y-1)'' instead of ``(* x
; (expt x (- y 1)))'' or, in LaTeX notation, ``$x \times expt(x,y-1)$''.
; However, in 2017, this so-called ``infix'' option was deprecated because no
; one used it, and in 2023, we removed the last vestiges of it from the ACL2
; source code.  But the history of our experiments with infix is worth noting.

; Bob Boyer wrote the original infix printer for the Nqthm theorem prover.  The
; original functionality was to convert a Lisp-style input file for Nqthm into
; a LaTeX file so that the definitions and theorems could be included in
; journal papers in conventional notation.  In 1992 and 1993, Michael K. Smith,
; who worked with us at Computational Logic, Inc., added the option of
; producing Scribe output.

; The source code for the Nqthm infix printer is available as part of the
; Nqthm-1992 archive:

; ftp://ftp.cs.utexas.edu/pub/boyer/nqthm/nqthm-2nd-edition.tar.gz

; In particular, see the subdirectory sinfix/ and the main source file there
; sinfix.lisp.

; The printer is also documented in the book A Computational Logic Handbook,
; Second Edition, Academic Press, NY, 1997, pp 421-422.

; The motivation of writing such a printer was recorded in sinfix.lisp:

;   We hope this notation will facilitate the communication of work with Nqthm
;   to those who do not happily read Lisp notation.  But we have no expectation
;   that this notation will make it easier for the Nqthm user to formulate or
;   to prove theorems.

; As the above-mentioned Handbook notes, however,

;   Unfortunately, ``conventional'' notation is remarkably unconventional as
;   soon as one begins dealing with non-arithmetic operators (and even with
;   arithmetic operators if one must distinguish, say, Peano addition from
;   rational addition).

; The facility allowed the user to include a table noting how given Nqthm
; function calls were to be printed and that table was included in the LaTeX or
; Scribe output.

; Don Knuth pronounced the output ``beautiful'' when Boyer showed it to him.

; Yuan Yu used the infix printer in his paper with Boyer describing Yu's
; remarkable formalization of the Motorola 68020 and proofs of the correctness
; of several dozen machine code programs compiled by standard C compilers.  The
; Nqthm source code for the paper and the resulting .tex and .ps files may be
; found in the Nqthm-1992 archives under examples/yu/mc20-1.*.

; ACL2 was being developed concurrently by Boyer, Moore, and Kaufmann during
; this period and an ACL2 version of the printer was included, thanks to Mike
; Smith again, in the early versions of ACL2.  Mike also adapted the printer to
; produce infix-style terminal output if certain options were enabled.

; However, the facility never caught on.  Papers were generally published in
; the native Common Lisp notation or informally translated to conventional
; notation.  We suspect the main reason it never caught on is that ACL2 users
; were (and are) more interested in applying formal methods to industrial
; designs, and in communicating that work to other knowledgeable ACL2 users,
; than in writing papers about their work for a more general audience.  By 2017
; we decided that we would no longer maintain the infix printer code in the
; ACL2 sources and we eliminated it completely in 2023.

(defun fmt-state-p (state)
  (declare (xargs :stobjs state))
  (and (state-p state)
       (small-nat-guard (f-get-global 'fmt-hard-right-margin state))
       (small-nat-guard (f-get-global 'fmt-soft-right-margin state))
       (alistp (table-alist 'evisc-table (w state)))
       (eviscerate-top-state-p state)
; Probably unnecessary, but makes some proofs easier since compress1 is the
; identity for arrays like this:
       (equal (array-order (header 'iprint-ar
                                   (f-get-global 'iprint-ar state)))
              nil)
; Additions for ppr1 and ppr1-lst
       (small-nat-guard (ppr-flat-right-margin))
       (symbol-to-fixnat-alistp (table-alist 'ppr-special-syms (w state)))
       (not (assoc-eq 'quote
                      (table-alist 'ppr-special-syms (w state))))))

(defun flsz (x j maximum state eviscp)
  (declare (type #.*fixnat-type* j maximum)
           (xargs :guard ; for (print-base)
                  (fmt-state-p state)))
  (flsz1 x
         (the-fixnat (print-base))
         (print-radix)
         (round-to-small t j)
         (round-to-small t maximum)
         state eviscp))

(defun max-width (lst maximum)
; We allow maximum to be negative simply because ppr1 might use -1 as the
; initial value.  With that exception, max-width should always return
; a small natural number.
  (declare (type #.*small-type* maximum)
           (xargs :guard (ppr-tuple-lst-p lst)))
  (cond ((endp lst) maximum)
        ((> (cadr (car lst)) maximum)
         (max-width (cdr lst) (cadr (car lst))))
        (t (max-width (cdr lst) maximum))))

(mutual-recursion

(defun ppr1 (x print-base print-radix width rpc state eviscp)

; We create a ppr tuple for x, i.e., a list structure that tells us how to
; prettyprint x, in a column of the given width.  Rpc stands for `right paren
; count' and is the number of right parens that will follow the printed version
; of x.  For example, in printing the x in (f (g (h x)) u) there will always be
; 2 right parens after it.  So we cannot let x use the entire available width,

; only the width-2.  Rpc would be 2.  Eviscp indicates whether we are to think
; of evisc marks as printing as atom-like strings or whether they're just
; themselves as data.

  (declare (type (unsigned-byte 5) print-base)
           (type #.*small-nat-type* width rpc)
           (xargs :guard (and (print-base-p print-base)
                              (unsigned-byte-p #.*small-nat-bits* (ppr-flat-right-margin))
                              (symbol-to-fixnat-alistp
                               (table-alist 'ppr-special-syms (w state)))
                              (not (assoc-eq 'quote (table-alist 'ppr-special-syms (w state)))))
                  :measure (* 2 (acl2-count x))
                  :ruler-extenders :lambdas
                  :verify-guards nil))

  (if (mbt (symbol-to-fixnat-alistp
            (table-alist 'ppr-special-syms (w state))))
      (let ((sz (flsz1 x print-base print-radix rpc width state eviscp))
            (width-1 (+g! width -1)))
        (declare (type #.*small-nat-type* sz width-1))
        (cond ((or (atom x)
                   (evisceratedp eviscp x)
                   (and (<= sz width)
                        (<= sz (ppr-flat-right-margin))))
               (cons 'flat (cons sz (list x))))
              ((and (eq (car x) 'quote)
                    (consp (cdr x))
                    (null (cddr x)))
               (let* ((x1 (ppr1 (cadr x) print-base print-radix width-1 rpc state
                                eviscp)))
                 (cons 'quote (cons (+g! 1 (cadr x1)) x1))))
              (t
               (let* ((x1 (ppr1 (car x) print-base print-radix width-1
                                (if (null (cdr x)) (+g! rpc 1) 0)
                                state eviscp))

; If the fn is a symbol (or eviscerated, which we treat as a symbol), then the
; hd-sz is the length of the symbol.  Else, hd-sz is nil.  Think of (null
; hd-sz) as meaning "fn is a lambda expression" but, since we don't actually
; assume x is a term, ``fn'' could be any object!

                      (hd-sz (cond ((or (atom (car x))
                                        (evisceratedp eviscp (car x)))
                                    (cadr x1))
                                   (t nil)))

; Special-term-num non-nil means: print args after special-term-num(-th) arg
; indenting just 2 spaces.

                      (special-term-num (if (symbolp (car x))
                                            (special-term-num (car x) state)
                                            nil))
                      (special-term-num (and special-term-num
                                             (true-listp (cdr x))
                                             (>= (len (cdr x)) special-term-num)
                                             special-term-num))

; When printing the cdr of x (or the special-term-num(-th) cdr), give each
; argument the full width (minus 1 for the minimal amount of indenting).  Note
; that x2 contains the ppr tuples for the car and the cdr.

                      (xc (ppr1-lst (cdr (if special-term-num
                                             (nthcdr special-term-num x)
                                             x))
                                    print-base print-radix width-1
                                    (+g! rpc 1) special-term-num state eviscp))
                      (x2 (cons x1 xc))

; If the fn is a symbol, then we get the maximum width of any single argument.
; Otherwise, we get the maximum width of the fn and its arguments.  Xc could be
; nil, so if hd-sz is non-nil, maximum is -1, which represents the lack of a
; space before the arguments.  The possibility that maximum could be negative
; (and thus not an unsigned-byte) means we have to be careful below unless we
; know that either hd-sz is nil or that xc is non-nil.

                      (maximum (cond (hd-sz (max-width xc -1))
                                     (t (max-width x2 0)))))
                 (declare (type #.*small-type* maximum))
                 (cond ((null hd-sz)

; If the fn is lambda, we indent the args by 1 and report the width of the
; whole to be one more than the maximum computed above.

                        (cons 1 (cons (+g! 1 maximum) x2)))

; Hd-sz is non-nil, so maximum may be -1.

                       (special-term-num
                        (let* ((init-args (take special-term-num (cdr x)))
                               (opt-name-pp
                                (if (and init-args
                                         (symbolp (car init-args)))
                                    (ppr1 (car init-args)
                                          print-base print-radix
                                          (max (-f width hd-sz) 0)
                                          0 state eviscp)
                                    nil))
                               (opt-name-pp
                                (and opt-name-pp
                                     (<= (+g! hd-sz 1 (cadr opt-name-pp)) width-1)
                                     opt-name-pp))
                               (opt-name-sz
                                (if opt-name-pp (+g! 1 (cadr opt-name-pp)) 0))
                               (x1 (if opt-name-pp
                                       (cons 'flat (cons (+g! hd-sz opt-name-sz)
                                                         (list (car x)
                                                               (car init-args))))
                                       x1))
                               (init-args-pp
                                (and init-args
                                     (ppr1-lst (if opt-name-pp
                                                   (cdr init-args)
                                                   init-args)
                                               print-base print-radix width-1
                                               (if (null xc) (+g! rpc 1) 0)
                                               nil state eviscp)))
                               (max-init-args-pp (max-width init-args-pp 0))
                               (init-args-indent
                                (and init-args-pp
                                     (>= (+g! hd-sz opt-name-sz max-init-args-pp)
                                         width-1) ; Put on first line if false.
                                     (if (>= (+g! hd-sz max-init-args-pp)
                                             width-1)
                                         (max 1 (-g! width-1 max-init-args-pp))
                                         (+g! hd-sz 2))))
                               (xc-indent (if (or (>= maximum width-1)
                                                  (equal init-args-indent 1))
                                              1 2))
                               (maximum
                                (max (max hd-sz
                                          (+g! maximum xc-indent -1))
                                     (cond (init-args-indent
                                            (+g! init-args-indent -1 max-init-args-pp))
                                           (t (+g! hd-sz opt-name-sz 1 max-init-args-pp))))))
                          (declare (type #.*small-nat-type*
                                         maximum
                                         max-init-args-pp))
                          (cons 'special-term
                                (cons (+g! 1 maximum) ; 1 for left paren.
                                      (cons x1
                                            (cons (cons init-args-indent init-args-pp)
                                                  (cons xc-indent xc)))))))
                       ((<= (+g! hd-sz 2 maximum)
                            width)

; We can print WIDE if we have room for an open paren, the fn, a space, and the
; widest argument.

                        (cons 'wide
                              (cons (+g! hd-sz 2 maximum)
                                    x2)))
                       ((< maximum width)

; If the maximum is less than the width, we can do exact indenting of the
; arguments to make the widest argument come out on the right margin.  This
; exactness property is one of the things that makes this algorithm produce
; such beautiful output: we get the largest possible indentation, which makes
; it easy to identify peer arguments.  How much do we indent?  width-maximum
; will guarantee that the widest argument ends on the right margin.  However,
; we believe that it is more pleasing if argument columns occur at regular
; indents.  So we limit our indenting to 5 and just give up the white space
; over on the right margin.  Note that we compute the width of the whole term
; accordingly.

                        (cons (min 5 (-g! width maximum))
                              (cons (+g! maximum (min 5 (-g! width maximum)))
                                    x2)))

; If maximum is not less than width, we indent by 1.

                       (t (cons 1 (cons (+g! 1 maximum) x2))))))))
      nil))

; The next function computes a ppr tuple for each element of lst.  Typically
; these are all arguments to a function.  But of course, we prettyprint
; arbitrary constants and so have to handle the case that the list is not a
; true-list.

; If you haven't read about cons-ppr1, above, do so now.

(defun ppr1-lst (lst print-base print-radix width rpc pair-keywords-p state
                     eviscp)
  (declare (type (unsigned-byte 5) print-base)
           (type #.*small-nat-type* width)
           (type #.*small-nat-type* rpc)
           (xargs :guard (and (print-base-p print-base)
                              (unsigned-byte-p #.*small-nat-bits* (ppr-flat-right-margin))
                              (symbol-to-fixnat-alistp
                               (table-alist 'ppr-special-syms (w state)))
                              (not (assoc-eq 'quote (table-alist 'ppr-special-syms (w state)))))
                  :measure (1+ (* 2 (acl2-count lst)))
                  :ruler-extenders :lambdas
                  :verify-guards nil))
  (cond ((atom lst)

; If the list is empty and null, then nothing is printed (besides the parens
; which are being accounted for otherwise).  If the list is terminated by some
; non-nil atom, we will print a dot and the atom.  We do that by merging a dot
; tuple into the flat for the atom, if there's room on the line, using
; cons-ppr1.  Where this merged flat will go, i.e., will it be indented under
; the car as happens in the Essay on the Printing of Dotted Pairs, is the
; concern of ppr1-lst, not the cons-ppr1.  The cons-ppr1 below just produces a
; merged flat containing the dot, if the width permits.

         (cond ((null lst) nil)
               (t (cons-ppr1 '(dot 1)
                             (list (ppr1 lst print-base print-radix width rpc
                                         state eviscp))
                             width (ppr-flat-right-margin) nil eviscp))))

; The case for an eviscerated terminal cdr is handled the same way.

        ((evisceratedp eviscp lst)
         (cons-ppr1 '(dot 1)
                    (list (ppr1 lst print-base print-radix width rpc state
                                eviscp))
                    width (ppr-flat-right-margin) nil eviscp))

; If the list is a true singleton, we just use ppr1 and we pass it the rpc that
; was passed in because this last item will be followed by that many parens on
; the same line.

        ((null (cdr lst))
         (list (ppr1 (car lst) print-base print-radix width rpc state eviscp)))

; Otherwise, we know that the car is followed by more elements.  So its rpc is
; 0.

        (t (cons-ppr1 (ppr1 (car lst) print-base print-radix width 0 state
                            eviscp)
                      (ppr1-lst (cdr lst) print-base print-radix width rpc
                                pair-keywords-p state eviscp)
                      width (ppr-flat-right-margin) pair-keywords-p eviscp))))

)

(defun newline (channel state)
  (declare (xargs :guard (and (symbolp channel)
                              (open-output-channel-p channel :character state))))
  (princ$ #\Newline channel state))

(defun fmt-hard-right-margin (state)
  (declare (xargs :guard
                  (small-nat-guard (f-get-global 'fmt-hard-right-margin state))))
  (the #.*small-nat-type*
       (f-get-global 'fmt-hard-right-margin state)))

(defun fmt-soft-right-margin (state)
  (declare (xargs :guard
                  (small-nat-guard (f-get-global 'fmt-soft-right-margin state))))
  (the #.*small-nat-type*
       (f-get-global 'fmt-soft-right-margin state)))

(defun set-fmt-hard-right-margin (n state)
  (declare (xargs :guard t :stobjs state))
  (cond
   ((and (small-nat-guard n)
         (not (= n 0)))
    (f-put-global 'fmt-hard-right-margin n state))
   (t (prog2$ (er hard? 'set-fmt-hard-right-margin
                  "The fmt-hard-right-margin must be a positive integer no ~
                   greater than ~x0, but ~x1 is not."
                  *small-hi*
                  n)
              state))))

(defun set-fmt-soft-right-margin (n state)
  (declare (xargs :guard t :stobjs state))
  (cond
   ((and (small-nat-guard n)
         (not (= n 0)))
    (f-put-global 'fmt-soft-right-margin n state))
   (t (prog2$ (er hard? 'set-fmt-soft-right-margin
                  "The fmt-soft-right-margin must be a positive integer no ~
                   greater than ~x0, but ~x1 is not."
                  *small-hi*
                  n)
              state))))

(defun write-for-read (state)
  (declare (xargs :guard t))
  (f-get-global 'write-for-read state))

(defun spaces1 (n col hard-right-margin channel state)
  (declare (type #.*fixnat-type* n col)
           (type #.*small-nat-type* hard-right-margin)
           (type symbol channel)
           (xargs :measure (nfix (+ (* 2 n) col))
                  :guard (open-output-channel-p channel :character state)))
  (cond ((mbt (and (natp n)
                   (natp col)
                   (natp hard-right-margin)))
         (cond
          ((= n 0)
           state)
          ((> col hard-right-margin)
           (pprogn (if (write-for-read state)
                       state
                     (princ$ #\\ channel state))
                   (newline channel state)
                   (spaces1 n 0 hard-right-margin channel state)))
          (t (pprogn (princ$ #\Space channel state)
                     (spaces1 (the #.*fixnat-type* (1- n))
                              (the #.*fixnat-type* (1+ col))
                              hard-right-margin channel
                              state)))))
        (t state)))

; The use of *acl2-built-in-spaces-array* to circumvent the call to spaces1
; under spaces has saved about 25% in GCL and a little more than 50% in
; Allegro.

(defun make-spaces-array-rec (n acc)
  (if (zp n)
      (cons (cons 0 "") acc)
    (make-spaces-array-rec
     (1- n)
     (cons
      (cons n
            (coerce (make-list n :initial-element #\Space) 'string))
      acc))))

(defun make-spaces-array (n)
  (compress1
   'acl2-built-in-spaces-array
   (cons `(:HEADER :DIMENSIONS (,(1+ n))
                   :MAXIMUM-LENGTH ,(+ 2 n)
                   :DEFAULT nil ; should be ignored
                   :NAME acl2-built-in-spaces-array)
         (make-spaces-array-rec n nil))))

(defconst *acl2-built-in-spaces-array*

; Keep the 200 below in sync with the code in spaces.

  (make-spaces-array 200))

(defun spaces (n col channel state)
  (declare (type #.*fixnat-type* n col)
           (type symbol channel)
           (xargs :guard
                  (and (fmt-state-p state)
                       (open-output-channel-p channel :character state))))
  (let ((hard-right-margin (fmt-hard-right-margin state))
        (result-col (+f! n col)))
    (declare (type #.*small-nat-type* hard-right-margin)
             (type #.*fixnat-type* result-col))
    (if (and (<= result-col hard-right-margin)

; Keep the 200 below in sync with the code in *acl2-built-in-spaces-array*.

             (<= n 200))
        ;; actually (1+ hard-right-margin) would do
        (princ$ (aref1 'acl2-built-in-spaces-array
                       *acl2-built-in-spaces-array*
                       n)
                channel state)
      (spaces1 n col hard-right-margin channel state))))

(mutual-recursion

(defun flpr1 (x channel state eviscp)
  (declare (type symbol channel)
           (xargs :guard (open-output-channel-p channel :character state)
                  :verify-guards nil
                  :measure (1+ (* 2 (acl2-count x)))))
  (cond ((atom x)
         (prin1$ x channel state))
        ((evisceratedp eviscp x)
         (princ$ (IF (ATOM (CDR X)) ; <--- ADDED!
                     (CDR X)
                     "<ILL-FORMED-EVISCERATED-OBJECT>")
                 channel state))
        ((and (eq (car x) 'quote)
              (consp (cdr x))
              (null (cddr x)))
         (pprogn (princ$ #\' channel state)
                 (flpr1 (cadr x) channel state eviscp)))
        (t (pprogn (princ$ #\( channel state)
                   (flpr11 x channel state eviscp)))))

(defun flpr11 (x channel state eviscp)
  (declare (type symbol channel)
           (xargs :guard
                  (and (consp x)
                       (open-output-channel-p channel :character state))
                  :measure (* 2 (acl2-count x))))
  (if (mbt (consp x))
      (pprogn
       (flpr1 (car x) channel state eviscp)
       (cond ((null (cdr x)) (princ$ #\) channel state))
             ((or (atom (cdr x))
                  (evisceratedp eviscp (cdr x)))
              (pprogn
               (princ$ " . " channel state)
               (flpr1 (cdr x) channel state eviscp)
               (princ$ #\) channel state)))
             (t (pprogn
                 (princ$ #\Space channel state)
                 (flpr11 (cdr x) channel state eviscp)))))
      state))

)

(defun flpr (x channel state eviscp)
  (declare (type symbol channel)
           (xargs :guard (open-output-channel-p channel :character state)))
  (flpr1 x channel state eviscp))

(defun ppr2-flat (x channel state eviscp)

; We print the elements of x, separated by spaces.  If x is a non-nil atom, we
; print a dot and then x.

  (declare (xargs :guard
                  (and (symbolp channel)
                       (open-output-channel-p channel :character state))))
  (cond ((null x) state)
        ((or (atom x)
             (evisceratedp eviscp x))
         (pprogn (princ$ #\. channel state)
                 (princ$ #\Space channel state)
                 (flpr1 x channel state eviscp)))
        (t (pprogn
            (flpr1 (car x) channel state eviscp)
            (cond ((cdr x)
                   (pprogn (princ$ #\Space channel state)
                           (ppr2-flat (cdr x) channel state eviscp)))
                  (t state))))))

(mutual-recursion

(defun ppr2-column (lst loc col channel state eviscp)

; We print the elements of lst in a column.  The column number is col and we
; assume the print head is currently in column loc.  If loc <= col, to indent
; to col we print col-loc spaces; otherwise print 1 space.  After every element
; of lst but the last, we print a newline.

  (declare (type (unsigned-byte #.*small-nat-bits*) loc col)
           (xargs :guard
                  (and (ppr-tuple-lst-p lst)
                       (fmt-state-p state)
                       (symbolp channel)
                       (open-output-channel-p channel :character state))
                  :measure (acl2-count lst)
                  :ruler-extenders :lambdas
                  :verify-guards nil))
  (if (mbt (ppr-tuple-lst-p lst))
      (cond
       ((null lst) state)
       (t (pprogn
           (spaces (if (> col loc)
                       (+g! col (- loc))
                       1)
                   loc channel state)
           (ppr2 (car lst)
                 (if (> col loc)
                     col
                     (+g! loc 1))
                 channel state eviscp)
           (cond ((null (cdr lst)) state)
                 (t (pprogn
                     (newline channel state)
                     (ppr2-column (cdr lst) 0 col
                                  channel state eviscp)))))))
      state))

(defun ppr2 (x col channel state eviscp)

; We interpret the ppr tuple x.

  (declare (type (unsigned-byte #.*small-nat-bits*) col)
           (xargs :guard
                  (and (ppr-tuple-p x)
                       (fmt-state-p state)
                       (symbolp channel)
                       (open-output-channel-p channel :character state))
                  :measure (acl2-count x)
                  :ruler-extenders :lambdas
                  :verify-guards nil))
  (if (mbt (ppr-tuple-p x))
      (case
        (car x)
        (flat (ppr2-flat (cddr x) channel state eviscp))
        (matched-keyword
         (ppr2-flat (cddr x) channel state eviscp)) ; just like flat!
        (dot (princ$ #\. channel state))
        (quote (pprogn (princ$ #\' channel state)
                       (ppr2 (cddr x) (+g! 1 col) channel state eviscp)))
        (keypair (pprogn
                  (ppr2-flat (cddr (car (cddr x))) channel state eviscp)
                  (princ$ #\Space channel state)
                  (ppr2 (cdr (cddr x))
                        (+g! col 1 (cadr (car (cddr x))))
                        channel state eviscp)))
        (wide (pprogn
               (princ$ #\( channel state)
               (ppr2-flat (cddr (car (cddr x))) channel state eviscp)
               (ppr2-column (cdr (cddr x))
                            (+g! col 1 (cadr (car (cddr x))))
                            (+g! col 2 (cadr (car (cddr x))))
                            channel state eviscp)
               (princ$ #\) channel state)))
        (special-term
         (let* ((rx (cddr x)) ; actual arguments to print
                (x1 (car rx))
                (x1-sz (cadr x1))
                (init-args-pp-info (cadr rx))
                (init-args-indent
                 (car init-args-pp-info)) ; if null goes on first line
                (init-args-pp (cdr init-args-pp-info))
                (init-args-pp-col (cond (init-args-indent (+g! col init-args-indent))
                                        (t (+g! col x1-sz 2))))
                (x2-indent (car (cddr rx)))
                (x2 (cdr (cddr rx))))
           (pprogn
            (princ$ #\( channel state)
            (ppr2 x1 (+g! col 1) channel state eviscp)
            (if init-args-indent (newline channel state) state)
            (if init-args-pp (ppr2-column init-args-pp
                                          (if init-args-indent 0 (+g! col x1-sz 1))
                                          init-args-pp-col channel state eviscp)
                state)
            (newline channel state)
            (ppr2-column x2 0 (+g! col x2-indent) channel state eviscp)
            (princ$ #\) channel state))))
        (otherwise (pprogn
                    (princ$ #\( channel state)
                    (ppr2 (car (cddr x)) (+g! col (car x)) channel
                          state eviscp)
                    (cond ((cdr (cddr x))
                           (pprogn
                            (newline channel state)
                            (ppr2-column (cdr (cddr x))
                                         0
                                         (+g! col (car x))
                                         channel state eviscp)
                            (princ$ #\) channel state)))
                          (t (princ$ #\) channel state))))))
      state))
)

; We used to set *fmt-ppr-indentation* below to 5, but it the indentation was
; sometimes odd because when printing a list, some elements could be indented
; and others not.  At any rate, it should be less than the
; fmt-hard-right-margin in order to preserve the invariant that fmt0 is called
; on columns that do not exceed this value.

(defconst *fmt-ppr-indentation* 0)

(defun ppr (x col channel state eviscp)

; If eviscp is nil, then we pretty print x as given.  Otherwise, x has been
; eviscerated and we give special importance to the *evisceration-mark*.  NOTE
; WELL: This function does not eviscerate -- it assumes the evisceration has
; been done if needed.

  (declare (type #.*small-nat-type* col)
           (type symbol channel)
           (xargs :guard
                  (and (fmt-state-p state)
                       (open-output-channel-p channel :character state))))
  (let ((fmt-hard-right-margin (fmt-hard-right-margin state)))
    (declare (type #.*small-nat-type* fmt-hard-right-margin))
    (cond
     ((< col fmt-hard-right-margin)
      (ppr2 (ppr1 x (print-base) (print-radix)
                  (-g! fmt-hard-right-margin col)
                  0 state eviscp)
            col channel state eviscp))
     (t (let ((er
               (er hard? 'ppr
                   "The `col' argument to ppr must be less than value ~
                    of the state global variable ~
                    fmt-hard-right-margin, but ~x0 is not less than ~
                    ~x1."
                   col fmt-hard-right-margin)))
          (declare (ignore er))
          state)))))

(defconst *illegal-fmt-keys*

; Warning: Keep this in sync with the cases in illegal-fmt-string.

  '(bad-evisc-tuple
    bad-tilde-&v-arg
    bad-tilde-*-arg
    bad-tilde-@-arg
    bad-tilde-c-arg
    bad-tilde-n-arg
    bad-tilde-s-arg
    bad-tilde-t-arg-natp
    bad-tilde-t-arg-not-natp
    bad-tilde-_-arg
    find-alternative-skip
    find-alternative-start
    find-alternative-start1-a
    find-alternative-start1-b
    find-alternative-stop
    tilde-arg-points-past-string
    unbound-tilde-arg
    unrecognized-tilde-arg))

(defun illegal-fmt-string (key)

; Warning: Keep the cases below in sync with *illegal-fmt-keys*.

  (declare (xargs :guard (member-eq key *illegal-fmt-keys*)))
  (case key
    (bad-evisc-tuple
     "In the fmt string displayed below, the tilde directive at location ~x0 ~
      associates character ~x1 with ~x2, which does not satisfy ~x3.~|~%~x4")
    (bad-tilde-&v-arg
     "The tilde directive at location ~x0 in the fmt string below uses the ~
      variable ~x1.  That ~s2 directive requires a true list, but it was ~
      supplied the value ~x3.~|~%~x4")
    (bad-tilde-*-arg
     "The tilde directive, ~~*, at location ~x0 in the fmt string below uses ~
      the variable ~x1.  That directive requires a list of the form (\"str0\" ~
      \"str1\" \"str2\" \"str3\" lst . alist) such that lst is a true-list ~
      and alist satisfies ~x2, but it was supplied the value ~x3.~|~%~x4")
    (bad-tilde-@-arg
     "The tilde-@ directive at position ~x0 of the string below is illegal ~
      because its variable evaluated to ~x1, which does not satisfy ~
      ~x2.~|~%~x3")
    (bad-tilde-c-arg
     "The tilde-c directive at position ~x0 of the string below is illegal ~
      because its variable evaluated to ~x1, which is not of the form (n . ~
      width), where n and width are integers and width is nonnegative.~|~%~x2")
    (bad-tilde-n-arg
     "The tilde directive at location ~x0 in the fmt string below uses the ~
      variable ~x1.  That ~s2 directive requires either an integer or a CONS ~
      whose CAR is an integer, but it was supplied the value ~x3.~|~%~x4")
    (bad-tilde-s-arg
     "The tilde-~s0 directive at position ~x1 of the string below is illegal ~
      because its variable evaluated to ~x2, which is not a symbol, a string, ~
      or a number.~|~%~x3")
    (bad-tilde-t-arg-natp
     "It is illegal to tab past the value of (@ fmt-hard-right-margin), ~x0, ~
      and hence the directive ~~t~s1 to tab to column ~x2 is illegal.  See ~
      :DOC set-fmt-hard-right-margin.")
    (bad-tilde-t-arg-not-natp
     "The tilde directive at location ~x0 in the fmt string below uses the ~
      variable ~x1.  That ~~t directive requires a natural number, but it was ~
      supplied the value ~x2.~|~%~x3")
    (bad-tilde-_-arg
     "The tilde-_ directive at position ~x0 of the string below is illegal ~
      because its variable evaluated to ~x1, which fails to be a natural ~
      number not exceeding ~x2.~|~%~x3")
    (find-alternative-skip
     "While looking for the terminating bracket of a tilde alternative ~
      directive in the string below we ran off the end of the string.~|~%~x0")
    (find-alternative-start
     "The tilde-# directive at ~x0 in the fmt string below must be followed ~
      immediately by ~~[.~|~%~x1")
    (find-alternative-start1-a
     "The tilde-# directive ~s0 at position ~x1 of the string below ~
      does not have enough alternative clauses.  When the terminal bracket ~
      was reached we still needed ~#2~[~/1 more alternative~/~x3 more ~
      alternatives~].~|~%~x4")
    (find-alternative-start1-b
     "While searching for the appropriate alternative clause of a tilde-# ~
      directive in the string below, we ran off the end of the string.~|~%~x0")
    (find-alternative-stop
     "While looking for the end of a tilde-# directive's alternative clause ~
      in the string below, we ran off the end of the string.~|~%~x0")
    (tilde-arg-points-past-string
     "The tilde directive at location ~x0 in the fmt string below requires ~
      that we look at the character ~x1 further down in the string.  But the ~
      string terminates at location ~x2.~|~%~x3")
    (unbound-tilde-arg
     "Unbound Fmt Variable.  The tilde directive at location ~x0 in the fmt ~
      string below uses the variable ~x1.  But this variable is not bound in ~
      the association list, ~x2, supplied with the fmt string.~|~%~x3")
    (unrecognized-tilde-arg
     "The tilde directive at position ~x0 of the string below is ~
      unrecognized.~|~%~x1")
    (otherwise
     (er hard 'illegal-fmt-string
         "Implementation error in illegal-fmt-string: unknown key, ~x0."
         key))))

(defmacro illegal-fmt-msg (key &rest args)
  (declare (xargs :guard (member-eq key *illegal-fmt-keys*)))

; The final newline separates the string from a "See :DOC set-iprint" message,
; which can be printed by fmt-abbrev1 if a value is elided during printing an
; error message.

  `(msg "Illegal Fmt Syntax.  ~@0"
        (msg ,(illegal-fmt-string key)

; If you want to be able to trace illegal-fmt-string, then change the preceding
; s-expression to (illegal-fmt-string ',key) and the redefine functions that
; call this macro.

             ,@args)))

(defun scan-past-whitespace (s i maximum)
  (declare (type #.*fixnat-type* i maximum)
           (type string s)
           (xargs :guard (<= maximum (length s))
                  :measure (nfix (- maximum i))
                  :ruler-extenders :all))
  (the-fixnat
   (cond ((not (mbt (and (integerp i) (integerp maximum))))
          maximum)
         ((< i maximum)
          (cond ((member (charf s i) '(#\Space #\Tab #\Newline))
                 (scan-past-whitespace s (+f i 1) maximum))
                (t i)))
         (t maximum))))

(defun zero-one-or-more (x)
  (declare (xargs :guard (or (integerp x)
                             (true-listp x))))
  (let ((n (cond ((integerp x) x)
                 (t (length x)))))
    (case n
          (0 0)
          (1 1)
          (otherwise 2))))

(defun find-alternative-skip (s i maximum quiet)

; This function finds the first position after a list of alternatives.  i is
; the value of find-alternative-stop, i.e., it points to the ~ in the ~/ or ~]
; that closed the alternative used.

; Suppose s is "~#7~[ab~/cd~/ef~]acl2".
;               01234567890123456789
; If i is 11, the answer is 17.

; Note that the returned position is positive in case of success.  In case of
; failure: this function logically returns 0, and if quiet is nil then it
; causes a hard error.

  (declare (type #.*fixnat-type* i maximum)
           (type string s)
           (xargs :guard (and (<= maximum (length s))
                              (<= i maximum))
                  :measure (nfix (- maximum i))
                  :ruler-extenders :lambdas))
  (the-fixnat
   (cond ((and (mbt (and (integerp i) (integerp maximum)))
               (< i (1-f maximum)))
          (let ((char-s-i (charf s i)))
            (declare (type character char-s-i))
            (case char-s-i
              (#\~
               (let ((i+2 (+f 2 i))
                     (char-s-1+i (charf s (1+f i))))
                 (declare (type character char-s-1+i)
                          (type #.*fixnat-type* i+2))
                 (case char-s-1+i
                   (#\] i+2)
                   (#\[ (let ((new-i
                               (find-alternative-skip s i+2 maximum quiet)))
                          (declare (type #.*fixnat-type* new-i))
                          (cond
                           ((and (not (= new-i 0))
                                 (mbt (and (integerp new-i)
                                           (< i new-i))))
                            (find-alternative-skip s new-i maximum quiet))
                           (t 0))))
                   (otherwise (find-alternative-skip s i+2 maximum quiet)))))
              (otherwise (find-alternative-skip s (+f 1 i) maximum quiet)))))
         (t (er-hard?-val?
             0 quiet 'find-alternative-skip
             "~@0"
             (illegal-fmt-msg find-alternative-skip s))))))

(defun find-alternative-start1 (x s i maximum quiet)

; This function recurs on x in support of find-alternative-start.  See the
; comment in find-alternative-start, in particular for a discussion of the
; error cases.

; Suppose s is "~#7~[ab~/cd~/ef~]acl2".  The indices into s are:
;               01234567890123456789
; This function is supposed to be called with i pointing to the character
; immediately following "~[", which is 5 in this example.

  (declare (type #.*fixnat-type* x i maximum)
           (type string s)
           (xargs :guard (and (<= maximum (length s))
                              (<= i maximum))
                  :measure (nfix (- maximum i))
                  :ruler-extenders :lambdas))
  (the-fixnat
   (cond ((= x 0) i)
         ((and (mbt (and (natp x)
                         (integerp i)
                         (integerp maximum)))
               (< i (1-f maximum)))
          (let ((char-s-i (charf s i)))
            (declare (type character char-s-i))
            (case char-s-i
              (#\~
               (let ((char-s-1+-i (charf s (1+f i))))
                 (declare (type character char-s-1+-i))
                 (case char-s-1+-i
                   (#\/ (find-alternative-start1
                         (1-f x) s (+f 2 i) maximum quiet))
                   (#\] (er-hard?-val?
                         0 quiet 'find-alternative-start1
                         "~@0"
                         (illegal-fmt-msg find-alternative-start1-a
                                          "terminating"
                                          i
                                          (zero-one-or-more x)
                                          x
                                          s)))
                   (#\[ (let ((k (find-alternative-skip s (+f 2 i) maximum
                                                        quiet)))
                          (declare (type #.*fixnat-type* k))
                          (cond
                           ((= k 0) ; error case
                            0)
                           (t (find-alternative-start1 x s k maximum quiet)))))
                   (otherwise
                    (find-alternative-start1 x s (+f 2 i) maximum quiet)))))
              (otherwise
               (find-alternative-start1 x s (+f 1 i) maximum quiet)))))
         (t (er-hard?-val?
             0 quiet 'find-alternative-start1
             "~@0"
             (illegal-fmt-msg find-alternative-start1-b s))))))

(defun fmt-char (s i j maximum err-flg)

; This function attempts to return the character of s at index (+ i j).  If
; that index is not less than maximum, an error occurs and the null character
; is logically returned.

  (declare (type #.*fixnat-type* i maximum)
           (type (integer 1 4) j)
           (type string s)
           (xargs :guard (and (<= maximum (length s)) ; typically, =
                              (< i maximum))))
  (the character
       (let ((index (+f! i j)))
         (declare (type #.*fixnat-type* index))
         (cond ((< index maximum)

; In spite of the guard, we do the inexpensive runtime check above since we may
; call fmt-char under a :program mode function, e.g., fmt.

                (charf s index))
               (t
                (prog2$ ; return an arbitrary character
                 (cond
                  (err-flg

; This calculation is a bit ugly.  We are making it in April, 2018, after many
; years of an error message for ~X01 (or ~P34, etc. -- any of ~X, ~Y, ~P, or
; ~Q) stating that the tilde directive starts at location n where n-1 should be
; reported -- in which case, we need to look j+1 = 3 further down the string
; from the tilde.

                   (mv-let (i j)
                     (if (or (= 0 i)
                             (eql (charf s i) #\~)
                             (not (eql (charf s (1-f i)) #\~))) ; never true?
                         (mv i j)
                       (mv (1-f i) (1+f j)))
                     (er hard? 'fmt-char
                         "~@0"
                         (illegal-fmt-msg
                          tilde-arg-points-past-string
                          i j maximum s))))
                  (t nil))
                 *null-char*))))))

(defun find-alternative-start (x s i maximum quiet)

; This function returns the position of the first character in the xth
; alternative, assuming i points to the ~ that begins the alternative
; directive.  If x is not an integer, we assume it is a non-empty list.  If its
; length is 1, pick the 0th alternative.  Otherwise, pick the 1st.  This means
; we can test on a list to get a "plural" test.

; Suppose s is "~#7~[ab~/cd~/ef~]acl2".  The indices into s are:
;               01234567890123456789
; This function is supposed to be called with i equal to the position of #\~ in
; "~#", which in this case is 0.  Suppose character #\7 is associated with 1.
; That's the value of x.  This function will return 9, the position of the
; beginning of alternative x.

; Note that the returned position is positive in case of success.  In case of
; failure: this function logically returns 0, and if quiet is nil then it
; causes a hard error.

; find-alternative-start1-a:
;             A "~]" was reached before there were enough alternatives, and j
;             is the position of that "~".

; find-alternative-start1-b
;             The indicated alternative was never reached.

; find-alternative-skip
;             A "~]" was not reached.

; find-alternative-start
;             The "~[" was missing after the initial "~#c".

; tilde-arg-points-past-string
;             The end of the string comes too soon to look.

  (declare (type #.*fixnat-type* i maximum)
           (type string s)
           (xargs :guard (<= maximum (length s))))
  (the-fixnat
   (cond
    ((not (< i (-f maximum 4)))
     (er-hard?-val?
      0 quiet 'find-alternative-start
      "~@0"
      (illegal-fmt-msg
       tilde-arg-points-past-string
       i 4 maximum s)))
    (t
     (let ((x (cond ((natp x) (the-fixnat! x 'find-alternative-start))
                    ((and (consp x)
                          (atom (cdr x)))
                     0)
                    (t 1))))
       (declare (type #.*fixnat-type* x))
       (cond ((not (and (eql (the character (fmt-char s i 3 maximum t)) #\~)
                        (eql (the character (fmt-char s i 4 maximum t)) #\[)))
              (er-hard?-val?
               0 quiet 'find-alternative-start
               "~@0"
               (illegal-fmt-msg find-alternative-start i s)))
             (t (find-alternative-start1 x s (+f i 5) maximum quiet))))))))

(defun find-alternative-stop (s i maximum quiet)

; This function finds the end of the alternative into which i is pointing.  i
; is usually the position of first character of the current alternative.  The
; answer points to the ~ in the ~/ or ~] closing the alternative.

; Suppose s is "~#7~[ab~/cd~/ef~]acl2".
;               01234567890123456789
; and i is 9.  Then the answer is 11.

; Note that the returned position is positive in case of success.  In case of
; failure: this function logically returns 0, and if quiet is nil then it
; causes a hard error.

  (declare (type #.*fixnat-type* i maximum)
           (type string s)
           (xargs :guard (and (<= maximum (length s))
                              (<= i maximum))
                  :measure (nfix (- (1+ maximum) i))
                  :ruler-extenders :lambdas))
  (the-fixnat
   (cond ((and (mbt (and (integerp i)
                         (integerp maximum)))
               (< i (1-f maximum)))
          (let ((char-s-i (charf s i)))
            (declare (type character char-s-i))
            (case char-s-i
              (#\~ (let ((char-s-1+i (charf s (1+f i))))
                     (declare (type character char-s-1+i))
                     (case char-s-1+i
                       (#\/ i)
                       (#\[ (let ((k (find-alternative-skip s (+f 2 i)
                                                            maximum quiet)))
                              (declare (type #.*fixnat-type* k))
                              (cond
                               ((= k 0) ; error case
                                k)
                               (t (find-alternative-stop s k maximum quiet)))))
                       (#\] i)
                       (otherwise (find-alternative-stop
                                   s (+f 2 i) maximum quiet)))))
              (otherwise (find-alternative-stop s (+f 1 i) maximum quiet)))))
         (t (er-hard?-val?
             0 quiet 'find-alternative-stop
             "~@0"
             (illegal-fmt-msg find-alternative-stop s))))))

(defun punctp (c)

; Warning: Keep this in sync with fmt0&v.

  (if (member c '(#\. #\, #\: #\; #\? #\! #\) #\]))
      c
    nil))

(defun fmt-tilde-s1 (s i maximum col channel state)
  (declare
   (type #.*fixnat-type* i maximum col)
   (type string s)
   (type symbol channel)
   (xargs :guard (and (fmt-state-p state)
                      (<= (the-fixnat maximum) (length s))
                      (open-output-channel-p channel :character state))
          :ruler-extenders :lambdas
          :measure (cond ((not (and (fmt-state-p state)
                                    (fixnat-guard i)
                                    (fixnat-guard maximum)
                                    (fixnat-guard col)
                                    (stringp s)
                                    (<= maximum (length s))
                                    (open-output-channel-p channel
                                                           :character
                                                           state)
                                    (< i maximum)))
                          0) ; irrelevant
                         ((and (> col (fmt-hard-right-margin state))
                               (not (write-for-read state)))
                          (+ 2 (nfix (* 2 (- maximum i)))))
                         (t (+ 1 (nfix (* 2 (- maximum i))))))))
  (the2s
   #.*fixnat-type*
   (cond
    ((not (mbt (and (fmt-state-p state)
                    (fixnat-guard i)
                    (fixnat-guard maximum)
                    (fixnat-guard col)
                    (stringp s)
                    (<= maximum (length s))
                    (open-output-channel-p channel :character state))))
     (mv (nfix col) state))
    ((not (< i maximum))
     (mv col state))
    ((and (> col (fmt-hard-right-margin state))
          (not (write-for-read state)))
     (pprogn
      (princ$ #\\ channel state)
      (newline channel state)
      (fmt-tilde-s1 s i maximum 0 channel state)))
    (t
     (let ((c (charf s i))
           (fmt-soft-right-margin (fmt-soft-right-margin state)))
       (declare (type character c)
                (type #.*small-nat-type* fmt-soft-right-margin))
       (cond ((and (> col fmt-soft-right-margin)
                   (eql c #\Space))
              (pprogn
               (newline channel state)
               (fmt-tilde-s1 s
                             (the-fixnat
                              (scan-past-whitespace s (+f i 1) maximum))
                             maximum 0 channel state)))
             ((and (> col fmt-soft-right-margin)
                   (or (eql c #\-)
                       (eql c #\_))
                   (not (= (1+f i) maximum)))

; If we are beyond the soft right margin and we are about to print a
; hyphen or underscore and it is not the last character in the string,
; then print it and do a terpri.  If it is the last character, as it
; is in say, the function name "1-", then we don't do the terpri and
; hope there is a better place to break soon.  The motivating example
; for this was in seeing a list of function names get printed in a way
; that produced a comma as the first character of the newline, e.g.,
; "... EQL, 1+, 1-
; , ZEROP and PLUSP."

              (pprogn
               (princ$ c channel state)
               (if (eql c #\-) state (princ$ #\- channel state))
               (newline channel state)
               (fmt-tilde-s1 s
                             (the-fixnat
                              (scan-past-whitespace s (+f i 1) maximum))
                             maximum 0 channel state)))
             (t
              (pprogn
               (princ$ c channel state)
               (fmt-tilde-s1 s (1+f i) maximum
                             (cond
                              ((eql c #\Newline) 0)
                              ((= col (fixnum-bound))
                               (fixnum-bound))
                              (t (1+f col)))
                             channel state)))))))))

(defun fmt-tilde-cap-s1 (s i maximum col channel state)
  (declare
   (type #.*fixnat-type* i col maximum)
   (type string s)
   (type symbol channel)
   (xargs :guard
          (and (fmt-state-p state)
               (<= (the-fixnat maximum) (length s))
               (open-output-channel-p channel :character state))
          :ruler-extenders
          :lambdas
          :measure
          (cond ((not (and (fmt-state-p state)
                           (fixnat-guard i)
                           (fixnat-guard maximum)
                           (fixnat-guard col)
                           (stringp s)
                           (<= maximum (length s))
                           (open-output-channel-p channel :character state)
                           (< i maximum)))
                 0) ; irrelevant
                (t (nfix (- maximum i))))))
  (the2s
   #.*fixnat-type*
   (cond ((not (mbt (and (fmt-state-p state)
                         (fixnat-guard i)
                         (fixnat-guard maximum)
                         (fixnat-guard col)
                         (stringp s)
                         (<= maximum (length s))
                         (open-output-channel-p channel :character state))))
          (mv 0 state))
         ((not (< i maximum))
          (mv col state))
         (t
          (let ((c (charf s i)))
            (declare (type character c))
            (pprogn
             (princ$ c channel state)
             (fmt-tilde-cap-s1 s (1+f i) maximum
                               (cond ((eql c #\Newline) 0)
                                     ((= col (fixnum-bound)) col)
                                     (t (1+f col)))
                               channel state)))))))

(defun fmt-var (s alist i maximum)

; We return the value associated in alist with the character at position i+2 of
; s.  We assume that there is a tilde character at position i or (less
; frequently) i-1.  An error occurs (from fmt-var) if i+2 is not less than
; maximum.

; There is a call of assoc below that appears both in the guard and in the
; body.  This is not normally inefficient, since normally the guard will not be
; evaluated when under a call of a function whose symbol-class is :program or
; :common-lisp-compliant.  We want this assoc call in the guard in order to
; have confidence that we won't encounter the hard error below (rather than the
; alternative, which is to omit the assoc call from the guard and use (er hard?
; ...) instead of (er hard ...)).

  (declare (type #.*fixnat-type* i maximum)
           (type string s)
           (xargs :guard (and (<= maximum (length s)) ; typically, =
                              (< i maximum)
                              (character-alistp alist))))
  (let* ((c (the character (fmt-char s i 2 maximum t)))
         (x (assoc c alist)))
    (declare (type character c))
    (cond (x (cdr x))
          (t (let ((tilde-position

; This calculation is a bit ugly.  We are making it in April, 2018, after many
; years of an error message for ~X01 (or ~P34, etc. -- any of ~X, ~Y, ~P, or
; ~Q) stating that the tilde directive starts at location n where n-1 should be
; reported.

                    (if (eql (charf s i) #\~)
                        i
                      (1-f i))))
               (er hard? 'fmt-var
                   "~@0"
                   (illegal-fmt-msg unbound-tilde-arg tilde-position c alist
                                    s)))))))

(defun splat-atom (x print-base print-radix indent col channel state)

; See also splat-atom!, which ignores margins.

  (declare (type (unsigned-byte 5) print-base)
           (type #.*fixnat-type* indent col)
           (type symbol channel)
           (xargs :guard
                  (and (atom x)
                       (print-base-p print-base)
                       (fmt-state-p state)
                       (open-output-channel-p channel :character state))))
  (the2s
   #.*fixnat-type*
   (let* ((sz (flsz-atom x print-base print-radix 0 state))
          (too-bigp (> (+f! col sz)
                       (fmt-hard-right-margin state))))
     (pprogn (if too-bigp
                 (pprogn (newline channel state)
                         (spaces indent 0 channel state))
               state)
             (prin1$ x channel state)
             (mv (if too-bigp (+f! indent sz) (+f! col sz))
                 state)))))

(defun splat-atom! (x print-base print-radix col channel state)

; See also splat-atom, which takes account of margins by possibly printing
; newlines.

  (declare (type (unsigned-byte 5) print-base)
           (type #.*fixnat-type* col)
           (type symbol channel)
           (xargs :guard (and (atom x)
                              (print-base-p print-base)
                              (open-output-channel-p channel :character
                                                     state))))
  (the2s
   #.*fixnat-type*
   (pprogn (prin1$ x channel state)
           (mv (flsz-atom x print-base print-radix col state)
               state))))

(defun splat-string (x indent col channel state)

; This variant of splat-atom prints the string x flat, without the quotes.

  (declare (type string x)
           (type #.*fixnat-type* indent col)
           (type symbol channel)
           (xargs :guard (and (open-output-channel-p channel :character
                                                     state)
                              (fmt-state-p state))))
  (the2s
   #.*fixnat-type*
   (let* ((sz (min (fixnum-bound) (length x)))
          (too-bigp (> (+f! col sz)
                       (fmt-hard-right-margin state))))
     (declare (type #.*fixnat-type* sz))
     (pprogn (if too-bigp
                 (pprogn (newline channel state)
                         (spaces indent 0 channel state))
               state)
             (princ$ x channel state)
             (mv (if too-bigp (+f! indent sz) (+f! col sz))
                 state)))))

; Splat, below, prints out an arbitrary ACL2 object flat, introducing
; the single-gritch notation for quote and breaking lines between lexemes
; to avoid going over the hard right margin.  It indents all but the first
; line by indent spaces.

(mutual-recursion

(defun splat (x print-base print-radix indent eviscp col channel state)
  (declare (type (unsigned-byte 5) print-base)
           (type #.*fixnat-type* indent col)
           (type symbol channel)
           (xargs :guard
                  (and (print-base-p print-base)
                       (fmt-state-p state)
                       (open-output-channel-p channel :character state))
                  :ruler-extenders :lambdas
                  :measure (1+ (* 2 (acl2-count x)))))
  (the2s
   #.*fixnat-type*
   (cond ((atom x)
          (splat-atom x print-base print-radix indent col channel state))
         ((and (evisceratedp eviscp x)

; We know (cdr x) is a string, but we need the following for guard
; verification.  That's OK; it's cheap.

               (stringp (cdr x)))
          (splat-string (cdr x) indent col channel state))
         ((and (eq (car x) 'quote)
               (consp (cdr x))
               (null (cddr x)))
          (pprogn (princ$ #\' channel state)
                  (splat (cadr x) print-base print-radix indent eviscp
                         (+f! 1 col) channel state)))
         (t (pprogn (princ$ #\( channel state)
                    (splat1 x print-base print-radix indent eviscp (+f! 1 col)
                            channel state))))))

(defun splat1 (x print-base print-radix indent eviscp col channel state)
  (declare (type cons x)
           (type (unsigned-byte 5) print-base)
           (type #.*fixnat-type* indent col)
           (type symbol channel)
           (xargs :guard
                  (and (print-base-p print-base)
                       (fmt-state-p state)
                       (open-output-channel-p channel :character state))
                  :ruler-extenders :lambdas
                  :measure (* 2 (acl2-count x))))
  (the2s
   #.*fixnat-type*
   (cond
    ((mbt (consp x)) ; for termination
     (mv-let (col state)
       (splat (car x) print-base print-radix indent eviscp col channel state)
       (cond ((null (cdr x))
              (pprogn (princ$ #\) channel state)
                      (mv (+f! 1 col) state)))
             ((atom (cdr x))
              (cond ((> (+f! 3 col)
                        (fmt-hard-right-margin state))
                     (pprogn (newline channel state)
                             (spaces indent 0 channel state)
                             (princ$ ". " channel state)
                             (mv-let (col state)
                               (splat (cdr x)
                                      print-base print-radix indent
                                      eviscp
                                      (+f! indent 2)
                                      channel state)
                               (pprogn (princ$ #\) channel state)
                                       (mv (+f! 1 col) state)))))
                    (t (pprogn
                        (princ$ " . " channel state)
                        (mv-let (col state)
                          (splat (cdr x)
                                 print-base print-radix indent eviscp
                                 (+f! 3 col)
                                 channel state)
                          (pprogn (princ$ #\) channel state)
                                  (mv (+f! 1 col) state)))))))
             (t (pprogn
                 (princ$ #\Space channel state)
                 (splat1 (cdr x) print-base print-radix indent eviscp
                         (+f! 1 col) channel state))))))
    (t ; impossible case
     (mv 0 state)))))

)

(defun number-of-digits (n print-base print-radix)

; We compute the width of the field necessary to express the integer n
; in the given print-base.  We assume minus signs are printed but plus
; signs are not.  Thus, if n is -123 we return 4, if n is 123 we
; return 3.

  (declare (type (unsigned-byte 5) print-base)
           (type integer n)
           (xargs :guard (print-base-p print-base)
                  :measure (cond ((not (and (integerp n)
                                            (print-base-p print-base)))
                                  0)
                                 ((< n 0)
                                  (1+ (- n)))
                                 (t n))
                  :ruler-extenders :lambdas))
  (the-fixnat
   (cond ((not (mbt (and (integerp n)
                         (print-base-p print-base)))) ; impossible
          0)
         ((< n 0) (+f! 1 (number-of-digits (abs n) print-base print-radix)))
         ((< n print-base)
          (cond ((null print-radix)
                 1)
                ((= print-base 10) ; `.' suffix
                 2)
                (t ; #b, #o, or #x prefix
                 3)))
         (t (+f! 1 (number-of-digits (floor n print-base) print-base
                                     print-radix))))))

(defun left-pad-with-blanks (n width col channel state)

; Print the integer n right-justified in a field of width width.
; We return the final column (assuming we started in col) and state.

  (declare (type integer n)
           (type (integer 0 *) width)
           (type #.*fixnat-type* col)
           (type symbol channel)
           (xargs :guard
                  (and (open-output-channel-p channel :character state)
                       (fmt-state-p state))))
  (the2s
   #.*fixnat-type*
   (cond
    ((> width (fixnum-bound))
     (prog2$ (er hard? 'left-pad-with-blanks
                 "It is illegal to supply a padding width of greater than ~x0."
                 (fixnum-bound))
             (mv (fixnum-bound) state)))
    (t
     (let ((d (number-of-digits n (print-base) (print-radix))))
       (declare (type #.*fixnat-type* d))
       (cond ((>= d width)
              (pprogn (prin1$ n channel state)
                      (mv (+f! col d) state)))
             (t (pprogn
                 (spaces (-f (the-fixnat width) d) col channel state)
                 (prin1$ n channel state)
                 (mv (+f! col width) state)))))))))

(defmacro maybe-newline (body)

; This macro is used in fmt0 to force a newline only when absolutely
; necessary.  It knows the locals of fmt0, in particular, col,
; channel, and state.  We wrap this macro around code that is about to
; print a character at col.  Once upon a time we just started fmt0
; with a newline if we were past the hard right margin, but that
; produced occasional lines that ended naturally at the hard right
; margin and then had a backslash inserted in anticipation of the 0
; characters to follow.  It was impossible to tell if more characters
; follow because there may be tilde commands between where you are and
; the end of the line, and they may or may not print things.

  `(mv-letc (col state)
            (cond
             ((and (> col (fmt-hard-right-margin state))
                   (not (write-for-read state)))
              (pprogn (princ$ #\\ channel state)
                      (newline channel state)
                      (mv 0 state)))
             (t (mv col state)))
            ,body))

; To support the convention that er, fmt, and even individual fmt
; commands such as ~X can control their own evisceration parameters,
; we now introduce the idea of an evisceration tuple, or evisc-tuple.

(defun evisc-tuple (print-level print-length alist hiding-cars)

; See :doc set-evisc-tuple for a lot of information about evisc-tuples.  Also
; see the Essay on Iprinting for a related topic.

; This is really just a record constructor, but we haven't got defrec
; yet so we do it by hand.  See set-evisc-tuple.

; We sometimes write out constant evisc tuples!  However they are commented
; nearby with (evisc-tuple ...).

; The primitive consumers of evisc tuples all call eviscerate-top or
; eviscerate-stobjs-top.

;         car   cadr        caddr        cadddr

  (list alist   print-level print-length hiding-cars))

(defun world-evisceration-alist (state alist)
  (declare (xargs :stobjs state))
  (let ((wrld (w state)))
    (cond ((null wrld) ; loading during the build
           alist)
          (t (cons (cons wrld *evisceration-world-mark*)
                   alist)))))

(defun abbrev-evisc-tuple (state)

; As of January 2009 the abbrev-evisc-tuple is used in error, warning$,
; observation, pstack, break-on-error, and miscellany such as running commands
; where little output is desired, say for :ubt or rebuild.  We don't put this
; complete of a specification into the documentation, however, in case later we
; tweak the set of uses of the abbrev-evisc-tuple.  This comment should
; similarly not be viewed as definitive if it is long after January 2009.

  (declare (xargs :guard t))
  (let ((evisc-tuple (f-get-global 'abbrev-evisc-tuple state)))
    (cond
     ((eq evisc-tuple :default)
      (cons (world-evisceration-alist state nil)
            '(5 7 nil)))
     (t evisc-tuple))))

(defmacro gag-mode ()
  '(f-get-global 'gag-mode state))

(defun term-evisc-tuple (flg state)

; This evisceration tuple is used when we are printing terms or lists of terms.
; If state global 'term-evisc-tuple has value other than :default, then we
; return that value.  Otherwise:

; We don't hide the world or state because they aren't (usually) found in
; terms.  This saves us a little time.  If the global value of
; 'eviscerate-hide-terms is t, we print (HIDE ...) as <hidden>.  Otherwise not.
; Flg controls whether we actually eviscerate on the basis of structural depth
; and length.  If flg is t we do.  The choice of the print-length 4 is
; motivated by the idea of being able to print IF as (IF # # #) rather than (IF
; # # ...).  Print-level 3 lets us print a clause as ((NOT (PRIMEP #)) ...)
; rather than ((NOT #) ...).

  (let ((evisc-tuple (f-get-global 'term-evisc-tuple state)))
    (cond ((not (eq evisc-tuple :default))
           evisc-tuple)
          ((f-get-global 'eviscerate-hide-terms state)
           (cond (flg
;;; (evisc-tuple 3 4 nil '(hide))
                  '(nil 3 4 (hide)))
                 (t
;;; (evisc-tuple nil nil nil '(hide))
                  '(nil nil nil (hide)))))
          (flg ;;; (evisc-tuple 3 4 nil nil)
           '(nil 3 4 nil))
          (t nil))))

(defun gag-mode-evisc-tuple (state)
  (cond ((gag-mode)
         (let ((val (f-get-global 'gag-mode-evisc-tuple state)))
           (if (eq val :DEFAULT)
               nil
             val)))
        (t (term-evisc-tuple nil state))))

(defun ld-evisc-tuple (state)
  (let ((evisc-tuple (f-get-global 'ld-evisc-tuple state)))
    (assert$ (not (eq evisc-tuple :default)) ; only abbrev, term evisc-tuples
             evisc-tuple)))

(defun brr-evisc-tuple (state)

; It would be nice if we could call (brr-evisc-tuple-oracle-update state) here
; to make sure that 'brr-evisc-tuple has the latest value set by
; set-site-evisc-tuple.  The only reason it wouldn't is the unwind protection
; cleanup in wormhole1.  But we can't change state in this function.  On the
; other hand, ld-read-command calls the oracle updater before every command is
; read.

  (let ((val (f-get-global 'brr-evisc-tuple state)))
    (cond
     ((eq val :default)
      (term-evisc-tuple t state))
     (t val))))

(defun fmt-ppr (x width rpc col channel state eviscp)
  (declare (type #.*fixnat-type* width rpc col)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (open-output-channel-p channel :character
                                                     state))))
  (ppr2 (ppr1 x (print-base) (print-radix)
              (round-to-small t width)
              (round-to-small t rpc)
              state eviscp)
        (round-to-small t col)
        channel state eviscp))

(defun scan-past-empty-fmt-directives1 (s alist i maximum clk)

; We return a natural number j with i <= j < maximum, such that fmt printing of
; the characters of s from i through j-1, with respect to alist, produces no
; output.  It is thus always sound to return i, but we aim to do better than
; that when feasible.

  (declare (type #.*fixnat-type* i maximum clk)
           (type string s)
           (xargs :ruler-extenders :lambdas
                  :verify-guards nil
                  :guard (and (<= maximum (length s)) ; typically, =
                              (character-alistp alist))))
  (the-fixnat
   (cond
    ((or (not (mbt (and (natp i)
                        (natp maximum)
                        (<= maximum (length s))
                        (<= maximum (fixnum-bound)))))
         (>= i maximum)
         (zp clk))
     (min (fixnum-bound)
          (nfix i)))
    (t (let ((c (charf s i)))
         (declare (type character c))
         (cond
          ((eql c #\~)
           (let ((fmc (the character (fmt-char s i 1 maximum t))))
             (declare (type character fmc))
             (case
               fmc
               ((#\s #\S)
                (cond
                 ((equal (fmt-var s alist i maximum) "")
                  (scan-past-empty-fmt-directives1 s alist (+f! i 3) maximum
                                                  (1-f clk)))
                 (t i)))
               (#\@
                (let ((val (fmt-var s alist i maximum)))
                  (cond
                   ((not (msgp val))
                    (er-hard?-val?
                     i nil 'scan-past-empty-fmt-directives1
                     "~@0"
                     (illegal-fmt-msg bad-tilde-@-arg
                                      i val 'msgp s)))
                   ((equal val "")
                    (scan-past-empty-fmt-directives1 s alist (+f! i 3) maximum
                                                     (1-f clk)))
                   ((stringp val) i)
                   ((equal (car val) "")
                    (scan-past-empty-fmt-directives1 s alist (+f! i 3) maximum
                                                     (1-f clk)))
                   (t (let ((len (length (car val)))
                            (alist1 (append (cdr val) alist)))
                        (if (and (<= len (fixnum-bound)) ; for guard
                                 (equal (scan-past-empty-fmt-directives1
                                         (car val) alist1 0 len (1-f clk))
                                        len))
                            (scan-past-empty-fmt-directives1 s alist (+f! i 3)
                                                             maximum
                                                             (1-f clk))
                          i))))))
               (#\#
                (let* ((n (find-alternative-start
                           (fmt-var s alist i maximum) s i maximum nil))
                       (m (if (= n 0)
                              0
                            (find-alternative-stop s n maximum nil)))
                       (o (if (= m 0)
                              0
                            (find-alternative-skip s m maximum nil))))
                  (declare (type #.*fixnat-type* n)
                           (type #.*fixnat-type* m o))
                  (cond
                   ((= o 0) ; error case; can't reach here
                    0)
                   ((or (= n m) ; optimization
                        (= (scan-past-empty-fmt-directives1 s alist n m
                                                            (1-f clk))
                           m))
                    (scan-past-empty-fmt-directives1 s alist o maximum
                                                    (1-f clk)))
                   (t i))))
               (otherwise i))))
          (t i)))))))

(defun scan-past-empty-fmt-directives (s alist i maximum)
  (declare (type #.*fixnat-type* i maximum)
           (type string s)
           (xargs :guard (and (<= maximum (length s)) ; typically, =
                              (character-alistp alist))))
  (scan-past-empty-fmt-directives1 s alist i maximum (fixnum-bound)))

(defun-inline min-fixnat (x y)
  (declare (type #.*fixnat-type* x y))
  (the #.*fixnat-type* (if (< x y) x y)))

(defun out-of-time-the2s (fn state)
  (declare (xargs :stobjs state))
  (the2s
   #.*fixnat-type*
   (prog2$ (er hard? fn
               "Clock ran out in ~x0!"
               fn)
           (mv 0 state))))

(defun char? (s i)
  (declare (xargs :guard (and (stringp s)
                              (natp i))))
  (the character
       (if (and (mbt (natp i))
                (< i (length s)))
           (char s i)
         (prog2$ (er hard? 'char?
                     "Unexpected out of bounds index ~x0 for string ~s1!"
                     i s)
                 *null-char*))))

(mutual-recursion

(defun fmt0* (str0 str1 str2 str3 lst alist col channel state evisc-tuple clk)

; This odd function prints out the members of lst.  If the list has no
; elements, str0 is used.  If the list has 1 element, str1 is used
; with #\* bound to the element.  If the list has two elements, str2
; is used with #\* bound to the first element and then str1 is used
; with #\* bound to the second.  If the list has more than two
; elements, str3 is used with #\* bound successively to each element
; until there are only two left.  The function is used in the
; implementation of ~&, ~v, and ~*.

  (declare (type #.*fixnat-type* col clk)
           (type string str0 str1 str2 str3)
           (type symbol channel)
           (xargs :guard (and (fixnat-guard (length str0))
                              (fixnat-guard (length str1))
                              (fixnat-guard (length str2))
                              (fixnat-guard (length str3))
                              (true-listp lst)
                              (character-alistp alist)
                              (fmt-state-p state)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))
                  :measure (nfix clk)
                  :ruler-extenders :lambdas
                  :verify-guards nil))
  (the2s
   #.*fixnat-type*
   (cond ((zp clk)
          (out-of-time-the2s 'fmt0* state))
         ((not (mbt (fixnat-guard col)))
          (mv 0 state))
         ((endp lst)
          (fmt0 str0 alist 0 (length str0) col nil channel
                state evisc-tuple (1-f clk)))
         ((null (cdr lst))
          (fmt0 str1
                (cons (cons #\* (car lst)) alist)
                0 (length str1) col nil channel
                state evisc-tuple (1-f clk)))
         ((null (cddr lst))
          (mv-letc (col state)
                   (fmt0 str2
                         (cons (cons #\* (car lst)) alist)
                         0 (length str2)
                         col nil channel state evisc-tuple (1-f clk))
                   (fmt0* str0 str1 str2 str3 (cdr lst) alist col channel
                          state evisc-tuple (1-f clk))))
         (t (mv-letc (col state)
                     (fmt0 str3
                           (cons (cons #\* (car lst)) alist)
                           0 (length str3)
                           col nil channel state evisc-tuple (1-f clk))
                     (fmt0* str0 str1 str2 str3 (cdr lst) alist col channel
                            state evisc-tuple (1-f clk)))))))

(defun fmt0&v (flg lst punct col channel state evisc-tuple clk)
  (declare (type #.*fixnat-type* col clk)
           (type symbol channel)
           (xargs :guard (and (true-listp lst)
                              (fmt-state-p state)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))
                  :measure (nfix clk)
                  :ruler-extenders :lambdas))
  (the2s
   #.*fixnat-type*
   (cond
    ((zp clk)
     (out-of-time-the2s 'fmt0&v state))
    ((not (mbt (fixnat-guard col)))
     (mv 0 state))
    (t
     (case flg
       (&
        (case
          punct
          (#\. (fmt0* "" "~x*." "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\, (fmt0* "" "~x*," "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\: (fmt0* "" "~x*:" "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\; (fmt0* "" "~x*;" "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\? (fmt0* "" "~x*?" "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\! (fmt0* "" "~x*!" "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\) (fmt0* "" "~x*)" "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\] (fmt0* "" "~x*]" "~x* and " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          ((nil)
           (fmt0* "" "~x*" "~x* and " "~x*, " lst nil col channel
                  state evisc-tuple (1-f clk)))
          (otherwise
           (prog2$ (er hard? 'fmt0&v
                       "Implementation error: Missing punctp case, ~x0"
                       punct)
                   (mv 0 state)))))
       (otherwise
        (case
          punct
          (#\. (fmt0* "" "~x*." "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\, (fmt0* "" "~x*," "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\: (fmt0* "" "~x*:" "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\; (fmt0* "" "~x*;" "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\? (fmt0* "" "~x*?" "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\! (fmt0* "" "~x*!" "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\) (fmt0* "" "~x*)" "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          (#\] (fmt0* "" "~x*]" "~x* or " "~x*, " lst nil col channel
                      state evisc-tuple (1-f clk)))
          ((nil)
           (fmt0* "" "~x*" "~x* or " "~x*, " lst nil col channel
                  state evisc-tuple (1-f clk)))
          (otherwise
           (prog2$ (er hard? 'fmt0&v
                       "Implementation error: Missing punctp case, ~x0"
                       punct)
                   (mv 0 state))))))))))

(defun spell-number (n cap col channel state evisc-tuple clk)

; If n is an integerp we spell out the name of the cardinal number n
; (for a few cases) or else we just print the decimal representation
; of n.  E.g., n=4 makes us spell "four".  If n is a consp then we
; assume its car is an integer and we spell the corresponding ordinal
; number, e.g., n= '(4 . th) makes us spell "fourth".  We capitalize
; the word if cap is t.

  (declare (type #.*fixnat-type* col clk)
           (type symbol channel)
           (xargs :guard (and (or (integerp n)
                                  (and (consp n)
                                       (integerp (car n))))
                              (fmt-state-p state)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))
                  :measure (nfix clk)
                  :ruler-extenders :lambdas))
  (the2s
   #.*fixnat-type*
   (cond
    ((zp clk)
     (out-of-time-the2s 'spell-number state))
    ((not (mbt (fixnat-guard col)))
     (mv 0 state))
    (t
     (let ((str
            (cond ((integerp n)
                   (cond ((int= n 0) (if cap "Zero" "zero"))
                         ((int= n 1) (if cap "One" "one"))
                         ((int= n 2) (if cap "Two" "two"))
                         ((int= n 3) (if cap "Three" "three"))
                         ((int= n 4) (if cap "Four" "four"))
                         ((int= n 5) (if cap "Five" "five"))
                         ((int= n 6) (if cap "Six" "six"))
                         ((int= n 7) (if cap "Seven" "seven"))
                         ((int= n 8) (if cap "Eight" "eight"))
                         ((int= n 9) (if cap "Nine" "nine"))
                         ((int= n 10) (if cap "Ten" "ten"))
                         ((int= n 11) (if cap "Eleven" "eleven"))
                         ((int= n 12) (if cap "Twelve" "twelve"))
                         ((int= n 13) (if cap "Thirteen" "thirteen"))
                         (t "~x0")))
                  ((and (consp n)
                        (<= 0 (car n))
                        (<= (car n) 13))
                   (cond ((int= (car n) 0) (if cap "Zeroth" "zeroth"))
                         ((int= (car n) 1) (if cap "First" "first"))
                         ((int= (car n) 2) (if cap "Second" "second"))
                         ((int= (car n) 3) (if cap "Third" "third"))
                         ((int= (car n) 4) (if cap "Fourth" "fourth"))
                         ((int= (car n) 5) (if cap "Fifth" "fifth"))
                         ((int= (car n) 6) (if cap "Sixth" "sixth"))
                         ((int= (car n) 7) (if cap "Seventh" "seventh"))
                         ((int= (car n) 8) (if cap "Eighth" "eighth"))
                         ((int= (car n) 9) (if cap "Ninth" "ninth"))
                         ((int= (car n) 10) (if cap "Tenth" "tenth"))
                         ((int= (car n) 11) (if cap "Eleventh" "eleventh"))
                         ((int= (car n) 12) (if cap "Twelfth" "twelfth"))
                         (t (if cap "Thirteenth" "thirteenth"))))
                  (t (let ((d (mod (abs (car n)) 10)))

; We print -11th, -12th, -13th, ... -20th, -21st, -22nd, etc., though
; what business anyone has using negative ordinals I can't imagine.

                       (cond ((or (int= d 0)
                                  (> d 3)
                                  (int= (car n) -11)
                                  (int= (car n) -12)
                                  (int= (car n) -13))
                              "~x0th")
                             ((int= d 1) "~x0st")
                             ((int= d 2) "~x0nd")
                             (t "~x0rd")))))))
       (declare (type string str))
       (fmt0 (the-string! str 'spell-number)
             (cond ((integerp n)
                    (cond ((and (<= 0 n) (<= n 13)) nil)
                          (t (list (cons #\0 n)))))
                   (t (cond ((and (<= 0 (car n)) (<= (car n) 13)) nil)
                            (t (list (cons #\0 (car n)))))))
             0 (the-fixnat! (length str) 'spell-number)
             col nil channel state evisc-tuple (1-f clk)))))))

(defun fmt-tilde-s (s col channel state clk)

; If s is a symbol or a string, we print it out, breaking on hyphens but not
; being fooled by fmt directives inside it.  We also allow s to be a number
; (not sure why this was ever allowed, but we continue to support it).  We
; return the new col and state.

  (declare (type #.*fixnat-type* col clk)
           (type symbol channel)
           (xargs :guard (and (or (symbolp s)
                                  (stringp s)
                                  (acl2-numberp s))
                              (fmt-state-p state)
                              (open-output-channel-p channel :character state))
                  :measure (nfix clk)
                  :ruler-extenders :lambdas))
  (the2s
   #.*fixnat-type*
   (cond
    ((zp clk)
     (out-of-time-the2s 'fmt-tilde-s state))
    ((not (mbt (fixnat-guard col)))
     (mv 0 state))
    ((acl2-numberp s)
     (pprogn (prin1$ s channel state)
             (mv (flsz-atom s (print-base) (print-radix) col state) state)))
    ((stringp s)
     (fmt-tilde-s1 s 0 (the-fixnat! (length s) 'fmt-tilde-s) col
                   channel state))
    (t
     (let ((str (symbol-name s)))
       (cond
        ((keywordp s)
         (cond
          ((needs-slashes str state)
           (splat-atom s (print-base) (print-radix) 0 col channel state))
          (t (fmt0 ":~s0" (list (cons #\0 str)) 0 4 col nil channel state nil
                   (1-f clk)))))
        ((symbol-in-current-package-p s state)
         (cond
          ((needs-slashes str state)
           (splat-atom s (print-base) (print-radix) 0 col channel state))
          (t (fmt-tilde-s1 str 0
                           (the-fixnat! (length str) 'fmt-tilde-s)
                           col channel state))))
        (t
         (let ((p (symbol-package-name s)))
           (cond
            ((or (needs-slashes p state)
                 (needs-slashes str state))
             (splat-atom s (print-base) (print-radix) 0 col channel state))
            (t (fmt0 "~s0::~-~s1"
                     (list (cons #\0 p)
                           (cons #\1 str))
                     0 10 col nil channel state nil (1-f clk))))))))))))

(defun fmt-tilde-cap-s (s col channel state clk)

; This variant of fmt-tilde-s avoids printing newlines during the printing of
; s.

  (declare (type #.*fixnat-type* col clk)
           (type symbol channel)
           (xargs :guard (and (or (symbolp s)
                                  (stringp s)
                                  (acl2-numberp s))
                              (fmt-state-p state)
                              (open-output-channel-p channel :character state))
                  :measure (nfix clk)
                  :ruler-extenders :lambdas))
  (the2s
   #.*fixnat-type*
   (cond
    ((zp clk)
     (out-of-time-the2s 'fmt-tilde-cap-s state))
    ((not (mbt (fixnat-guard col)))
     (mv 0 state))
    ((acl2-numberp s)
     (splat-atom! s (print-base) (print-radix) col channel state))
    ((stringp s)
     (fmt-tilde-cap-s1 s 0 (the-fixnat! (length s) 'fmt-tilde-s) col
                       channel state))
    (t
     (let ((str (symbol-name s)))
       (cond
        ((keywordp s)
         (cond
          ((needs-slashes str state)
           (splat-atom! s (print-base) (print-radix) col channel state))
          (t (fmt0 ":~S0" (list (cons #\0 str)) 0 4 col nil channel state nil
                   (1-f clk)))))
        ((symbol-in-current-package-p s state)
         (cond
          ((needs-slashes str state)
           (splat-atom! s (print-base) (print-radix) col channel state))
          (t (fmt-tilde-cap-s1 str 0
                               (the-fixnat! (length str) 'fmt-tilde-s)
                               col channel state))))
        (t
         (let ((p (symbol-package-name s)))
           (cond
            ((or (needs-slashes p state)
                 (needs-slashes str state))
             (splat-atom! s (print-base) (print-radix) col channel state))
            (t (fmt0 "~S0::~S1"
                     (list (cons #\0 p)
                           (cons #\1 str))
                     0 8 col nil channel state nil (1-f clk))))))))))))

(defun fmt0 (s alist i maximum col pn channel state evisc-tuple clk)

; Note: This has functionality related to fmx-cw-msg-1-body, so if you change
; one of those, consider changing the other and consider changing each :DOC
; topic.

; Pn is either nil or else punctuation to print when we reach the end of s,
; presumably not in column 0.

  (declare (type #.*fixnat-type* i maximum col clk)
           (type atom pn)
           (type string s)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (<= (the-fixnat maximum) (length s))
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))
                  :measure (nfix clk)
                  :ruler-extenders :lambdas))
  (the2s
   #.*fixnat-type*
   (cond
    ((zp clk)
     (out-of-time-the2s 'fmt0 state))
    ((not (mbt (fixnat-guard col)))
     (mv 0 state))
    ((>= i maximum)
     (cond (pn (pprogn (princ$ pn channel state)
                       (mv (+f! 1 col) state)))
           (t (mv col state))))
    (t
     (let ((c (charf s i)))
       (declare (type character c))
       (cond
        ((eql c #\~)
         (let ((fmc (fmt-char s i 1 maximum t)))
           (declare (type character fmc))
           (case
             fmc
             ((#\p #\q #\P #\Q #\x #\y #\X #\Y)

; The only difference between pqPQ and xyXY has been that the former could
; cause infix printing when that was supported.  (But see the comment below
; about "hyphenate" for how we can cause the latter to enable hyphenation.)

; The difference between the lowercase directives and the uppercase ones is
; that the uppercase ones take two fmt-vars, e.g., ~X01, and use the contents
; of the second one as the evisceration value.  Otherwise the uppercase
; directives behave as their lowercase counterparts.

; On symbols, ~x and ~y are alike and just print starting in col.  On non-
; symbols they both prettyprint.  But ~y starts printing in col while ~x may do
; a terpri and indent first.  ~x concludes with a terpri if it put out a terpri
; before printing.  ~y always concludes with a terpri, so you know where you
; end up.

              (maybe-newline
               (let* ((caps (or (eql fmc #\P) (eql fmc #\Q)
                                (eql fmc #\X) (eql fmc #\Y)))
                      (px (or (eql fmc #\p) (eql fmc #\P)
                              (eql fmc #\x) (eql fmc #\X)))
                      (qy (not px))
                      (local-evisc-tuple
                       (cond (caps
                              (let ((x (fmt-var s alist (1+f i) maximum)))
                                (cond
                                 ((not (standard-evisc-tuplep x))
                                  (er-hard?-val?
                                   nil nil 'fmt0
                                   "~@0"
                                   (illegal-fmt-msg
                                    bad-evisc-tuple
                                    i
                                    (char? s (+f! i 3))
                                    x 'standard-evisc-tuplep s)))
                                 (t x))))
                             (t evisc-tuple)))
                      (evisc-table (table-alist 'evisc-table (w state)))
                      (eviscp (or local-evisc-tuple evisc-table)))
                 (mv-let (x state)
                   (cond (eviscp (eviscerate-top
                                  (fmt-var s alist i maximum)
                                  (cadr local-evisc-tuple)  ;;; print-level
                                  (caddr local-evisc-tuple) ;;; print-length
                                  (car local-evisc-tuple)   ;;; alist
                                  evisc-table
                                  (cadddr local-evisc-tuple) ;;; hiding-cars
                                  state))
                         (t (mv (fmt-var s alist i maximum)
                                state)))

; Through Version_3.4, ACL2 could hyphenate rule names during proof commentary
; because of the following COND branch in the case of ~x/~y/~X/~Y (though
; fmt-symbol-name has since been renamed as fmt-tilde-s).  We have decided to
; opt instead for uniform treatment of ~x/~y/~X/~Y and ~p/~q/~P/~Q, especially
; since we no longer are considering support for infix printing for the latter
; group.  By avoiding hyphenation we make it easier for a user to grab a rule
; name from the output, though now one might want to do some hyphenation by
; hand when preparing proof output for publication.

;                   ((and (or (symbolp x)
;                             (acl2-numberp x))
;                         (member-eq fmc '(#\x #\y #\X #\Y)))
;                    (mv-letc (col state)
;                             (fmt-tilde-s x col channel state)
;                             (fmt0 s alist
;                                   (+f i (if (or (eql fmc #\X)
;                                                 (eql fmc #\Y))
;                                             4
;                                           3))
;                                   maximum col nil channel state
;                                   evisc-tuple)))

                   (let* ((fmt-hard-right-margin (fmt-hard-right-margin state))
                          (sz (flsz x col fmt-hard-right-margin state eviscp))
                          (incr (the-fixnat (if caps 4 3)))
                          (c ; either (< (+ i incr) maximum) or error
                           (fmt-char s i incr maximum nil))
                          (punctp (punctp c))
                          (print-pn (and pn
                                         (not punctp) ; optimization
                                         (= (+f! i incr) maximum)))
                          (p+ (if (or punctp print-pn) 1 0)))
                     (declare (type #.*small-nat-type* fmt-hard-right-margin)
                              (type #.*fixnat-type* sz incr p+)
                              (type character c))
                     (cond
                      ((and px
                            (> col (the-fixnat *fmt-ppr-indentation*))
                            (> (+f! p+ sz) fmt-hard-right-margin)
                            (not (> (+f! p+
                                         (flsz x
                                               (the-fixnat
                                                *fmt-ppr-indentation*)
                                               fmt-hard-right-margin
                                               state eviscp))
                                    fmt-hard-right-margin)))
                       (pprogn
                        (newline channel state)
                        (spaces1 (the-fixnat *fmt-ppr-indentation*) 0
                                 fmt-hard-right-margin
                                 channel state)
                        (fmt0 s alist i maximum
                              (the-fixnat *fmt-ppr-indentation*)
                              pn channel state evisc-tuple (1-f clk))))
                      ((or qy
                           (> (+f! p+ sz)
                              fmt-hard-right-margin))
                       (pprogn
                        (cond (qy state)
                              ((= col 0) state)
                              (t (newline channel state)))
                        (if qy
                            state
                          (spaces1 (the-fixnat *fmt-ppr-indentation*)
                                   0 fmt-hard-right-margin channel state))
                        (let* ((i1 (the-fixnat
                                    (if punctp

; As noted above, if we get to here then (< (+ i incr) maximum).  We are OK
; with i1 and i2 being maximum.  This reasoning is actually overkill, since
; it's OK for the i argument of fmt0 to exceed maximum.

                                        (+f! i 1 incr)
                                      (+f! i incr))))
                               (i2 (if qy ; then respect trailing whitespace
                                       i1
                                     (scan-past-whitespace s i1 maximum)))
                               (new-col (min-fixnat fmt-hard-right-margin
                                                    (if qy
                                                        col
                                                      *fmt-ppr-indentation*))))
                          (declare (type #.*fixnat-type* i1 i2 new-col))
                          (pprogn
                           (fmt-ppr
                            x
                            (-f fmt-hard-right-margin new-col)
                            p+ new-col channel state eviscp)
                           (cond (punctp (princ$ c channel state))
                                 (print-pn (princ$ pn channel state))
                                 (t state))
                           (newline channel state)
                           (fmt0 s alist i2 maximum 0
                                 (and (not print-pn) pn)
                                 channel state
                                 evisc-tuple (1-f clk))))))
                      (t (pprogn
                          (flpr x channel state eviscp)
                          (fmt0 s alist
                                (+f! i (if caps 4 3))
                                maximum sz pn
                                channel state evisc-tuple (1-f clk))))))))))
             (#\@ (let ((s1 (fmt-var s alist i maximum))
                        (i0 (scan-past-empty-fmt-directives s alist
                                                            (+f! i 3)
                                                            maximum)))
                    (declare (type #.*fixnat-type* i0))
                    (mv-let (i1 pn pn@)
                      (cond ((< i0 maximum)
                             (let ((punctp (punctp (charf s i0))))
                               (cond (punctp (mv (+f 1 i0) pn punctp))
                                     (t (mv i0 pn nil)))))
                            (t ; print any pending punctuation with s1
                             (mv i0 nil pn)))
                      (declare (type #.*fixnat-type* i1))
                      (mv-letc (col state)
                               (cond ((stringp s1)
                                      (fmt0 s1 alist 0
                                            (the-fixnat! (length s1) 'fmt0)
                                            col pn@ channel state evisc-tuple
                                            (1-f clk)))
                                     ((msgp s1)
                                      (fmt0 (car s1)
                                            (append (cdr s1) alist)
                                            0
                                            (the-fixnat! (length (car s1))
                                                         'fmt0)
                                            col pn@ channel state evisc-tuple
                                            (1-f clk)))
                                     (t (mv (er-hard-val
                                             0 'fmt0 "~@0"
                                             (illegal-fmt-msg
                                              bad-tilde-@-arg
                                              i s1 'msgp s))
                                            state)))
                               (fmt0 s alist i1 maximum col pn
                                     channel state evisc-tuple (1-f clk))))))
             (#\# (let* ((n (find-alternative-start
                             (fmt-var s alist i maximum) s i maximum nil))
                         (m (find-alternative-stop s n maximum nil))
                         (o (find-alternative-skip s m maximum nil)))
                    (declare (type #.*fixnat-type* n)
                             (type #.*fixnat-type* m o))
                    (mv-let (pn1 pn2 o)
                      (cond ((= o maximum)
                             (mv pn nil o))
                            ((punctp (charf s o))
                             (mv (charf s o) pn (1+f o)))
                            (t
                             (mv nil pn o)))
                      (declare (type #.*fixnat-type* o))
                      (mv-letc (col state)
                               (fmt0 s alist n m col pn1 channel state
                                     evisc-tuple (1-f clk))
                               (fmt0 s alist o maximum col pn2
                                     channel state evisc-tuple (1-f clk))))))
             (#\* (let ((x (fmt-var s alist i maximum)))
                    (cond
                     ((or (< (len x) 5)
                          (not (and (stringp (car x))
                                    (fixnat-guard (length (car x)))
                                    (stringp (cadr x))
                                    (fixnat-guard (length (cadr x)))
                                    (stringp (caddr x))
                                    (fixnat-guard (length (caddr x)))
                                    (stringp (cadddr x))
                                    (fixnat-guard (length (cadddr x)))
                                    (true-listp (car (cddddr x)))
                                    (character-alistp (cdr (cddddr x))))))
                      (mv (er-hard-val
                           0 'fmt0 "~@0"
                           (illegal-fmt-msg
                            bad-tilde-*-arg
                            i
                            (char? s (+f! i 2))
                            'character-alistp
                            x
                            s))
                          state))
                     (t
                      (mv-letc (col state)
                               (fmt0* (car x) (cadr x) (caddr x) (cadddr x)
                                      (car (cddddr x))
                                      (append (cdr (cddddr x)) alist)
                                      col channel state evisc-tuple (1-f clk))
                               (fmt0 s alist (+f! i 3) maximum col pn
                                     channel state evisc-tuple (1-f clk)))))))
             ((#\& #\v)
              (let ((i+3 (+f! i 3))
                    (lst (fmt-var s alist i maximum)))
                (declare (type #.*fixnat-type* i+3))
                (cond
                 ((not (true-listp lst))
                  (mv (er-hard-val
                       0 'fmt0 "~@0"
                       (illegal-fmt-msg
                        bad-tilde-&v-arg
                        i
                        (char? s (+f! i 2))
                        (if (eql fmc #\&) "~&" "~v")
                        lst
                        s))
                      state))
                 (t
                  (mv-letc (col state)
                           (fmt0&v (if (eql fmc #\&) '& 'v)
                                   lst
                                   (punctp (and (< i+3 maximum)
                                                (char s i+3)))
                                   col channel state evisc-tuple (1-f clk))
                           (fmt0 s alist
                                 (the-fixnat
                                  (cond
                                   ((punctp (and (< i+3 maximum)
                                                 (char s i+3)))
                                    (+f! i 4))
                                   (t i+3)))
                                 maximum col pn channel state evisc-tuple
                                 (1-f clk)))))))
             ((#\n #\N)
              (let ((k (fmt-var s alist i maximum)))
                (cond
                 ((not (or (integerp k)
                           (and (consp k)
                                (integerp (car k)))))
                  (mv (er-hard-val
                       0 'fmt0 "~@0"
                       (illegal-fmt-msg
                        bad-tilde-n-arg
                        i
                        (char? s (+f! i 2))
                        (if (eql fmc #\n) "~n" "~N")
                        k
                        s))
                      state))
                 (t
                  (maybe-newline
                   (mv-letc (col state)
                            (spell-number k
                                          (eql fmc #\N)
                                          col channel state evisc-tuple
                                          (1-f clk))
                            (fmt0 s alist (+f! i 3) maximum col pn
                                  channel state evisc-tuple (1-f clk))))))))
             (#\t (maybe-newline
                   (let ((goal-col (fmt-var s alist i maximum))
                         (fmt-hard-right-margin (fmt-hard-right-margin state)))
                     (declare (type #.*small-nat-type* fmt-hard-right-margin))
                     (cond ((or (not (natp goal-col))
                                (> goal-col fmt-hard-right-margin))
                            (prog2$
                             (if (natp goal-col)
                                 (er hard? 'fmt0
                                     "~@0"
                                     (illegal-fmt-msg
                                      bad-tilde-t-arg-natp
                                      fmt-hard-right-margin
                                      (string (fmt-char s i 2 maximum t))
                                      goal-col))
                               (er hard? 'fmt0
                                   "~@0"
                                   (illegal-fmt-msg
                                    bad-tilde-t-arg-not-natp
                                    i
                                    (char? s (+f! i 2))
                                    goal-col
                                    s)))
                             (mv col state)))
                           (t
; So, goal-col <= fmt-hard-right-margin < (fixnum-bound).
                            (pprogn
                             (cond
                              ((>= col (the-fixnat goal-col))
                               (pprogn (newline channel state)
                                       (spaces1 (the-fixnat goal-col) 0
                                                fmt-hard-right-margin
                                                channel state)))
                              (t (spaces1 (-f goal-col col) col
                                          fmt-hard-right-margin
                                          channel state)))
                             (fmt0 s alist (+f! i 3) maximum
                                   (the-fixnat goal-col)
                                   pn channel state evisc-tuple (1-f clk))))))))
             (#\c (maybe-newline
                   (let ((pair (fmt-var s alist i maximum)))
                     (cond ((and (consp pair)
                                 (integerp (car pair))
                                 (integerp (cdr pair))
                                 (>= (cdr pair) 0))
                            (mv-letc (col state)
                                     (left-pad-with-blanks (car pair)
                                                           (cdr pair)
                                                           col channel state)
                                     (fmt0 s alist (+f! i 3) maximum col pn
                                           channel state evisc-tuple
                                           (1-f clk))))
                           (t (mv (er-hard-val
                                   0 'fmt0 "~@0"
                                   (illegal-fmt-msg
                                    bad-tilde-c-arg
                                    i pair s))
                                  state))))))
             ((#\f #\F)
              (let ((evisc-table
                     (append? (car evisc-tuple) ;;; alist

; We normally would pass the alist above into eviscerate-top below, as the
; argument just above evisc-table, and bind evisc-table to the table-alist call
; on the line just below.  However, the call of splat below expects a single
; alist.

                              (table-alist 'evisc-table (w state)))))
                (mv-let
                  (x state)
                  (cond (evisc-table (eviscerate-top
                                      (fmt-var s alist i maximum)
                                      nil ;;; print-level
                                      nil ;;; print-length
                                      nil
                                      evisc-table
                                      nil ;;; hiding-cars
                                      state))
                        (t (mv (fmt-var s alist i maximum)
                               state)))
                  (maybe-newline
                   (mv-letc (col state)
                            (splat x
                                   (print-base) (print-radix)
                                   (if (eql fmc #\F) (+f! 1 col) 0)
                                   evisc-table col channel state)
                            (fmt0 s alist (+f! i 3) maximum col pn
                                  channel state evisc-tuple (1-f clk)))))))
             ((#\s #\S)
              (let ((x (fmt-var s alist i maximum)))
                (cond
                 ((or (symbolp x)
                      (stringp x)
                      (acl2-numberp x))
                  (maybe-newline
                   (mv-letc (col state)
                            (if (eql fmc #\s)
                                (fmt-tilde-s x col channel state (1-f clk))
                              (fmt-tilde-cap-s x col channel state (1-f clk)))
                            (fmt0 s alist (+f! i 3) maximum
                                  (min col (fixnum-bound))
                                  pn
                                  channel state evisc-tuple (1-f clk)))))
                 (t (mv (er-hard-val
                         0 'fmt0 "~@0"
                         (illegal-fmt-msg
                          bad-tilde-s-arg
                          (if (eql fmc #\s) "s" "S")
                          i x s))
                        state)))))
             (#\Space (let ((exceeds-margin
                             (or (> col (fmt-hard-right-margin state))
                                 (> col (fmt-soft-right-margin state)))))
                        (pprogn
                         (cond (exceeds-margin (newline channel state))
                               (t state))
                         (princ$ #\Space channel state)
                         (fmt0 s alist (+f! i 2) maximum
                               (cond (exceeds-margin
                                      1)
                                     (t (1+f col)))
                               pn channel state evisc-tuple (1-f clk)))))
             (#\_ (maybe-newline
                   (let ((fmt-hard-right-margin
                          (fmt-hard-right-margin state)))
                     (declare (type #.*small-nat-type* fmt-hard-right-margin))
                     (let* ((n0 (fmt-var s alist i maximum))
                            (n (if (and (natp n0)
                                        (<= n0 (floor (fixnum-bound) 2)))
                                   n0
                                 (er-hard-val
                                  0 'fmt0 "~@0"
                                  (illegal-fmt-msg
                                   bad-tilde-_-arg
                                   i n0 (floor (fixnum-bound) 2) s)))))
                       (declare (type #.*fixnat-type* n))
                       (let ((new-col (+f! col n)))
                         (declare (type #.*fixnat-type* new-col))
                         (pprogn
                          (spaces n col channel state)
                          (cond
                           ((> new-col fmt-hard-right-margin)
                            (newline channel state))
                           (t state))
                          (fmt0 s alist (+f! i 3) maximum
                                (the-fixnat
                                 (cond
                                  ((> new-col fmt-hard-right-margin)
                                   0)
                                  (t new-col)))
                                pn channel state evisc-tuple (1-f clk))))))))
             (#\Newline
              (fmt0 s alist (scan-past-whitespace s (+f! i 2) maximum)
                    maximum col pn channel state evisc-tuple (1-f clk)))
             (#\| (pprogn
                   (if (int= col 0) state (newline channel state))
                   (fmt0 s alist (+f! i 2)
                         maximum 0 pn channel state evisc-tuple (1-f clk))))
             (#\% (pprogn
                   (newline channel state)
                   (fmt0 s alist (+f! i 2)
                         maximum 0 pn channel state evisc-tuple (1-f clk))))
             (#\~ (maybe-newline
                   (pprogn
                    (princ$ #\~ channel state)
                    (fmt0 s alist (+f! i 2) maximum (+f! 1 col) pn
                          channel state evisc-tuple (1-f clk)))))
             (#\- (cond ((> col (fmt-soft-right-margin state))
                         (pprogn
                          (princ$ #\- channel state)
                          (newline channel state)
                          (fmt0 s alist
                                (scan-past-whitespace s (+f! i 2) maximum)
                                maximum 0 pn channel state evisc-tuple
                                (1-f clk))))
                        (t (fmt0 s alist (+f! i 2) maximum col pn
                                 channel state evisc-tuple (1-f clk)))))
             (otherwise (mv (er-hard-val
                             0 'fmt0 "~@0"
                             (illegal-fmt-msg
                              unrecognized-tilde-arg
                              i s))
                            state)))))
        ((and (> col (fmt-soft-right-margin state))
              (eql c #\Space))
         (pprogn (newline channel state)
                 (fmt0 s alist
                       (scan-past-whitespace s (+f i 1) maximum)
                       maximum
                       0 pn channel state evisc-tuple (1-f clk))))
        ((and (>= col (fmt-soft-right-margin state))
              (eql c #\-))
         (pprogn (princ$ c channel state)
                 (newline channel state)
                 (fmt0 s alist
                       (scan-past-whitespace s (+f i 1) maximum)
                       maximum
                       0 pn channel state evisc-tuple (1-f clk))))
;       ((and (eql c #\Space)
; I cut out this code in response to Kaufmann's complaint 38.  The idea is
; *not* to ignore spaces after ~% directives.  I've left the code here to
; remind me of what I used to do, in case I see output that is malformed.
;            (int= col 0))
;       (fmt0 s alist (+f i 1) maximum 0 channel state evisc-tuple))
        (t (maybe-newline
            (pprogn (princ$ c channel state)
                    (fmt0 s alist (+f i 1) maximum
                          (if (eql c #\Newline) 0 (+f! col 1))
                          pn channel state evisc-tuple (1-f clk)))))))))))

)

(defun tilde-*-&v-strings (flg lst punct)

; This function returns an object that when bound to #\0 will cause
; ~*0 to print a conjunction (flg='&) or disjunction (flg='v) of the
; strings in lst, followed by punctuation punct, which must be #\. or
; #\,.

; WARNING:  This displayed strings are not equal to the strings in lst
; because whitespace may be inserted!

; ~& doesn't print a list of short strings very well because the first
; group is printed flat across the line, then when the line gets too
; long, the next string is indented and followed by a newline, which
; allows another bunch to be printed flat.  This function prints them
; with ~s which actually breaks the strings up internally in a way
; that does not preserve their equality.  "history-management.lisp"
; might have a newline inserted after the hyphen.

  (case
   flg
   (&
    (case
     punct
     (#\. (list "" "\"~s*\"." "\"~s*\" and " "\"~s*\", " lst))
     (#\, (list "" "\"~s*\"," "\"~s*\" and " "\"~s*\", " lst))
     (#\: (list "" "\"~s*\":" "\"~s*\" and " "\"~s*\", " lst))
     (#\; (list "" "\"~s*\";" "\"~s*\" and " "\"~s*\", " lst))
     (#\! (list "" "\"~s*\"!" "\"~s*\" and " "\"~s*\", " lst))
     (#\) (list "" "\"~s*\")" "\"~s*\" and " "\"~s*\", " lst))
     (#\? (list "" "\"~s*\"?" "\"~s*\" and " "\"~s*\", " lst))
     (otherwise
      (list "" "\"~s*\"" "\"~s*\" and " "\"~s*\", " lst))))
   (otherwise
    (case
     punct
     (#\. (list "" "\"~s*\"." "\"~s*\" or " "\"~s*\", " lst))
     (#\, (list "" "\"~s*\"," "\"~s*\" or " "\"~s*\", " lst))
     (#\: (list "" "\"~s*\":" "\"~s*\" or " "\"~s*\", " lst))
     (#\; (list "" "\"~s*\";" "\"~s*\" or " "\"~s*\", " lst))
     (#\! (list "" "\"~s*\"!" "\"~s*\" or " "\"~s*\", " lst))
     (#\) (list "" "\"~s*\")" "\"~s*\" or " "\"~s*\", " lst))
     (#\? (list "" "\"~s*\"?" "\"~s*\" or " "\"~s*\", " lst))
     (otherwise
      (list "" "\"~s*\"" "\"~s*\" or " "\"~s*\", " lst))))))

(defun fmt1 (str alist col channel state evisc-tuple)

; WARNING:  The master copy of the tilde-directives list is in :DOC fmt.

  (declare (type #.*fixnat-type* col)
           (type string str)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))))
  (the2s
   #.*fixnat-type*
   (cond
    ((not (character-alistp alist))
     (mv (prog2$ (er hard! 'fmt0
                     "The second argument of any of the FMT family of ~
                      functions must satisfy ~x0, but ~x1 does not."
                     'character-alistp
                     alist)
                 col)
         state))
    (t
     (mv-let (col state)
       (fmt0 str alist 0
             (min (length str) (fixnum-bound))
             col nil channel state evisc-tuple
             (fixnum-bound))
       (declare (type #.*fixnat-type* col))
       (prog2$ (and (eq channel *standard-co*)
                    (maybe-finish-output$ *standard-co* state))
               (mv col state)))))))

(defun fmt (str alist channel state evisc-tuple)

; WARNING: IF you change the list of tilde-directives, change the copy of it in
; the :DOC for fmt1 and fms.

; For a discussion of our style of pretty-printing, see
; http://www.cs.utexas.edu/~boyer/pretty-print.pdf.

  (declare (type string str)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))))
  (the2s
   #.*fixnat-type*
   (pprogn
    (newline channel state)
    (fmt1 str alist 0 channel state evisc-tuple))))

(defun fms (str alist channel state evisc-tuple)

; WARNING: The master copy of the tilde-directives list is in :DOC fmt.

  (declare (type string str)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))))
  (pprogn
   (newline channel state)
   (mv-let (col state)
           (fmt1 str alist 0 channel state evisc-tuple)
           (declare (ignore col))
           state)))

(defun fmt1! (str alist col channel state evisc-tuple)

; WARNING: The master copy of the tilde-directives list is in :DOC fmt.

  (declare (type #.*fixnat-type* col)
           (type string str)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))))
  (the2s
   #.*fixnat-type*
   (mv-let (erp col state)
     (state-global-let*
      ((write-for-read t))
      (mv-let (col state)
        (fmt1 str alist col channel state evisc-tuple)
        (mv nil col state)))
     (declare (ignore erp))
     (mv col state))))

(defun fmt! (str alist channel state evisc-tuple)

; WARNING: The master copy of the tilde-directives list is in :DOC fmt.

  (declare (type string str)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))))
  (the2s
   #.*fixnat-type*
   (mv-let (erp col state)
     (state-global-let*
      ((write-for-read t))
      (mv-let (col state)
        (fmt str alist channel state evisc-tuple)
        (mv nil col state)))
     (declare (ignore erp))
     (mv col state))))

(defun fms! (str alist channel state evisc-tuple)

; WARNING: The master copy of the tilde-directives list is in :DOC fmt.

  (declare (type string str)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep evisc-tuple))))
  (mv-let (erp val state)
          (state-global-let*
           ((write-for-read t))
           (pprogn (fms str alist channel state evisc-tuple)
                   (mv nil nil state)))
          (declare (ignore erp val))
          state))

(defmacro fmx (str &rest args)
  (declare (xargs :guard (<= (length args) 10)))
  `(fmt1 ,str
         ,(make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                               #\5 #\6 #\7 #\8 #\9)
                             args)
         0 *standard-co* state nil))

(defmacro fmx-cw-msg-1-body ()

; Note: This has functionality related to fmt0, so if you change one of those,
; consider changing the other and consider changing each :DOC topic.

; Note: Keep this in sync with fmt0 and :DOC fmt.

; This unusual way of specifying a function body is useful for sharing code
; between the definition of fmx-cw-msg-1 and the rewrite rule,
; fmx-cw-msg-1-opener.

; Warning: To see the effect of changing this definition during an interactive
; session, you will also need to redefine fmx-cw-msg-1 (say, by redefining it
; to be a term different from, but provably equal to, (fmx-cw-msg-1-body)).

  '(cond
    ((zp clk) ; impossible?
     (msg "Stack depth exceeded for guard check!"))
    ((or (not (mbt (natp i)))
         (not (mbt (natp maximum)))
         (>= i maximum))
     nil)
    (t
     (let ((c0 (the character (charf s i)))
           (i+1 (1+f i))
           (clk-1 (1-f clk)))
       (declare (type character c0)
                (type #.*fixnat-type* i+1 clk-1))
       (cond
        ((eql c0 #\~)
         (cond
          ((not (< i+1 maximum))
           (illegal-fmt-msg
            tilde-arg-points-past-string
            i 1 maximum s))
          (t
           (let ((c1 (the character (charf s i+1))))
             (declare (type character c1))
             (case
               c1
               ((#\Space #\Newline #\| #\% #\~ #\-)
                nil)
               (otherwise
                (let ((i+2 (+f i 2)))
                  (declare (type #.*fixnat-type* i+2))
                  (cond
                   ((not (< i+2 maximum))
                    (illegal-fmt-msg
                     tilde-arg-points-past-string
                     i 2 maximum s))
                   (t
                    (let* ((c2 (the character (charf s i+2)))
                           (pair2 (assoc c2 alist))
                           (val2 (cdr pair2))
                           (i+3 (+f i 3)))
                      (declare (type character c2)
                               (type #.*fixnat-type* i+3))
                      (cond
                       ((not pair2)
                        (illegal-fmt-msg
                         unbound-tilde-arg
                         i c2 alist s))
                       (t
                        (case
                          c1
                          ((#\p #\q #\x #\y)
                           (fmx-cw-msg-1 s alist i+3 maximum clk-1))
                          ((#\P #\Q #\X #\Y)
                           (cond
                            ((not (< i+3 maximum))
                             (illegal-fmt-msg
                              tilde-arg-points-past-string
                              i 3 maximum s))
                            (t
                             (let* ((c3 (the character (charf s i+3)))
                                    (pair3 (assoc c3 alist))
                                    (val3 (cdr pair3)))
                               (declare (type character c3))
                               (cond
                                ((not pair3)
                                 (illegal-fmt-msg
                                  unbound-tilde-arg
                                  i c3 alist s))
                                ((not (standard-evisc-tuplep val3))
                                 (illegal-fmt-msg
                                  bad-evisc-tuple
                                  i c3 val3 'standard-evisc-tuplep s))
                                (t
                                 (fmx-cw-msg-1 s alist
                                               (+f i 4)
                                               maximum
                                               clk-1)))))))
                          (#\@
                           (or
                            (cond
                             ((and (stringp val2)
                                   (< (length val2) (fixnum-bound)))
                              (fmx-cw-msg-1
                               val2 alist 0
                               (length val2)
                               clk-1))
                             ((and (consp val2)
                                   (msgp val2)
                                   (< (length (car val2)) (fixnum-bound)))
                              (fmx-cw-msg-1 (car val2)
                                            (append (cdr val2) alist)
                                            0
                                            (length (car val2))
                                            clk-1))
                             (t
                              (illegal-fmt-msg
                               bad-tilde-@-arg
                               i val2 'character-alistp s)))
                            (fmx-cw-msg-1 s alist i+3 maximum clk-1)))
                          (#\#
                           (cond
                            ((not (< i+3 maximum))
                             (illegal-fmt-msg
                              tilde-arg-points-past-string
                              i 3 maximum s))
                            (t
                             (let ((i+4 (+f i 4)))
                               (declare (type #.*fixnat-type* i+4))
                               (cond
                                ((not (< i+4 maximum))
                                 (illegal-fmt-msg
                                  tilde-arg-points-past-string
                                  i 4 maximum s))
                                (t
                                 (let ((n (find-alternative-start
                                           c2 s i maximum t))
                                       (max+1 (1+f maximum)))
                                   (declare (type #.*fixnum-type* n max+1))
                                   (cond
                                    ((= n max+1)
                                     (illegal-fmt-msg
                                      find-alternative-start i s))
                                    ((= n maximum)
                                     (illegal-fmt-msg
                                      find-alternative-skip s))
                                    ((= n (-f maximum))
                                     (illegal-fmt-msg
                                      find-alternative-start1-b s))
                                    ((< n 0)
                                     (illegal-fmt-msg
                                      find-alternative-start1-a
                                      "starting"
                                      i
                                      (zero-one-or-more (-f n))
                                      (-f n)
                                      s))
                                    (t
                                     (let ((m (find-alternative-stop
                                               s n maximum t)))
                                       (declare (type #.*fixnat-type* m))
                                       (cond
                                        ((eql m max+1)
                                         (illegal-fmt-msg
                                          find-alternative-stop
                                          s))
                                        (t
                                         (let ((o (find-alternative-skip
                                                   s m maximum t)))
                                           (declare
                                            (type #.*fixnat-type* o))
                                           (cond
                                            ((= o 0)
                                             (illegal-fmt-msg
                                              find-alternative-skip
                                              s))
                                            (t
                                             (or (fmx-cw-msg-1
                                                  s alist n m clk-1)
                                                 (fmx-cw-msg-1
                                                  s alist o maximum
                                                  clk-1)))))))))))))))))
                          ((#\& #\v)
                           (cond
                            ((not (true-listp val2))
                             (illegal-fmt-msg
                              bad-tilde-&v-arg
                              i c2
                              (if (eql c1 #\&) "~&" "~v")
                              val2 s))
                            (t
                             (fmx-cw-msg-1 s alist i+3 maximum clk-1))))
                          (#\*
                           (cond
                            ((not (and (>= (len val2) 5)
                                       (character-alistp
                                        (cdr (cddddr val2)))))
                             (illegal-fmt-msg
                              bad-tilde-*-arg
                              i c2 'character-alistp val2 s))
                            (t
                             (fmx-cw-msg-1 s alist i+3 maximum clk-1))))
                          ((#\n #\N)
                           (cond
                            ((not (or (integerp val2)
                                      (and (consp val2)
                                           (integerp (car val2)))))
                             (illegal-fmt-msg
                              bad-tilde-n-arg
                              i
                              c2
                              (if (eql c1 #\n) "~n" "~N")
                              val2
                              s))
                            (t
                             (fmx-cw-msg-1 s alist i+3 maximum clk-1))))
                          (#\t
                           (let ((goal-col val2))
                             (cond
                              ((not (natp goal-col))
                               (illegal-fmt-msg
                                bad-tilde-t-arg-not-natp
                                i
                                c2
                                goal-col
                                s))
                              (nil ; (> goal-col fmt-hard-right-margin)

; We don't have state available, so we cannot obtain the current value of the
; state global, fmt-hard-right-margin.  Thus we use a condition of nil above.
; We could use the default value for that global, as shown below, but that
; might frustrate users who set a bigger value and thus expect to be able to
; tab past the default.

                               (illegal-fmt-msg
                                bad-tilde-t-arg-natp
                                *fmt-hard-right-margin-default*
                                (string c2)
                                goal-col))
                              (t
                               (fmx-cw-msg-1 s alist i+3 maximum clk-1)))))
                          (#\c
                           (let ((pair val2))
                             (cond
                              ((and (consp pair)
                                    (integerp (car pair))
                                    (integerp (cdr pair))
                                    (>= (cdr pair) 0))
                               (fmx-cw-msg-1 s alist i+3 maximum clk-1))
                              (t
                               (illegal-fmt-msg
                                bad-tilde-c-arg
                                i pair s)))))
                          ((#\f #\F)
                           (fmx-cw-msg-1 s alist i+3 maximum clk-1))
                          ((#\s #\S)
                           (let ((x val2))
                             (cond
                              ((or (symbolp x)
                                   (stringp x)
                                   (acl2-numberp x))
                               (fmx-cw-msg-1 s alist i+3 maximum clk-1))
                              (t
                               (illegal-fmt-msg
                                bad-tilde-s-arg
                                (if (eql c1 #\s) "s" "S")
                                i x s)))))
                          (#\_
                           (cond
                            ((and (natp c2)
                                  (<= c2
                                      (floor (fixnum-bound) 2)))
                             (fmx-cw-msg-1 s alist i+3 maximum clk-1))
                            (t
                             (illegal-fmt-msg
                              bad-tilde-_-arg
                              i c2 (floor (fixnum-bound) 2) s))))
                          ((#\Newline #\| #\% #\~ #\-)
                           (fmx-cw-msg-1 s alist i+2 maximum clk-1))
                          (otherwise
                           (illegal-fmt-msg
                              unrecognized-tilde-arg
                              i s)))))))))))))))
        (t (fmx-cw-msg-1 s alist i+1 maximum clk-1)))))))

(defun fmx-cw-msg-1 (s alist i maximum clk)
  (declare (type #.*fixnat-type* i maximum clk)
           (type string s)
           (xargs :guard (and (character-alistp alist)
                              (< (length s) (fixnum-bound))
                              (<= maximum (length s)))
                  :guard-hints (("Goal" :in-theory (disable nth)))
                  :measure (nfix clk)))
  (fmx-cw-msg-1-body))

(defun fmx-cw-msg (str alist)
  (declare (xargs :guard t))
  (cond
   ((not (stringp str))
    (msg "Not a string:~|~x0" str))
   ((not (character-alistp alist))
    (msg "Not a character-alistp:~|~x0" alist))
   (t (let ((len (length str)))
        (cond
         ((not (< len (fixnum-bound)))
          (msg "String is too long:~|~x0" str))
         (t (fmx-cw-msg-1 str alist 0 (length str) (fixnum-bound))))))))

(defun fmx-cw-fn-guard (str alist)
  (declare (xargs :guard t))
  (null (fmx-cw-msg str alist)))

(defun fmx-cw-fn (str alist)
  (declare (xargs :guard (fmx-cw-fn-guard str alist)))
  (fmt-to-comment-window str alist 0 nil nil))

(defun fmx!-cw-fn (str alist)
  (declare (xargs :guard (fmx-cw-fn-guard str alist)))
  (fmt-to-comment-window! str alist 0 nil nil))

(defmacro fmx-cw (str &rest args)

; WARNING: Keep this in sync with cw, cw!, and other fmx-cw macros.

; This is a guarded version of cw.
; See the comments there, including this warning:

; WARNING: Keep this in sync with cw!.

  `(fmx-cw-fn ,str
              (pairlis2 '(#\0 #\1 #\2 #\3 #\4
                          #\5 #\6 #\7 #\8 #\9)
                        (list ,@args))))

(defmacro fmx!-cw (str &rest args)

; WARNING: Keep this in sync with cw, cw!, and other fmx-cw macros.

; This is a guarded version of cw.
; See the comments there, including this warning:

; WARNING: Keep this in sync with cw!.

  `(fmx!-cw-fn ,str
               (pairlis2 '(#\0 #\1 #\2 #\3 #\4
                           #\5 #\6 #\7 #\8 #\9)
                         (list ,@args))))

(defun fmt-doc-example1 (lst i)
  (cond ((null lst) nil)
        (t (cons (cons "~c0 (~n1)~tc~y2~|"
                       (list (cons #\0 (cons i 5))
                             (cons #\1 (list i))
                             (cons #\2 (car lst))))
                 (fmt-doc-example1 (cdr lst) (1+ i))))))

(defun fmt-doc-example (x state)
  (fmt "Here is a true list:  ~x0.  It has ~#1~[no elements~/a single ~
        element~/~n2 elements~], ~@3~%~%We could print each element in square ~
        brackets:~%(~*4).  And if we wished to itemize them into column 15 we ~
        could do it like this~%0123456789012345~%~*5End of example."
       (list (cons #\0 x)
             (cons #\1 (cond ((null x) 0) ((null (cdr x)) 1)(t 2)))
             (cons #\2 (length x))
             (cons #\3 (cond ((< (length x) 3) "and so we can't print the third one!")
                             (t (cons "the third of which is ~x0."
                                      (list (cons #\0 (caddr x)))))))
             (cons #\4 (list "[empty]"
                             "[the end: ~y*]"
                             "[almost there: ~y*], "
                             "[~y*], "
                             x))
             (cons #\5 (list* "" "~@*" "~@*" "~@*"
                              (fmt-doc-example1 x 0)
                              (list (cons #\c 15)))))
         *standard-co* state nil))

(defconst *see-doc-set-iprint*

; We give this string a name so that it can be referenced in books; see for
; example community book books/misc/wet.lisp.

  "~|(See :DOC set-iprint to be able to see elided values in this message.)")

(defun fmt-abbrev1 (str alist col channel state suffix-msg)
  (declare (type string str)
           (type #.*fixnat-type* col)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep
                               (abbrev-evisc-tuple state)))))
  (the2s
   #.*fixnat-type*
   (pprogn
    (f-put-global 'evisc-hitp-without-iprint nil state)
    (mv-let (col state)
      (fmt1 str alist col channel state (abbrev-evisc-tuple state))
      (fmt1 "~@0~@1"
            (list
             (cons #\0
                   (cond ((f-get-global 'evisc-hitp-without-iprint
                                        state)
                          (assert$? ; not worth the effort to verify
                           (not (iprint-enabledp state))
                           *see-doc-set-iprint*))
                         (t "")))
             (cons #\1 suffix-msg))
            col channel state nil)))))

(defun fmt-abbrev (str alist col channel state suffix-msg)
  (declare (type string str)
           (type #.*fixnat-type* col)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep
                               (abbrev-evisc-tuple state)))))
  (mv-let (col state)
    (fmt-abbrev1 str alist col channel state suffix-msg)
    (declare (ignore col))
    state))

(defconst *fmt-ctx-spacers*
  '(defun
     #+:non-standard-analysis defun-std
     mutual-recursion
     defuns
     defthm
     #+:non-standard-analysis defthm-std
     defaxiom
     defconst
     defstobj defabsstobj
     defpkg
     deflabel
     deftheory
     defchoose
     verify-guards
     verify-termination
     defmacro
     in-theory
     in-arithmetic-theory
     regenerate-tau-database
     push-untouchable
     remove-untouchable
     reset-prehistory
     disable-ubt
     set-body
     table
     encapsulate
     include-book))

(defun fmt-ctx (ctx col channel state)

; We print the context in which an error has occurred.  We interpret ctx
; according to its type, to make it convenient to construct the more common
; contexts.  If ctx is nil, we print nothing.  If ctx is a symbol, we print it
; from #\0 via "~x0".  If ctx is a pair whose car is a symbol, we print its car
; and cdr from #\0 and #\1 respectively with "(~x0 ~x1 ...)".  Otherwise, we
; print it from #\0 with "~@0".

; We print no other words, spaces or punctuation.  We return the new
; col and state.

  (declare (type #.*fixnat-type* col)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep
                               (abbrev-evisc-tuple state)))))

; The following bit of raw-Lisp code can be useful when observing
; "ACL2 Error in T:".

; #-acl2-loop-only
; (when (eq ctx t) (break))

  (the2s
   #.*fixnat-type*
   (cond ((null ctx)
          (mv col state))
         ((symbolp ctx)
          (fmt1 "~x0" (list (cons #\0 ctx)) col channel state nil))
         ((and (consp ctx)
               (symbolp (car ctx)))
          (fmt1 "(~@0~x1 ~x2 ...)"
                (list (cons #\0
                            (if (member-eq (car ctx) *fmt-ctx-spacers*) " " ""))
                      (cons #\1 (car ctx))
                      (cons #\2 (cdr ctx)))
                col channel state nil))
         (t (fmt-abbrev1 "~@0" (list (cons #\0 ctx)) col channel state "")))))

(defun fmt-in-ctx (ctx col channel state)

; We print the phrase " in ctx:  ", if ctx is non-nil, and return
; the new col and state.

  (declare (type #.*fixnat-type* col)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep
                               (abbrev-evisc-tuple state)))))
  (the2s
   #.*fixnat-type*
   (cond ((null ctx)
          (fmt1 ":  " nil col channel state nil))
         (t (mv-let (col state)
                    (fmt1 " in " nil col channel state nil)
                    (mv-let (col state)
                            (fmt-ctx ctx col channel state)
                            (fmt1 ":  " nil col channel state nil)))))))

(defun er-off-p1 (summary wrld)

; This function is used by er-soft, er-hard?, and er-hard to determine whether
; a given error should be printed.

  (declare (xargs :guard (and (or (null summary)
                                  (stringp summary))
                              (plist-worldp wrld)
                              (string-alistp
                               (table-alist 'inhibit-er-table wrld)))))
  (and summary
       (assoc-string-equal
        summary
        (table-alist 'inhibit-er-table wrld))))

(defun er-off-p (summary state)
  (declare (xargs :stobjs state
                  :guard (and (or (null summary)
                                  (stringp summary))
                              (string-alistp
                               (table-alist 'inhibit-er-table (w state))))))
  (er-off-p1 summary (w state)))

(defun error-fms-channel (hardp ctx summary str alist channel state newlines)

; This function prints the "ACL2 Error" banner and ctx, then the
; user's str and alist, and then two carriage returns.  It returns state.

; Historical Note about ACL2

; Once upon a time we accomplished all this with something like: "ACL2
; Error (in ~xc): ~@s~%~%" and it bound #\c and #\s to ctx and str in
; alist.  That suffers from the fact that it may overwrite the user's
; bindings of #\c and #\s -- unlikely if this error call was generated
; by our er macro.  We rewrote the function this way simply so we
; would not have to remember that some variables are special.

  (declare (type string str)
           (type symbol channel)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (open-output-channel-p channel :character state)
                              (standard-evisc-tuplep
                               (abbrev-evisc-tuple state))
                              (or (null summary)
                                  (stringp summary))
                              (string-alistp
                               (table-alist 'inhibit-er-table (w state))))))
  (cond ((er-off-p summary state)
         state)
        (t
         (flet ((newlines (n channel state)
                          (case n
                            (0 state)
                            (1 (newline channel state))
                            (2 (pprogn (newline channel state)
                                       (newline channel state)))
                            (t (prog2$ (er hard? 'error-fms-channel
                                           "Error: The NEWLINES argument of ~
                                            error-fms-channel must be 0, 1, ~
                                            or 2, hence ~x0 is illegal."
                                           n)
                                       state)))))
           (with-output-lock
            (pprogn
             (newlines newlines channel state)
             (mv-let (col state)
               (fmt1 (if hardp
                         "HARD ACL2 ERROR~#0~[~/ [~s1]~]"
                       "ACL2 Error~#0~[~/ [~s1]~]")
                     (list (cons #\0 (if summary 1 0))
                           (cons #\1 summary))
                     0 channel state nil)
               (mv-let (col state)
                 (fmt-in-ctx ctx col channel state)
                 (fmt-abbrev str alist col channel state "")))
             (newlines newlines channel state)))))))

(defun standard-co (state)
  (declare (xargs :guard t))
  (f-get-global 'standard-co state))

(defun error-fms (hardp ctx summary str alist state)

; See error-fms-channel.  Here we also print extra newlines.

; Note that this function does not suppress error output except in the case
; that the summary string is inhibited (see :DOC set-inhibit-er).

; Keep in sync with error-fms-cw.

  (declare (type string str)
           (xargs :guard (and (fmt-state-p state)
                              (character-alistp alist)
                              (standard-evisc-tuplep
                               (abbrev-evisc-tuple state))
                              (or (null summary)
                                  (stringp summary))
                              (string-alistp
                               (table-alist 'inhibit-er-table (w state)))
                              (symbolp (standard-co state))
                              (open-output-channel-p (standard-co state)
                                                     :character
                                                     state))))
  (let ((chan (f-get-global 'standard-co state)))
    (error-fms-channel hardp ctx summary str alist chan state 2)))

#-acl2-loop-only
(defvar *accumulated-warnings* nil)

(defun push-warning-frame (state)
  #-acl2-loop-only
  (setq *accumulated-warnings*
        (cons nil *accumulated-warnings*))
  state)

(defun absorb-frame (lst stk)
  (if (consp stk)
      (cons (union-equal lst (car stk))
            (cdr stk))
    stk))

(defun pop-warning-frame (accum-p state)

; When a "compound" event has a "sub-event" that generates warnings, we want
; the warning strings from the sub-event's summary to appear in the parent
; event's summary.  Accum-p should be nil if and only if the sub-event whose
; warning frame we are popping had its warnings suppressed.

; Starting after Version_4.1, we use the ACL2 oracle to explain warning frames.
; Previously we kept these frames with a state global variable,
; 'accumulated-warnings, rather than in the raw lisp variable,
; *accumulated-warnings*.  But then we introduced warning$-cw1 to support the
; definitions of translate1-cmp and translate-cmp, which do not modify the ACL2
; state.  See the Essay on Context-message Pairs (cmp) for an explanation.
; Since warning$-cw1 uses a wormhole, the warning frames based on a state
; global variable were unavailable when printing warning summaries.

  #+acl2-loop-only
  (declare (ignore accum-p))
  #+acl2-loop-only
  (mv-let (erp val state)
          (read-acl2-oracle state)
          (declare (ignore erp))
          (mv val state))
  #-acl2-loop-only
  (let ((stk *accumulated-warnings*))
    (cond ((consp stk)
           (progn (setq *accumulated-warnings*
                        (if accum-p
                            (absorb-frame (car stk)
                                          (cdr stk))
                          (cdr stk)))
                  (mv (car stk) state)))
          (t (mv (er hard 'pop-warning-frame
                     "The 'accumulated-warnings stack is empty.")
                 state)))))

(defun push-warning (summary state)
  #+acl2-loop-only
  (declare (ignore summary))
  #-acl2-loop-only
  (when (consp *accumulated-warnings*)

; We used to cause an error, shown below, if the above test fails.  But
; WARNINGs are increasingly used by non-events, such as :trans and (thm ...)
; and rather than protect them all with push-warning-frame/pop-warning-frame we
; are just adopting the policy of not pushing warnings if the stack isn't set
; up for them.  Here is the old code.

;            (prog2$ (er hard 'push-warning
;                        "The 'accumulated-warnings stack is empty but we were ~
;                         asked to add ~x0 to the top frame."
;                        summary)
;                     state)

    (setq *accumulated-warnings*
          (cons (add-to-set-equal summary (car *accumulated-warnings*))
                (cdr *accumulated-warnings*))))
  state)

; The ACL2 Record Facilities

; Our record facility gives us the ability to declare "new" types of
; structures which are represented as lists.  If desired the lists
; are tagged with the name of the new record type.  Otherwise they are
; not tagged and are called "cheap" records.

; The expression (DEFREC SHIP (X . Y) NIL) declares SHIP to
; be a tagged (non-cheap) record of two components X and Y.  An
; example concrete SHIP is '(SHIP 2 . 4).  Note that cheapness refers
; only to whether the record is tagged and whether the tag is tested
; upon access and change, not whether the final cdr is used.

; To make a ship:  (MAKE SHIP :X x :Y y) or (MAKE SHIP :Y y :X x).
; To access the Xth component of the ship object obj: (ACCESS SHIP obj :X).
; To change the Xth component to val: (CHANGE SHIP obj :X val).
; Note the use of keywords in these forms.

; It is possible to change several fields at once, e.g.,
; (CHANGE SHIP obj :X val-x :Y val-y).  In general, to cons up a changed
; record one only does the conses necessary.

; The implementation of records is as follows.  DEFREC expands
; into a collection of macro definitions for certain generated function
; symbols.  In the example above we define the macros:

; |Make SHIP record|
; |Access SHIP record field X|
; |Access SHIP record field Y|
; |Change SHIP record fields|

; The macro expression (MAKE SHIP ...) expands to a call of the first
; function.  (ACCESS SHIP ... :X) expands to a call of the second.
; (CHANGE SHIP obj :X val-x :Y val-y) expands to
; (|Change SHIP record fields| obj :X val-x :Y val-y).

; The five new symbols above are defined as macros that further expand
; into raw CAR/CDR nests if the record is cheap and a similar nest
; that first checks the type of the record otherwise.

; In using the record facility I have sometimes pondered which fields I should
; allocate where to maximize access speed.  Other times I have just laid them
; out in an arbitrary fashion.  In any case, the following functions might be
; useful if you are wondering how to lay out a record.  That is, grab the
; following progn and execute it in the full ACL2 system.  (It cannot be
; executed at this point in basis.lisp because it uses functions defined
; elsewhere; it is here only to be easy to find when looking up the comments
; about records.)  Note that it changes the default-defun-mode to :program.  Then
; invoke :sbt n, where n is an integer.

; For example
; ACL2 g>:sbt 5

; The Binary Trees with Five Tips
; 2.400  ((2 . 2) 2 3 . 3)
; 2.600  (1 (3 . 3) 3 . 3)
; 2.800  (1 2 3 4 . 4)

; Sbt will print out all of the interesting binary trees with the
; given number of tips.  The integer appearing at a tip is the number
; of car/cdrs necessary to access that field of a cheap record laid
; out as shown.  That is also the number of conses required to change
; that single field.  The decimal number in the left column is the
; average number of car/cdrs required to access a field, assuming all
; fields are accessed equally often.  The number of trees generated
; grows exponentially with n.  Roughly 100 trees are printed for size
; 10.  Beware!

; The function (analyze-tree x state) is also helpful.  E.g.,

; ACL2 g>(analyze-tree '((type-alist . term) cl-ids rewrittenp
;                          force-flg . rune-or-non-rune)
;                        state)

; Shape:  ((2 . 2) 2 3 4 . 4)
; Field Depths:
; ((TYPE-ALIST . 2)
;  (TERM . 2)
;  (CL-IDS . 2)
;  (REWRITTENP . 3)
;  (FORCE-FLG . 4)
;  (RUNE-OR-NON-RUNE . 4))
; Avg Depth:  2.833

; (progn
;   (program)
;   (defun bump-binary-tree (tree)
;     (cond ((atom tree) (1+ tree))
;           (t (cons (bump-binary-tree (car tree))
;                    (bump-binary-tree (cdr tree))))))
;
;   (defun cons-binary-trees (t1 t2)
;     (cons (bump-binary-tree t1) (bump-binary-tree t2)))
;
;   (defun combine-binary-trees1 (t1 lst2 ans)
;     (cond ((null lst2) ans)
;           (t (combine-binary-trees1 t1 (cdr lst2)
;                                     (cons (cons-binary-trees t1 (car lst2))
;                                           ans)))))
;
;   (defun combine-binary-trees (lst1 lst2 ans)
;     (cond
;      ((null lst1) ans)
;      (t (combine-binary-trees (cdr lst1)
;                               lst2
;                               (combine-binary-trees1 (car lst1) lst2 ans)))))
;
;   (mutual-recursion
;
;    (defun all-binary-trees1 (i n)
;      (cond ((= i 0) nil)
;            (t (revappend (combine-binary-trees (all-binary-trees i)
;                                                (all-binary-trees (- n i))
;                                                nil)
;                          (all-binary-trees1 (1- i) n)))))
;
;    (defun all-binary-trees (n)
;      (cond ((= n 1) (list 0))
;            (t (all-binary-trees1 (floor n 2) n))))
;    )
;
;   (defun total-access-time-binary-tree (x)
;     (cond ((atom x) x)
;           (t (+ (total-access-time-binary-tree (car x))
;                 (total-access-time-binary-tree (cdr x))))))
;
;   (defun total-access-time-binary-tree-lst (lst)
;
; ; Pairs each tree in lst with its total-access-time.
;
;     (cond ((null lst) nil)
;           (t (cons (cons (total-access-time-binary-tree (car lst))
;                          (car lst))
;                    (total-access-time-binary-tree-lst (cdr lst))))))
;
;   (defun show-binary-trees1 (n lst state)
;     (cond ((null lst) state)
;           (t (let* ((tat (floor (* (caar lst) 1000) n))
;                     (d0 (floor tat 1000))
;                     (d1 (- (floor tat 100) (* d0 10)))
;                     (d2 (- (floor tat 10) (+ (* d0 100) (* d1 10))))
;                     (d3 (- tat (+ (* d0 1000) (* d1 100) (* d2 10)))))
;
;                (pprogn
;                 (mv-let (col state)
;                         (fmt1 "~x0.~x1~x2~x3  ~x4~%"
;                               (list (cons #\0 d0)
;                                     (cons #\1 d1)
;                                     (cons #\2 d2)
;                                     (cons #\3 d3)
;                                     (cons #\4 (cdar lst)))
;                               0
;                               *standard-co* state nil)
;                         (declare (ignore col))
;                         state)
;                 (show-binary-trees1 n (cdr lst) state))))))
;
;   (defun show-binary-trees (n state)
;     (let ((lst (reverse
;                 (merge-sort-car->
;                  (total-access-time-binary-tree-lst
;                   (all-binary-trees n))))))
;       (pprogn
;        (fms "The Binary Trees with ~N0 Tips~%"
;             (list (cons #\0 n))
;             *standard-co* state nil)
;        (show-binary-trees1 n lst state))))
;
;   (defun analyze-tree1 (x i)
;     (cond ((atom x) i)
;           (t (cons (analyze-tree1 (car x) (1+ i))
;                    (analyze-tree1 (cdr x) (1+ i))))))
;
;   (defun analyze-tree2 (x i)
;     (cond ((atom x) (list (cons x i)))
;           (t (append (analyze-tree2 (car x) (1+  i))
;                      (analyze-tree2 (cdr x) (1+  i))))))
;
;   (defun analyze-tree3 (x)
;     (cond ((atom x) 1)
;           (t (+ (analyze-tree3 (car x)) (analyze-tree3 (cdr x))))))
;
;   (defun analyze-tree (x state)
;     (let* ((binary-tree (analyze-tree1 x 0))
;            (alist (analyze-tree2 x 0))
;            (n (analyze-tree3 x))
;            (k (total-access-time-binary-tree binary-tree)))
;       (let* ((tat (floor (* k 1000) n))
;              (d0 (floor tat 1000))
;              (d1 (- (floor tat 100) (* d0 10)))
;              (d2 (- (floor tat 10) (+ (* d0 100) (* d1 10))))
;              (d3 (- tat (+ (* d0 1000) (* d1 100) (* d2 10)))))
;         (pprogn
;          (fms "Shape:  ~x0~%Field Depths:  ~x1~%Avg Depth:  ~x2.~x3~x4~x5~%"
;               (list (cons #\0 binary-tree)
;                     (cons #\1 alist)
;                     (cons #\2 d0)
;                     (cons #\3 d1)
;                     (cons #\4 d2)
;                     (cons #\5 d3))
;               *standard-co* state nil)
;          (value :invisible)))))
;
;   (defmacro sbt (n) `(pprogn (show-binary-trees ,n state) (value :invisible))))
;

(defun record-maker-function-name (name)
  (intern-in-package-of-symbol
   (coerce (append (coerce "Make " 'list)
                   (coerce (symbol-name name) 'list)
                   (coerce " record" 'list))
           'string)
   name))

; Record-accessor-function-name is now in axioms.lisp.

(defun record-changer-function-name (name)
  (intern-in-package-of-symbol
   (coerce
    (append (coerce "Change " 'list)
            (coerce (symbol-name name) 'list)
            (coerce " record fields" 'list))
    'string)
   name))

(defmacro make (&rest args)
  (cond ((keyword-value-listp (cdr args))
         (cons (record-maker-function-name (car args)) (cdr args)))
        (t (er hard 'record-error
               "Make was given a non-keyword as a field specifier.  ~
                The offending form is ~x0."
               (cons 'make args)))))

; Access is now in axioms.lisp.

(defmacro change (&rest args)
  (cond ((keyword-value-listp (cddr args))
         (cons (record-changer-function-name (car args)) (cdr args)))
        (t (er hard 'record-error
               "Change was given a non-keyword as a field specifier.  ~
                The offending form is ~x0."
               (cons 'change args)))))

(defun make-record-car-cdrs1 (lst var)
  (cond ((null lst) var)
        (t (list (car lst) (make-record-car-cdrs1 (cdr lst) var)))))

(defun make-record-car-cdrs (field-layout car-cdr-lst)
  (cond ((atom field-layout)
         (cond ((null field-layout) nil)
               (t (list (make-record-car-cdrs1 car-cdr-lst field-layout)))))
        (t (append (make-record-car-cdrs (car field-layout)
                                         (cons 'car car-cdr-lst))
                   (make-record-car-cdrs (cdr field-layout)
                                         (cons 'cdr car-cdr-lst))))))

(defun make-record-accessors (name field-lst car-cdrs cheap)
  (cond ((null field-lst) nil)
        (t
         (cons (cond
                (cheap
                 (list 'defabbrev
                       (record-accessor-function-name name (car field-lst))
                       (list (car field-lst))
                       (car car-cdrs)))
                (t (list 'defabbrev
                         (record-accessor-function-name name (car field-lst))
                         (list (car field-lst))
                         (sublis (list (cons 'name name)
                                       (cons 'x (car field-lst))
                                       (cons 'z (car car-cdrs)))
                                 '(prog2$ (or (and (consp x)
                                                   (eq (car x) (quote name)))
                                              (record-error (quote name) x))
                                          z)))))
               (make-record-accessors name
                                      (cdr field-lst)
                                      (cdr car-cdrs)
                                      cheap)))))

(defun symbol-name-tree-occur (sym sym-tree)

; Sym is a symbol -- in fact, a keyword in proper usage -- and
; sym-tree is a tree of symbols.  We ask whether a symbol with
; the same symbol-name as key occurs in sym-tree.  If so, we return
; that symbol.  Otherwise we return nil.

  (cond ((symbolp sym-tree)
         (cond ((equal (symbol-name sym) (symbol-name sym-tree))
                sym-tree)
               (t nil)))
        ((atom sym-tree)
         nil)
        (t (or (symbol-name-tree-occur sym (car sym-tree))
               (symbol-name-tree-occur sym (cdr sym-tree))))))

(defun some-symbol-name-tree-occur (syms sym-tree)
  (cond ((null syms) nil)
        ((symbol-name-tree-occur (car syms) sym-tree) t)
        (t (some-symbol-name-tree-occur (cdr syms) sym-tree))))

(defun make-record-changer-cons (fields field-layout x)

; Fields is the list of keyword field specifiers that are being
; changed.  Field-layout is the user's layout of the record.  X is the
; name of the variable holding the instance of the record.

  (cond ((not (some-symbol-name-tree-occur fields field-layout))
         x)
        ((atom field-layout)
         field-layout)
        (t
         (list 'cons
               (make-record-changer-cons fields
                                         (car field-layout)
                                         (list 'car x))
               (make-record-changer-cons fields
                                         (cdr field-layout)
                                         (list 'cdr x))))))

(defun make-record-changer-let-bindings (field-layout lst)

; Field-layout is the symbol tree provided by the user describing the
; layout of the fields.  Lst is the keyword/value list in a change
; form.  We want to bind each field name to the corresponding value.
; The only reason we take field-layout as an argument is that we
; don't know from :key which package 'key is in.

  (cond ((null lst) nil)
        (t (let ((var (symbol-name-tree-occur (car lst) field-layout)))
             (cond ((null var)
                    (er hard 'record-error
                        "A make or change form has used ~x0 as though ~
                         it were a legal field specifier in a record ~
                         with the layout ~x1."
                        (car lst)
                        field-layout))
                   (t
                    (cons (list var (cadr lst))
                          (make-record-changer-let-bindings field-layout
                                                            (cddr lst)))))))))

(defun make-record-changer-let (name field-layout cheap rec lst)
  (cond
   (cheap
    (list 'let (cons (list 'record-changer-not-to-be-used-elsewhere rec)
                     (make-record-changer-let-bindings field-layout lst))
          (make-record-changer-cons
           (evens lst)
           field-layout
           'record-changer-not-to-be-used-elsewhere)))
   (t
    (list 'let (cons (list 'record-changer-not-to-be-used-elsewhere rec)
                     (make-record-changer-let-bindings field-layout lst))
          (sublis
           (list (cons 'name name)
                 (cons 'cons-nest
                       (make-record-changer-cons
                        (evens lst)
                        field-layout
                        '(cdr record-changer-not-to-be-used-elsewhere))))
           '(prog2$ (or (and (consp record-changer-not-to-be-used-elsewhere)
                             (eq (car record-changer-not-to-be-used-elsewhere)
                                 (quote name)))
                        (record-error (quote name)
                                      record-changer-not-to-be-used-elsewhere))
                    (cons (quote name) cons-nest)))))))

(defun make-record-changer (name field-layout cheap)
  (list 'defmacro
        (record-changer-function-name name)
        '(&rest args)
        (list 'make-record-changer-let
              (kwote name)
              (kwote field-layout)
              cheap
              '(car args)
              '(cdr args))))

(defun make-record-maker-cons (fields field-layout)

; Fields is the list of keyword field specifiers being initialized in
; a record.  Field-layout is the user's specification of the layout.
; We lay down a cons tree isomorphic to field-layout whose tips are
; either the corresponding tip of field-layout or nil according to
; whether the keyword corresponding to the field-layout tip is in fields.

  (cond ((atom field-layout)
         (cond ((some-symbol-name-tree-occur fields field-layout)

; The above call is a little strange isn't it?  Field-layout is an
; atom, a symbol really, and here we are asking whether any element of
; fields symbol-name-tree-occurs in it.  We're really just exploiting
; some-symbol-name-tree-occur to walk down fields for us taking the
; symbol-name of each element and seeing if it occurs in (i.e., in
; this case, is) the symbol name of field-layout.

                field-layout)
               (t nil)))
        (t
         (list 'cons
               (make-record-maker-cons fields
                                       (car field-layout))
               (make-record-maker-cons fields
                                       (cdr field-layout))))))

(defun make-record-maker-let (name field-layout cheap lst)
  (cond
   (cheap
    (list 'let (make-record-changer-let-bindings field-layout lst)
          (make-record-maker-cons (evens lst)
                                  field-layout)))
   (t
    (list 'let (make-record-changer-let-bindings field-layout lst)
          (list 'cons
                (kwote name)
                (make-record-maker-cons (evens lst)
                                        field-layout))))))

(defun make-record-maker (name field-layout cheap)
  (list 'defmacro
        (record-maker-function-name name)
        '(&rest args)
        (list 'make-record-maker-let
              (kwote name)
              (kwote field-layout)
              cheap
              'args)))

(defun make-record-field-lst (field-layout)
  (cond ((atom field-layout)
         (cond ((null field-layout) nil)
               (t (list field-layout))))
        (t (append (make-record-field-lst (car field-layout))
                   (make-record-field-lst (cdr field-layout))))))

(defun record-maker-recognizer-name (name)

; We use the "WEAK-" prefix in order to avoid name clashes with stronger
; recognizers that one may wish to define.

  (declare (xargs :guard (symbolp name)))
  (intern-in-package-of-symbol
   (concatenate 'string "WEAK-" (symbol-name name) "-P")
   name))

(defun make-record-recognizer-body (field-layout)
  (declare (xargs :guard t))
  (cond
   ((consp field-layout)
    (cond
     ((consp (car field-layout))
      (cond
       ((consp (cdr field-layout))
        `(and (consp x)
              (let ((x (car x)))
                ,(make-record-recognizer-body (car field-layout)))
              (let ((x (cdr x)))
                ,(make-record-recognizer-body (cdr field-layout)))))
       (t
        `(and (consp x)
              (let ((x (car x)))
                ,(make-record-recognizer-body (car field-layout)))))))
     ((consp (cdr field-layout))
      `(and (consp x)
            (let ((x (cdr x)))
              ,(make-record-recognizer-body (cdr field-layout)))))
     (t '(consp x))))
   (t t)))

(defun make-record-recognizer (name field-layout cheap recog-name)
  `(defun ,recog-name (x)
     (declare (xargs :mode :logic :guard t)
              ,@(and cheap
                     (symbolp field-layout)
                     `((ignore x))))
     ,(cond
       (cheap (make-record-recognizer-body field-layout))
       (t `(and (consp x)
                (eq (car x) ',name)
                ,@(and (consp field-layout)
                       `((let ((x (cdr x)))
                           ,(make-record-recognizer-body field-layout)))))))))

(defun record-macros (name field-layout cheap recog-name)

; We considered avoiding the use of defabbrev, which introduces a LET, in
; make-record-accessors when cheap is nil.  But the following experiment
; convinced us that this wasn't worth messing with.  This experiment is based
; on the accessor introduced for the rune field by the defrec event for
; def-body.

;   (value :q)
;   (defabbrev foo-abbrev (rune)
;     (car (cdr (cdr (cdr (cdr rune))))))
;   (defmacro foo-mac (rune)
;     (list 'car
;           (list 'cdr
;                 (list 'cdr
;                       (list 'cdr (list 'cdr rune))))))
;   (defun f-abbrev (x)
;     (declare (xargs :guard (true-listp x)))
;     (foo-abbrev x))
;   (defun f-mac (x)
;     (declare (xargs :guard (true-listp x)))
;     (foo-mac x))
;   (defconstant *lstlst*
;     (loop for i from 1 to 10000000 collect (make-list 10)))
;   (defun test-abbrev ()
;     (loop for lst in *lstlst* always (eq (f-abbrev lst) nil)))
;   (defun test-mac ()
;     (loop for lst in *lstlst* always (eq (f-mac lst) nil)))
;   ; There was no observable time difference upon evaluating the following two
;   ; forms.
;   (time$ (test-abbrev))
;   (time$ (test-mac))

  (declare (xargs :guard (or recog-name (symbolp name))))
  (let ((recog-name (or recog-name
                        (record-maker-recognizer-name name))))
    (cons 'progn
          (append
           (make-record-accessors name
                                  (make-record-field-lst field-layout)
                                  (make-record-car-cdrs field-layout
                                                        (if cheap nil '(cdr)))
                                  cheap)
           (list
            (make-record-changer name field-layout cheap)
            (make-record-maker name field-layout cheap)
            (make-record-recognizer name field-layout cheap recog-name))))))

; WARNING: If you change the layout of records, you must change
; certain functions that build them in.  Generally, these functions
; are defined before defrec was defined, but need to access
; components.  See the warning associated with defrec rewrite-constant
; for a list of one group of such functions.  You might also search
; for occurrences of the word defrec prior to this definition of it.

(defmacro defrec (name field-lst cheap &optional recog-name)

; Warning: If when cheap = nil, the car of a record is no longer name, then
; consider changing the definition or use of record-type.

; A recognizer with guard t has is defined using recog-name, if supplied; else,
; by default, its name for (defrec foo ...) is the symbol WEAK-FOO-P, in the
; same package as foo.

  (record-macros name field-lst cheap recog-name))

(defmacro record-type (x)

; X is a non-cheap record, i.e., a record whose defrec has cheap = nil.

  `(car ,x))

; Warning and Observation

; Essay on Inhibited Output and the Illusion of Windows

; The "io" in io?, below, stands for "inhibit output".  Roughly speaking, it
; takes an unevaluated symbolic token denoting a "kind" of output, an output
; shape involving STATE, and a form with the indicated output signature.
; If the "kind" of output is currently inhibited, it returns all nils and the
; current state, e.g., (mv nil state nil) in the case where the output
; shape is something like (mv x state y).  If the kind of output is not
; inhibited, the form is evaluated and its value is returned.

; If form always returned an error triple, this could be said as:
; `(cond ((member-eq ',token (f-get-global 'inhibit-output-lst state))
;         (value nil))
;        (t ,form))
; This whole macro is just a simple way to do optionally inhibited output.

; The introduction of an emacs window-based interface, led us to put a little
; more functionality into this macro.  Each kind of output has a window
; associated with it.  If the kind of output is uninhibited, the io? macro
; sends to *standard-co* certain auxiliary output which causes the
; *standard-co* output by form to be shipped to the designated window.

; The association of windows is accomplished via the constant
; *window-descriptions* below which contains elements of the form (token str
; clear cursor-at-top pop-up), where token is a "kind" of output, str
; identifies the associated window, and the remaining components specify
; options for how output to the window is handled by default.  The io? macro
; provides keyword arguments for overriding these defaults.  If :clear t is
; specified, the window is cleared before the text is written into it,
; otherwise the text is appended to the end.  If :cursor-at-top t is specified,
; the cursor is left at the top of the inserted text, otherwise it is left at
; the bottom of the inserted text.  If :pop-up t is specified, the window is
; raised to the top of the desktop, otherwise the window remains where it was.

; We have purposely avoided trying to suggest that windows are objects in ACL2.
; We have no way to create them or manage them.  We merely ship a sequence of
; characters to *standard-co* and let the host do whatever it does with them.
; Extending ACL2 with some window abstraction is a desirable thing to do.  I
; would like to be able to manipulate windows as ACL2 objects.  But that is
; beyond the scope of the current work whose aim is merely to provide a more
; modern interface to ACL2 without doing too much violence to ACL2's
; applicative nature or to its claim to be Common Lisp.  Those two constraints
; make the introduction of true window objects truly interesting.

; Finally io? allows for the entire io process to be illusory.  This occurs if
; the commentp argument is t.  In this case, the io? form is logically
; equivalent to NIL.  The actual output is performed after opening a wormhole
; to state.

(defun io?-nil-output (lst default-bindings)
  (cond ((null lst) nil)
        (t (cons (cond ((eq (car lst) 'state) 'state)
                       ((cadr (assoc-eq (car lst) default-bindings)))
                       (t nil))
                 (io?-nil-output (cdr lst) default-bindings)))))

(defmacro check-exact-free-vars (ctx vars form)

; A typical use of this macro is (check-free-vars io? vars form) which just
; expands to the translation of form provided all vars occurring freely in form
; are among vars and vice-versa.  The first argument is the name of the calling
; routine, which is used in error reporting.

  (declare (xargs :guard (symbol-listp vars)))
  `(translate-and-test
    (lambda (term)
      (let ((vars ',vars)
            (all-vars (all-vars term)))
        (cond ((not (subsetp-eq all-vars vars))
               (msg "Free vars problem with ~x0:  Variable~#1~[~/s~] ~&1 ~
                     occur~#1~[s~/~] in ~x2 even though not declared."
                    ',ctx
                    (reverse (set-difference-eq all-vars vars))
                    term))
              ((not (subsetp-eq vars all-vars))
               (msg "Free vars problem with ~x0: Variable~#1~[~/s~] ~&1 ~
                     ~#1~[does~/do~] not occur in ~x2 even though declared."
                    ',ctx
                    (reverse (set-difference-eq vars all-vars))
                    term))
              (t t))))
    ,form))

(defun formal-bindings (vars)

; For example, if vars is (ab cd) then return the object
; ((list (quote ab) (list 'quote ab)) (list (quote cd) (list 'quote cd))).

  (if (endp vars)
      nil
    (cons (list 'list
                (list 'quote (car vars))
                (list 'list ''quote (car vars)))
          (formal-bindings (cdr vars)))))

(defrec io-record
  (io-marker . form)
  t)

(defun push-io-record (io-marker form state)
  (declare (xargs :guard t))
  (f-put-global 'saved-output-reversed
                (cons (make io-record
                            :io-marker io-marker
                            :form form)
                      (f-get-global 'saved-output-reversed state))
                state))

(defun saved-output-token-p (token state)
  (declare (xargs :stobjs state
                  :guard
                  (and (symbolp token)
                       (or (eq (f-get-global 'saved-output-token-lst state)
                               :all)
                           (true-listp (f-get-global 'saved-output-token-lst
                                                     state))))))
  (and (f-get-global 'saved-output-p state)
       (or (eq (f-get-global 'saved-output-token-lst state) :all)
           (member-eq token (f-get-global 'saved-output-token-lst state)))))

(defun io?-wormhole-bindings (i vars)
  (declare (xargs :guard (and (true-listp vars)
                              (natp i))))
  (cond ((endp vars) nil)
        (t (cons (list (car vars)
                       `(nth ,i (@ wormhole-input)))
                 (io?-wormhole-bindings (1+ i) (cdr vars))))))

(defconst *tracked-warning-summaries*

; If you want to prevent duplicate warning messages of another kind (i.e., with
; another summary string, e.g., "use" or "free-vars"), add it to this constant.
; Every element of this list should satisfy both stringp and standard-string-p.
; We use the wormhole data field of the 'COMMENT-WINDOW-IO wormhole to collect
; the explanations of those warnings whose summaries are listed here.  This
; prevents duplicate warnings.  See the note regarding the invariant we
; maintain in the defmacro of io? where we lay down the entry lambda for the
; wormhole.

  '("rewrite-lambda-object"))

(defmacro io? (token commentp shape vars body
                     &key
                     (clear 'nil clear-argp)
                     (cursor-at-top 'nil cursor-at-top-argp)
                     (pop-up 'nil pop-up-argp)
                     (default-bindings 'nil)
                     (chk-translatable 't)
                     (io-marker 'nil))

; Typical use (io? error nil (mv col state) (x y) (fmt ...)), meaning execute
; the fmt statement unless 'error is on 'inhibit-output-lst.  The mv expression
; is the shape of the output produced by the fmt expression, and the list (x y)
; for vars indicates the variables other than state that occur free in that
; expression.  See the comment above, and see the Essay on Saved-output for a
; comment that gives a convenient macro for obtaining the free variables other
; than state that occur free in body.

; Default-bindings is a list of doublets (symbol value).  It is used in order
; to supply a non-nil return value for other than state when io is suppressed.
; For example, fmt returns col and state, as suggested by the third (shape)
; argument below.  Without the :default-bindings, this form would evaluate to
; (mv nil state) if event IO is inhibited.  But there are fixnat declarations
; that require the first return value of fmt to be an integer, and we can
; specify the result in the inhibited case to be (mv 0 state) with the
; following :default-bindings:

; (io? event nil (mv col state) nil (fmt ...) :default-bindings ((col 0)))

; The values in :default-bindings are evaluated, so it would be equivalent to
; replace 0 with (- 4 4), for example.

; Keep argument list in sync with io?@par.

; Chk-translatable is only used when commentp is not nil, to check at translate
; time that the body passes translation relative to the given shape.
; (Otherwise such a check is only made when the wormhole call below is actually
; evaluated.)

; Parallelism blemish: avoid calling io? with commentp = t under
; with-output-lock.  During experimentation, we have ACL2(p) hang in such a
; case, because of the interaction of locks created by wormhole1 and
; with-output-lock.  (So more generally, avoid calling with-wormhole-lock in
; the scope of with-output-lock; the other way around is fine.)

  (declare (xargs :guard (and (symbolp token)
                              (symbol-listp vars)
                              (no-duplicatesp vars)
                              (not (member-eq 'state vars))
                              (assoc-eq token *window-descriptions*))))
  (let* ((associated-window (assoc-eq token *window-descriptions*))
         (expansion
          `(let* ((io?-output-inhibitedp
                   (member-eq ',token
                              (f-get-global 'inhibit-output-lst state)))
                  (io?-alist
                   (and (not io?-output-inhibitedp)
                        (list
                         (cons #\w ,(cadr associated-window))
                         (cons #\c ,(if clear-argp
                                        clear
                                      (caddr associated-window)))
                         (cons #\t ,(if cursor-at-top-argp
                                        cursor-at-top
                                      (cadddr associated-window)))
                         (cons #\p ,(if pop-up-argp
                                        pop-up
                                      (car (cddddr associated-window))))

; Peter Dillinger requested the following binding, so that he could specify a
; window prelude string that distinguishes between, for example, "prove",
; "event", and "summary" output, which with the default string would all just
; show up as window 4.

                         (cons #\k ,(symbol-name token))))))
             (pprogn
              (if (or io?-output-inhibitedp
                      (null (f-get-global 'window-interfacep state)))
                  state
                (mv-let (io?-col state)
                        (fmt1! (f-get-global 'window-interface-prelude state)
                               io?-alist 0 *standard-co* state nil)
                        (declare (ignore io?-col))
                        state))
              ,(let ((body
                      `(check-vars-not-free
                        (io?-output-inhibitedp io?-alist)
                        (check-exact-free-vars io? (state ,@vars) ,body)))
                     (nil-output (if (eq shape 'state)
                                     'state
                                   (cons 'mv (io?-nil-output (cdr shape)
                                                             default-bindings))))
                     (postlude
                      `(mv-let
                        (io?-col state)
                        (if (or io?-output-inhibitedp
                                (null (f-get-global 'window-interfacep state)))
                            (mv 0 state)
                          (fmt1! (f-get-global 'window-interface-postlude state)
                                 io?-alist 0 *standard-co* state nil))
                        (declare (ignore io?-col))
                        (check-vars-not-free
                         (io?-output-inhibitedp io?-alist io?-col)
                         ,shape))))
                 (let ((body (if commentp
                                 `(let ,(io?-wormhole-bindings 0 vars)
                                    ,body)
                               body)))
                   (cond
                    ((eq shape 'state)
                     `(pprogn
                       (if io?-output-inhibitedp state ,body)
                       ,postlude))
                    (t `(mv-let ,(cdr shape)
                                (if io?-output-inhibitedp
                                    ,nil-output
                                  ,body)
                                ,postlude)))))))))
    (cond
     (commentp
      (let ((form
             (cond
              ((eq shape 'state)
               `(pprogn ,expansion (value :q)))
              (t
               `(mv-let ,(cdr shape)
                        ,expansion
                        (declare
                         (ignore ,@(remove1-eq 'state (cdr shape))))
                        (value :q))))))
        `(prog2$
          ,(if chk-translatable
               `(chk-translatable ,body ,shape)
             nil)
          (wormhole 'comment-window-io
                    ',(cond ((or (eq token 'warning)
                                 (eq token 'warning!))

; ``Invariant'' on the Wormhole-Data field of the COMMENT-WINDOW-IO wormhole:

; We'd like to know that the wormhole-data field of the wormhole named
; comment-window-io is an alist and that any key in that alist that is
; string-equal to a member of *tracked-warning-summaries* is bound to a
; true-listp.  We can't actually guarantee that invariant since there is
; nothing to stop the user from invoking wormhole on that name.  We can't just
; prevent the translation of (wormhole 'comment-window-io ...) after boot-strap
; because many books use this macro to lay down such a form.  So instead of
; guaranteeing the invariant we merely check that the data field has the right
; shape when we need it.  The consequence of running this code after the user
; has violated the invariant is merely that some tracked warnings might be
; printed multiple times during a proof.

; Preventing Duplicate Warnings: When the comment window is being used for
; warnings, we assume the supplied input (i.e., the values of the expressions
; in `vars' here which will become the wormhole-input when we manufacture the
; actual wormhole) is exactly as laid down in the macro warning1-form.  We
; check that assumption below as we generate the entry lambda for the wormhole.
; Given that check, the entry lambda below can refer to summary, ctx, alist,
; and str which are, respectively, warning's ``label,'' the context, the fmt
; alist and the fmt string.  Note that the summary here is a string, e.g.,
; "Use" or "use" or "rewrite-lambda-object" and is colloquially called the
; warning's ``label'' or ``kind'' in the documentation.  Let's call ctx, alist,
; and str, collectively as (list ctx alist str), the ``explanation'' of the
; warning.  When the comment window is being used for warnings and the summary
; is string-equal to a member of *tracked-warning-summaries* we keep track of
; the explanations already printed for that summary.  If a warning to be
; printed has a tracked summary and its explanation is already on the alist
; paired with that summary in the wormhole-data we do not print the
; explanation.  We clear the data (of tracked summaries only) in print-summary.
; We spot check that the data field has the right shape according to our
; ``invariant'' above: if the summary is to be tracked, we check that the
; wormhole-data is an alist and that this particular summary string is bound to
; a true-list (so we can do a member-equal check on it).  If these
; ``invariants'' don't hold, we proceed as though the warning isn't to be
; tracked, i.e., we might print the same warning multiple times.

; Here is the entry lambda for warnings:
                             (assert$
                              (equal vars '(summary ctx alist str))
                              '(lambda (whs)
                                 (cond
                                  ((and summary
                                        (member-string-equal
                                         summary
                                         *tracked-warning-summaries*)
                                        (string-alistp
                                         (wormhole-data whs)))
                                   (let ((expln (list ctx alist str))
                                         (entry (or (assoc-string-equal
                                                     summary
                                                     (wormhole-data whs))
                                                    (cons summary nil))))
                                     (cond
                                      ((not (true-listp (cdr entry)))
                                       (set-wormhole-entry-code whs :ENTER))
                                      ((member-equal expln (cdr entry))
; This summary and explanation has already been printed.
                                       (set-wormhole-entry-code whs :SKIP))
                                      (t (make-wormhole-status
                                          whs
                                          :ENTER
; Note: It would, perhaps, be clearer to use put-assoc-string-equal to update
; the entry for this summary label.  But that function hasn't been defined and
; rather than define it we use (the probably faster) put-assoc-equal and
; instead of looking for the current spelling of the summary we look for (car
; entry), the first variation of this summary stored.  E.g., imagine multiple
; "Use" warnings, with different capitalization, e.g., "use", "Use", "USE",
; etc.  The first one stored becomes the ``standard key'' we look for with
; put-assoc-equal.

                                          (put-assoc-equal
                                           (car entry)
                                           (cons expln (cdr entry))
                                           (wormhole-data whs)))))))
                                  (t (set-wormhole-entry-code whs :ENTER))))))
                            (t

; Here is the entry lambda for non-warnings:

                             '(lambda (whs)
                                (set-wormhole-entry-code whs :ENTER))))
                    (list ,@vars)
                    ',form
                    :ld-error-action :return!
                    :ld-verbose nil
                    :ld-pre-eval-print nil
                    :ld-prompt nil))))
     (t `(pprogn
          (cond ((saved-output-token-p ',token state)
                 (push-io-record ,io-marker
                                 (list 'let
                                       (list ,@(formal-bindings vars))
                                       ',expansion)
                                 state))
                (t state))
          ,expansion)))))

#+acl2-par
(defmacro io?@par (token commentp &rest rst)

; This macro is the same as io?, except that it provides the extra property
; that the commentp flag is overridden to use comment-window printing.

; Keep the argument list in sync with io?.

; Parallelism blemish: surround the io? call below with a suitable lock.  Once
; this is done, remove any redundant locks around io?@par calls.

  (declare (ignore commentp))
  `(io? ,token t ,@rst))

(defmacro io?-prove (vars body &rest keyword-args)

; Keep in sync with io?-prove-cw.

  `(io? prove nil state ,vars
        (if (gag-mode) state ,body)
        ,@keyword-args))

(defun output-ignored-p (token state)
  (member-eq token
             (f-get-global 'inhibit-output-lst state)))

(defun error1-state-p (state)
  (declare (xargs :stobjs state))
  (and (fmt-state-p state)
; Avoid checking (abbrev-evisc-tuple state) here, since that makes conses.  It
; suffices to check state global 'abbrev-evisc-tuple.
       (let ((e (f-get-global 'abbrev-evisc-tuple state)))
         (or (eq e :default)
             (standard-evisc-tuplep e)))
       (string-alistp
        (table-alist 'inhibit-er-table (w state)))
       (symbolp (standard-co state))
       (open-output-channel-p (standard-co state) :character state)
; Since io? prints to *standard-co*, we need to require *standard-co* to be
; open, not just (standard-co state).
       (open-output-channel-p *standard-co* :character state)
       (true-listp (f-get-global 'inhibit-output-lst state))
       (stringp (f-get-global 'window-interface-prelude state))
       (stringp (f-get-global 'window-interface-postlude state))
       (or (eq (f-get-global 'saved-output-token-lst state)
               :all)
           (true-listp (f-get-global 'saved-output-token-lst state)))))

(defun state-p+ (state)

; This predicate is intended to hold of every ACL2 state and to contain all the
; properties of the ACL2 state that might be needed.  It is not in use as of
; its introduction in April 2024, but we include it so that the name is
; reserved.  For now, error1-state-p suffices for purposes we can think of.

; Maybe some day we will convince ourselves that this predicate always holds
; and add an #-acl2-loop-code body of t.

  (declare (xargs :stobjs state))
  (error1-state-p state))

(defun error1 (ctx summary str alist state)

; Warning: Keep this in sync with error1-safe and error1@par.

  (declare (type string str)
           (xargs :guard (and (error1-state-p state)
                              (character-alistp alist)
                              (or (null summary)
                                  (stringp summary)))))
  (pprogn
   (io? error nil state (alist str ctx summary)
        (error-fms nil ctx summary str alist state))
   (mv t nil state)))

#+acl2-par
(defun error1@par (ctx summary str alist state)

; Keep in sync with error1.  We accept state so that calls to error1 and
; error1@par look the same.

  (declare (ignore state))
  (prog2$
   (our-with-terminal-input ; probably not necessary because of (io? ... t ...)
    (io? error t state (alist str ctx summary)
         (error-fms nil ctx summary str alist state)
         :chk-translatable nil))
   (mv@par t nil state)))

(defun error1-safe (ctx str alist state)

; Warning: Keep this in sync with error1.

; Note: One can rely on this returning a value component of nil.

  (declare (type string str)
           (xargs :guard (and (error1-state-p state)
                              (character-alistp alist))))
  (pprogn
   (io? error nil state (alist str ctx)
        (error-fms nil ctx nil str alist state))
   (mv nil nil state)))

(defun set-inhibited-summary-types-fn (lst state)
  (declare (xargs :stobjs state
                  :mode :program))
  (let ((msg (chk-inhibited-summary-types 'set-inhibited-summary-types lst)))
    (cond (msg (er soft 'set-inhibited-summary-types "~@0" msg))
          (t (pprogn (f-put-global 'inhibited-summary-types lst state)
                     (value lst))))))

(defmacro set-inhibited-summary-types (lst)
  `(set-inhibited-summary-types-fn ,lst state))

(defconst *uninhibited-warning-summaries*
  '("Uncertified"
    "Provisionally certified"
    "Skip-proofs"
    "Defaxioms"
    "Ttags"

; Uncomment the following in order to see invariant-risk warnings during
; regression.
;   "Invariant-risk"

; The above are included because of soundness.  But the following are included
; so that we can see them even when inside include-book, since messages printed
; by missing-compiled-book may assume that such warnings are not inhibited.

    "Compiled file"
    "User-stobjs-modified"))

(defun warning-off-p1 (summary wrld ld-skip-proofsp)

; This function is used by warning$ to determine whether a given warning should
; be printed.  See also warning-disabled-p, which we can use to avoid needless
; computation on behalf of disabled warnings.

  (declare (xargs :guard (and (or (null summary)
                                  (stringp summary))
                              (plist-worldp wrld)
                              (string-alistp
                               (table-alist 'inhibit-warnings-table wrld)))))
  (or (and summary
           (assoc-string-equal
            summary
            (table-alist 'inhibit-warnings-table wrld)))

; The above is sufficient to turn off (warning$ "string" ...).  But even when
; the above condition isn't met, we turn off all warnings -- with the exception
; of those related to soundness -- while including a book.

      (and (or (eq ld-skip-proofsp 'include-book)
               (eq ld-skip-proofsp 'include-book-with-locals)
               (eq ld-skip-proofsp 'initialize-acl2))
           (not (and summary
                     (member-string-equal
                      summary
                      *uninhibited-warning-summaries*))))))

(defun warning-off-p (summary state)
  (warning-off-p1 summary (w state) (ld-skip-proofsp state)))

(defrec do-expressionp
  (stobjs-out . with-vars)
  nil)

(defrec state-vars

; Warning: Keep this in sync with default-state-vars.

; Note that do-expressionp is not actually a state global, even though most
; fields do name a state global.  That's OK, as we are careful about this in
; default-state-vars.  Also note that its value is either nil or a
; do-expressionp record.

  (((binding-count . boot-strap-flg) . ((temp-touchable-vars . safe-mode)
                                        . guard-checking-on))
   .
   ((ld-skip-proofsp . temp-touchable-fns) .
    ((parallel-execution-enabled . in-macrolet-def)
     do-expressionp warnings-as-errors . inhibit-output-lst)))
  nil)

(defconst *default-state-vars*

; Warning: if you change this definition, then change the defaults for the &key
; parameters accordingly in the definition of macro default-state-vars.

  (make state-vars
        :guard-checking-on t
        :inhibit-output-lst '(proof-tree)
        :binding-count 0))

(defmacro default-state-vars

; Warning: if you change the defaults for the &key parameters below, change the
; definition of *default-state-vars* accordingly.

    (state-p &rest args
             &key
             (safe-mode 'nil safe-mode-p)
             (boot-strap-flg 'nil boot-strap-flg-p)
             (temp-touchable-vars 'nil temp-touchable-vars-p)
             (guard-checking-on 't guard-checking-on-p)
             (ld-skip-proofsp 'nil ld-skip-proofsp-p)
             (temp-touchable-fns 'nil temp-touchable-fns-p)
             (parallel-execution-enabled 'nil parallel-execution-enabled-p)
             (in-macrolet-def ; not a state global, so avoid f-get-global below
              'nil)
             (do-expressionp ; not a state global, so avoid f-get-global below
              'nil)
             (binding-count ; not a state global, so avoid f-get-global below
              '0)
             (warnings-as-errors 'nil warnings-as-errors-p)
; Warning: If you change '(proof-tree) just below, make the corresponding
; change in enter-boot-strap-mode.
             (inhibit-output-lst ''(proof-tree) inhibit-output-lst-p))

; Warning: Keep this in sync with defrec state-vars.

; State-p is t to indicate that we use the current values of the relevant state
; globals.  Otherwise we use the specified defaults, which are supplied above
; for convenience but can be changed there (i.e., in this code) if better
; default values are found.

  (cond ((eq state-p t)
         `(make state-vars
                :safe-mode
                ,(if safe-mode-p
                     safe-mode
                   '(f-get-global 'safe-mode state))
                :boot-strap-flg
                ,(if boot-strap-flg-p
                     boot-strap-flg
                   '(f-get-global 'boot-strap-flg state))
                :temp-touchable-vars
                ,(if temp-touchable-vars-p
                     temp-touchable-vars
                   '(f-get-global 'temp-touchable-vars state))
                :guard-checking-on
                ,(if guard-checking-on-p
                     guard-checking-on
                   '(f-get-global 'guard-checking-on state))
                :ld-skip-proofsp
                ,(if ld-skip-proofsp-p
                     ld-skip-proofsp
                   '(f-get-global 'ld-skip-proofsp state))
                :temp-touchable-fns
                ,(if temp-touchable-fns-p
                     temp-touchable-fns
                   '(f-get-global 'temp-touchable-fns state))
                :parallel-execution-enabled
                ,(if parallel-execution-enabled-p
                     parallel-execution-enabled
                   '(f-get-global 'parallel-execution-enabled state))
                :in-macrolet-def
                ,in-macrolet-def
                :do-expressionp
                ,do-expressionp
                :binding-count
                ,binding-count
                :warnings-as-errors
                ,(if warnings-as-errors-p
                     warnings-as-errors
                   '(f-get-global 'warnings-as-errors state))
                :inhibit-output-lst
                ,(if inhibit-output-lst-p
                     inhibit-output-lst
                   '(f-get-global 'inhibit-output-lst state))))
        ((null args)
         '*default-state-vars*)
        (t ; state-p is not t
         `(make state-vars
                :safe-mode ,safe-mode
                :boot-strap-flg ,boot-strap-flg
                :temp-touchable-vars ,temp-touchable-vars
                :guard-checking-on ,guard-checking-on
                :ld-skip-proofsp ,ld-skip-proofsp
                :temp-touchable-fns ,temp-touchable-fns
                :parallel-execution-enabled ,parallel-execution-enabled
                :binding-count ,binding-count
                :warnings-as-errors ,warnings-as-errors
                :inhibit-output-lst ,inhibit-output-lst))))

(defrec warnings-as-errors
  (default . alist)
  nil)

(defabbrev warnings-as-errors-default (x)
  (and x ; else default is nil
       (access warnings-as-errors x :default)))

(defabbrev warnings-as-errors-alist (x)
  (and x ; else alist is nil
       (access warnings-as-errors x :alist)))


(defun set-warnings-as-errors-alist (strings flg alist
                                     uninhibited-warning-summaries)

; Note that this code is fine even in the presence of duplicates (up to case)
; in strings, or even a member of strings that is a key (up to case) in alist.
; We simply update the alist with the new, duplicate string while deleting the
; corresponding old key; so the final alist has keys that are duplicate-free up
; to case.

  (cond ((endp strings) alist)
        ((member-string-equal (car strings) uninhibited-warning-summaries)
         (er hard 'set-warnings-as-errors
             "It is illegal to specify that warnings of type ~x0 are to be ~
              converted to errors, because ~x0 is a member (up to case) of ~x1"
             (car strings)
             '*uninhibited-warning-summaries*))
        (t (set-warnings-as-errors-alist
            (cdr strings)
            flg
            (let ((pair (assoc-string-equal (car strings) alist)))
              (cond ((and (consp pair)
                          (eq (cdr pair) flg))
                     alist)
                    ((null pair)
                     (acons (car strings) flg alist))
                    (t
                     (acons (car strings)
                            flg
                            (remove1-assoc-string-equal (car strings)
                                                        alist)))))
            uninhibited-warning-summaries))))

(defun set-warnings-as-errors (flg strings state)

; If strings is :all then we reset to make that the default.

  (declare (xargs :guard (member-eq flg '(t nil :always))))
  (cond
   ((eq strings :all)
    (f-put-global 'warnings-as-errors
                  (make warnings-as-errors :default flg :alist nil)
                  state))
   ((string-listp strings)
    (let* ((old (f-get-global 'warnings-as-errors state))
           (default (warnings-as-errors-default old))
           (alist (warnings-as-errors-alist old)))
      (cond ((and (eq flg default)
                  (null (assoc-string-equal (car strings) alist)))
             state)
            (t (f-put-global 'warnings-as-errors
                             (if old
                                 (change warnings-as-errors
                                         old
                                         :alist
                                         (set-warnings-as-errors-alist
                                          strings flg alist
                                          *uninhibited-warning-summaries*))
                               (make warnings-as-errors
                                     :default nil
                                     :alist
                                     (set-warnings-as-errors-alist
                                      strings flg alist
                                      *uninhibited-warning-summaries*)))
                             state)))))
   (t (prog2$ (er hard 'set-warnings-as-errors
                  "Illegal second argument of ~x0, ~x1: must be :ALL or a ~
                   list of strings."
                  'set-warnings-as-errors
                  strings)
              state))))

(defun warning1-body (ctx summary str+ alist state)

; Str+ is either a string or a pair (str . raw-alist), where raw-alist is to be
; used in place of str and the input alist if we are in raw-warning-format
; mode.

  (let ((channel (f-get-global 'proofs-co state)))
    (pprogn
     (if summary
         (push-warning summary state)
       state)
     (cond
      ((f-get-global 'raw-warning-format state)
       (cond ((consp str+)
              (fms "~y0"
                   (list (cons #\0 (list :warning summary
                                         (cons (list :ctx ctx)
                                               (cdr str+)))))
                   channel state nil))
             (t
              (fms "(:WARNING ~x0~t1~y2)~%"
                   (list (cons #\0 summary)
                         (cons #\1 10) ; (length "(:WARNING ")
                         (cons #\2
                               (list (cons :ctx ctx)
                                     (cons :fmt-string str+)
                                     (cons :fmt-alist alist))))
                   channel state nil))))
      (t (let ((str (cond ((consp str+)
                           (assert$ (and (stringp (car str+))
                                         (alistp (cdr str+)))
                                    (car str+)))
                          (t str+))))
           (mv-let
             (col state)
             (fmt "ACL2 Warning~#0~[~/ [~s1]~]"
                  (list (cons #\0 (if summary 1 0))
                        (cons #\1 summary))
                  channel state nil)
             (mv-let (col state)
               (fmt-in-ctx ctx col channel state)
               (fmt-abbrev str alist col channel state "~%~%")))))))))

(defun warnings-as-errors-val-guard (summary warnings-as-errors)
  (declare (xargs :guard t))
  (and (or (null summary)
           (stringp summary))
       (or (null warnings-as-errors)
           (and (weak-warnings-as-errors-p warnings-as-errors)
                (string-alistp
                 (warnings-as-errors-alist warnings-as-errors))))))

(defun warnings-as-errors-val (summary warnings-as-errors)
  (declare (xargs :guard
                  (warnings-as-errors-val-guard summary warnings-as-errors)))
  (let* ((pair
          (and summary
               (assoc-string-equal summary (warnings-as-errors-alist
                                            warnings-as-errors))))
         (erp (if pair
                  (cdr pair)
                (warnings-as-errors-default warnings-as-errors))))
    (if (booleanp erp)
        erp
      :always)))

(defmacro warning1-form (commentp)

; See warning1.

  (declare (xargs :guard ; avoid capture
                  (not (or (eq commentp 'warnings-as-errors-val)
                           (eq commentp 'check-warning-off)
                           (eq commentp 'summary)))))
  `(mv-let (check-warning-off summary)
     (cond ((consp summary)
            (mv nil (car summary)))
           (t (mv t summary)))
     (let ((warnings-as-errors-val
            ,(if commentp
                 `(ec-call ; for guard verification of warning1-cw
                   (warnings-as-errors-val
                    summary
                    (access state-vars state-vars :warnings-as-errors)))
               `(warnings-as-errors-val
                 summary
                 (f-get-global 'warnings-as-errors state)))))
       (cond
        ((and (eq warnings-as-errors-val :always)
              (not (and summary
                        (member-string-equal
                         summary
                         *uninhibited-warning-summaries*))))
         (let ((str (cond ((consp str) ; see handling of str+ in warning1-body
                           (car str))
                          (t str))))

; We do not use io? here, because when commentp holds, io? makes a wormhole
; call that seems to avoid having the throw from hard-error go all the way to
; the top level.

           ,(cond
             (commentp
              `(and (not (ec-call ; for guard verification of warning1-cw
                          (member-equal 'error
                                        (access state-vars state-vars
                                                :inhibit-output-lst))))
                    (hard-error ctx (cons summary str) alist)))
             (t `(prog2$
                  (and (not (member-eq 'error
                                       (f-get-global 'inhibit-output-lst
                                                     state)))
                       (hard-error ctx (cons summary str) alist))
                  state)))))
        ((and check-warning-off
              (not (and summary
                        (member-string-equal
                         summary
                         *uninhibited-warning-summaries*)))
              ,(if commentp
                   '(or (ec-call ; for guard verification of warning1-cw
                         (member-equal 'warning
                                       (access state-vars state-vars
                                               :inhibit-output-lst)))
                        (warning-off-p1 summary
                                        wrld
                                        (access state-vars state-vars
                                                :ld-skip-proofsp)))
                 '(or (member-eq 'warning
                                 (f-get-global 'inhibit-output-lst state))
                      (warning-off-p summary state))))
         ,(if commentp nil 'state))
        ((and warnings-as-errors-val
              (not (and summary
                        (member-string-equal
                         summary
                         *uninhibited-warning-summaries*))))
         (let ((str (cond ((consp str) ; see handling of str+ in warning1-body
                           (car str))
                          (t str))))
; See comment above about not using io?.
           ,(cond
             (commentp
              `(and (not (ec-call ; for guard verification of warning1-cw
                          (member-equal 'error
                                        (access state-vars state-vars
                                                :inhibit-output-lst))))
                    (hard-error ctx (cons summary str) alist)))
             (t `(prog2$ (and (not (member-eq 'error
                                              (f-get-global 'inhibit-output-lst
                                                            state)))
                              (hard-error ctx (cons summary str) alist))
                         state)))))

; Note:  There are two io? expressions below.  They are just alike except
; that the first uses the token WARNING! and the other uses WARNING.  Keep
; them that way!

        ((and summary
              (member-string-equal summary *uninhibited-warning-summaries*))
         (io? WARNING! ,commentp state
              (summary ctx alist str)
              (warning1-body ctx summary str alist state)
              :chk-translatable nil))
        (t (io? WARNING ,commentp state
                (summary ctx alist str)
                (warning1-body ctx summary str alist state)
                :chk-translatable nil))))))

(defun warning1 (ctx summary str alist state)

; This function prints the "ACL2 Warning" banner and ctx, then the
; user's summary, str and alist, and then two carriage returns.

  (warning1-form nil))

(defmacro warning-disabled-p (summary)

; We can use this utility to avoid needless computation on behalf of disabled
; warnings.

  (declare (xargs :guard (stringp summary)))
  (let ((tp (if (member-equal summary *uninhibited-warning-summaries*)
                'warning!
              'warning)))
    `(and (or (output-ignored-p ',tp state)
              (warning-off-p ,summary state))

; Allow warning$ to be called even when it would normally be suppressed, if the
; warning is to be converted unconditionally to an error.

          (not (eq (warnings-as-errors-val
                    ,summary
                    (f-get-global 'warnings-as-errors state))
                   :always)))))

(defmacro er-soft (context summary str &rest str-args)
  (let ((alist (make-fmt-bindings *base-10-chars* str-args)))
    (list 'error1 context summary str alist 'state)))

#+acl2-par
(defmacro er-soft@par (context summary str &rest str-args)
  (let ((alist (make-fmt-bindings *base-10-chars* str-args)))
    (list 'error1@par context summary str alist 'state)))

(defmacro er-hard? (context summary str &rest str-args)
  (let ((alist (make-fmt-bindings *base-10-chars* str-args)))
    (list 'hard-error context (list 'cons summary str) alist)))

(defmacro er-hard (context summary str &rest str-args)
  (let ((alist (make-fmt-bindings *base-10-chars* str-args)))
    (list 'illegal context (list 'cons summary str) alist)))

(defmacro observation1-body (commentp)
  `(io? observation ,commentp state
        (str alist ctx abbrev-p)
        (let ((channel (f-get-global 'proofs-co state)))
          (mv-let
           (col state)
           (fmt "ACL2 Observation" nil channel state nil)
           (mv-let (col state)
                   (fmt-in-ctx ctx col channel state)
                   (cond (abbrev-p
                          (fmt-abbrev str alist col channel state "~|"))
                         ((null abbrev-p)
                          (mv-let (col state)
                                  (fmt1 str alist col channel state nil)
                                  (declare (ignore col))
                                  (newline channel state)))
                         (t
                          (prog2$ (er hard 'observation1
                                      "The abbrev-p (fourth) argument of ~
                                       observation1 must be t or nil, so the ~
                                       value ~x0 is illegal."
                                      abbrev-p)
                                  state))))))
        :chk-translatable nil))

(defun observation1 (ctx str alist abbrev-p state)


; This function prints the "ACL2 Observation" banner and ctx, then the
; user's str and alist, and then a carriage return.

  (observation1-body nil))

(defun observation1-cw (ctx str alist abbrev-p)
  (observation1-body t))

(defmacro observation (&rest args)

; A typical use of this macro might be:
; (observation ctx "5 :REWRITE rules are being stored under name ~x0." name).

  `(cond
    ((or (eq (ld-skip-proofsp state) 'include-book)
         (eq (ld-skip-proofsp state) 'include-book-with-locals)
         (eq (ld-skip-proofsp state) 'initialize-acl2))
     state)
    (t
     (observation1
      ,(car args)
      ,(cadr args)
      ,(make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                            #\5 #\6 #\7 #\8 #\9)
                          (cddr args))
      t
      state))))

(defmacro observation-cw (&rest args)

; See observation.  This macro uses wormholes to avoid modifying state, and
; prints even when including books.

  `(observation1-cw
    ,(car args)
    ,(cadr args)
    ,(make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                          #\5 #\6 #\7 #\8 #\9)
                        (cddr args))
    t))

; Start stobj support in raw Lisp

(defrec defstobj-field-template
  (((fieldp-name . type) . (init . length-name))
   (accessor-name . updater-name)
   (resize-name resizable . element-type)
   . other ; for a hash-table field
   )
  nil)

(defrec defstobj-template
  ((congruent-to . non-memoizable)
   (recognizer . creator)
   field-templates
   inline
   . non-executable)
  nil)

(defun packn1 (lst)
  (declare (xargs :guard (atom-listp lst)))
  (cond ((endp lst) nil)
        (t (append (explode-atom (car lst) 10)
                   (packn1 (cdr lst))))))

(defun packn-pos (lst witness)
  (declare (xargs :guard (and (atom-listp lst)
                              (symbolp witness))))
  (intern-in-package-of-symbol (coerce (packn1 lst) 'string)
                               witness))

(defun find-first-non-cl-symbol (lst)
  (declare (xargs :guard (atom-listp lst)))
  (cond ((endp lst) nil)
        ((and (symbolp (car lst))
              (not (equal (symbol-package-name (car lst))
                          "COMMON-LISP")))
         (car lst))
        (t (find-first-non-cl-symbol (cdr lst)))))

(defun packn (lst)
  (declare (xargs :guard (atom-listp lst)))

; This function produces a symbol which is named by concatenating string
; representations of the elements of lst, which may be any good atoms.  The
; package of the output symbol will be the package of the first symbol in the
; input list which is not in the "COMMON-LISP" package, or, if no such symbol
; exists, will be "ACL2".

; We treat the "COMMON-LISP" package as a special exception because in ACL2 we
; limit the usage of symbols in that package, for example by disallowing their
; use as function names.  We therefore prefer not to allow packn to create
; symbols in the "COMMON-LISP" package.  The function packn-pos may be called
; instead when it is desired to specify explicitly a package for the symbol.

  (packn-pos lst (or (find-first-non-cl-symbol lst)
                     'packn)))

(defun pack2 (n1 n2)
  (packn (list n1 n2)))

(defun defstobj-fnname-key2 (type)

; This function provides the value of the key2 argument of defstobj-fnname when
; it is not :top.

  (declare (xargs :guard t))
  (if (consp type)
      (case (car type)
        (array :array)
        (hash-table :hash-table)
        (stobj-table :stobj-table)
        (t :scalar))
    :scalar))

(defun doublet-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (equal x nil))
        (t (and (true-listp (car x))
                (eql (length (car x)) 2)
                (doublet-listp (cdr x))))))

(defun defstobj-fnname (root key1 key2 renaming-alist)

; Warning: Keep this in sync with stobj-updater-guess-from-accessor.

; This function generates the actual name we will use for a function generated
; by defstobj.  Root and renaming-alist are, respectively, a symbol and an
; alist.  Key1 describes which function name we are to generate (:length,
; :resize, :recognizer, etc.).  Key2 is irrelevant if key1 is :recognizer or
; :creator; often key is :top in those cases, though this is not necessary.
; Otherwise key2 describes the ``type'' of root. and is either :array,
; :hash-table, :stobj-table, or :scalar (see defstobj-fnname-key2).  Note that
; if renaming-alist is nil, then this function returns the ``default'' name
; used.  If renaming-alist pairs some default name with an illegal name, the
; result is, of course, an illegal name.

  (declare (xargs :guard (and (symbolp root)
                              (member-eq key1
                                         '(:recognizer
                                           :length :resize :accessor :updater
                                           :creator :boundp :accessor? :remove
                                           :count :clear :init))
                              (symbolp key2)
                              (doublet-listp renaming-alist))))
  (let* ((default-fnname
           (case key1
             (:recognizer
              (packn-pos (list root "P") root))

; This function can legitimately return nil for key1 values of :length
; and :resize.  We are careful in the assoc-eq call below not to look
; for nil on the renaming-alist.  That check is probably not
; necessary, but we include it for robustness.

             (:length
              (and (eq key2 :array)
                   (packn-pos (list root "-LENGTH") root)))
             (:resize
              (and (eq key2 :array)
                   (packn-pos (list "RESIZE-" root) root)))
             (:accessor
              (case key2
                (:array (packn-pos (list root "I") root))
                ((:hash-table :stobj-table)
                 (packn-pos (list root "-GET") root))
                (otherwise root)))
             (:updater
              (case key2
                (:array (packn-pos (list "UPDATE-" root "I") root))
                ((:hash-table :stobj-table)
                 (packn-pos (list root "-PUT") root))
                (otherwise (packn-pos (list "UPDATE-" root) root))))
             (:creator
              (packn-pos (list "CREATE-" root) root))
             (:boundp
              (and (or (eq key2 :hash-table)
                       (eq key2 :stobj-table))
                   (packn-pos (list root "-BOUNDP") root)))
             (:accessor?
              (and (eq key2 :hash-table)
                   (packn-pos (list root "-GET?") root)))
             (:remove
              (and (or (eq key2 :hash-table)
                       (eq key2 :stobj-table))
                   (packn-pos (list root "-REM") root)))
             (:count
              (and (or (eq key2 :hash-table)
                       (eq key2 :stobj-table))
                   (packn-pos (list root "-COUNT") root)))
             (:clear
              (and (or (eq key2 :hash-table)
                       (eq key2 :stobj-table))
                   (packn-pos (list root "-CLEAR") root)))
             (:init
              (and (or (eq key2 :hash-table)
                       (eq key2 :stobj-table))
                   (packn-pos (list root "-INIT") root)))
             (otherwise
              (er hard 'defstobj-fnname
                  "Implementation error (bad case); please contact the ACL2 ~
                   implementors."))))
         (temp (and default-fnname ; see comment above
                    (assoc-eq default-fnname renaming-alist))))
    (if temp (cadr temp) default-fnname)))

(defun defined-constant (name w)

; Name is a defined-constant if it has been declared with defconst.
; If name is a defined-constant then we can show that it satisfies
; legal-constantp, because when a name is declared as a constant we
; insist that it satisfy the syntactic check.  But there are
; legal-constantps that aren't defined-constants, e.g., any symbol
; that could be (but hasn't yet been) declared as a constant.  We
; check, below, that name is a symbolp just to guard the getprop.

; This function returns the quoted term that is the value of name, if
; name is a constant.  That result is always non-nil (it may be (quote
; nil) of course).

  (and (symbolp name)
       (getpropc name 'const nil w)))

(defun fix-stobj-array-type (type wrld)

; Keep in sync with fix-stobj-hash-table-type and fix-stobj-table-type.

; Note: Wrld may be a world or nil.  If wrld is nil and we are in raw Lisp,
; then this function should be called in a context where the symbol-value is
; available for any symbol introduced by a previous defconst event.  Our
; intended use case meets that criterion: evaluation of a defstobj form during
; loading of the compiled file for a book.

; Note that the values in the #-acl2-loop-only and #+acl2-loop-only cases are
; different, but that's OK since this function will never be converted to logic
; mode.  See :DOC program-only.

  (let* ((max (car (caddr type)))
         (n (cond ((consp wrld)
                   (let ((qc (defined-constant max wrld)))
                     (and qc (unquote qc))))
                  (t
                   #-acl2-loop-only
                   (assert$ (eq wrld nil)
                            (and (symbolp max)
                                 (symbol-value max)))
                   #+acl2-loop-only
                   (er hard 'fix-stobj-array-type
                       "Implementation error: Attempted to get logical result ~
                        for fix-stobj-array-type when the world is empty.")))))
    (cond (n (list (car type)
                   (cadr type)
                   (list n)))
          (t type))))

(defun fix-stobj-hash-table-type (type wrld)

; This function is analogous to fix-stobj-array-type; see comments there, and
; keep in sync with fix-stobj-array-type and fix-stobj-table-type.

  (cond
   ((null (cddr type)) ; (HASH-TABLE test)
    type)
   (t ; (HASH-TABLE test size) or (HASH-TABLE test size type-indicator)
    (let* ((size0 (caddr type))
           (size (cond ((consp wrld)
                        (let ((qc (defined-constant size0 wrld)))
                          (and qc (unquote qc))))
                       (t
                        #-acl2-loop-only
                        (assert$ (eq wrld nil)
                                 (and size0
                                      (symbolp size0)
                                      (symbol-value size0)))
                        #+acl2-loop-only
                        (er hard 'fix-stobj-hash-table-type
                            "Implementation error: Attempted to get logical ~
                             result for fix-stobj-hash-table-type when the ~
                             world is empty.")))))
      (cond (size (list* (car type)
                         (cadr type)
                         size
                         (cdddr type)))
            (t type))))))

(defun fix-stobj-table-type (type wrld)

; This function is analogous to fix-stobj-array-type; see comments there, and
; keep in sync with fix-stobj-array-type and fix-stobj-hash-table-type.

  (cond
   ((null (cdr type)) ; (STOBJ-TABLE)
    type)
   (t ; (STOBJ-TABLE size)
    (let* ((size0 (cadr type))
           (size (cond ((consp wrld)
                        (let ((qc (defined-constant size0 wrld)))
                          (and qc (unquote qc))))
                       (t
                        #-acl2-loop-only
                        (assert$ (eq wrld nil)
                                 (and size0
                                      (symbolp size0)
                                      (symbol-value size0)))
                        #+acl2-loop-only
                        (er hard 'fix-stobj-hash-table-type
                            "Implementation error: Attempted to get logical ~
                             result for fix-stobj-table-type when the world ~
                             is empty.")))))
      (cond (size (list* (car type)
                         size
                         (cddr type)))
            (t type))))))

(defun defstobj-field-templates (field-descriptors renaming wrld)

; Note: Wrld may be a world or nil.  See fix-stobj-array-type.

  (cond
   ((endp field-descriptors) nil)
   (t
    (let* ((field-desc (car field-descriptors))
           (field (if (atom field-desc)
                      field-desc
                    (car field-desc)))
           (type (if (consp field-desc)
                     (or (cadr (assoc-keyword :type (cdr field-desc)))
                         t)
                   t))
           (element-type (if (consp field-desc)
                             (cadr (assoc-keyword :element-type
                                                  (cdr field-desc)))
                           nil))
           (init (if (consp field-desc)
                     (cadr (assoc-keyword :initially (cdr field-desc)))
                   nil))
           (resizable (if (consp field-desc)
                          (cadr (assoc-keyword :resizable (cdr field-desc)))
                        nil))
           (key2 (defstobj-fnname-key2 type))
           (fieldp-name (defstobj-fnname field :recognizer key2 renaming))
           (accessor-name (defstobj-fnname field :accessor key2 renaming))
           (updater-name (defstobj-fnname field :updater key2 renaming))
           (boundp-name (defstobj-fnname field :boundp key2 renaming))
           (accessor?-name (defstobj-fnname field :accessor? key2
                             renaming))
           (remove-name (defstobj-fnname field :remove key2 renaming))
           (count-name (defstobj-fnname field :count key2 renaming))
           (clear-name (defstobj-fnname field :clear key2 renaming))
           (init-name (defstobj-fnname field :init key2 renaming))
           (resize-name (defstobj-fnname field :resize key2 renaming))
           (length-name (defstobj-fnname field :length key2 renaming)))
      (cons (make defstobj-field-template
                  :fieldp-name fieldp-name
                  :type (cond ((and (consp type)
                                    (eq (car type) 'array))
                               (fix-stobj-array-type type wrld))
                              ((and (consp type)
                                    (eq (car type) 'hash-table))
                               (fix-stobj-hash-table-type type wrld))
                              ((and (consp type)
                                    (eq (car type) 'stobj-table))
                               (fix-stobj-table-type type wrld))
                              (t type))
                  :init init
                  :accessor-name accessor-name
                  :updater-name updater-name
                  :length-name length-name
                  :resize-name resize-name
                  :resizable resizable
                  :element-type element-type
                  :other
                  (list boundp-name
                        accessor?-name
                        remove-name
                        count-name
                        clear-name
                        init-name))
            (defstobj-field-templates
              (cdr field-descriptors) renaming wrld))))))

(defconst *defstobj-keywords*
  '(:renaming :inline :congruent-to :non-memoizable :non-executable))

; The following function is used to implement a slightly generalized
; form of macro args, namely one in which we can provide an arbitrary
; number of ordinary arguments terminated by an arbitrary number of
; keyword argument pairs.

(defun partition-rest-and-keyword-args1 (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) (mv nil nil))
        ((keywordp (car x))
         (mv nil x))
        (t (mv-let (rest keypart)
                   (partition-rest-and-keyword-args1 (cdr x))
                   (mv (cons (car x) rest)
                       keypart)))))

(defun partition-rest-and-keyword-args2 (keypart keys alist)

; We return t if keypart is ill-formed as noted below.  Otherwise, we
; return ((:keyn . vn) ... (:key1 . v1)).

  (declare (xargs :guard (and (true-listp keypart)
                              (true-listp keys)
                              (alistp alist))))
  (cond ((endp keypart) alist)
        ((and (keywordp (car keypart))
              (consp (cdr keypart))
              (not (assoc-eq (car keypart) alist))
              (member (car keypart) keys))
         (partition-rest-and-keyword-args2 (cddr keypart)
                                           keys
                                           (cons (cons (car keypart)
                                                       (cadr keypart))
                                                 alist)))
        (t t)))

(defun partition-rest-and-keyword-args (x keys)

; X is assumed to be a list of the form (a1 ... an :key1 v1 ... :keyk
; vk), where no ai is a keyword.  We return (mv erp rest alist), where
; erp is t iff the keyword section of x is ill-formed.  When erp is
; nil, rest is '(a1 ... an) and alist is '((:key1 . v1) ... (:keyk
; . vk)).

; The keyword section is ill-formed if it contains a non-keyword in an
; even numbered element, if it binds the same keyword more than once,
; or if it binds a keyword other than those listed in keys.

  (declare (xargs :guard (and (true-listp x)
                              (true-listp keys))))
  (mv-let (rest keypart)
          (partition-rest-and-keyword-args1 x)
          (let ((alist (partition-rest-and-keyword-args2 keypart keys nil)))
            (cond
             ((eq alist t) (mv t nil nil))
             (t (mv nil rest alist))))))

(defun defstobj-template (name args wrld)

; Note: Wrld may be a world or nil.  See fix-stobj-array-type.

; We unpack the args to get the renamed field descriptors.  We return a
; defstobj-template with fields (namep create-name fields inline congruent-to),
; where: namep is the name of the recognizer for the single-threaded object;
; create-name is the name of the constructor for the stobj; fields is a list
; corresponding to the field descriptors, but normalized with respect to the
; renaming, types, etc.; inline is t if :inline t was specified in the defstobj
; event, else nil; and congruent-to is the :congruent-to field of the defstobj
; event (default: nil).  A field in fields is of the form (recog-name type init
; accessor-name updater-name length-name resize-name resizable).  The last
; three fields are nil unless type has the form (ARRAY ptype (n)), in which
; case ptype is a primitive type and n is a positive integer.  Init is the evg
; of a constant term, i.e., should be quoted to be treated as a term.

  (mv-let
   (erp field-descriptors key-alist)
   (partition-rest-and-keyword-args args *defstobj-keywords*)
   (cond
    (erp

; If the defstobj has been admitted, this won't happen.

     (er hard 'defstobj
         "The keyword arguments to the DEFSTOBJ event must appear ~
          after all field descriptors.  The allowed keyword ~
          arguments are ~&0, and these may not be duplicated.  Thus, ~
          ~x1 is ill-formed."
         *defstobj-keywords*
         (list* 'defstobj name args)))
    (t
     (let ((renaming (cdr (assoc-eq :renaming key-alist)))
           (inline (cdr (assoc-eq :inline key-alist)))
           (congruent-to (cdr (assoc-eq :congruent-to key-alist)))
           (non-memoizable (cdr (assoc-eq :non-memoizable key-alist)))
           (non-executable (cdr (assoc-eq :non-executable key-alist))))
       (make defstobj-template
             :recognizer (defstobj-fnname name :recognizer :top renaming)
             :creator (defstobj-fnname name :creator :top renaming)
             :field-templates (defstobj-field-templates
                                field-descriptors renaming wrld)
             :non-memoizable non-memoizable
             :non-executable non-executable
             :inline inline
             :congruent-to congruent-to))))))

(defun simple-array-type (array-etype dimensions)
  (declare (ignore dimensions))
  (cond
   ((eq array-etype t)
    `(simple-vector *))
   ((eq array-etype '*)
    (er hard 'simple-array-type
        "Implementation error: We had thought that * is an invalid type-spec! ~
         ~ Please contact the ACL2 implementors."))
   (t `(simple-array ,array-etype (*)))))

#-acl2-loop-only
(defun-one-output copy-array-aref (a1 a2 i n)
  (declare (type fixnum i n))

; Copy the first n elements of array a1 into array a2, starting with index i,
; and then return a2.  See also copy-array-svref and copy-array-fix-aref.
; Note that this copying does not copy substructures, so in the case that a1 is
; an array of stobjs, if 0 <= i < n then the ith element of a1 will be EQ to
; the ith element of a2 after the copy is complete.

; Addition of (type simple-array a1 a2) to the declare form did not affect the
; output of disassemble in either CCL or SBCL.  So it seems best not to
; consider whether a1 and a2 must be simple-arrays.

  (cond
   ((>= i n) a2)
   (t (setf (aref a2 i)
            (aref a1 i))
      (copy-array-aref a1 a2
                       (the fixnum (1+ i))
                       n))))

#-acl2-loop-only
(defun-one-output copy-array-svref (a1 a2 i n)
  (declare (type fixnum i n)
           (type simple-vector a1 a2))

; This is a variant of copy-array-aref for simple vectors a1 and a2.

  (cond
   ((>= i n) a2)
   (t (setf (svref a2 i)
            (svref a1 i))
      (copy-array-svref a1 a2
                        (the fixnum (1+ i))
                        n))))

#-acl2-loop-only
(defun-one-output copy-array-fix-aref (a1 a2 i n)
  (declare (type fixnum i n)
           (type (simple-array fixnum (*)) a1 a2))

; This is a variant of copy-array-aref for arrays of fixnums a1 and a2.  We
; need this special version to avoid fixnum boxing in GCL during resizing.

  (cond
   ((>= i n) a2)
   (t (setf (aref a2 i)
            (aref a1 i))
      (copy-array-fix-aref a1 a2
                           (the fixnum (1+ i))
                           n))))

; In raw Lisp, the live version of state is held in the constant
; *the-live-state* (whose value is actually just a symbol because we don't
; really represent the live state as an object).  But what is the live version
; of a user-defined stobj?  See the raw lisp variable *user-stobj-alist*.

(defmacro live-stobjp (name)

; Note that unlike the raw Lisp representation of a stobj, no ordinary ACL2
; object is a vector, unless it is a string; nor is any ordinary ACL2 object a
; hash table (unlike the raw Lisp representation of a single-field stobj whose
; field is a hash table).

  `(or (and (typep ,name 'vector)
            (not (stringp ,name)))
       (typep ,name 'hash-table)))

(defun absstobj-name (name type)

; Warning: The (absstobj-name name :CREATOR) should equal (defstobj-fnname name
; :CREATOR :TOP nil), because of the use of the latter in
; parse-with-local-stobj.

  (declare (type symbol name type))
  (mv-let (prefix suffix)
          (case type
            (:A (mv nil "$A")) ; abstract
            (:C (mv nil "$C")) ; concrete (really, foundation)
            (:CREATOR (mv "CREATE-" nil))
            (:RECOGNIZER (mv nil "P"))
            (:RECOGNIZER-LOGIC (mv nil "$AP"))
            (:RECOGNIZER-EXEC (mv nil "$CP"))
            (:CORR-FN (mv nil "$CORR"))
            (:CORRESPONDENCE (mv nil "{CORRESPONDENCE}"))
            (:PRESERVED (mv nil "{PRESERVED}"))
            (:GUARD-THM (mv nil "{GUARD-THM}"))
            (otherwise (mv (er hard 'absstobj-name
                               "Unrecognized type, ~x0."
                               type)
                           nil)))
          (let* ((s (symbol-name name))
                 (s (if prefix (concatenate 'string prefix s) s))
                 (s (if suffix (concatenate 'string s suffix) s)))
            (intern-in-package-of-symbol s name))))

(defrec defstobj-redundant-raw-lisp-discriminator-value

; This record is used both for defstobj and defabsstobj events.

; The first field, :event, completely determines the other fields.  We store
; those for convenience.  Note that since the :event determines the other
; fields, all fields are based on the original event: the possibility of an
; attached stobj is not considered in populating these fields.

  ((event recognizer . creator)
   .
   (congruent-stobj-rep non-memoizable . non-executable))
  nil)

(defrec stobj-property
  ((recognizer . creator)
   names ; accessors and updaters
   . live-var)
  nil)

(defun get-stobj-creator (stobj wrld)

; This function assumes that wrld is an ACL2 logical world, although wrld may
; be nil when we call this in raw Lisp.

; If stobj is a stobj name, return the name of its creator; else nil.

  (cond ((eq stobj 'state) 'state-p)
        ((not (symbolp stobj)) nil)
        (wrld (let ((prop (getpropc stobj 'stobj nil wrld)))
                (and prop
                     (access stobj-property prop :creator))))
        (t
         #-acl2-loop-only
         (let ((d (get (the-live-var stobj)
                       'redundant-raw-lisp-discriminator)))
           (cond ((member-eq (car d) '(defstobj defabsstobj))
                  (access defstobj-redundant-raw-lisp-discriminator-value
                          (cdr d)
                          :creator))
                 (t nil)))
         #+acl2-loop-only
         (er hard 'stobj-creator
             "Implementation error: The call ~x0 is illegal, because ~
              get-stobj-creator must not be called inside the ACL2 loop (as ~
              is the case here) with wrld = nil."
             `(get-stobj-creator ,stobj nil)))))

(defmacro the$ (type val)
  (cond ((eq type t)
         val)
        (t `(the ,type ,val))))

#-acl2-loop-only
(defun make-hash-table-with-defaults (test size rehash-size rehash-threshold)

; We leave it to the underlying Lisp implementation to provide the size,
; rehash-size, and rehash-threshold in place of nil.  The test is required to
; be non-nil, and in fact, is required to have value EQ, EQL, HONS-EQUAL, or
; EQUAL.  Note that stobj hash tables with test HONS-EQUAL are actually EQL
; hash tables in the HONS version of ACL2.

; In CCL the relevant defaults appear to be:
; (:SIZE 60 :REHASH-SIZE 1.5 :REHASH-THRESHOLD 0.85)

; In SBCL the relevant defaults appear to be:
; (:SIZE 16 :REHASH-SIZE 1.5 :REHASH-THRESHOLD 1.0)

  (apply 'make-hash-table
         `(:test ,(if (eq test 'hons-equal) 'eql test)
           ,@(and size `(:size

; The GCL implementation installed at UT CS on 9/16/2020 does not allow
; hash tables of size 0.

                         ,(if (= size 0) 1 size)))
           ,@(and rehash-size `(:rehash-size ,(float rehash-size)))
           ,@(and rehash-threshold `(:rehash-threshold ,(float rehash-threshold))))))

(defmacro get-stobj-scalar-field (elt-type fld)

; Warning: Keep this in sync with make-stobj-scalar-field.

; Through Version_8.2, a scalar field of a stobj with non-trivial type was
; represented as a 1-element array of that type.  This presumably had the
; advantage of avoiding fixnum boxing in GCL for types contained in fixnum.  We
; thus preserve this approach for GCL, but for other Lisps (which presumably do
; not do GCL-style boxing) we avoid the extra indirection through the
; one-element array.

  #+gcl
  `(aref (the (simple-array ,elt-type (1))
              ,fld)
         0)
  #-gcl
  `(the ,elt-type ,fld))

(defmacro make-stobj-scalar-field (elt-type init)

; Warning: Keep this in sync with get-stobj-scalar-field.  See the comments
; there.

  #+gcl
  `(make-array$ 1
                :element-type ',elt-type
                :initial-element ,init)
  #-gcl
  `(the ,elt-type ,init))

(mutual-recursion

(defun maybe-contained-in-character (type)
  (cond ((atom type)
         (or (eq type 'character)
             (eq type 'standard-char)

; We probably don't need to consider 'nil, since no element can have that
; type.  But we have decided to be conservative here.

             (eq type 'nil)))
        ((eq (car type) 'and)
         (some-maybe-contained-in-character (cdr type)))
        ((eq (car type) 'member)

; In GCL, an array type whose elements are, for example, of type (member #\a
; #\b #\c) can be a string.

         (character-listp (cdr type)))
        ((eq (car type) 'not)

; Probably every type-spec of the form (not ...) fails to be contained in
; character.  But we are conservative here and only make that conclusion for
; (not x) where x is an atom.

         (consp (cadr type)))
        ((eq (car type) 'satisfies)

; In GCL, an array type whose elements are of type (satisfies character) can be
; a string.  Since the predicate could be an alias for character, or a subtype
; of character, we are conservative here.

         t)
        ((eq (car type) 'or)
         (all-maybe-contained-in-character (cdr type)))
        (t nil)))

(defun some-maybe-contained-in-character (lst)
  (cond ((endp lst) nil)
        (t (or (maybe-contained-in-character (car lst))
               (some-maybe-contained-in-character (cdr lst))))))

(defun all-maybe-contained-in-character (lst)
  (cond ((endp lst) t)
        (t (and (maybe-contained-in-character (car lst))
                (all-maybe-contained-in-character (cdr lst))))))
)

(defun single-field-type-p (type)

; Normally, when a stobj has a single field which is either an array or a hash
; table, the "backbone" of the stobj is omitted, avoiding one level of
; indirection: in other words, the stobj *is* its field.  However, in the case
; of an array whose type specifies elements that are characters, that array may
; be a string (depending on the host Lisp and exactly how the type is
; specified), which is problematic since the utility live-stobjp depends on
; live stobjs not being strings.  See community book
; books/system/tests/stobj-issues.lisp.  Here, we check whether we can safely
; give the special "single-field" treatment of avoiding the "backbone", based
; on the type of the single field, returning t only if that is indeed safe.

  (and (consp type)
       (cond ((eq (car type) 'array)
              (not (maybe-contained-in-character (cadr type))))
             ((or (eq (car type) 'hash-table)
                  (eq (car type) 'stobj-table))
              t)
             (t nil))))

#-acl2-loop-only
(defg *current-stobj-gensym-ht*
  (make-hash-table :test 'eq))

#-acl2-loop-only
(defun current-stobj-gensym (name)

; This function returns an interned symbol that is a stand-in for name, to use
; as a hash-table key.  It will be replaced in *current-stobj-gensym-ht*
; whenever we undo a defstobj or defabsstobj for name.  The prefix "current"
; emphasizes that this table associates only currently-defined stobjs with
; hash-table keys.  When a stobj is undone then its name is removed as a key
; in *current-stobj-gensym-ht*; see maybe-push-undo-stack.

  (declare (type symbol name))
  (let* ((ht *current-stobj-gensym-ht*)
         (val (gethash name ht)))
    (declare (type hash-table ht))
    (or val
        (if (stobjp name t (w *the-live-state*))
            (setf (gethash name ht)
                  (acl2-gentemp (symbol-name name)))
          (error "Attempted to access a stobj-table entry for ~s,~%which is ~
                  not currently the name of a stobj."
                 name)))))

#-acl2-loop-only
(defun clean-stobj-table (ht)

; Returns the number of keys removed.

  (declare (type hash-table ht))
  (let ((valid-keys nil))
    (maphash (lambda (stobj sym)
               (declare (ignore stobj))
               (push sym valid-keys))
             (the hash-table *current-stobj-gensym-ht*))
    (let ((bad-keys nil))
      (maphash (lambda (sym stobj)
                 (declare (ignore stobj))
                 (when (not (member-eq sym valid-keys))
                   (push sym bad-keys)))
               ht)
      (loop for sym in bad-keys
            do
            (remhash sym ht))
      (length bad-keys))))

(defmacro stobj-hash-table-test (type)
  `(cadr ,type))

(defmacro stobj-hash-table-init-size (type)
  `(caddr ,type))

(defmacro stobj-hash-table-element-type (type)
  `(or (cadddr ,type) t))

#+(and ccl (not acl2-loop-only))
(defvar *ccl-issue-446*

; This variable is true when CCL Issue #446 is unresolved in the current
; CCL-based ACL2.  It is based on (deftest ccl.issue#446 ...) in:
; https://github.com/Clozure/ccl-tests/blob/5957b07b93a988099866b69d591990fb016f038a/ansi-tests/ccl.lsp

  (let ((ar (make-array 10 :element-type '(signed-byte 63) :initial-element 0)))
    (setf (aref ar 0) #x-7FFFFFFE47AFEF96)
    (not (= #x-7FFFFFFE47AFEF96
            (aref (the (simple-array (signed-byte 64) (10))
                       ar)
                  0)))))

(defun defstobj-field-fns-raw-defs (var flush-var inline n field-templates)

; Warning:  See the guard remarks in the Essay on Defstobj Definitions.

  (cond
   ((endp field-templates) nil)
   (t
    (append
     (let* ((field-template (car field-templates))
            (type (access defstobj-field-template field-template :type))
            (init (access defstobj-field-template field-template :init))
            (arrayp (and (consp type) (eq (car type) 'array)))
            (hashp (and (consp type) (eq (car type) 'hash-table)))
            (etype0 (cond (arrayp (cadr type))
                          (hashp (stobj-hash-table-element-type type))
                          (t nil)))
            (stobj-tablep (and (consp type) (eq (car type) 'stobj-table)))
            (hash-test (if hashp
                           (stobj-hash-table-test type)
                         (and stobj-tablep 'eq)))
            (single-fieldp

; Warning: Keep this in sync with the binding of single-fieldp in
; defstobj-raw-init.

; We avoid some indirection by arranging that when there is a single field that
; is an array, hash-table, or stobj-table, the stobj is the entire structure.
; If that changes, for example to keep indirection for hash tables, then
; consider changing the definition of live-stobjp.

             (and (= n 0)
                  (null (cdr field-templates))
                  (single-field-type-p type)))
            (fld (if single-fieldp
                     var
                   `(svref ,var ,n)))
            (stobj-creator
             (get-stobj-creator (if (or arrayp hashp)
                                    etype0
                                  type)
                                nil))
            (scalar-type ; used only when arrayp = hashp = stobj-tablep = nil
             (if stobj-creator t type))
            (array-etype (and arrayp
                              (if stobj-creator

; Stobj-creator is non-nil when array-etype is a stobj.  The real element type,
; then, is simple-array rather than a simple-array-type, so we might say that
; the parent stobj array is not simple.  But we will assume that the advantage
; of having a simple-vector for the parent stobj outweighs the advantage of
; having a simple-vector element type declaration.

                                  t
                                (or (access defstobj-field-template
                                            field-template
                                            :element-type)
                                    etype0))))
            (simple-type (and arrayp
                              (simple-array-type array-etype (caddr type))))
            (array-length (and arrayp (car (caddr type))))
            (vref (and arrayp
                       (if (eq (car simple-type) 'simple-vector)
                           'svref
                         'aref)))
            (accessor-name (access defstobj-field-template
                                   field-template
                                   :accessor-name))
            (updater-name (access defstobj-field-template
                                  field-template
                                  :updater-name))
            (length-name (access defstobj-field-template
                                 field-template
                                 :length-name))
            (resize-name (access defstobj-field-template
                                 field-template
                                 :resize-name))
            (resizable (access defstobj-field-template
                               field-template
                               :resizable))
            (other (access defstobj-field-template
                           field-template
                           :other))
            (boundp-name (nth 0 other))
            (accessor?-name (nth 1 other))
            (remove-name (nth 2 other))
            (count-name (nth 3 other))
            (clear-name (nth 4 other))
            (init-name (nth 5 other)))
       (cond
        ((or hashp stobj-tablep)
         (let ((key (if stobj-tablep
                        '(current-stobj-gensym k)
                      (if (eq hash-test 'hons-equal)
                          '(hons-copy k)
                        'k))))
           `((,accessor-name
              ,@(cond ((and hashp
                            (null init)
                            (not stobj-creator))
                       `((k ,var)
                         ,@(and inline (list *stobj-inline-declare*))
                         (values (gethash ,key (the hash-table ,fld)))))
                      (t
                       `((k ,var
; We use v for the default, since we know that v is not ,var.
                            ,@(and stobj-tablep '(v)))
                         ,@(and inline (list *stobj-inline-declare*))
                         (multiple-value-bind
                          (val boundp)
                          (gethash ,key (the hash-table ,fld))
                          (if boundp
                              val
; Keep the following in sync with the accessor?-name case below.
                            ,(cond (stobj-creator
                                    (assert$ hashp `(,stobj-creator)))
                                   (init
                                    (assert$
                                     hashp
                                     (if (eq etype0 'double-float)

; For efficiency, it would be nice to write `(quote ,(to-df init)), to avoid
; re-evaluating to-df each time there's a hash-table miss.  However, to-df is
; not yet defined in the boot-strap.  It doesn't seem important enough to deal
; with this issue in general, but init is probably often 0 so we optimize for
; that case.

                                         (if (eql init 0)
                                             '(df0)
                                           `(to-df (quote ,init)))
                                       `(quote ,init))))
                                   (t
                                    (assert$ stobj-tablep 'v)))))))))
             (,updater-name
              (k v ,var)
              ,@(and inline (list *stobj-inline-declare*))
              (progn
                (memoize-flush ,var)
                (setf (gethash ,key (the hash-table ,fld))
                      v)
                ,var))
             (,boundp-name
              (k ,var)
              ,@(and inline (list *stobj-inline-declare*))
              (multiple-value-bind (val boundp)
                                   (gethash ,key (the hash-table ,fld))
                                   (declare (ignore val))
                                   (if boundp t nil)))
             ,@(and hashp ; skip this for a stobj-table
; Keep the following in sync with the accessor-name case above.
                    `((,accessor?-name
                       (k ,var)
                       ,@(and inline (list *stobj-inline-declare*))
                       (multiple-value-bind
                        (val boundp)
                        (gethash ,key (the hash-table ,fld))
                        (if boundp
                            (mv val t)
                          (mv ,(cond (stobj-creator `(,stobj-creator))
                                     (init `(quote ,init))
                                     (t nil))
                              nil))))))
             (,remove-name
              (k ,var)
              ,@(and inline (list *stobj-inline-declare*))
              (progn
                #-acl2-loop-only
                (memoize-flush ,var)
                (remhash ,key (the hash-table ,fld))
                ,var))
             (,count-name
              (,var)
              ,@(and inline (list *stobj-inline-declare*))
              (progn ,@(and stobj-tablep
                            `((clean-stobj-table
                               (the hash-table ,fld))))
                     (hash-table-count (the hash-table ,fld))))
             (,clear-name
              (,var)
              (progn
                #-acl2-loop-only
                (memoize-flush ,var)
                (clrhash (the hash-table ,fld))
                ,@(and (not single-fieldp)
                       (list var))))
             (,init-name
              (ht-size rehash-size rehash-threshold ,var)
              (progn
                #-acl2-loop-only
                (memoize-flush ,var)
                (setf ,fld
                      (make-hash-table-with-defaults ',hash-test
                                                     ht-size
                                                     rehash-size
                                                     rehash-threshold))
                ,@(and (not single-fieldp)
                       (list var)))))))
        (arrayp
         `((,length-name
            (,var)
            ,@(and inline (list *stobj-inline-declare*))
            ,@(if (not resizable)
                  `((declare (ignore ,var))
                    ,array-length)
                `((the (and fixnum (integer 0 *))
                       (length ,fld)))))
           (,resize-name
            (i ,var)
            ,@(if (not resizable)
                  `((declare (ignore i))
                    (prog2$
                     (er hard ',resize-name
                         "The array field corresponding to accessor ~x0 of ~
                          stobj ~x1 was not declared :resizable t.  ~
                          Therefore, it is illegal to resize this array."
                         ',accessor-name
                         ',var)
                     ,var))
                `((if (not (and (integerp i)
                                (>= i 0)
                                (< i array-dimension-limit)))
                      (hard-error
                       ',resize-name
                       "Attempted array resize failed because the requested ~
                        size ~x0 was not a nonnegative integer less than the ~
                        value of Common Lisp constant array-dimension-limit, ~
                        which is ~x1.  These bounds on array sizes are fixed ~
                        by ACL2."
                       (list (cons #\0 i)
                             (cons #\1 array-dimension-limit)))
                    (let* ((var ,var)
                           (old ,(if single-fieldp
                                     'var
                                   `(svref var ,n)))
                           (min-index (min i (length old)))
                           (new (make-array$ i

; The :initial-element below is probably not necessary in the case
; that we are downsizing the array.  At least, CLtL2 does not make any
; requirements about specifying an :initial-element, even when an
; :element-type is supplied.  However, it seems harmless enough to go
; ahead and specify :initial-element even for downsizing: resizing is
; not expected to be fast, we save a case split here (at the expense
; of this comment!), and besides, we are protecting against the
; possibility that some Common Lisp will fail to respect the spec and
; will cause an error by trying to initialize a fixnum array (say)
; with NILs.

                                             :initial-element
                                             ,(if (and (eq etype0
                                                           'double-float)
                                                       (dfp init))
                                                  `(to-df ,init)
                                                `',init)
                                             :element-type
                                             ',array-etype)))
                      (memoize-flush ,flush-var)
                      (prog1 (setf ,(if single-fieldp
                                        'var
                                      `(svref var ,n))
                                   (,(pack2 'copy-array- vref)
                                    old new 0 min-index))
                        ,@(and stobj-creator
                               `((when (< (length old) i)
                                   (loop for j from (length old) to (1- i)
                                         do (setf (svref new j)
                                                  (,stobj-creator)))))))
                      ,@(and (not single-fieldp)
                             '(var)))))))
           (,accessor-name
            (i ,var)
            (declare (type (and fixnum (integer 0 *)) i))
            ,@(and inline (list *stobj-inline-declare*))
            (the$ ,array-etype
                  ,(let ((type1

; Here is a workaround for CCL bug #446
; (https://github.com/Clozure/ccl/issues/446).  We need #-acl2-loop-only
; because subtypep isn't defined in ACL2.  It might not be difficult to define
; it, at least for current purposes, but ideally CCL will be fixed soon and
; this hack can be retired.  When that happens, also remove
; defstobj-field-fns-raw-defs from *initial-program-fns-with-raw-code*.

                          #+(and ccl (not acl2-loop-only))
                          (if (and simple-type
                                   *ccl-issue-446*
                                   (subtypep array-etype 'integer)
                                   (not (subtypep array-etype 'fixnum))
                                   (not (subtypep array-etype '(integer 0 *))))
                              `(simple-array * ,(caddr type))
                            simple-type)
                          #-(and ccl (not acl2-loop-only))
                          simple-type))
                     `(,vref (the ,type1 ,fld)
                             (the (and fixnum (integer 0 *)) i)))))
           (,updater-name
            (i v ,var)
            (declare (type (and fixnum (integer 0 *)) i)
                     ,@(and (not (eq array-etype t))
                            `((type ,array-etype v))))
            ,@(and inline (list *stobj-inline-declare*))
            (progn
              (memoize-flush ,flush-var)

; See the long comment below for the updater in the scalar case, about
; supporting *1* functions.

              (setf (,vref ,(if (eq simple-type t)
                                fld
                              `(the ,simple-type ,fld))
                           (the (and fixnum (integer 0 *)) i))
                    (the$ ,array-etype v))
              ,var))))
        ((eq scalar-type t)
         `((,accessor-name (,var)
                           ,@(and inline (list *stobj-inline-declare*))
                           ,fld)
           (,updater-name (v ,var)
                          ,@(and inline (list *stobj-inline-declare*))
                          (progn
                            (memoize-flush ,flush-var)

; For the case of a stobj field, we considered causing an error here since the
; raw Lisp code for stobj-let avoids calling updaters because there is no need:
; updates for fields that are stobjs have already updated destructively.
; However, a raw Lisp updater can be called by a *1* function, say *1*f,
; applied to live stobjs, when guard checking does not pass control to the raw
; Lisp function, f.  Perhaps we could optimize to avoid this, but there is no
; need; this setf is fast and is only called on behalf of executing *1*
; function calls.  See the comment referencing "defstobj-field-fns-raw-defs" in
; community book misc/nested-stobj-tests.lisp.  To see this point in action,
; evaluate the forms under that comment after modifying this definition by
; uncommenting the following line of code.

;                           ,@(when stobj-creator '((break$))) ; see just above

                            (setf ,fld v)
                            ,var))))
        (t
         (assert$
          (not stobj-creator) ; scalar-type is t for stobj-creator
          `((,accessor-name (,var)
                            ,@(and inline (list *stobj-inline-declare*))
                            (the$ ,scalar-type
                                  (get-stobj-scalar-field ,scalar-type ,fld)))
            (,updater-name (v ,var)
                           ,@(and (not (eq scalar-type t))
                                  `((declare (type ,scalar-type v))))
                           ,@(and inline (list *stobj-inline-declare*))
                           (progn
                             (memoize-flush ,flush-var)
                             (setf (get-stobj-scalar-field ,scalar-type ,fld)
                                   (the$ ,scalar-type v))
                             ,var)))))))
     (defstobj-field-fns-raw-defs
       var flush-var inline (1+ n) (cdr field-templates))))))

(defun defstobj-raw-init-fields (field-templates)

; Keep this in sync with defstobj-axiomatic-init-fields.

  (cond
   ((endp field-templates) nil)
   (t (let* ((field-template (car field-templates))
             (type (access defstobj-field-template field-template :type))
             (arrayp (and (consp type) (eq (car type) 'array)))
             (hashp (and (consp type) (eq (car type) 'hash-table)))
             (stobj-tablep (and (consp type) (eq (car type) 'stobj-table)))
             (hash-test (if hashp
                            (cadr type)
                          (and stobj-tablep 'eq)))
             (hash-init-size (if hashp
                                 (stobj-hash-table-init-size type)
                               (and stobj-tablep (cadr type))))
             (array-etype0 (and arrayp (cadr type)))
             (array-size (and arrayp (car (caddr type))))
             (stobj-creator
; This variable is used only for initialization.  The initial hash table is
; nil, so we don't need the creator for hash tables.
              (and (not hashp) ; optimization (see comment above)
                   (get-stobj-creator (if arrayp array-etype0 type)
                                      nil)))
             (array-etype (and arrayp

; See comment for this binding in defstobj-field-fns-raw-defs.

                               (if stobj-creator
                                   t
                                 (or (access defstobj-field-template
                                             field-template
                                             :element-type)
                                     array-etype0))))
             (init (access defstobj-field-template field-template :init)))
        (cond
         (arrayp
          (cons (cond (stobj-creator
                       (assert$
                        (null init) ; checked by chk-stobj-field-descriptor
                        (assert$

; We expect array-size to be a natural number, as this is checked by
; chk-stobj-field-descriptor (using fix-stobj-array-type).  It is important
; that array-size not be a Lisp form that references the variable AR, even
; after macroexpansion, in order to avoid capture by the binding of AR below.

                         (natp array-size)
                         `(let ((ar (make-array$ ,array-size

; Do not be tempted to use :initial-element (,stobj-creator) here, because that
; would presumably share structure among all the created stobjs.

                                                 :element-type ',array-etype)))
                            (loop for i from 0 to ,(1- array-size)
                                  do
                                  (setf (svref ar i) (,stobj-creator)))
                            ar))))
                      ((and (eq array-etype0 'double-float)
                            (dfp init))
                       `(make-array$ ,array-size
                                     :element-type ',array-etype
                                     :initial-element
                                     (to-df ,init)))
                      (t `(make-array$ ,array-size
                                       :element-type ',array-etype
                                       :initial-element ',init)))
                (defstobj-raw-init-fields (cdr field-templates))))
         ((or hashp stobj-tablep)
          (cons `(make-hash-table-with-defaults ',hash-test
                                                ,hash-init-size
                                                nil
                                                nil)
                (defstobj-raw-init-fields (cdr field-templates))))
         ((eq type t)
          (cons (kwote init)
                (defstobj-raw-init-fields (cdr field-templates))))
         (stobj-creator
          (cons `(,stobj-creator)
                (defstobj-raw-init-fields (cdr field-templates))))
         ((and (eq type 'double-float)
               (dfp init))
          (cons `(make-stobj-scalar-field ,type
                                          (to-df ,init))
                (defstobj-raw-init-fields (cdr field-templates))))
         (t (cons `(make-stobj-scalar-field ,type ',init)
                  (defstobj-raw-init-fields (cdr field-templates)))))))))

(defun defstobj-raw-init-setf-forms (var index raw-init-fields acc)
  (cond ((endp raw-init-fields) acc) ; no need to reverse
        (t (defstobj-raw-init-setf-forms
             var
             (1+ index)
             (cdr raw-init-fields)
             (cons `(setf (svref ,var ,index)
                          ,(car raw-init-fields))
                   acc)))))

(defun defstobj-raw-init (template)

; This function generates the initialization code for the live object
; representing the stobj name.

  (let* ((field-templates (access defstobj-template template :field-templates))
         (raw-init-fields (defstobj-raw-init-fields field-templates))
         (len (length field-templates))
         (single-fieldp

; Warning: Keep this binding in sync with the binding of single-fieldp in
; defstobj-field-fns-raw-defs.

          (and (= len 1)
               (single-field-type-p (access defstobj-field-template
                                            (car field-templates)
                                            :type)))))
    (cond
     (single-fieldp `,(car raw-init-fields))
     (t `(cond
          ((< ,len call-arguments-limit)

; This check is necessary because GCL complains when VECTOR is called on more
; than 64 arguments.  Actually, the other code -- where LIST is called instead
; of VECTOR -- is in principle just as problematic when field-templates is at
; least as long as call-arguments-limit.  However, GCL has (through 2015 at
; least) been forgiving when LIST is called with too many arguments (as per
; call-arguments-limit).

           (vector ,@raw-init-fields))
          (t
           (let ((v (make-array$ ,len)))
             ,@(defstobj-raw-init-setf-forms 'v 0 raw-init-fields nil)
             v)))))))

(defun defstobj-component-recognizer-calls (field-templates n var ans)

; Warning:  See the guard remarks in the Essay on Defstobj Definitions.

; Given a list of defstobj-field-template records with n+1 field names -- for
; example regp, pcp, ... -- such that var is some symbol, v, we return a
; corresponding list -- for example ((regp (nth 0 v)) (pcp (nth 1 v)) ...).
; Except, for each field corresponding to a non-resizable array then we also
; include a corresponding length statement in the list.

  (cond ((endp field-templates)
         (reverse ans))
        (t (defstobj-component-recognizer-calls
             (cdr field-templates)
             (+ n 1)
             var
             (let* ((type (access defstobj-field-template
                                  (car field-templates)
                                  :type))
                    (nonresizable-ar (and (consp type)
                                          (eq (car type) 'array)
                                          (not (access defstobj-field-template
                                                       (car field-templates)
                                                       :resizable))))
                    (pred-stmt `(,(access defstobj-field-template
                                          (car field-templates)
                                          :fieldp-name)
                                 (nth ,n ,var))))
               (if nonresizable-ar
                   (list* `(equal (len (nth ,n ,var)) ,(car (caddr type)))
                          pred-stmt
                          ans)
                 (cons pred-stmt ans)))))))

(defun stobjp (x known-stobjs w)

; We recognize whether x is to be treated as a stobj name.  Known-stobjs is a
; list of all such names, or else T, standing for all stobj names in w.  During
; translation, only certain known stobjs in w are considered stobjs, as per the
; user's :stobjs declare xargs.  If you want to know whether x has been defined
; as a stobj in w, use known-stobjs = t.

; Slight abuse permitted: Sometimes known-stobjs will be a list of stobj flags!
; E.g., we might supply (NIL NIL STATE NIL $S) where (STATE $S) is technically
; required.  But we should never ask if NIL is a stobj because we only ask this
; of variable symbols.  But just to make this an ironclad guarantee, we include
; the first conjunct below.

  (declare (xargs :guard (and (plist-worldp w)
                              (or (eq known-stobjs t)
                                  (true-listp known-stobjs)))))
  (and x
       (symbolp x)
       (if (eq known-stobjs t)
           (getpropc x 'stobj nil w)
         (member-eq x known-stobjs))))

(defun translate-stobj-type-to-guard (x var wrld)

; This function is a variant of translate-declaration-to-guard.  Like that
; function, x is an alleged type about the variable symbol var -- think
; (DECLARE (TYPE x ...)) -- and results in an UNTRANSLATED term about var if x
; is seen to be a valid type-spec for ACL2.  Unlike that function, here we
; allow x to be a stobj name, which may be used as a type in a field of another
; stobj (introduced after x).  We return nil if x is not either sort of valid
; type spec.

; Our intended use of this function is in generation of guards for recognizers
; of stobj fields that may themselves be stobjs.  We do not use this however in
; accessors or updaters, where translate-declaration-to-guard suffices: we do
; not want to generate a stobj recognizer since the child stobj is supplied
; explicitly using :stobjs.

  (or (translate-declaration-to-guard x var wrld)
      (and (not (eq x 'state))
           (symbolp x)
           #-acl2-loop-only
           (let ((d (get (the-live-var x)
                         'redundant-raw-lisp-discriminator)))
             (and (consp d)
                  (member-eq (car d) '(defstobj defabsstobj))
                  (list (access defstobj-redundant-raw-lisp-discriminator-value
                                (cdr d)
                                :recognizer)
                        var)))
           #+acl2-loop-only
           (let ((prop (getpropc x 'stobj nil wrld)))
             (and prop
                  (list (access stobj-property prop :recognizer)
                        var))))))

(defun defstobj-component-recognizer-axiomatic-defs (name template
                                                          field-templates wrld)

; Warning:  See the guard remarks in the Essay on Defstobj Definitions.

; It is permissible for wrld to be nil, as this merely defeats additional
; checking by translate-declaration-to-guard-gen.

; We return a list of defs (see defstobj-axiomatic-defs) for all the
; recognizers for the single-threaded resource named name with the given
; template.  The answer contains the top-level recognizer as well as the
; definitions of all component recognizers.  The answer contains defs for
; auxiliary functions used in array and hash-table component recognizers.  The
; defs are listed in an order suitable for processing (components first, then
; top-level).

  (cond
   ((endp field-templates)
    (let* ((recog-name (access defstobj-template template :recognizer))
           (field-templates (access defstobj-template template
                                    :field-templates))
           (n (length field-templates)))

; Rockwell Addition: See comment below.

; Note: The recognizer for a stobj must be Boolean!  That is why we
; conclude the AND below with a final T.  The individual field
; recognizers need not be Boolean and sometimes are not!  For example,
; a field with :TYPE (MEMBER e1 ... ek) won't be Boolean, nor with
; certain :TYPE (OR ...) involving MEMBER.  The reason we want the
; stobj recognizer to be Boolean is so that we can replace it by T in
; guard conjectures for functions that have been translated with the
; stobj syntactic restrictions.  See optimize-stobj-recognizers.

      (list `(,recog-name (,name)
                          (declare (xargs :guard t
                                          :verify-guards t))
                          (and (true-listp ,name)
                               (= (length ,name) ,n)
                               ,@(defstobj-component-recognizer-calls
                                   field-templates 0 name nil)
                               t)))))
   (t
    (let ((recog-name (access defstobj-field-template
                              (car field-templates)
                              :fieldp-name))
          (type (access defstobj-field-template
                        (car field-templates)
                        :type)))
      (cons (cond
             ((and (consp type)
                   (eq (car type) 'array))
              (let ((etype (cadr type)))
                `(,recog-name (x)
                              (declare (xargs :guard t
                                              :verify-guards t))
                              (if (atom x)
                                  (equal x nil)
                                (and ,(translate-stobj-type-to-guard
                                       etype '(car x) wrld)
                                     (,recog-name (cdr x)))))))
             ((and (consp type)
                   (eq (car type) 'hash-table)
                   (not (eq (stobj-hash-table-element-type type) t)))
              `(,recog-name (x)
                            (declare (xargs :guard t
                                            :verify-guards t))
                            (cond
                             ((atom x) t)
                             ((consp (car x))
                              (and ,(translate-stobj-type-to-guard
                                     (stobj-hash-table-element-type type)
                                     '(cdar x)
                                     wrld)
                                   (,recog-name (cdr x))))
                             (t (,recog-name (cdr x))))))
             ((and (consp type)
                   (or (eq (car type) 'hash-table)
                       (eq (car type) 'stobj-table)))
              `(,recog-name (x)
                            (declare (xargs :guard t
                                            :verify-guards t)
                                     (ignore x))
                            t))
             (t (let ((type-term (translate-stobj-type-to-guard
                                  type 'x wrld)))

; We might not use x in the type-term and so have to declare it ignorable.

                  `(,recog-name (x)
                                (declare (xargs :guard t
                                                :verify-guards t)
                                         (ignorable x))
                                ,type-term))))
            (defstobj-component-recognizer-axiomatic-defs
              name template (cdr field-templates) wrld))))))

(defun congruent-stobj-rep (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              wrld
                              (plist-worldp wrld))))
  (assert$
   wrld ; use congruent-stobj-rep-raw if wrld is not available
   (or (getpropc name 'congruent-stobj-rep nil wrld)
       name)))

(defun all-but-last (l)
  (declare (xargs :guard (true-listp l) ; and let's verify termination/guards:
                  :mode :logic))
  (cond ((endp l) nil)
        ((endp (cdr l)) nil)
        (t (cons (car l) (all-but-last (cdr l))))))

(defun defstobj-raw-defs (name template congruent-stobj-rep wrld)

; Warning:  See the guard remarks in the Essay on Defstobj Definitions.

; This function generates a list of defs.  Each def is such that
; (defun . def) is a well-formed raw Lisp definition.  The defuns can
; be executed in raw lisp to define the versions of the recognizers,
; accessors, and updaters (and for array fields, length and resize
; functions) that are run when we know the guards are satisfied.  Many
; of these functions anticipate application to the live object itself.

; It is permissible for wrld to be nil, as this merely defeats additional
; checking by translate-declaration-to-guard-gen.  If wrld is nil, then
; congruent-stobj-rep should be the result of calling congruent-stobj-rep on
; name and the world where the corresponding defstobj is executed.  If wrld is
; non-nil, then it should be an ACL2 world and congruent-stobj-rep is
; irrelevant.

; WARNING: If you change the formals of these generated raw defs be
; sure to change the formals of the corresponding axiomatic defs.

  (let* ((recog (access defstobj-template template :recognizer))
         (creator (access defstobj-template template :creator))
         (field-templates (access defstobj-template template :field-templates))
         (inline (access defstobj-template template :inline)))
    (append
     (all-but-last
      (defstobj-component-recognizer-axiomatic-defs name template
        field-templates wrld))
     `((,recog (,name)
               (cond
                ((live-stobjp ,name)
                 t)
                (t (and (true-listp ,name)
                        (= (length ,name) ,(length field-templates))
                        ,@(defstobj-component-recognizer-calls
                            field-templates 0 name nil)))))
       (,creator ()
                 ,(defstobj-raw-init template))
       ,@(defstobj-field-fns-raw-defs
           name
           (cond
            ((access defstobj-template template :non-memoizable)
             nil)
            (wrld (let ((congruent-to (access defstobj-template template
                                              :congruent-to)))
                    (if congruent-to
                        (congruent-stobj-rep congruent-to wrld)
                      name)))
            (t congruent-stobj-rep))
           inline 0 field-templates)))))

(defun defconst-name (name)
  (intern-in-package-of-symbol
   (concatenate 'string "*" (symbol-name name) "*")
   name))

(defun defstobj-defconsts (names index)
  (if (endp names)
      nil
    (cons `(defconst ,(defconst-name (car names)) ,index)
          (defstobj-defconsts (cdr names) (1+ index)))))

(defun strip-accessor-names (field-templates)
  (if (endp field-templates)
      nil
    (cons (access defstobj-field-template (car field-templates)
                  :accessor-name)
          (strip-accessor-names (cdr field-templates)))))

(defun the-live-var (name)

; Through Version_8.2, for a stobj named st, (the-live-var st) was a special
; variable.  However, now the live stobj corresponding to st is stored on the
; raw Lisp alist *user-stobj-alist* under the key st.

; Back when we stored it under the value of the the-live-var, we thought that
; one might wonder why we didn't choose to name this object $s.  Below we
; explain our earlier thinking.  Now that we use only (the-live-var name) only
; to store properties, perhaps we could instead store those properties on name;
; but when we eliminated the special variable in October 2019, that didn't seem
; worthwhile to explore.

; Historical Plaque for Why the Live Var for $S Is Not $S

; [Otherwise] Consider how hard it would then be to define the raw defs
; (below).  $S is the formal parameter, and naturally so since we want
; translate to enforce the rules on single-threadedness.  The raw code
; has to check whether the actual is the live object.  We could hardly
; write (eq $S $S).

  (declare (xargs :guard (symbolp name)))
  (packn-pos (list "*THE-LIVE-" name "*") name))

#-acl2-loop-only
(defun congruent-stobj-rep-raw (name)
  (assert name)
  (let ((d (get (the-live-var name) 'redundant-raw-lisp-discriminator)))
    (assert (member (car d) '(defstobj defabsstobj)
                    :test #'eq))
    (assert (cdr d))
    (access defstobj-redundant-raw-lisp-discriminator-value
            (cdr d)
            :congruent-stobj-rep)))

#-acl2-loop-only
(defmacro defstobj (&whole event name &rest args)

; Warning: If you change this definition, consider the possibility of making
; corresponding changes to the #-acl2-loop-only definition of defabsstobj.

; This function is run when we evaluate (defstobj name . args) in raw lisp.
; A typical such form is

; (defstobj $st
;   (flag :type t :initially run)
;   (pc   :type (integer 0 255) :initially 128)
;   (mem  :type (array (integer 0 255) (256)) :initially 0))

; Warning: If this event ever generates proof obligations, remove it from the
; list of exceptions in install-event just below its "Comment on irrelevance of
; skip-proofs".

; This function must contend with a problem analogous to the one addressed by
; acl2::defconst in acl2.lisp: the need to avoid re-declaration of the same
; stobj.  We use redundant-raw-lisp-discriminator in much the same way as in
; the raw lisp defmacro of acl2::defconst.

  (let* ((template (defstobj-template name args nil))
         (congruent-to (access defstobj-template template :congruent-to))
         (congruent-stobj-rep (if congruent-to
                                  (congruent-stobj-rep-raw congruent-to)
                                name))
         (recognizer (access defstobj-template template :recognizer))
         (creator (access defstobj-template template :creator))
         (non-memoizable (access defstobj-template template :non-memoizable))
         (non-executable (access defstobj-template template :non-executable))
         (init-form (defstobj-raw-init template))
         (the-live-name (the-live-var name)))
    `(progn
       ,@(and (null congruent-to)

; It has occurred to us that this defg form might be avoidable when
; non-memoizable is true, since the purpose of st-lst is probably only to
; support memoize-flush.  However, it seems harmless enough to lay down this
; form even when non-memoizable is true, so we go ahead and do so rather than
; think carefully about avoiding it.

              `((defg ,(st-lst name) nil)))

; Now we lay down the defuns of the recognizers, accessors and updaters as
; generated by defstobj-raw-defs.  The boilerplate below just adds the DEFUN to
; the front of each def generated, preserving the order of the defs as
; generated.  We deal here with the :inline case; note that
; *stobj-inline-declare* was added in defstobj-field-fns-raw-defs.

       ,@(mapcar (function (lambda (def)
                             (if (member-equal *stobj-inline-declare* def)
                                 (cons 'DEFABBREV
                                       (remove-stobj-inline-declare def))
                               (cons 'DEFUN def))))
                 (defstobj-raw-defs name template congruent-stobj-rep nil))
       ,@(defstobj-defconsts
           (strip-accessor-names (access defstobj-template template
                                         :field-templates))
           0)
       (let* ((event ',event)
              (recognizer ',recognizer)
              (creator ',creator)
              (congruent-stobj-rep ',congruent-stobj-rep)
              (non-memoizable ',non-memoizable)
              (non-executable ',non-executable)
              (old-pair (assoc-eq ',name *user-stobj-alist*))
              (d (and (or old-pair non-executable) ; optimization
                      (get ',the-live-name
                           'redundant-raw-lisp-discriminator)))
              (ok-p (and (consp d)
                         (eq (car d) 'defstobj)
                         (equal (access
                                 defstobj-redundant-raw-lisp-discriminator-value
                                 (cdr d)
                                 :event)
                                event))))
         (cond
          (ok-p ',name)
          ((and old-pair (not (raw-mode-p *the-live-state*)))

; If the old stobj was non-executable, then it should be OK to redeclare it
; since there is no issue about what to do with the old value (there isn't
; one).

           (interface-er
            "Illegal attempt to redeclare the single-threaded object ~s0."
            ',name))
          (t
           (setf (get ',the-live-name 'redundant-raw-lisp-discriminator)
                 (cons 'defstobj
                       (make defstobj-redundant-raw-lisp-discriminator-value
                             :event event
                             :recognizer recognizer
                             :creator creator
                             :congruent-stobj-rep congruent-stobj-rep
                             :non-memoizable non-memoizable
                             :non-executable non-executable)))
           (cond (*hcomp-book-ht*

; There is no need to update *user-stobj-alist* or
; *non-executable-user-stobj-lst* when doing the early load of compiled files.
; In particular, there is no need to create the stobj for insertion into the
; *user-stobj-alist*, and this optimization can save considerable space at
; include-book time.  Note that any *user-stobj-alist* built during an early
; load of compiled files is anyhow discarded at the end of the load, and also
; note that when make-event is called with non-nil :check-expansion, only the
; expansion is created by macroexpansion in raw Lisp -- these observations add
; confidence to this optimization.

                  (assert (null old-pair))
                  nil)
                 (old-pair ; hence raw-mode
                  (fms "Note:  Redefining and ~@0 stobj ~x1 in ~
                        raw mode.~%"
                       (list (cons #\0 (if non-executable
                                           "removing executability of"
                                         "reinitializing"))
                             (cons #\1 ',name))
                       (standard-co *the-live-state*) *the-live-state* nil)
                  (cond
                   (non-executable
                    (assert (not (member-eq ',name
                                            *non-executable-user-stobj-lst*)))
                    (push ',name *non-executable-user-stobj-lst*)
                    (setq *user-stobj-alist*
                          (remove1-assoc-eq ',name *user-stobj-alist*)))
                   (t (setf (cdr old-pair) ,init-form))))
                 (non-executable
                  (pushnew ',name *non-executable-user-stobj-lst*))
                 (t
                  (setq *user-stobj-alist* ; update-user-stobj-alist
                        (cons (cons ',name ,init-form)
                              *user-stobj-alist*))))
           ',name))))))

; End of stobj support in raw lisp

(defrec ld-history-entry
; This form conceptually belongs with other forms pertaining to ld-history in
; ld.lisp.  But we use this in initialize-state-globals below.
  ((input error-flg)
   stobjs-out/value . user-data)
  nil)

; We need to have state globals bound for prin1$ etc. to work, because of calls
; of with-print-controls.  We may also need the dolist form below for tracing,
; which uses current-package for printing and current-acl2-world for
; current-acl2-world suppression.  State globals such as 'compiler-enabled,
; whose value depends on the host Common Lisp implementation, are initialized
; here rather than in *initial-global-table*, so that the value of any defconst
; (such as *initial-global-table*) is independent of the host Common Lisp
; implementation.  That is important to avoid trivial soundness bugs based on
; variance of a defconst value from one underlying Lisp to another.

#-acl2-loop-only
(initialize-state-globals)

; Local stobj support

(defun parse-with-local-stobj (x)

; X is the cdr of a with-local-stobj call.  We return (mv erp stobj-name
; mv-let-form creator-name).

  (declare (xargs :guard t))
  (case-match x
    ((st
      ('mv-let . mv-let-body))
     (cond ((symbolp st)
            (mv nil st (cons 'mv-let mv-let-body)
                (defstobj-fnname st :creator :top nil)))
           (t (mv t nil nil nil))))
    ((st
      ('mv-let . mv-let-body)
      creator)
     (mv nil st (cons 'mv-let mv-let-body) creator))
    (& (mv t nil nil nil))))

#-acl2-loop-only
(defun-one-output mv-let-for-with-local-stobj (mv-let-form st creator flet-fns
                                                           w program-p)

; If w is not nil, then it is the current ACL2 world and we are to oneify the
; appropriate subforms with the indicated program-p argument.  If w is nil,
; then program-p is irrelevant.

; It was tempting to have an acl2-loop-only version of the body below as well,
; which would omit the binding of the live var.  But if someone were to
; verify-termination of this function, we could presumably prove nil using the
; discrepancy between the two versions.  So we take the attitude that
; with-local-stobj is a special form, like let, that is not defined.

; In the case that st is STATE, this form does not take responsibility for
; restoring state, for example by restoring values of state global variables
; and by closing channels that may have been created during evaluation of the
; producer form.  A with-local-state form thus needs to take responsibility for
; restoring state; see for example the definition of channel-to-string.

  (let ((producer (caddr mv-let-form))
        (rest (cdddr mv-let-form)))
    `(mv-let ,(cadr mv-let-form)
             (let* (,@(and (not (eq st 'state))
                           `((,st (,creator))))
                    ,@(cond ((eq st 'state)
                             '((*wormholep*

; We are in a local state, so it is irrelevant whether or not we are in a
; wormhole, since (conceptually at least) the local state will be thrown away
; after making changes to it.

                                nil)
                               (*file-clock* *file-clock*)))))
               ,(let ((p (if w
                             (oneify producer flet-fns w program-p)
                           producer)))
                  (if (eq st 'state)
                      `(if (f-get-global 'parallel-execution-enabled
                                         *the-live-state*)
                           (with-local-state-lock ,p)
                         ,p)
                    p)))
             (declare (ignore ,st))
             ,@(if w
                   (if (cdr rest) ; rest is ((declare (ignore ...)) body)
                       (list (car rest)
                             (oneify (cadr rest) flet-fns w program-p))
                     (list (oneify (car rest) flet-fns w program-p)))
                 rest))))

#-acl2-loop-only ; see the comment in mv-let-for-with-local-stobj
(defmacro with-local-stobj (&rest args)

; See books/system/tests/local-stobj.lisp for some tests.

  (mv-let (erp st mv-let-form creator)
          (parse-with-local-stobj args)
          (if (or erp
                  (not (and (true-listp mv-let-form)
                            (<= 3 (length mv-let-form)))))
              (er hard 'with-local-stobj
                  "Macroexpansion of a with-local-stobj call caused an error. ~
                   See :DOC with-local-stobj.")
            (mv-let-for-with-local-stobj mv-let-form st creator nil nil nil))))

; The following definitions were moved here from other-events.lisp so that it
; is included in the toothbrush.

(defun parse-version (version)

; Version is an ACL2 version string, as in state global 'acl2-version.  We
; return (mv major minor incrl rest), where either major is nil, indicating an
; ill-formed version; or else major, minor, and incrl are natural numbers
; indicating the major, minor, and incrl version, and rest is the part of the
; string starting with #\(, if any.  For example,
; (parse-version "ACL2 Version 2.10") is (mv 2 10 0 "") and
; (parse-version "ACL2 Version 2.10.1(r)") is (mv 2 10 1 "(r)").

  (declare (xargs :guard (stringp version)))
  (let* ((root "ACL2 Version")
         (pos0 (if (and (stringp version)
                        (<= 13 (length version))
                        (equal (subseq version 0 12) root)
                        (or (eql (char version 12) #\Space)
                            (eql (char version 12) #\_)))
                   13
                 nil))
         (pos-lparen (position #\( version))
         (end0 (or pos-lparen
                   (length version)))
         (rest (subseq version end0 (length version)))
         (from-pos0 (and pos0 (subseq version pos0 end0)))
         (pos1-from-pos0 (and pos0 (position #\. from-pos0)))
         (pos1 (and pos1-from-pos0 (+ pos0 pos1-from-pos0)))
         (major (and pos1 (decimal-string-to-number
                           (subseq version pos0 pos1)
                           (- pos1 pos0) 0)))
         (from-pos1 (and pos1 (subseq version (1+ pos1) end0)))
         (pos2-from-pos1 (and pos1 (position #\. from-pos1)))
         (pos2 (if pos2-from-pos1
                   (+ (1+ pos1) pos2-from-pos1)
                 (and pos1 end0)))
         (minor (and pos2 (decimal-string-to-number
                           (subseq version (1+ pos1) pos2)
                           (1- (- pos2 pos1)) 0)))
         (incrl (if (and pos2 (< pos2 end0))
                    (decimal-string-to-number
                     (subseq version (1+ pos2) end0)
                     (1- (- end0 pos2))
                     0)
                  0)))
    (mv major minor incrl rest)))

(defun pcd2 (n channel state)
  (declare (xargs :guard (integerp n)))
  (cond ((< n 10)
         (pprogn (princ$ "0" channel state)
                 (princ$ n channel state)))
        (t (princ$ n channel state))))

(defun power-rep (n b)
  (if (< n b)
      (list n)
    (cons (rem n b)
          (power-rep (floor n b) b))))

(defun decode-idate (n)
  (let ((tuple (power-rep n 100)))
    (cond
     ((< (len tuple) 6)
      (er hard 'decode-idate
          "Idates are supposed to decode to a list of at least length six ~
           but ~x0 decoded to ~x1."
          n tuple))
     ((equal (len tuple) 6) tuple)
     (t

; In this case, tuple is (secs mins hrs day month yr1 yr2 ...) where 0
; <= yri < 100 and (yr1 yr2 ...) represents a big number, yr, in base
; 100.  Yr is the number of years since 1900.

        (let ((secs (nth 0 tuple))
              (mins (nth 1 tuple))
              (hrs  (nth 2 tuple))
              (day  (nth 3 tuple))
              (mo   (nth 4 tuple))
              (yr (power-eval (cdr (cddddr tuple)) 100)))
          (list secs mins hrs day mo yr))))))

(defun print-idate (n channel state)
  (let* ((x (decode-idate n))
         (sec (car x))
         (minimum (cadr x))
         (hrs (caddr x))
         (day (cadddr x))
         (mo (car (cddddr x)))
         (yr (cadr (cddddr x))))  ; yr = years since 1900.  It is possible
                                  ; that yr > 99!
    (pprogn
     (princ$ (nth (1- mo)
              '(|January| |February| |March| |April| |May|
                |June| |July| |August| |September|
                |October| |November| |December|))
             channel state)
     (princ$ #\Space channel state)
     (princ$ day channel state)
     (princ$ "," channel state)
     (princ$ #\Space channel state)
     (princ$ (+ 1900 yr) channel state)
     (princ$ "  " channel state)
     (pcd2 hrs channel state)
     (princ$ ":" channel state)
     (pcd2 minimum channel state)
     (princ$ ":" channel state)
     (pcd2 sec channel state)
     state)))

; This definition was originally in acl2-init.lisp, but cmulisp warned that
; *open-output-channel-key*, print-idate, and idate were undefined.
#-acl2-loop-only
(defun saved-build-date-string ()
  (with-output-to-string
   (str)
   (setf (get 'tmp-channel *open-output-channel-key*)
         str)
   (print-idate (idate)
                'tmp-channel
                *the-live-state*)
   (remprop 'tmp-channel *open-output-channel-key*)
   str))

; Quitting

(defun good-bye-fn (status)
  (declare (xargs :mode :logic :guard t))
  #-acl2-loop-only
  (exit-lisp (ifix status))
  status)

(defmacro good-bye (&optional (status '0))
  `(good-bye-fn ,status))

(defmacro exit (&optional (status '0))
  `(good-bye-fn ,status))

(defmacro quit (&optional (status '0))
  `(good-bye-fn ,status))

; Saving an Executable Image

#-acl2-loop-only
(defparameter *initial-cbd* nil)

#-acl2-loop-only
(defvar *return-from-lp* nil)

#-acl2-loop-only
(defvar *lp-init-forms* nil)

(defun expand-tilde-to-user-home-dir (str os ctx state)

; Note that character `~' need not get special treatment by Windows.  See
; comment just above error message below, and see absolute-pathname-string-p.

  (cond ((or (equal str "~")
             (and (< 1 (length str))
                  (eql (char str 0) #\~)
                  (eql (char str 1) #\/)))
         (let ((user-home-dir (f-get-global 'user-home-dir state)))
           (cond
            (user-home-dir
             (concatenate 'string
                          user-home-dir
                          (subseq str 1 (length str))))
            (t

; On Linux or Mac OS, it is surprising to find that user-home-dir is nil.  (See
; the definition of lp to see how it is set.)  But on Windows, it seems that
; this could be the case, say outside an environment like Cygwin, MSYS, or
; MinGW.

             (let ((certify-book-info (f-get-global 'certify-book-info state)))
               (prog2$ (and (or certify-book-info
                                (not (eq os :mswindows)))
                            (er hard ctx
                                "The use of ~~/ for the user home directory ~
                                 in filenames is not supported ~@0."
                                (if certify-book-info
                                    "inside books being certified"
                                  "for this host Common Lisp")))
                       str))))))
        (t str)))

(defun save-exec-fn (exec-filename extra-startup-string host-lisp-args
                                   toplevel-args inert-args return-from-lp
                                   init-forms)

  #-acl2-loop-only
  (progn

    (when (not (our-probe-file (directory-namestring exec-filename)))

; Without this check, CCL will create a directory for us; yet SBCL will not.
; We prefer consistent behavior across all Lisps.  Here we choose to require
; the directory to exist already, to prevent users from creating directories
; they don't want by mistake.

      (error "~s is unable to save to file ~s, because its directory does not ~
              exist."
             'save-exec exec-filename))

; Parallelism blemish: it may be a good idea to reset the parallelism variables
; in all #+acl2-par compilations before saving the image.

    (when (and init-forms return-from-lp)

; For each of return-from-lp and init-forms, a non-nil value takes us through a
; different branch of LP.  Rather than support the use of both, we cause an
; error.

      (er hard 'save-exec
          "The use of non-nil values for both :init-forms and :return-from-lp ~
           is not supported for save-exec.  Consider using only :init-forms, ~
           with (value :q) as the final form."))
    (setq *return-from-lp* return-from-lp)
    (setq *lp-init-forms* init-forms)
    #-sbcl (when toplevel-args
             (er hard 'save-exec
                 "Keyword argument :toplevel-args is only allowed when the ~
                  host Lisp is SBCL."))
    (if (not (eql *ld-level* 0))
        (er hard 'save-exec
            "Please type :q to exit the ACL2 read-eval-print loop and then try ~
             again."))
    (if (equal extra-startup-string "")
        (er hard 'save-exec
            "The extra-startup-string argument of save-exec must be ~x0 or ~
             else a non-empty string."
            nil)
      (setq *saved-string*
            (format
             nil
             "~a~%MODIFICATION NOTICE:~%~%~a~%"
             *saved-string*
             (cond ((null extra-startup-string)
                    "This ACL2 executable was created by saving a session.")
                   (t extra-startup-string)))))
    #-(or gcl cmu sbcl allegro clisp ccl lispworks)
    (er hard 'save-exec
        "Sorry, but save-exec is not implemented for this Common Lisp.")

; The forms just below, before the call of save-exec-raw, are there so that the
; initial (lp) will set the :cbd correctly.

    (f-put-global 'connected-book-directory nil *the-live-state*)
    (setq *initial-cbd* nil)
    (setq *startup-package-name* (package-name *package*))
    (setq *saved-build-date-lst*

; By using setq here for *saved-build-date* instead of a let-binding for
; save-exec-raw, it happens that saving more than once in the same session (for
; Lisps that allow this, such as Allegro CL but not GCL) would result in extra
; "; then ..." strings.  But that seems a minor problem, and avoids having to
; think about the effect of having a let-binding in force above a save of an
; image.

          (cons (saved-build-date-string)
                *saved-build-date-lst*))
    (save-exec-raw (expand-tilde-to-user-home-dir exec-filename
                                                  (os (w *the-live-state*))
                                                  'save-exec
                                                  *the-live-state*)
                   host-lisp-args
                   #+sbcl toplevel-args
                   inert-args))
  #+acl2-loop-only
  (declare (ignore exec-filename extra-startup-string host-lisp-args
                   toplevel-args inert-args return-from-lp init-forms))
  nil ; Won't get to here in GCL and perhaps other lisps
  )

(defmacro save-exec (exec-filename extra-startup-string
                                   &key
                                   host-lisp-args toplevel-args inert-args
                                   return-from-lp init-forms)
  `(save-exec-fn ,exec-filename ,extra-startup-string ,host-lisp-args
                 ,toplevel-args ,inert-args ,return-from-lp ,init-forms))

(defconst *slash-dot-dot*
  (concatenate 'string *directory-separator-string* ".."))

(defconst *length-slash-dot-dot*
  (length *slash-dot-dot*))

(defun find-dot-dot (full-pathname i)

; Termination and even guard-verification are proved in community book
; books/system/extend-pathname.lisp.

  (declare (xargs :guard (and (stringp full-pathname)
                              (natp i)
                              (<= i (length full-pathname)))
                  :measure (nfix (- (length full-pathname) i))))
  (let ((pos (search *slash-dot-dot* full-pathname :start2 i)))
    (and pos
         (let ((pos+3 (+ pos *length-slash-dot-dot*)))
           (cond
            ((or (eql pos+3 (length full-pathname))
                 (eql (char full-pathname pos+3) *directory-separator*))
             pos)
            ((mbt (<= pos+3 (length full-pathname)))
             (find-dot-dot full-pathname pos+3)))))))

(mutual-recursion

; The :measure declarations in this mutual-recursion nest are in support of
; community book books/system/extend-pathname.lisp.  The :guard declarations
; below are intended to be correct, but we won't really know until guards have
; been verified; it seems quite possible that the guards will need to be
; adjusted.

(defun cancel-dot-dots (full-pathname)
  (declare (xargs :guard (stringp full-pathname)
                  :measure (* 2 (length full-pathname))))
  (let ((p (find-dot-dot full-pathname 0)))
    (cond ((and p
                (mbt ; termination help
                 (and (natp p)
                      (stringp full-pathname)
                      (< p (length full-pathname)))))
           (let ((new-p
                  (merge-using-dot-dot
                   (subseq full-pathname 0 p)
                   (subseq full-pathname (1+ p) (length full-pathname)))))
             (and (mbt ; termination help
                   (and (stringp new-p)
                        (< (length new-p) (length full-pathname))))
                  (cancel-dot-dots new-p))))
          (t full-pathname))))

(defun get-parent-directory (p0)

; P is an absolute pathname for a directory, not a file, where p does not end
; in "/".  We return an absolute pathname for its parent directory, not
; including the trailing "/".  See also get-directory-of-file, which is a
; related function for files.

  (declare (xargs :guard (stringp p0)
                  :measure (1+ (* 2 (length p0)))))
  (let* ((p (and (mbt (stringp p0))
                 (cancel-dot-dots p0)))
         (posn (search *directory-separator-string* p :from-end t)))
    (cond
     (posn (subseq p 0 posn))
     (t (er hard? 'get-parent-directory
            "Implementation error!  Unable to get parent directory for ~
             directory ~x0."
            p0)))))

(defun merge-using-dot-dot (p s)

; P is the absolute pathname of a directory without the final "/".  S is a
; pathname (for a file or a directory) that may start with any number of
; sequences "../" and "./".  We want to "cancel" the leading "../"s in s
; against directories at the end of p, and eliminate leading "./"s from s
; (including leading "." if that is all of s).  The result should syntactically
; represent a directory (end with a "/" or "."  or be "") if and only if s
; syntactically represents a directory.

; This code is intended to be simple, not necessarily efficient.

  (declare (xargs :guard (and (stringp p)
                              (stringp s)
                              (not (equal s "")))
                  :measure (+ 1 (* 2 (+ (length p) (length s))))))
  (cond
   ((not (mbt ; termination help
          (and (stringp p)
               (stringp s)
               (not (equal s "")))))
    nil)
   ((equal p "") s)
   ((equal s "..")
    (concatenate 'string
                 (get-parent-directory p)
                 *directory-separator-string*))
   ((equal s ".")
    (concatenate 'string
                 p
                 *directory-separator-string*))
   ((and (>= (length s) 3)
         (eql (char s 0) #\.)
         (eql (char s 1) #\.)
         (eql (char s 2) #\/)
         (mbt (<= (length (get-parent-directory p)) ; termination help
                  (length p))))
    (merge-using-dot-dot (get-parent-directory p)
                         (subseq s 3 (length s))))
   ((and (>= (length s) 2)
         (eql (char s 0) #\.)
         (eql (char s 1) #\/))
    (merge-using-dot-dot p (subseq s 2 (length s))))
   (t
    (concatenate 'string p *directory-separator-string* s))))

)

; Print-object$ etc.

(defun comment-string-p1 (s i end)

; We assume that i points to the start of a line of s.

  (declare (type #.*fixnat-type* end)
           (xargs :measure (nfix (- end i))
                  :guard (and (natp i)
                              (stringp s)
                              (= end (length s))
                              (<= i end))))
  (cond
   ((not (mbt (and (unsigned-byte-p *fixnat-bits* end)
                   (natp i)
                   (stringp s)
                   (= end (length s))
                   (<= i end))))
    (er hard 'comment-string-p1
        "Guard violation!"))
   (t (let ((j (scan-past-whitespace s i end)))
        (cond
         ((= j end) t)
         ((eql (char s i) #\;)
          (let ((p (search *newline-string* s :start2 j)))
            (or (null p)
                (comment-string-p1 s (1+ p) end))))
         (t nil))))))

(defun comment-string-p (s)
  (declare (xargs :guard t))
  (and (stringp s)
       (let ((len (length s)))
         (and (unsigned-byte-p *fixnat-bits* len)
              (comment-string-p1 s 0 len)))))

(defrec print-control

; The alist maps Lisp variables to values, like the bindings in calls of
; with-print-controls..  So a key might be *PRINT-BASE* but not PRINT-BASE or
; :PRINT-BASE.

  (header . alist)
  nil)

(defconst *print-control-defaults*

; Warning: Keep this in sync with print-control-alistp.

  `((print-base ',(cdr (assoc-eq 'print-base *initial-global-table*))
                set-print-base)
    (print-case ',(cdr (assoc-eq 'print-case *initial-global-table*))
                set-print-case)
    (print-circle ',(cdr (assoc-eq 'print-circle *initial-global-table*))
                  set-print-circle)
    (print-escape ',(cdr (assoc-eq 'print-escape *initial-global-table*))
                  set-print-escape)
    (print-length ',(cdr (assoc-eq 'print-length *initial-global-table*))
                  set-print-length)
    (print-level ',(cdr (assoc-eq 'print-level *initial-global-table*))
                 set-print-level)
    (print-lines ',(cdr (assoc-eq 'print-lines *initial-global-table*))
                 set-print-lines)
    (print-pretty ',(cdr (assoc-eq 'print-pretty *initial-global-table*))
                  set-print-pretty)
    (print-radix ',(cdr (assoc-eq 'print-radix *initial-global-table*))
                  set-print-radix)
    (print-readably ',(cdr (assoc-eq 'print-readably *initial-global-table*))
                    set-print-readably)
    (print-right-margin ',(cdr (assoc-eq 'print-right-margin
                                         *initial-global-table*))
                        set-print-right-margin)))

(defun print-control-alistp (alist)

; Warning: Keep this in sync with *print-control-defaults*.

  (declare (xargs :guard (alistp alist) :mode :logic))
  (cond
   ((endp alist) t)
   ((let ((key (caar alist))
          (val (cdar alist)))
      (case key
        (*print-base* (print-base-p val))
        (*print-case* (member-eq val '(:upcase :downcase)))
        ((*print-length* *print-level* *print-lines* *print-right-margin*)
         (check-null-or-natp val key))
        ((*print-circle* *print-escape* *print-pretty* *print-radix*
                         *print-readably*)
         t)
        (otherwise
         (hard-error 'print-control-p
                     "The symbol ~x0 is not a legal print control variable."
                     (list (cons #\0 key))))))
    (print-control-alistp (cdr alist)))
   (t nil)))

(defconst *raw-print-vars-keys*
  (strip-cars *raw-print-vars-alist*))

(defun alist-keys-subsetp (x keys)
  (declare (xargs :guard (and (alistp x)
                              (symbol-listp keys))))
  (cond ((endp x) t)
        ((member-eq (caar x) keys)
         (alist-keys-subsetp (cdr x) keys))
        (t nil)))

(defun print-control-p (x)
  (declare (xargs :guard t))
  (and (weak-print-control-p x)
       (or (null (access print-control x :header))
           (comment-string-p (access print-control x :header)))
       (alistp (access print-control x :alist))
       (alist-keys-subsetp (access print-control x :alist)
                           *raw-print-vars-keys*)
       (print-control-alistp (access print-control x :alist))))

(defun print-object$-fn (x control channel state-state)

; Wart: We use state-state instead of state because of a bootstrap problem.

; This function is a version of print-object$ that allows specification of the
; serialize-character, which can be nil, #\Y, or #\Z (the normal case).  It
; also allows, if serialize-character is not specified, the specification of a
; header (comment) to print and of print-controls.

; See print-object$ for additional comments.

  (declare (ignorable control)
           (xargs :guard (and (state-p1 state-state)

; We considered placing the following conjunct here.
;   (or (member control '(nil #\Y #\Z))
;       (print-control-p control))

; When trying that, we also added print-object$-fn to
; *system-verify-guards-alist* (together with print-control-p and some of its
; supporting function symbols).  Unfortunately, we ran into problems applying
; verify-termination to print-object$-fn (in books/system/fmx-cw.lisp), because
; it has raw Lisp code.  On further reflection it seemed that we can just do a
; runtime check on print-control-p, which is presumably a cheap check compared
; to printing.

                              (symbolp channel)
                              (open-output-channel-p1 channel
                                                      :object
                                                      state-state))))
  #-acl2-loop-only
  (when (live-state-p state-state)
    (when *wormholep*

; There is no standard object output channel and hence this channel is
; directed to some unknown user-specified sink and we can't touch it.

      (wormhole-er 'print-object$ (list x channel)))
    (let ((stream (get-output-stream-from-channel channel))
          (controlp (and control
                         (not (characterp control)))))
      (when (and controlp
                 (not (print-control-p control)))
; See comment about this check in the :guard above.
        (er hard? 'print-object$-fn
            "Illegal print-control record, ~x0"
            control))

; Note: If you change the following bindings, consider changing the
; corresponding bindings in print-object$.

      (with-print-controls
       (and controlp
            (access print-control control :alist))
       ((*print-circle* (and *print-circle-stream*
                             (f-get-global 'print-circle state-state))))
       (let ((header (if controlp
                         (access print-control control :header)
                       *newline-string*)))
         (when header ; hence (stringp header)
           (princ$ header channel state-state)
           (unless (eql (char header (1- (length header))) #\Newline)
             (terpri stream))))
       (or (let ((serialize-character
                  (and (not controlp)
                       control)))
             (cond (serialize-character
                    (write-char #\# stream)
                    (write-char serialize-character stream)
                    (ser-encode-to-stream x stream)
                    t)))
           (prin1 x stream))
       (force-output stream)))
    (return-from print-object$-fn state-state))
  (let ((entry (cdr (assoc-eq channel (open-output-channels state-state)))))
    (update-open-output-channels
     (add-pair channel
               (cons (car entry)
                     (cons x
                           (cdr entry)))
               (open-output-channels state-state))
     state-state)))

(defun print-object$ (x channel state)

; WARNING: The "Remark on print-circle-files" in :DOC print-control mentions
; that ACL2 binds state global variable print-circle to t before writing
; certificate files and some other files.  In order for that binding to cause
; structure sharing, ACL2 implementors should be sure to use
; with-output-object-channel-sharing rather than calling open-output-channel
; directly, so that Lisp global *print-circle-stream* is initialized, which is
; necessary for binding *print-circle* to t in print-object$-fn.

; We believe that if in a single Common Lisp session, one prints an object and
; then reads it back in with print-object$ and read-object, one will get back
; an equal object under the assumptions that (a) the package structure has not
; changed between the print and the read and (b) that *package* has the same
; binding.  On a toothbrush, all calls of defpackage will occur before any
; read-objecting or print-object$ing, so the package structure will be the
; same.  It is up to the user to set current-package back to what it was at
; print time if he hopes to read back in the same object.

; Warning: For soundness, we need to avoid using iprinting when writing to
; certificate files.  We do all such writing with print-object$, so we rely on
; print-object$ not to use iprinting.

  (declare (xargs :guard (and (symbolp channel)
                              (open-output-channel-p channel :object state))))
  (print-object$-fn x (get-serialize-character state) channel state))

(defun print-object$-preserving-case (x channel state)

; Logically, this function is just print-object$.  Is it unsound to identify
; these functions, since they print differently?  We think not, because the
; only way to see what resides in a file is with the various ACL2 reading
; functions, which all use a file-clock.  See the discussion of "deus ex
; machina" in :doc current-package.

  (declare (xargs :guard (and (eq (get-serialize-character state)

; It's not clear that it makes sense to print preserving case when doing
; serialize printing.  If that capability is needed we can address weakening the
; guard to match the guard of print-object$.

                                  nil)
                              (symbolp channel)
                              (open-output-channel-p channel :object state))))
  #-acl2-loop-only
  (cond ((live-state-p state)
         (cond
          #+gcl
          ((not (fboundp 'system::set-readtable-case))
           (cerror "Use print-object$ instead"
                   "Sorry, but ~s is not supported in this older version of ~%~
                    GCL (because raw Lisp function ~s is undefined)."
                   'print-object$-preserving-case
                   'system::set-readtable-case))
          (t
           (return-from print-object$-preserving-case
             (let ((*acl2-readtable* (copy-readtable *acl2-readtable*)))
               (set-acl2-readtable-case :preserve)
               (print-object$ x channel state)))))))
  (print-object$ x channel state))

(defmacro print-object$+ (x channel
                            &rest args
                            &key
                            (header 'nil headerp)
                            (serialize-character 'nil serialize-character-p)
                            &allow-other-keys)
  (declare (xargs :guard (keyword-value-listp args)))
  (cond
   ((and serialize-character-p
         (not (eq serialize-character nil))
         (not (equal serialize-character ''nil))
         (cddr args))
    (er hard 'print-object$+
        "It is illegal for a call of ~x0 to specify a value for ~
         :SERIALIZE-CHARACTER other than ~x1 or ~x2 when at least one other ~
         keyword argument is supplied."
        'print-object$+
        nil
        ''nil))
   (t `(print-object$-fn ,x
                         ,(if (and serialize-character-p
                                   (not (eq serialize-character nil))
                                   (not (equal serialize-character ''nil)))
                              serialize-character
                            `(make print-control
                                   :header ,(if headerp
                                                header
                                              *newline-string*)
                                   :alist ,(print-object$+-alist args)))
                         ,channel
                         state))))

; Below are notions related to sysfiles and book-names.

; Essay on Book-names

; In October 2022 we completed changes to support relocation of book
; directories.  A key change was to use sysfiles, which are data structures of
; the form (:kwd . relative-pathname-string) as full-book-names when possible
; -- not only in book certificates but also in structures in the ACL2 world
; that contain full-book-names.  More specifically, full-book-names can now be
; either sysfiles or canonical absolute pathname strings.  We consistently use
; "full-book-name" in variable and record field names that represent arbitrary
; full-book-names for which a sysfile will be used whenever it can be.  By
; contrast, a "full-book-string" is a (generally canonical) absolute pathname
; string for a book.

; Note that entries (:kwd . string) in (project-dir-alist (w state)) resemble
; sysfiles, but their string component is an absolute pathname.  We do not
; consider these to be sysfiles, though the recognizer sysfile-p is too weak to
; make this distinction.

; As suggested above, the sysfile-filename of a sysfile is a relative pathname.
; In (project-dir-alist (w state)), a pair (:kwd . "dir/") -- not considered a
; sysfile, as noted above, as "dir/" is an absolute pathname -- maps :kwd to a
; canonical absolute directory pathname, "dir/".  Then in a book's certificate,
; the full-book-name for a book residing in "dir/path" (where "path" is thus a
; relative pathname) would be (:kwd . "path").

; When ACL2 uses a full-book-name, the sysfile form is preferred (when
; applicable; of course some pathnames don't lie under any directory in the
; project-dir-alist).  Thus, virtually all world structures use
; full-book-names, including the following, listed alphabetically.  (Note that
; namex is not included.)

;   *hcomp-book-ht*
;   *load-compiled-stack*
;   active-book-name
;   book-path (including include-book-path and package-entry-book-path)
;   bookdata file headers (see maybe-write-bookdata)
;   cert-obj record fields :pre-alist and :post-alist
;   ee-entry: the cadr, when the car is include-book
;   ignore-cert-files (state global)
;   include-book-alist
;   pcert-books (world global)
;   puff-included-books table
;   skip-proofs-seen
;   ttags-allowed
;   ttags-seen

; There are a few structures that use full-book-strings instead of
; full-book-names, because it seems more convenient to do so and this doesn't
; seem to get in the way of relocating book directories.  Among these are namex
; and the :full-book-string field of the useless-runes record.  But almost
; always we use full-book-names, not only to support relocation but also to
; simplify source code maintenance -- it seems easiest to assume that we are
; dealing with full-book-names (with very few exceptions), which in particular
; allows EQUAL to be used to determine whether two full-book-names refer to the
; same file, than to have to consider whether one might be a sysfile and the
; other a string.  It is simple to convert from full-book-names to
; full-book-strings, or vice-versa, using utilities defined below.

; A full-book-name always includes the .lisp extension, but a book-name that is
; not a full-book-name might or might not include that extension.  How that
; works out should be clear from context (otherwise we should add suitable
; comments).

(defmacro make-sysfile (key str)

; At one time we tried to save conses by returning `(quote (,key . ,str)) when
; (and (keywordp key) (stringp str)).  But with GCL 2.6.14 we got an error from
; confirm-apply-books during certification of "projects/apply/base.lisp",
; perhaps because of the call there of make-sysfile -- that may have created a
; code constant that is destructively modified somehow (e.g., by
; replace-project-dir-alist), though we haven't confirmed that.  At any rate,
; the error went away when we removed that special handling for (and (keywordp
; key) (stringp str)).

  `(cons ,key ,str))

(defun sysfile-p (x)

; This predicate is a weak recognizer for a sysfile, which is a pair (:kwd
; . "relative-pathname"), which represents the interpretation of the given
; relative pathname with respect to the absolute pathname associated with the
; given keyword in the project-dir-alist of the logical world.  A
; full-book-name is always either an absolute pathname or a sysfile.  See
; book-name-to-filename and valid-book-name-p.

  (declare (xargs :guard t))
  (and (consp x)
       (keywordp (car x))
       (stringp (cdr x))))

(defun sysfile-key (x)
  (declare (xargs :guard (sysfile-p x)))
  (car x))

(defun sysfile-filename (x)
  (declare (xargs :guard (sysfile-p x)))
  (cdr x))

(defun project-dir-alist (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (global-val 'project-dir-alist wrld))

(defun project-dir-lookup (key alist ctx)

; At the top level, alist is presumably (project-dir-alist (w state)).  We
; guarantee that the value of key in alist exists and is a string.  Except, we
; allow that to fail if ctx is nil, returning nil in that case.

; We use hons-assoc-equal below not because of hons (in fact hons-assoc-equal
; has no under-the-hood code for fast alists), but because its guard is t and
; that allows a guard of t here and simplifies guard verification.

  (declare (xargs :guard t))
  (let ((ans (cdr (hons-assoc-equal key alist))))
    (cond ((stringp ans)

; It is tempting to check (absolute-pathname-string-p str t (os (w state))),
; but we don't have state (or world) here.  The caller could supply it, or the
; caller could do the check; but actually, we know that this will truly be an
; absolute pathname, and if anyone needs that fact they can do the check.

           ans)
          ((null ctx) nil)
          (t (prog2$
              (er-hard? ctx "Missing project"
                        "The project-dir-alist needs an entry for the keyword ~
                         ~x0 but that keyword is missing the current ~
                         project-dir-alist, ~x1.  See :DOC project-dir-alist."
                        key alist)
; Dumb default so caller gets a sufficiently short string:
              *directory-separator-string*)))))

(defun project-dir (key wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (project-dir-lookup key (project-dir-alist wrld) 'project-dir))

(defun system-books-dir (state)

; As of this writing, this function is not used in the ACL2 sources.  But it's
; convenient to introduce it here for use in books.

  (declare (xargs :stobjs state))
  (project-dir :system (w state)))

(defun string-prefixp-1 (str1 i str2)
  (declare (type string str1 str2)
           (type #.*fixnat-type* i)
           (xargs :guard (and (<= i (length str1))
                              (<= i (length str2)))))
  (cond ((zpf i) t)
        (t (let ((i (1-f i)))
             (declare (type #.*fixnat-type* i))
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

(defun project-dir-prefix-entry (filename project-dir-alist)

; Return the first entry in project-dir-alist whose filename is a prefix of the
; given filename, if there is one.  Otherwise return nil, which is appropriate
; when filename isn't under a project directory.

  (declare (xargs :guard (stringp filename)))
  (cond ((atom project-dir-alist) nil)
        ((and (consp (car project-dir-alist)) ; always t (for guard proof)
              (stringp (cdar project-dir-alist)) ; always t (for guard proof)
              (<= (length (cdar project-dir-alist))
                  (fixnum-bound)) ; (for guard proof)
              (string-prefixp (cdar project-dir-alist) filename))
         (car project-dir-alist))
        (t (project-dir-prefix-entry filename (cdr project-dir-alist)))))

(defun filename-to-book-name-1 (filename project-dir-alist)

; This version of filename-to-book-name takes a project-dir-alist instead of a
; world.

  (declare (xargs :guard t))
  (let ((pair (and (stringp filename)
                   (project-dir-prefix-entry filename
                                             project-dir-alist))))

    (cond (pair ; (:kwd . "relative-pathname/")
           (make-sysfile (car pair)
                         (subseq filename (length (cdr pair)) nil)))
          (t filename))))

(defun filename-to-book-name (filename wrld)

; Filename is a (pathname) string.  If there is a corresponding valid sysfile
; then that is returned; otherwise filename is returned unchanged.  In
; particular, filename is returned unchanged if it is a relative pathname.

  (declare (xargs :guard (plist-worldp wrld)))
  (filename-to-book-name-1 filename (project-dir-alist wrld)))

(defun our-merge-pathnames (p s)

; This is something like the Common Lisp function merge-pathnames.  P and s are
; (Unix-style) pathname strings, where s is a relative pathname.  (If s may be
; an absolute pathname, use extend-pathname instead.)  We allow p to be nil,
; which is a case that arises when p is (f-get-global 'connected-book-directory
; state) during boot-strapping; otherwise p should be an absolute directory
; pathname (though we allow "" as well).

  (cond
   ((and (not (equal s ""))
         (eql (char s 0) *directory-separator*))
    (er hard 'our-merge-pathnames
        "Attempt to merge with an absolute filename, ~p0.  Please contact the ~
         ACL2 implementors."
        s))
   ((or (null p) (equal p ""))
    s)
   ((stringp p) ; checked because of structured pathnames before Version_2.5
    (merge-using-dot-dot
     (if (eql (char p (1- (length p)))
              *directory-separator*)
         (subseq p 0 (1- (length p)))
       p)
     s))
   (t
    (er hard 'our-merge-pathnames
        "The first argument of our-merge-pathnames must be a string, ~
         but the following is not:  ~p0."
        p))))

(defun book-name-p (x)

; This predicate is a basic recognizer for book-names.  See also
; valid-book-name-p, which is more restrictive.

  (declare (xargs :guard t))
  (or (stringp x)
      (sysfile-p x)))

(defun book-name-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (book-name-p (car x))
                (book-name-listp (cdr x))))))

(defun book-name-to-filename-1 (x project-dir-alist ctx)

; See book-name-to-filename and especially the Warning there.

  (declare (xargs :guard (book-name-p x)))
  (cond
   ((consp x) ; (sysfile-p x)
    (let ((dir (project-dir-lookup (sysfile-key x)
                                   project-dir-alist
                                   ctx)))
      (and (stringp dir) ; true if ctx is non-nil; otherwise error occurred
           (concatenate 'string dir (sysfile-filename x)))))
   (t x)))

(defun book-name-to-filename (x wrld ctx)

; If x is a sysfile then we return the absolute pathname obtained by
; concatenating the absolute directory string represented by the sysfile-key of
; x with the sysfile-filename of x, which should be a relative pathname.

; If x is a sysfile whose key is not in the project-dir-alist of wrld, then a
; hard error occurs using ctx if ctx is not nil.  Otherwise nil is returned.

; Warning: The resulting filename need not be canonical unless x is a
; full-book-name (such as key of the include-book-alist, for example); e.g., it
; may contain soft links or "..".

  (declare (xargs :guard (and (book-name-p x)
                              (plist-worldp wrld))))
  (cond ((and (consp x) ; (sysfile-p x)
              (absolute-pathname-string-p (sysfile-filename x)
                                          nil
                                          (os wrld)))
         (er hard? ctx
             "Implementation error the sysfile ~x0 has an absolute pathname as ~
             its sysfile-filename component."
             x))
        (t (book-name-to-filename-1 x (project-dir-alist wrld) ctx))))

(defun book-name-lst-to-filename-lst (x project-dir-alist ctx)

; Note that unlike book-name-to-filename (but like book-name-to-filename-1),
; the second argument is a project-dir-alist rather than the world in which it
; sits.  (Otherwise the project-dir-alist would need to be accessed from the
; world for each sysfile element of the list, x.)

; Ctx should be non-nil, resulting in an error when a sysfile cannot be
; interpreted with respect to project-dir-alist, unless the caller is prepared
; to check for nil in the list that is returned.

; This checks (via assert$ in book-name-to-filename), for each sysfile in x,
; that its filename is a relative pathname.  If it is desired to avoid that
; check, write a version of this function that calls book-name-to-filename-1
; instead of book-name-to-filename.  As of this writing, efficiency does not
; seem to be a concern for calls of this function.

  (declare (xargs :guard (book-name-listp x)))
  (cond
   ((endp x) nil)
   (t (cons (book-name-to-filename-1 (car x) project-dir-alist ctx)
            (book-name-lst-to-filename-lst (cdr x) project-dir-alist ctx)))))

(defun valid-book-name-p (x os project-dir-alist)

; See also the weaker book-name recognizer, book-name-p.  Even the present
; recognizer could be strengthened, by insisting that if x is a sysfile then
; its key is bound to the longest possible prefix for the file represented.
; The strongest predicate would be to proceed as in translate-book-names:
; translate a sysfile x to a full-book-name using book-name-to-filename-1,
; canonicalize using extend-pathname or extend-pathname+, and then translate
; back to a (presumed) sysfile with filename-to-book-name-1.  The result should
; be x.

  (or (stringp x)
      (and (sysfile-p x)
           (project-dir-lookup (sysfile-key x) project-dir-alist nil)
           (stringp (sysfile-filename x))
           (not (absolute-pathname-string-p (sysfile-filename x) nil os)))))

(defun get-invalid-book-name-1 (lst os project-dir-alist)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((valid-book-name-p (car lst) os project-dir-alist)
         (get-invalid-book-name-1 (cdr lst) os project-dir-alist))
        (t (car lst))))

(defun get-invalid-book-name (lst os wrld)
  (declare (xargs :guard (and (true-listp lst)
                              (plist-worldp wrld))))
  (get-invalid-book-name-1 lst os (project-dir-alist wrld)))

(defun append-strip-cars (x y)

; This is (append (strip-cars x) y).

  (cond ((null x) y)
        (t (cons (car (car x)) (append-strip-cars (cdr x) y)))))

(defun append-strip-cdrs (x y)

; This is (append (strip-cdrs x) y).

  (cond ((null x) y)
        (t (cons (cdr (car x)) (append-strip-cdrs (cdr x) y)))))

(defun substring-p (i1 s1 len i2 s2)

; This predicate recognizes when the substring of s1 (with length len) starting
; at s1 equals the substring of s2 starting at i2.

  (declare (type string s1 s2)
           (type (integer 0 *) i1 len i2)
           (xargs :guard (and (<= i1 len)
                              (= len (length s1))
; There is at least as much room to increase i2 as there is to increase i1:
                              (>= (- (length s2) i2)
                                  (- len i1)))
                  :measure (nfix (- len i1))))
  (cond ((mbe :logic (not (and (natp i1)
                               (natp len)
                               (< i1 len)))
              :exec (= i1 len))
         t)
        ((eql (the character (char s1 i1))
              (the character (char s2 i2)))
         (substring-p (1+ i1) s1 len (1+ i2) s2))
        (t nil)))

(defun string-suffixp (suffix string)
  (declare (type string suffix string))
  (let ((len-suffix (length suffix))
        (len-string (length string)))
    (and (<= len-suffix len-string)
         (substring-p 0 suffix len-suffix
                      (- len-string len-suffix) string))))
