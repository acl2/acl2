; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

(in-package "ACL2")

(deflabel syntax
  :doc
  ":Doc-Section Miscellaneous

  the syntax of ACL2 is that of Common Lisp~/

  For the details of ACL2 syntax, see CLTL.  For examples of ACL2
  syntax, use ~c[:]~ilc[pe] to print some of the ACL2 system code.  For example:
  ~bv[]
  :pe assoc-equal
  :pe dumb-occur
  :pe var-fn-count
  :pe add-linear-variable-to-alist
  ~ev[]~/

  There is no comprehensive description of the ACL2 syntax yet, except
  that found in CLTL.  Also ~pl[term].")

(deflabel term
  :doc
  ":Doc-Section Miscellaneous

  the three senses of well-formed ACL2 expressions or formulas~/
  ~bv[]
  Examples of Terms:
  (cond ((caar x) (cons t x)) (t 0))   ; an untranslated term

  (if (car (car x)) (cons 't x) '0)    ; a translated term

  (car (cons x y) 'nil v)              ; a pseudo-term
  ~ev[]~/

  In traditional first-order predicate calculus a ``term'' is a
  syntactic entity denoting some object in the universe of
  individuals.  Often, for example, the syntactic characterization of
  a term is that it is either a variable symbol or the application of
  a function symbol to the appropriate number of argument terms.
  Traditionally, ``atomic formulas'' are built from terms with
  predicate symbols such as ``equal'' and ``member;'' ``formulas'' are
  then built from atomic formulas with propositional ``operators''
  like ``not,'' ``and,'' and ``implies.'' Theorems are formulas.
  Theorems are ``valid'' in the sense that the value of a theorem is
  true, in any model of the axioms and under all possible assignments
  of individuals to variables.

  However, in ACL2, terms are used in place of both atomic formulas
  and formulas.  ACL2 does not have predicate symbols or propositional
  operators as distinguished syntactic entities.  The ACL2 universe of
  individuals includes a ``true'' object (denoted by ~c[t]) and a
  ``false'' object (denoted by ~c[nil]), predicates and propositional
  operators are functions that return these objects.  Theorems in ACL2
  are terms and the ``validity'' of a term means that, under no
  assignment to the variables does the term evaluate to ~c[nil].

  We use the word ``term'' in ACL2 in three distinct senses.  We will
  speak of ``translated'' terms, ``untranslated'' terms, and
  ``pseudo-'' terms.

  ~em[Translated Terms:  The Strict Sense and Internal Form]

  In its most strict sense, a ``term'' is either a legal variable
  symbol, a quoted constant, or the application of an n-ary function
  symbol or closed ~c[lambda] expression to a true list of n terms.

  The legal variable symbols are symbols other than ~c[t] or ~c[nil]
  which are not in the keyword package, do not start with ampersand,
  do not start and end with asterisks, and if in the main Lisp
  package, do not violate an appropriate restriction (~pl[name]).

  Quoted constants are expressions of the form ~c[(quote x)], where ~c[x] is
  any ACL2 object.  Such expressions may also be written ~c['x].

  Closed ~c[lambda] expressions are expressions of the form
  ~c[(lambda (v1 ... vn) body)] where the ~c[vi] are distinct legal
  variable symbols, ~c[body] is a term, and the only free variables in
  ~c[body] are among the ~c[vi].

  The function ~c[termp], which takes two arguments, an alleged term ~c[x] and
  a logical world ~c[w] (~pl[world]), recognizes terms of a given
  extension of the logic.  ~c[Termp] is defined in ~c[:]~ilc[program] mode.
  Its definition may be inspected with ~c[:]~ilc[pe] ~c[termp] for a complete
  specification of what we mean by ``term'' in the most strict sense.
  Most ACL2 term-processing functions deal with terms in this strict
  sense and use ~c[termp] as a ~il[guard].  That is, the ``internal form''
  of a term satisfies ~c[termp], the strict sense of the word ``term.''

  ~em[Untranslated Terms:  What the User Types]

  While terms in the strict sense are easy to explore (because their
  structure is so regular and simple) they can be cumbersome to type.
  Thus, ACL2 supports a more sugary syntax that includes uses of
  macros and constant symbols.  Very roughly speaking, macros are
  functions that produce terms as their results.  Constants are
  symbols that are associated with quoted objects.  Terms in this
  sugary syntax are ``translated'' to terms in the strict sense; the
  sugary syntax is more often called ``untranslated.''  Roughly
  speaking, translation just implements macroexpansion, the
  replacement of constant symbols by their quoted values, and the
  checking of all the rules governing the strict sense of ``term.''

  More precisely, macro symbols are as described in the documentation
  for ~ilc[defmacro].  A macro, ~c[mac], can be thought of as a function,
  ~c[mac-fn], from ACL2 objects to an ACL2 object to be treated as an
  untranslated term.  For example, ~ilc[caar] is defined as a macro symbol;
  the associated macro function maps the object ~c[x] into the object
  ~c[(car (car x))].  A macro form is a ``call'' of a macro symbol,
  i.e., a list whose ~ilc[car] is the macro symbol and whose ~ilc[cdr] is an
  arbitrary true list of objects, used as a term.  Macroexpansion is
  the process of replacing in an untranslated term every occurrence of
  a macro form by the result of applying the macro function to the
  appropriate arguments.  The ``appropriate'' arguments are determined
  by the exact form of the definition of the macro; macros support
  positional, keyword, optional and other kinds of arguments.
  ~l[defmacro].

  In addition to macroexpansion and constant symbol dereferencing,
  translation implements the mapping of ~ilc[let] and ~ilc[let*] forms into
  applications of ~c[lambda] expressions and closes ~c[lambda] expressions
  containing free variables.  Thus, the translation of
  ~bv[]
  (let ((x (1+ i))) (cons x k))
  ~ev[]
  can be seen as a two-step process that first produces
  ~bv[]
  ((lambda (x) (cons x k)) (1+ i))
  ~ev[]
  and then
  ~bv[]
  ((lambda (x k) (cons x k)) (1+ i) k) .
  ~ev[]
  Observe that the body of the ~ilc[let] and of the first ~c[lambda]
  expression contains a free ~c[k] which is finally bound and passed
  into the second ~c[lambda] expression.

  Translation also maps ~ilc[flet] forms into applications of ~c[lambda]
  expressions.  ~l[flet].

  When we say, of an event-level function such as ~ilc[defun] or ~ilc[defthm],
  that some argument ``must be a term'' we mean an untranslated term.
  The event functions translate their term-like arguments.

  To better understand the mapping between untranslated terms and
  translated terms it is convenient to use the keyword command ~c[:]~ilc[trans]
  to see examples of translations.  ~l[trans] and also
  ~pl[trans1].

  Finally, we note that the theorem prover prints terms in
  untranslated form.  But there can be more than one correct untranslated
  term corresponding to a given translated term.  For example, the
  translated term ~c[(if x y 'nil)] can be untranslated as ~c[(if x y nil)]
  and can also be untranslated as ~c[(and x y)].  The theorem prover
  attempts to print an untranslated term that is as helpful to the
  user as possible.  In particular, consider a term of the form
  ~c[(nth k st)] where ~c[st] is a single-threaded object
  (~pl[stobj]) and the ~c[kth] accessor of ~c[st] is, say, ~c[kn].  The
  theorem prover typically would expand ~c[(kn st)] to ~c[(nth k st)].  If
  ~c[k] is large then it could be difficult for the user to make sense out
  of a proof transcript that mentions the expanded term.  Fortunately,
  the untranslation of ~c[(nth k st)] would be ~c[(nth *kn* st)]; here
  ~c[*kn*] would be a constant (~pl[defconst]) added by the ~ilc[defstobj]
  event introducing ~c[st], defined to have value ~c[k].  The user can
  extend this user-friendly style of printing applications of ~ilc[nth] to
  stobjs; ~pl[add-nth-alias].  These remarks about printing
  applications of function ~ilc[nth] extend naturally to function
  ~ilc[update-nth].  Moreover, the prover will attempt to treat terms as
  ~il[stobj]s for the above purpose when appropriate.  For example, if
  function ~c[foo] has ~il[signature] ~c[((foo * st) => (mv * * * st))], where
  ~c[st] is introduced with ~c[(defstobj st f0 f1)], then the ~il[term]
  ~c[(nth '1 (mv-nth '3 (foo x st0)))] will be printed as
  ~c[(nth *f1* (mv-nth 3 (foo x st0)))].

  ~em[Pseudo-Terms:  A Common Guard for Metafunctions]

  Because ~c[termp] is defined in ~c[:]~ilc[program] mode, it cannot be used
  effectively in conjectures to be proved.  Furthermore, from the
  perspective of merely guarding a term processing function, ~c[termp]
  often checks more than is required.  Finally, because ~c[termp]
  requires the logical ~il[world] as one of its arguments it is impossible
  to use ~c[termp] as a ~il[guard] in places where the logical ~il[world] is not
  itself one of the arguments.

  For these reasons we support the idea of ``pseudo-terms.''  A
  pseudo-term is either a symbol (but not necessarily one having the
  syntax of a legal variable symbol), a true list beginning with ~c[quote]
  (but not necessarily well-formed), or the ``application of'' a
  symbol or pseudo ~c[lambda] expression to a true list of
  pseudo-terms.  A pseudo ~c[lambda] expression is an expression of the
  form ~c[(lambda (v1 ... vn) body)] where the ~c[vi] are all symbols
  and ~c[body] is a pseudo-term.

  Pseudo-terms are recognized by the unary function ~ilc[pseudo-termp].  If
  ~c[(termp x w)] is true, then ~c[(pseudo-termp x)] is true.  However, if ~c[x]
  fails to be a (strict) term it may nevertheless still be a
  pseudo-term.  For example, ~c[(car a b)] is not a term, because ~ilc[car] is
  applied to the wrong number of arguments, but it is a pseudo-term.

  The structures recognized by ~ilc[pseudo-termp] can be recursively
  explored with the same simplicity that terms can be.  In particular,
  if ~c[x] is not a ~c[variablep] or an ~c[fquotep], then ~c[(ffn-symb x)] is the
  function (~c[symbol] or ~c[lambda] expression) and ~c[(fargs x)] is the list of
  argument pseudo-terms.  A metafunction (~pl[meta]) or clause-processor
  (~pl[clause-processor]) may use ~ilc[pseudo-termp] as the ~il[guard].")

(mutual-recursion

(defun termp (x w)
  (cond ((atom x) (legal-variablep x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cddr x))))
        ((symbolp (car x))
         (let ((arity (arity (car x) w)))
           (and arity
                (true-listp (cdr x))
                (eql (length (cdr x)) arity)
                (term-listp (cdr x) w))))
        ((and (consp (car x))
              (true-listp (car x))
              (eq (car (car x)) 'lambda)
              (equal 3 (length (car x)))
              (arglistp (cadr (car x)))
              (termp (caddr (car x)) w)
              (null (set-difference-eq
                     (all-vars (caddr (car x)))
                     (cadr (car x))))
              (term-listp (cdr x) w)
              (equal (length (cadr (car x)))
                     (length (cdr x))))
         t)
        (t nil)))

(defun term-listp (x w)
  (cond ((atom x) (equal x nil))
        ((termp (car x) w) (term-listp (cdr x) w))
        (t nil)))

)

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

  ":Doc-Section Miscellaneous

  the formals list of a macro definition~/
  ~bv[]
  Examples:
  (x y z)
  (x y z &optional max (base '10 basep))
  (x y &rest rst)
  (x y &key max base)
  (&whole sexpr x y)
  ~ev[]~/

  The ``lambda-list'' of a macro definition may include simple formal
  parameter names as well as appropriate uses of the following
  ~c[lambda]-list keywords from CLTL (pp. 60 and 145), respecting the
  order shown:
  ~bv[]
    &whole,
    &optional,
    &rest,
    &body,
    &key, and
    &allow-other-keys.
  ~ev[]
  ACL2 does not support ~c[&aux] and ~c[&environment].  In addition, we make
  the following restrictions:~bq[]

  (1) initialization forms in ~c[&optional] and ~c[&key] specifiers must be
  quoted values;

  (2) ~c[&allow-other-keys] may only be used once, as the last specifier; and

  (3) destructuring is not allowed.

  ~eq[]You are encouraged to experiment with the macro facility.  One way
  to do so is to define a macro that does nothing but return the
  quotation of its arguments, e.g.,
  ~bv[]
  (defmacro demo (x y &optional opt &key key1 key2)
    (list 'quote (list x y opt key1 key2)))
  ~ev[]
  You may then execute the macro on some sample forms, e.g.,
  ~bv[]
    term                         value
  (demo 1 2)                (1 2 NIL NIL NIL)
  (demo 1 2 3)              (1 2 3 NIL NIL)
  (demo 1 2 :key1 3)        error:  non-even key/value arglist
                            (because :key1 is used as opt)
  (demo 1 2 3 :key2 5)      (1 2 3 NIL 5)
  ~ev[]
  In particular, Common Lisp specifies that if you use both ~c[&rest] and
  ~c[&key], then both will be bound using the same list of arguments.  The
  following example should serve to illustrate how this works.
  ~bv[]
  ACL2 !>(defmacro foo (&rest args &key k1 k2 k3)
           (list 'quote (list args k1 k2 k3)))

  Summary
  Form:  ( DEFMACRO FOO ...)
  Rules: NIL
  Warnings:  None
  Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
   FOO
  ACL2 !>(foo :k1 3 :k2 4 :k3 5)
  ((:K1 3 :K2 4 :K3 5) 3 4 5)
  ACL2 !>(foo :k1 3 :k2 4)
  ((:K1 3 :K2 4) 3 4 NIL)
  ACL2 !>
  ~ev[]

  Also ~pl[trans].~/"

  (getprop x 'macro-args
           '(:error "We thought macro-args was only called if there ~
                     were (zero or more) macro-args.")
           'current-acl2-world w))

(defconst *macro-expansion-ctx* "macro expansion")

(defun remove-keyword (word l)
  (cond ((null l) nil)
        ((eq word (car l))
         (remove-keyword word (cddr l)))
        (t (list* (car l) (cadr l) (remove-keyword word (cddr l))))))

(defun ev-fncall-null-body-er (fn latches)
  (mv t
      (msg "ACL2 cannot evaluate the undefined function ~x0." fn)
      latches))

(defconst *safe-mode-guard-er-addendum*
  "  The guard is being checked because this function is a primitive and a ~
   \"safe\" mode is being used for macroexpansion, defpkg, or another ~
   operation where safe mode is required.")

(defun error-trace-suggestion (two-leading-spaces)

; Warning: Do not eliminate the message about print-gv without first reading
; the comment about it in ev-fncall-guard-er-msg.

  (declare (xargs :mode :program))
  (msg "~s0To debug see :DOC print-gv, see :DOC trace, and see :DOC wet."
       (if two-leading-spaces
           "  "
         "")))

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

            #-acl2-loop-only
            ((and temp (eq (cdr temp) (car vals)))
             (latch-stobjs1 (cdr stobjs-out)
                            (cdr vals)
                            latches))
            (temp
             (latch-stobjs1 (cdr stobjs-out)
                            (cdr vals)
                            (put-assoc-eq (car stobjs-out)
                                          (car vals)
                                          latches)))
            (t (er hard 'latch-stobjs
                   "We are trying to latch a value for the ~
                    single-threaded object named ~x0, but there is no ~
                    entry for that name in the stobj latches ~
                    provided.  The possible latch names are ~
                    ~&1.~#2~[~/  This error most likely is caused by ~
                    the attempt to ev a form that is not ``supposed'' ~
                    to mention stobjs but does.  Often when dealing ~
                    with forms that are not supposed to mention ~
                    stobjs we call ev with last argument NIL and then ~
                    ignore the resulting latches.~]"
                   (car stobjs-out)
                   (strip-cars latches)
                   (if latches 0 1))))))
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

#-acl2-loop-only
; We deliberately do not assign a value for the following.  It is let-bound in
; ev and friends and assigned during the evaluation of *1* functions.  If we
; call *1* functions directly in raw Lisp, we will presumably get an
; unbound-variable error, but at least that will call our attention to the fact
; that it should be bound before calling *1* functions.
(defvar *raw-guard-warningp*)

#-acl2-loop-only
(defun raw-ev-fncall (fn args latches hard-error-returns-nilp aok)
  (let ((*aokp* aok))
    (the #+acl2-mv-as-values (values t t t)
         #-acl2-mv-as-values t
         (let* ((w (w *the-live-state*))
                (throw-raw-ev-fncall-flg t)
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
                #+acl2-mv-as-values ; stobjs-out might not be needed otherwise
                (stobjs-out (if (eq fn 'return-last)

; Things can work out fine if we imagine that return-last returns a single
; value: in the case of (return-last ... (mv ...)), the mv returns a list and
; we just pass that along.

                                '(nil)
                              (stobjs-out fn w)))
                (val (catch 'raw-ev-fncall
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

                (w (w *the-live-state*)))

; Observe that if a throw to 'raw-ev-fncall occurred during the 
; (apply fn args) then the local variable throw-raw-ev-fncall-flg
; is t and otherwise it is nil.  If a throw did occur, val is the
; value thrown.

           (cond
            (throw-raw-ev-fncall-flg
             (mv t (ev-fncall-msg val w) latches))
            (t #-acl2-mv-as-values ; adjust val for the multiple value case
               (let* ((stobjs-out ; see comment in earlier stobjs-out binding
                       (if (eq fn 'return-last)
                           '(nil)
                         (stobjs-out fn w)))
                      (val
                       (cond ((null (cdr stobjs-out)) val)
                             (t (cons val (mv-refs (1- (length stobjs-out))))))))
                 (mv nil
                     val
                     (latch-stobjs stobjs-out
                                   val
                                   latches)))
               #+acl2-mv-as-values ; val already adjusted for multiple value case
               (mv nil
                   val
                   (latch-stobjs stobjs-out
                                 val
                                 latches))))))))

(defun translated-acl2-unwind-protectp4 (term)

; This hideous looking function recognizes those terms that are the
; translations of (acl2-unwind-protect "expl" body cleanup1 cleanup2).
; The acl2-unwind-protect macro expands into an MV-LET and that MV-LET
; is translated in one of two ways depending on whether it occurs in a
; definition body (i.e., stobjs-out of translate11 is non-t) or in a
; definition (i.e., stobjs-out is t).  We look for both translations.
; We return 4 results.  The first is t or nil according to whether
; term is of one of the two forms.  If nil, the other results are nil.
; If term is of either form, we return in the other three results:
; body, cleanup1 and cleanup2 such that term is equivalent to
; (acl2-unwind-protect "expl" body cleanup1 cleanup2).

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
   ((('LAMBDA ('ACL2-UNWIND-PROTECT-ERP
               'ACL2-UNWIND-PROTECT-VAL 'STATE . vars) 
      ('IF 'ACL2-UNWIND-PROTECT-ERP 
           ('(LAMBDA (STATE ACL2-UNWIND-PROTECT-VAL ACL2-UNWIND-PROTECT-ERP) 
                     (CONS ACL2-UNWIND-PROTECT-ERP 
                           (CONS ACL2-UNWIND-PROTECT-VAL
                                 (CONS STATE 'NIL)))) 
            cleanup1 'ACL2-UNWIND-PROTECT-VAL 'ACL2-UNWIND-PROTECT-ERP) 
           ('(LAMBDA (STATE ACL2-UNWIND-PROTECT-VAL ACL2-UNWIND-PROTECT-ERP) 
                     (CONS ACL2-UNWIND-PROTECT-ERP 
                           (CONS ACL2-UNWIND-PROTECT-VAL
                                 (CONS STATE 'NIL)))) 
            cleanup2 'ACL2-UNWIND-PROTECT-VAL 'ACL2-UNWIND-PROTECT-ERP))) 
     ('MV-NTH ''0 body) 
     ('MV-NTH ''1 body) 
     ('MV-NTH ''2 body) 
     . vars)
    (declare (ignore vars))
    (mv t body cleanup1 cleanup2))
   (& (mv nil nil nil nil))))

(defun translated-acl2-unwind-protectp (term)

; Just for convenience we define the predicate version of translated-acl2-
; unwind-protectp4 to return t or nil according to whether term is the
; translation of an acl2-unwind-protect expression.

  (mv-let (ans body cleanup1 cleanup2)
          (translated-acl2-unwind-protectp4 term)
          (declare (ignore body cleanup1 cleanup2))
          ans))

(defun stobjp (x known-stobjs w)

; We recognize whether x is to be treated as a stobj name.
; Known-stobjs is a list of all such names, or else T, standing for
; all stobj names in w.  During translation, only a subset of the
; known stobjs in w are considered stobjs, as per the user's :stobjs
; declare xargs.  If you want to know whether x has been defstobj'd in
; w, use known-stobjs = t.

; Slight abuse permitted: Sometimes known-stobjs will be a list of
; stobj flags!  E.g., we might supply (NIL NIL STATE NIL $S) where
; (STATE $S) is technically required.  But we should never ask if NIL
; is a stobj because we only ask this of variable symbols.  But just
; to make this an ironclad guarantee, we include the first conjunct
; below.

  (and x
       (symbolp x)
       (if (eq known-stobjs t)
           (getprop x 'stobj nil 'current-acl2-world w)
         (member-eq x known-stobjs))))

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
;                   (INFIXP)
;                   (INHIBIT-OUTPUT-LST SUMMARY)
;                   (IN-LOCAL-FLG . NIL)
;                   (LD-LEVEL . 0)
;                   (LD-REDEFINITION-ACTION)
;                   (LD-SKIP-PROOFSP)
;                   (MORE-DOC-MAX-LINES . 45)
;                   (MORE-DOC-MIN-LINES . 35)
;                   (MORE-DOC-STATE)
;                   (PRINT-DOC-START-COLUMN . 15)
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

; Name is a name defined in wrld.  We determine whether it is one of ours or is
; user-defined.

; If name is not defined -- more precisely, if we have not yet laid down an
; 'absolute-event-number property for it -- then we return nil except in the
; boot-strap world.

  (cond ((global-val 'boot-strap-flg wrld) t)
        (t (getprop name 'predefined nil 'current-acl2-world wrld))))

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
; acl2.lisp, to avoid a CLISP complier warning.

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
                 (binop-table ,wrld)
                 (untranslate-preprocess-fn ,wrld)
                 ,wrld))

#-acl2-loop-only
(defmacro raw-guard-warningp-binding ()

; We bind *raw-guard-warningp* in calls of ev-fncall, ev, ev-lst, ev-w,
; ev-w-lst, and ev-fncall-w.  The initial binding is t if guard-checking is on,
; else nil.  When a *1* function is poised to call warn-for-guard-body to print
; a warning related to guard violations, it first checks that
; *raw-guard-warningp*.  Hence, we do not want to re-assign this variable once
; it is bound to nil by warn-for-guard-body, because we only want to see the
; corresponding guard warning once per top-level evaluation.  We do however
; want to re-assign this variable from t to nil once the warning has been
; printed and also if guard-checking has been turned off, in particular for the
; situation involving the prover that is described in the next paragraph.  (But
; if guard-checking were, surprisingly, to transition instead from nil to t,
; and we failed to re-assign this variable from nil to t, we could live with
; that.)

; Note that *raw-guard-warningp* will be bound to t just under the trans-eval
; at the top level.  If we then enter the prover we will bind guard-checking-on
; to nil, and we then want to re-bind *raw-guard-warningp* to nil if we enter
; ev-fncall during the proof, so that the proof output will not contain guard
; warning messages.  (This was handled incorrectly in Version_2.9.1.)

  '(if (and (boundp '*raw-guard-warningp*)
            (null *raw-guard-warningp*)) 
       nil
     (eq (f-get-global 'guard-checking-on *the-live-state*)
         t)))

(defun untouchable-fn-p (fn w)
  (and (not (member-eq fn *user-defined-functions-table-keys*)) ; optimization
       (member-eq fn (global-val 'untouchable-fns w))))

(defun save-ev-fncall-guard-er (fn guard stobjs-in args)
  (wormhole-eval 'ev-fncall-guard-er-wormhole
                 '(lambda (whs)
                    (make-wormhole-status
                     whs
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
  (declare (xargs :guard (doubleton-list-p bindings)))
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
                     (binop-table ,wrld)
                     (untranslate-preprocess-fn ,wrld)
                     ,wrld))

(mutual-recursion

; Here we combine what may naturally be thought of as two separate
; mutual-recursion nests: One for evaluation and one for untranslate.  However,
; functions in the ev nest call untranslate1 for error messages, and
; untranslate1 calls ev-fncall-w.  We are tempted to place the definitions of
; the untranslate functions first, but Allegro CL (6.2 and 7.0) produces a
; bogus warning in that case (which goes away if the char-code case is
; eliminated from ev-fncall-rec-logical!).

(defun ev-fncall-rec-logical (fn args w big-n safe-mode gc-off latches
                                 hard-error-returns-nilp aok)

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
           (guard-checking-off
            (and gc-off (not safe-mode-requires-check)))
           (extra (and gc-off
                       (cond (safe-mode-requires-check t)
                             ((getprop fn 'stobj-function nil
                                       'current-acl2-world w)
                              :live-stobj)
                             (t nil)))))

; Keep this in sync with *primitive-formals-and-guards*.

      (case fn
        (ACL2-NUMBERP
         (mv nil (acl2-numberp x) latches))
        (BAD-ATOM<=
         (cond ((or guard-checking-off
                    (and (bad-atom x)
                         (bad-atom y)))
                (mv nil (bad-atom<= x y) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (BINARY-*
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (acl2-numberp y)))
                (mv nil
                    (* x y)
                    latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (BINARY-+
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (acl2-numberp y)))
                (mv nil (+ x y) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (UNARY--
         (cond ((or guard-checking-off
                    (acl2-numberp x))
                (mv nil (- x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (UNARY-/
         (cond ((or guard-checking-off
                    (and (acl2-numberp x)
                         (not (= x 0))))
                (mv nil (/ x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (<
         (cond ((or guard-checking-off
                    (and (real/rationalp x)
                         (real/rationalp y)))
                (mv nil (< x y) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (CAR
         (cond ((or guard-checking-off
                    (or (consp x)
                        (eq x nil)))
                (mv nil (car x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (CDR
         (cond ((or guard-checking-off
                    (or (consp x)
                        (eq x nil)))
                (mv nil (cdr x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (CHAR-CODE
         (cond ((or guard-checking-off
                    (characterp x))
                (mv nil (char-code x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (CHARACTERP
         (mv nil (characterp x) latches))
        (CODE-CHAR
         (cond ((or guard-checking-off
                    (and (integerp x)
                         (<= 0 x)
                         (< x 256)))
                (mv nil (code-char x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (COMPLEX
         (cond ((or guard-checking-off
                    (and (real/rationalp x)
                         (real/rationalp y)))
                (mv nil (complex x y) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
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
               (t (ev-fncall-guard-er fn args w latches extra))))
        (CONS
         (mv nil (cons x y) latches))
        (CONSP
         (mv nil (consp x) latches))
        (DENOMINATOR
         (cond ((or guard-checking-off
                    (rationalp x))
                (mv nil (denominator x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (EQUAL
         (mv nil (equal x y) latches))
        #+:non-standard-analysis
        (FLOOR1
         (cond ((or guard-checking-off
                    (realp x))
                (mv nil (floor x 1) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (IF
         (mv nil
             (er hard 'ev-fncall-rec
                 "This function should not be called with fn = 'IF!")
             latches))
        (IMAGPART
         (cond ((or guard-checking-off
                    (acl2-numberp x))
                (mv nil (imagpart x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (INTEGERP
         (mv nil (integerp x) latches))
        (INTERN-IN-PACKAGE-OF-SYMBOL
         (cond ((or guard-checking-off
                    (and (stringp x)
                         (symbolp y)))
                (mv nil (intern-in-package-of-symbol x y) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (NUMERATOR
         (cond ((or guard-checking-off
                    (rationalp x))
                (mv nil (numerator x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (PKG-IMPORTS
         (cond ((or guard-checking-off
                    (stringp x))
                (mv nil (pkg-imports x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (PKG-WITNESS
         (cond ((or guard-checking-off
                    (and (stringp x) (not (equal x ""))))
                (mv nil (pkg-witness x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (RATIONALP
         (mv nil (rationalp x) latches))
        #+:non-standard-analysis
        (REALP
         (mv nil (realp x) latches))
        (REALPART
         (cond ((or guard-checking-off
                    (acl2-numberp x))
                (mv nil (realpart x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (STRINGP
         (mv nil (stringp x) latches))
        (SYMBOL-NAME
         (cond ((or guard-checking-off
                    (symbolp x))
                (mv nil (symbol-name x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
        (SYMBOL-PACKAGE-NAME
         (cond ((or guard-checking-off
                    (symbolp x))
                (mv nil (symbol-package-name x) latches))
               (t (ev-fncall-guard-er fn args w latches extra))))
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
         (ev-fncall-null-body-er fn latches))
        (otherwise
         (let ((alist (pairlis$ (formals fn w) args))
               (body (body fn nil w))
               (attachment (and aok
                                (cdr (assoc-eq fn (all-attachments w))))))
           (mv-let
            (er val latches)
            (ev-rec (if guard-checking-off
                        ''t
                      (guard fn nil w))
                    alist
                    w (decrement-big-n big-n) (eq extra t) guard-checking-off
                    latches
                    hard-error-returns-nilp
                    aok)
            (cond
             (er (mv er val latches))
             ((null val)
              (ev-fncall-guard-er fn args w latches extra))
             (attachment
              (ev-fncall-rec-logical attachment args w
                                     (decrement-big-n big-n)
                                     safe-mode gc-off latches
                                     hard-error-returns-nilp aok))
             ((null body)
              (ev-fncall-null-body-er fn latches))
             (t
              (mv-let
               (er val latches)
               (ev-rec body alist
                       w (decrement-big-n big-n) (eq extra t)
                       guard-checking-off
                       latches
                       hard-error-returns-nilp
                       aok)
               (cond
                (er (mv er val latches))
                ((eq fn 'return-last) ; avoid taking stobjs-out of return-last
                 (mv nil val latches))
                (t (mv nil
                       val
                       (latch-stobjs
                        (stobjs-out fn w)
                        val
                        latches)))))))))))))))

(defun ev-fncall-rec (fn args w big-n safe-mode gc-off latches
                         hard-error-returns-nilp aok)

; WARNING: This function should only be called with *raw-guard-warningp* bound.

  (declare (xargs :guard (plist-worldp w)))
  #-acl2-loop-only
  (cond (*ev-shortcut-okp*
         (cond ((fboundp fn)

; If fn is unbound and we used the logical code below, we'd get a
; hard error as caused by (formals fn w).

                (return-from ev-fncall-rec
                             (raw-ev-fncall fn args latches
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
  (ev-fncall-rec-logical fn args w big-n safe-mode gc-off latches
                         hard-error-returns-nilp aok))

(defun ev-rec-return-last (fn arg2 arg3 alist w big-n safe-mode gc-off latches
                              hard-error-returns-nilp aok)

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
; below.  Note that fn is not mbe1-raw, so this binding is legal.

; Unlike the raw Lisp definition of return-last, we see no need to bind
; *attached-fn-called* here (for the #+hons version), because that would amount
; to trying to manage the use of memoization with calls of top-level calls of
; ev-rec on behalf of the trans-eval call under ld-read-eval-print.

                            t))
      (ev-rec arg2 alist w (decrement-big-n big-n) safe-mode gc-off latches
              hard-error-returns-nilp

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
                (ev-rec arg3 alist w (decrement-big-n big-n) safe-mode gc-off
                        latches hard-error-returns-nilp aok))
               (with-guard-checking1-raw
                (return-last
                 'with-guard-checking1-raw
                 arg2-val
                 (ev-rec arg3 alist w (decrement-big-n big-n) safe-mode
                         (gc-off1 arg2-val)
                         latches hard-error-returns-nilp aok)))
               (otherwise
                #+acl2-loop-only
                (ev-rec arg3 alist w (decrement-big-n big-n)
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
                                      *return-last-fn-big-n*
                                      *return-last-fn-safe-mode*
                                      *return-last-fn-gc-off*
                                      *return-last-fn-latches*
                                      *return-last-fn-hard-error-returns-nilp*
                                      *return-last-fn-aok*)))))))))))

(defun ev-rec (form alist w big-n safe-mode gc-off latches
                    hard-error-returns-nilp aok)

; WARNING: This function should only be called with *raw-guard-warningp* bound.

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

         (ev-rec-acl2-unwind-protect form alist
                                     w (decrement-big-n big-n) safe-mode gc-off
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
                     (ev-rec body alist
                             w (decrement-big-n big-n) safe-mode gc-off latches
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
                 (ev-rec (fargn form 1) alist
                         w (decrement-big-n big-n) safe-mode gc-off
                         latches
                         hard-error-returns-nilp
                         aok)
                 (cond
                  (test-er (mv t test latches))
                  (test
                   (ev-rec (fargn form 2) alist
                           w (decrement-big-n big-n) safe-mode gc-off
                           latches
                           hard-error-returns-nilp
                           aok))
                  (t (ev-rec (fargn form 3) alist
                             w (decrement-big-n big-n) safe-mode gc-off
                             latches
                             hard-error-returns-nilp
                             aok)))))
        ((eq (ffn-symb form) 'mv-list)
         (ev-rec (fargn form 2) alist
                 w (decrement-big-n big-n) safe-mode gc-off
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
                       alist w (decrement-big-n big-n) safe-mode gc-off latches
                       hard-error-returns-nilp aok))
              (t (ev-rec-return-last fn (fargn form 2) (fargn form 3)
                                     alist w big-n safe-mode gc-off latches
                                     hard-error-returns-nilp aok))))
            (t ; first arg is not quotep with special behavior; treat as progn
             (mv-let (args-er args latches)
                     (ev-rec-lst (fargs form) alist
                                 w (decrement-big-n big-n) safe-mode gc-off
                                 latches
                                 hard-error-returns-nilp
                                 aok)
                     (cond (args-er (mv t args latches))
                           (t (mv nil (car (last args)) latches))))))))
        (t (mv-let (args-er args latches)
                   (ev-rec-lst (fargs form) alist
                               w (decrement-big-n big-n) safe-mode gc-off
                               latches
                               hard-error-returns-nilp
                               aok)
                   (cond
                    (args-er (mv t args latches))
                    ((flambda-applicationp form)
                     (ev-rec (lambda-body (ffn-symb form))
                             (pairlis$ (lambda-formals (ffn-symb form)) args)
                             w (decrement-big-n big-n) safe-mode gc-off
                             latches
                             hard-error-returns-nilp
                             aok))
                    (t (ev-fncall-rec (ffn-symb form) args
                                      w (decrement-big-n big-n) safe-mode
                                      gc-off latches
                                      hard-error-returns-nilp aok)))))))

(defun ev-rec-lst (lst alist w big-n safe-mode gc-off latches
                       hard-error-returns-nilp aok)

; WARNING: This function should only be called with *raw-guard-warningp* bound.

  (declare (xargs :guard (and (plist-worldp w)
                              (term-listp lst w)
                              (symbol-alistp alist))))
  (cond
   ((zp-big-n big-n)
    (mv t (cons "Evaluation ran out of time." nil) latches))
   ((null lst) (mv nil nil latches))
   (t (mv-let (first-er first-val first-latches)
              (ev-rec (car lst) alist
                      w (decrement-big-n big-n) safe-mode gc-off
                      latches
                      hard-error-returns-nilp
                      aok)
              (cond
               (first-er (mv first-er first-val first-latches))
               (t
                (mv-let (rest-er rest-val rest-latches)
                        (ev-rec-lst (cdr lst) alist
                                    w (decrement-big-n big-n) safe-mode gc-off
                                    first-latches
                                    hard-error-returns-nilp
                                    aok)
                        (cond
                         (rest-er (mv rest-er rest-val rest-latches))
                         (t (mv nil
                                (cons first-val rest-val)
                                rest-latches))))))))))

(defun ev-rec-acl2-unwind-protect (form alist w big-n safe-mode gc-off
                                        latches hard-error-returns-nilp aok)

; WARNING: This function should only be called with *raw-guard-warningp* bound.

; Sketch: We know that form is a termp wrt w and that it is recognized by
; translated-acl2-unwind-protectp.  We therefore unpack it into its body and
; two cleanup forms and give it special attention.  If the body evaluates
; without either an abort or any kind of "evaluation error" (e.g., ubv, udf, or
; guard error) then we return exactly what we would have returned had we
; evaluated form without special treatment.  But if body causes an evaluation
; error we run the cleanup1 code, just as Common Lisp would had the body been
; compiled and caused a hard lisp error.  Furthermore, if the evaluation of
; body is aborted, we ensure that the cleanup1 code is EV'd upon unwinding.

; See the unwind-protect essay in axioms.lisp.

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
; i.e., body terminating without an evaluation error but signalling an error --
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

; The Unwind-Protect Essay says that we have the freedom to give arbitrary
; semantics to acl2-unwind-protect in the face of an abort.  So in this raw
; Lisp code, we take the liberty of binding *ev-shortcut-okp* to t even though
; when this cleanup code is executed, we may violate the requirement that the
; values of state globals guard-checking-on and safe-mode are respected in the
; arguments to ev-rec when *ev-shortcut-okp* is t.  This seems like quite a
; minor violation when doing cleanup.

                            (let ((*ev-shortcut-okp* t))
                              (mv-let (erp val latches)
                                (ev-rec cleanup1 alist
                                        w big-n safe-mode gc-off
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
      (ev-rec body alist w big-n safe-mode gc-off latches
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
                 w big-n safe-mode gc-off
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
       ((car body-val) ; "soft error," i.e., body signalled error

; We think this call of acl2-unwind is unnecessary.  It is here in
; case the evaluation of body pushed some additional forms onto the
; unwind protect stack and it removes those forms down to the one we
; pushed.  But if a soft error has arisen, any forms pushed would have
; been popped on the way back to here.  But this code is safer.

        #-acl2-loop-only
        (cond (temp (acl2-unwind -1 temp)))

; Because body is known to produce an error triple we know its car is
; the error flag, the cadr is the value, and the caddr is a state
; The test above therefore detects that the body signalled an error.

        (mv-let
         (clean-erp clean-val clean-latches)
         (ev-rec cleanup1
                 (put-assoc-eq 'state
                               (cdr (assoc-eq 'state body-latches))
                               alist)
                 w big-n safe-mode gc-off
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
                 w big-n safe-mode gc-off
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

(defun ev-fncall-w (fn args w safe-mode gc-off hard-error-returns-nilp aok)
  (declare (xargs :guard (plist-worldp w)))

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

  (cond
   ((untouchable-fn-p fn w)
    (mv t
        (msg "Attempted to call ev-fncall-w with function ~x0, which is untouchable."
             fn)))

; See the comment in ev for why we don't check the time limit here.

   (t
    #-acl2-loop-only
    (let ((*ev-shortcut-okp* t)
          (*raw-guard-warningp* (raw-guard-warningp-binding)))
      (state-free-global-let*
       ((safe-mode safe-mode)
        (guard-checking-on

; Guard-checking-on will be t or nil -- not :nowarn, :all, or :none, but it
; doesn't seem that this would be a problem.

         (not gc-off)))
       (mv-let
        (erp val latches)
        (ev-fncall-rec fn args w (big-n) safe-mode gc-off
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
                           safe-mode gc-off hard-error-returns-nilp aok)))
               (mv erp val)))))
    #+acl2-loop-only
    (mv-let
     (erp val latches)
     (ev-fncall-rec fn args w (big-n) safe-mode gc-off
                    nil ; latches
                    hard-error-returns-nilp
                    aok)
     (declare (ignore latches))
     (mv erp val)))))

(defun ev-fncall-guard-er-msg (fn guard stobjs-in args w extra)

; Guard is printed directly, so should generally be in untranslated form.

  (prog2$
   (save-ev-fncall-guard-er fn guard stobjs-in args)
   (mv-let
    (evisc-obj empty-iprint-alist)
    (eviscerate-stobjs ; see below

; Note: We cons a nil onto the evisceration stobj marks to account for consing
; fn onto the quoted arg list in the evisceration tuple commented on below.

     (cons nil (evisceration-stobj-marks stobjs-in t))
     (cons fn (untranslate*-lst (kwote-lst args) nil w))
     3 4 nil (table-alist 'evisc-table w) nil

; Note that the iprint-alist is nil.  We never do iprinting for guard errors,
; because it seems awkward to do so (see comments below).  We consider that a
; minor inconvenience to the user, since the call below of
; error-trace-suggestion refers to print-gv.

     nil)
    (assert$
     (symbolp empty-iprint-alist)
     (msg
      "The guard for the~#0~[ :program~/~] function call ~x1, which is ~P23, ~
       is violated by the arguments in the call ~P45.~@6~@7~@8~@9"
      (if (programp fn w) 0 1)
      (cons fn (formals fn w))
      guard
      nil ; might prefer (term-evisc-tuple nil state) if we had state here

; Note: The following value is printed with ~P45 above.  One might
; wonder why we didn't create a suitable evisc-tuple for #\5.  The
; reason is that we do not support stobj evisceration in evisc-tuples.
; So we eviscerate the thing the way we want, now.

      evisc-obj

; The following evisceration tuple is pretty subtle.  We cannot
; provide a tuple of nil or else the evisceration marks in the object
; above are not recognized.  We cannot provide a trivial evisceration
; tuple like (evisc-tuple nil nil nil nil), because it then goes out
; of its way to ensure that the evisceration marks are printed as
; evisceration marks!  So we use the alist component of the
; evisceration tuple to override this protection of the evisceration
; mark!

      (evisc-tuple nil nil
                   (list (cons *evisceration-mark* *evisceration-mark*))
                   nil)
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
; or is defined by defstobj.

             (msg "~|This error is being reported even though guard-checking ~
                   has been turned off, because the stobj argument of ~x0 is ~
                   the ``live'' ~p1 and ACL2 does not support non-compliant ~
                   live stobj manipulation."
                  fn
                  (find-first-non-nil stobjs-in)))
            ((eq extra :no-extra) "")
            (extra *safe-mode-guard-er-addendum*)
            (t ""))
      (error-trace-suggestion t)
      (if (keywordp extra) ; skip the following for safe-mode or stobjs
          ""
        "  See :DOC set-guard-checking for information about suppressing this ~
         check with (set-guard-checking :none), as recommended for new ~
         users."))))))

(defun ev-fncall-guard-er (fn args w latches extra)
  (mv t
      (ev-fncall-guard-er-msg fn
                              (untranslate* (guard fn nil w) t w)
                              (stobjs-in fn w) args w extra)
      latches))

(defun ev-fncall-msg (val wrld)
  (cond
   ((and (consp val)
         (eq (car val) 'ev-fncall-null-body-er))

; We get here if val is of the form (ev-fncall-null-body-er fn).

    (msg "ACL2 cannot ev the call of undefined function ~x0 on argument ~
          list:~|~%~x1~|~%~@2"
         (cadr val)
         (cddr val)
         (error-trace-suggestion nil)))
   ((and (consp val)
         (eq (car val) 'ev-fncall-guard-er))

; We get here if val is of the form (ev-fncall-guard-er fn args guard
; stobjs-in safep).  This happens if a :program function finds its
; guard violated or a :logic function finds its guard violated while
; guard-checking is on.

    (ev-fncall-guard-er-msg (cadr val) (cadddr val) (car (cddddr val))
                            (caddr val) wrld (cadr (cddddr val))))
   ((and (consp val)
         (eq (car val) 'ev-fncall-creator-er))

; This is similar to the preceding case, except that there are no stobjs-in.

    (msg
     "An attempt has been made to call the stobj creator function ~x0.  This ~
      error is being reported even though guard-checking may have been turned ~
      off, because ACL2 does not support non-compliant live stobj ~
      manipulation.  If you did not explicitly call ~x0 then this error is ~
      probably due to an attempt to evaluate a with-local-stobj form directly ~
      in the top-level loop.  Such forms are only allowed in the bodies of ~
      functions and in theorems.  Also see :DOC with-local-stobj.~@1"
     (cadr val)
     (error-trace-suggestion t)))
   ((and (consp val)
         (eq (car val) 'pkg-witness-er))
    (msg
     "The call ~x0 is illegal because the second argument is not the name of a ~
      package currently known to ACL2."
     (list 'pkg-witness (cadr val))))
   ((and (consp val)
         (eq (car val) 'pkg-imports-er))
    (msg
     "The call ~x0 is illegal because the argument is not the name of a ~
      package currently known to ACL2."
     (list 'pkg-imports (cadr val))))
   ((and (consp val)
         (eq (car val) 'program-only-er))
    (msg
     "The call ~x0 is an illegal call of a function that has been marked as ~
      ``program-only,'' and hence has special raw Lisp code.  This call is ~
      illegal because program-only functions are only allowed to invoke their ~
      raw Lisp code, but in this case there was an attempt to invoke ~
      executable counterpart code ~#2~[because of guard-checking (see :DOC ~
      guard-evaluation-table)~/because it is being called under a ``safe ~
      mode'' that is used, for example, during macroexpansion~]."
     (cons (cadr val) (caddr val))
     (cadr val)
     (if (cadr (cddddr val)) 1 0)))
   ((eq val 'illegal)
    (msg "Evaluation aborted.~@0"
         (error-trace-suggestion t)))
   (t (er hard 'raw-ev-fncall
          "An unrecognized value, ~x0, was thrown to 'raw-ev-fncall.~@1"
          val
          (error-trace-suggestion t)))))

(defun untranslate1 (term iff-flg binop-tbl preprocess-fn wrld)

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
                                       nil ; safe-mode
                                       nil ; gc-off
                                       nil ; hard-error-returns-nilp
                                       t)
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
           (make-let-or-let*
            (collect-non-trivial-bindings (lambda-formals (ffn-symb term))
                                          (untranslate1-lst (fargs term)
                                                            nil
                                                            binop-tbl
                                                            preprocess-fn
                                                            wrld))
            (untranslate1 (lambda-body (ffn-symb term)) iff-flg binop-tbl
                          preprocess-fn wrld)))
          ((and (eq (ffn-symb term) 'nth)
                (quotep (fargn term 1))
                (integerp (cadr (fargn term 1)))
                (<= 0 (cadr (fargn term 1))))
           (let ((accessor-name (accessor-root (cadr (fargn term 1))
                                               (fargn term 2)
                                               wrld)))
             (list 'nth
                   (or accessor-name
                       (cadr (fargn term 1)))
                   (untranslate1 (fargn term 2) nil binop-tbl preprocess-fn
                                 wrld))))
          ((and (eq (ffn-symb term) 'update-nth)
                (quotep (fargn term 1))
                (integerp (cadr (fargn term 1)))
                (<= 0 (cadr (fargn term 1))))
           (let ((accessor-name (accessor-root (cadr (fargn term 1))
                                               (fargn term 3)
                                               wrld)))
             (list 'update-nth
                   (or accessor-name
                       (cadr (fargn term 1)))
                   (untranslate1 (fargn term 2) nil binop-tbl preprocess-fn
                                 wrld)
                   (untranslate1 (fargn term 3) nil binop-tbl preprocess-fn
                                 wrld))))
          ((and (eq (ffn-symb term) 'update-nth-array)
                (quotep (fargn term 1))
                (integerp (cadr (fargn term 1)))
                (<= 0 (cadr (fargn term 1))))
           (let ((accessor-name (accessor-root (cadr (fargn term 1))
                                               (fargn term 4)
                                               wrld)))
             (list 'update-nth-array
                   (or accessor-name
                       (cadr (fargn term 1)))
                   (untranslate1 (fargn term 2) nil binop-tbl preprocess-fn
                                 wrld)
                   (untranslate1 (fargn term 3) nil binop-tbl preprocess-fn
                                 wrld)
                   (untranslate1 (fargn term 4) nil binop-tbl preprocess-fn
                                 wrld))))
          ((eq (ffn-symb term) 'binary-+)
           (cons '+
                 (untranslate1-lst (right-associated-args 'binary-+ term)
                                   nil binop-tbl preprocess-fn wrld)))
          ((eq (ffn-symb term) 'unary-/)
           (list '/ (untranslate1 (fargn term 1) nil binop-tbl preprocess-fn
                                  wrld)))
          ((eq (ffn-symb term) 'unary--)
           (list '- (untranslate1 (fargn term 1) nil binop-tbl preprocess-fn
                                  wrld)))
          ((eq (ffn-symb term) 'if)
           (case-match term
             (('if x1 *nil* *t*)
              (list 'not (untranslate1 x1 t binop-tbl preprocess-fn wrld)))
             (('if x1 x2  *nil*)
              (untranslate-and (untranslate1 x1 t binop-tbl preprocess-fn wrld)
                               (untranslate1 x2 iff-flg binop-tbl preprocess-fn
                                             wrld)
                               iff-flg))
             (('if x1 *nil* x2)
              (untranslate-and (list 'not (untranslate1 x1 t binop-tbl
                                                        preprocess-fn wrld))
                               (untranslate1 x2 iff-flg binop-tbl preprocess-fn
                                             wrld)
                               iff-flg))
             (('if x1 x1 x2)
              (untranslate-or (untranslate1 x1 iff-flg binop-tbl preprocess-fn
                                            wrld)
                              (untranslate1 x2 iff-flg binop-tbl preprocess-fn
                                            wrld)))
             (('if x1 x2 *t*)

; Observe that (if x1 x2 t) = (if x1 x2 (not nil)) = (if x1 x2 (not x1)) =
; (if (not x1) (not x1) x2) = (or (not x1) x2).

              (untranslate-or (list 'not (untranslate1 x1 t binop-tbl
                                                       preprocess-fn wrld))
                              (untranslate1 x2 iff-flg binop-tbl preprocess-fn
                                            wrld)))
             (('if x1 *t* x2)
              (cond
               ((or iff-flg
                    (and (nvariablep x1)
                         (not (fquotep x1))
                         (member-eq (ffn-symb x1)
                                    *untranslate-boolean-primitives*)))
                (untranslate-or (untranslate1 x1 t binop-tbl
                                              preprocess-fn wrld)
                                (untranslate1 x2 iff-flg binop-tbl
                                              preprocess-fn wrld)))
               (t (untranslate-if term iff-flg binop-tbl preprocess-fn wrld))))
             (& (untranslate-if term iff-flg binop-tbl preprocess-fn wrld))))
          ((and (eq (ffn-symb term) 'not)
                (nvariablep (fargn term 1))
                (not (fquotep (fargn term 1)))
                (member-eq (ffn-symb (fargn term 1)) '(< o<)))
           (list (if (eq (ffn-symb (fargn term 1)) '<) '<= 'o<=)
                 (untranslate1 (fargn (fargn term 1) 2) nil binop-tbl
                               preprocess-fn wrld)
                 (untranslate1 (fargn (fargn term 1) 1) nil binop-tbl
                               preprocess-fn wrld)))
          ((eq (ffn-symb term) 'not)
           (dumb-negate-lit (untranslate1 (fargn term 1) t binop-tbl
                                          preprocess-fn wrld)))
          ((member-eq (ffn-symb term) '(implies iff))
           (fcons-term* (ffn-symb term)
                        (untranslate1 (fargn term 1) t binop-tbl preprocess-fn
                                      wrld)
                        (untranslate1 (fargn term 2) t binop-tbl preprocess-fn
                                      wrld)))
          ((eq (ffn-symb term) 'cons) (untranslate-cons term binop-tbl
                                                        preprocess-fn wrld))
          ((and (eq (ffn-symb term) 'synp)

; Even though translate insists that the second argument of synp is quoted, can
; we really guarantee that every termp given to untranslate came through
; translate?  Not necessarily; for example, maybe substitution was performed
; for some reason (say, in the proof-checker one replaces the quoted argument
; by a variable known to be equal to it).

                (quotep (fargn term 2)))

; We store the quotation of the original form of a syntaxp or bind-free
; hypothesis in the second arg of its expansion.  We do this so that we
; can use it here and output something that the user will recognise.

           (cadr (fargn term 2)))
          (t (cond ((and (eq (ffn-symb term) 'return-last)
                         (quotep (fargn term 1))
                         (let* ((key (unquote (fargn term 1)))
                                (fn (and (symbolp key)
                                         key
                                         (return-last-lookup key wrld))))
                           (and fn
                                (cons fn
                                      (untranslate1-lst (cdr (fargs term)) nil
                                                        binop-tbl preprocess-fn
                                                        wrld))))))
                   (t (let ((op (cdr (assoc-eq (ffn-symb term) binop-tbl))))
                        (cond
                         (op (cons op
                                   (untranslate1-lst
                                    (cond
                                     ((and (cdr (fargs term))
                                           (null (cddr (fargs term))))
                                      (right-associated-args (ffn-symb term)
                                                             term))
                                     (t (fargs term)))
                                    nil binop-tbl preprocess-fn wrld)))
                         (t
                          (mv-let
                           (fn guts)
                           (car-cdr-nest term)
                           (cond (fn (list fn
                                           (untranslate1 guts nil binop-tbl
                                                         preprocess-fn wrld))) 
                                 (t (cons (ffn-symb term)
                                          (untranslate1-lst (fargs term) nil
                                                            binop-tbl
                                                            preprocess-fn
                                                            wrld))))))))))))))

(defun untranslate-cons1 (term binop-tbl preprocess-fn wrld)

; This function digs through a 'cons nest, untranslating each of the
; elements and the final non-cons cdr.  It returns two results:  the
; list of untranslated elements and the untranslated final term.

  (cond ((variablep term) (mv nil (untranslate1 term nil binop-tbl
                                                preprocess-fn wrld)))
        ((fquotep term) (mv nil (untranslate1 term nil binop-tbl preprocess-fn
                                              wrld)))
        ((eq (ffn-symb term) 'cons)
         (mv-let (elements x)
                 (untranslate-cons1 (fargn term 2) binop-tbl preprocess-fn
                                    wrld)
                 (mv (cons (untranslate1 (fargn term 1) nil binop-tbl
                                         preprocess-fn wrld)
                           elements)
                     x)))
        (t (mv nil (untranslate1 term nil binop-tbl preprocess-fn wrld)))))

(defun untranslate-cons (term binop-tbl preprocess-fn wrld)

; Term is a non-quote term whose ffn-symb is 'cons.  We untranslate
; it into a CONS, a LIST, or a LIST*.

  (mv-let (elements x)
          (untranslate-cons1 term binop-tbl preprocess-fn wrld)
          (cond ((eq x nil) (cons 'list elements))
                ((null (cdr elements)) (list 'cons (car elements) x))
                (t (cons 'list* (append elements (list x)))))))

(defun untranslate-if (term iff-flg binop-tbl preprocess-fn wrld)
  (cond ((> (case-length nil term) 2)
         (case-match term
                     (('if (& key &) & &)
                      (list* 'case key
                             (untranslate-into-case-clauses
                              key term iff-flg binop-tbl preprocess-fn
                              wrld)))))
        ((> (cond-length term) 2)
         (cons 'cond (untranslate-into-cond-clauses term iff-flg binop-tbl
                                                    preprocess-fn
                                                    wrld)))
        (t (list 'if
                 (untranslate1 (fargn term 1) t binop-tbl preprocess-fn wrld)
                 (untranslate1 (fargn term 2) iff-flg binop-tbl preprocess-fn
                               wrld)
                 (untranslate1 (fargn term 3) iff-flg binop-tbl preprocess-fn
                               wrld)))))

(defun untranslate-into-case-clauses (key term iff-flg binop-tbl preprocess-fn
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
                                         (untranslate1 x iff-flg binop-tbl
                                                       preprocess-fn wrld))
                                   (untranslate-into-case-clauses
                                    key y iff-flg binop-tbl preprocess-fn wrld)
                                  ))
                            (t (cons (list val (untranslate1 x iff-flg
                                                             binop-tbl
                                                             preprocess-fn
                                                             wrld))
                                     (untranslate-into-case-clauses
                                      key y iff-flg binop-tbl preprocess-fn
                                      wrld)))))
                     ((and (eq pred 'member)
                           (eqlable-listp val))
                      (cons (list val (untranslate1 x iff-flg binop-tbl
                                                    preprocess-fn wrld))
                            (untranslate-into-case-clauses
                             key y iff-flg binop-tbl preprocess-fn wrld)))
                     (t (list (list 'otherwise
                                    (untranslate1 term iff-flg binop-tbl
                                                  preprocess-fn wrld))))))
              (& (list (list 'otherwise
                             (untranslate1 term iff-flg binop-tbl preprocess-fn
                                           wrld))))))

(defun untranslate-into-cond-clauses (term iff-flg binop-tbl preprocess-fn
                                           wrld)

; We know cond-length is greater than 1; else this doesn't terminate.

  (case-match term
              (('if x1 x2 x3)
               (cons (list (untranslate1 x1 t binop-tbl preprocess-fn wrld)
                           (untranslate1 x2 iff-flg binop-tbl preprocess-fn
                                         wrld))
                     (untranslate-into-cond-clauses x3 iff-flg binop-tbl
                                                    preprocess-fn wrld)))
              (& (list (list t (untranslate1 term iff-flg binop-tbl
                                             preprocess-fn wrld))))))

(defun untranslate1-lst (lst iff-flg binop-tbl preprocess-fn wrld)
  (cond ((null lst) nil)
        (t (cons (untranslate1 (car lst) iff-flg binop-tbl preprocess-fn wrld)
                 (untranslate1-lst (cdr lst) iff-flg binop-tbl preprocess-fn
                                   wrld)))))

;; RAG - I relaxed the guards for < and complex to use realp instead
;; of rationalp.  I also added complexp, realp, and floor1.

)

(defun ev-fncall (fn args state latches hard-error-returns-nilp aok)
  (declare (xargs :guard (state-p state)))
  (let #-acl2-loop-only ((*ev-shortcut-okp* (live-state-p state))
                         (*raw-guard-warningp* (raw-guard-warningp-binding)))
       #+acl2-loop-only ()

; See the comment in ev for why we don't check the time limit here.

       (ev-fncall-rec fn args (w state) (big-n)
                      (f-get-global 'safe-mode state)
                      (gc-off state)
                      latches hard-error-returns-nilp aok)))
  
(defun ev (form alist state latches hard-error-returns-nilp aok)
  (declare (xargs :guard (and (state-p state)
                              (termp form (w state))
                              (symbol-alistp alist))))
  (let #-acl2-loop-only ((*ev-shortcut-okp* (live-state-p state))
                         (*raw-guard-warningp* (raw-guard-warningp-binding)))
       #+acl2-loop-only ()

; At one time we called time-limit4-reached-p here so that we can quit if we
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
;        ((time-limit4-reached-p
;          "Out of time in the evaluator (ev).") ; nil, or throws
;         (mv t ; value shouldn't matter
;             (cons "Implementation error" nil)
;             latches))
;        (t
       (ev-rec form alist
               (w state) (big-n)
               (f-get-global 'safe-mode state)
               (gc-off state)
               latches hard-error-returns-nilp aok)))

(defun ev-lst (lst alist state latches hard-error-returns-nilp aok)
  (declare (xargs :guard (and (state-p state)
                              (term-listp lst (w state))
                              (symbol-alistp alist))))
  (let #-acl2-loop-only ((*ev-shortcut-okp* (live-state-p state))
                         (*raw-guard-warningp* (raw-guard-warningp-binding)))
       #+acl2-loop-only ()

; See the comment in ev for why we don't check the time limit here.

       (ev-rec-lst lst alist
                   (w state)
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
                                 (binop-table wrld)
                                 (untranslate-preprocess-fn wrld)
                                 wrld))
          (t val)))
      (untranslate1-lst lst
                        iff-flg
                        (binop-table wrld)
                        (untranslate-preprocess-fn wrld)
                        wrld))))

(defun ev-w (form alist w safe-mode gc-off hard-error-returns-nilp aok)

; WARNING: Do not call this function if alist contains the live state
; or any other live stobjs and evaluation of form could modify any of
; those stobjs.  Otherwise, the calls of ev-rec below violate
; requirement (1) in The Essay on EV, which is stated explicitly for
; ev but, in support of ev, is applicable to ev-rec as well.  Note
; that users cannot make such a call because they cannot put live
; stobjs into alist.

; Unlike ev-fncall-w, we do not check for untouchables (by traversing
; the form before evaluating) and hence we must make ev-w untouchable.
; It would be simple enough to create a user-available version of
; ev-w, if requested, which would need to do an untouchables check.

  (declare (xargs :guard (and (plist-worldp w)
                              (termp form w)
                              (symbol-alistp alist))))

; See the comment in ev for why we don't check the time limit here.

  #-acl2-loop-only
  (let ((*ev-shortcut-okp* t)
        (*raw-guard-warningp* (raw-guard-warningp-binding)))
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
      (ev-rec form alist w (big-n) safe-mode gc-off
              nil ; latches
              hard-error-returns-nilp
              aok)
      (progn (when latches
               (er hard! 'ev-w
                   "The call ~x0 returned non-nil latches."
                   (list 'ev-w form alist '<wrld> safe-mode gc-off
                         hard-error-returns-nilp aok)))
             (mv erp val)))))
  #+acl2-loop-only
  (mv-let (erp val latches)
          (ev-rec form alist w (big-n) safe-mode gc-off
                  nil ; latches
                  hard-error-returns-nilp
                  aok)
          (declare (ignore latches))
          (mv erp val)))

(defun ev-w-lst (lst alist w safe-mode gc-off hard-error-returns-nilp aok)

; WARNING: See the warning in ev-w, which explains that live stobjs must not
; occur in alist.

; See the comment in ev-w about untouchables.

  (declare (xargs :guard (and (plist-worldp w)
                              (term-listp lst w)
                              (symbol-alistp alist))))

; See the comment in ev for why we don't check the time limit here.

  #-acl2-loop-only
  (let ((*ev-shortcut-okp* t)
        (*raw-guard-warningp* (raw-guard-warningp-binding)))
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
      (ev-rec-lst lst alist w (big-n) safe-mode gc-off
                  nil ; latches
                  hard-error-returns-nilp
                  aok)
      (progn (when latches
               (er hard 'ev-w-lst
                   "The call ~x0 returned non-nil latches."
                   (list 'ev-w-lst lst alist '<wrld> safe-mode gc-off
                         hard-error-returns-nilp aok)))
             (mv erp val)))))
  #+acl2-loop-only
  (mv-let (erp val latches)
          (ev-rec-lst lst alist w (big-n) safe-mode gc-off
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
; See also the analogue cmp-plus-bindings-to-trans-tuple.

  `(assert$ (not (eq ctx t))
            (mv-let (ctx msg-or-val)
                    ,form
                    (cond (ctx (cond (msg-or-val (er soft ctx "~@0" msg-or-val))
                                     (t (silent-error state))))
                          (t (value msg-or-val))))))

(defun er-cmp-fn (ctx msg)
  (declare (xargs :guard t))
  (mv ctx msg))

(defmacro er-cmp (ctx str &rest args)
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

  (declare (xargs :guard (and (doubleton-list-p alist)
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

(defun warning1-cmp (ctx summary str alist wrld state-vars)

; This function has the same effect as warning1, except that printing is in a
; wormhole and hence doesn't modify state.

  (warning1-form t))

(defmacro warning$-cmp (&rest args)

; This macro assumes that wrld and state-vars are bound to a world and
; state-vars record, respectively.

; Warning: Keep this in sync with warning$.

  (list 'warning1-cmp
        (car args)

; We seem to have seen a GCL 2.6.7 compiler bug, laying down bogus calls of
; load-time-value, when replacing (consp (cadr args)) with (and (consp (cadr
; args)) (stringp (car (cadr args)))).  But it seems fine to have the semantics
; of warning$ be that conses are quoted in the second argument position.

        (if (consp (cadr args))
            (kwote (cadr args))
          (cadr args))
        (caddr args)
        (make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                             #\5 #\6 #\7 #\8 #\9)
                           (cdddr args))
        'wrld
        'state-vars))

(defun chk-length-and-keys (actuals form wrld)
  (cond ((null actuals)
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

(defun bind-macro-args-keys1 (args actuals allow-flg alist form wrld
                                   state-vars)

; We need parameter state-vars because of the call of warning$-cmp below.

  (cond ((null args)
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
                               (t alist))))
             (prog2$
              (cond ((assoc-keyword key (cddr tl))
                     (warning$-cmp *macro-expansion-ctx* "Duplicate-Keys"
                                   "The keyword argument ~x0 occurs twice in ~
                                    ~x1.  This situation is explicitly ~
                                    allowed in Common Lisp (see CLTL2, page ~
                                    80) but it often suggests a mistake was ~
                                    made.  The leftmost value for ~x0 is used."
                                   key form))
                    (t nil))
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
               form wrld state-vars))))))

(defun bind-macro-args-keys (args actuals alist form wrld state-vars)
  (er-progn-cmp
   (chk-length-and-keys actuals form wrld)
   (cond ((assoc-keyword :allow-other-keys
                         (cdr (assoc-keyword :allow-other-keys
                                             actuals)))
          (er-cmp *macro-expansion-ctx*
                  "ACL2 prohibits multiple :allow-other-keys because ~
                            implementations differ significantly concerning ~
                            which value to take."))
         (t (value-cmp nil)))
   (bind-macro-args-keys1
    args actuals
    (let ((tl
           (assoc-keyword :allow-other-keys actuals)))
      (and tl (cadr tl)))
    alist form wrld state-vars)))

(defun bind-macro-args-after-rest (args actuals alist form wrld state-vars)
  (cond
   ((null args) (value-cmp alist))
   ((eq (car args) '&key)
    (bind-macro-args-keys (cdr args) actuals alist form wrld state-vars))
   (t (er-cmp *macro-expansion-ctx*
              "Only keywords and values may follow &rest or &body; error in ~
               macro expansion of ~x0."
              form))))

(defun bind-macro-args-optional (args actuals alist form wrld state-vars)
  (cond ((null args)
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
  (cond ((null args)
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
  (cond ((and (consp args)
              (eq (car args) '&whole))
         (bind-macro-args1 (cddr args) (cdr form)
                           (list (cons (cadr args) form))
                           form wrld state-vars))
        (t (bind-macro-args1 args (cdr form) nil form wrld state-vars))))

(defun macroexpand1-cmp (x ctx wrld state-vars)
  (let ((gc-off (gc-off1 (access state-vars state-vars :guard-checking-on))))
    (er-let*-cmp
     ((alist (bind-macro-args
              (macro-args (car x) wrld)
              x wrld state-vars)))
     (mv-let (erp guard-val)
             (ev-w (guard (car x) nil wrld) alist wrld t
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
                            following error:~|~%~@1"
                           x
                           guard-val
                           (car x)))
              ((null guard-val)
               (er-cmp ctx
                       "In the attempt to macroexpand the form ~x0 the guard, ~
                        ~x1, for ~x2 failed."
                       x
                       (guard (car x) nil wrld)
                       (car x)))
              (t (mv-let (erp expansion)
                         (ev-w
                          (getprop (car x) 'macro-body
                                   '(:error "Apparently macroexpand1 was ~
                                             called where there was no ~
                                             macro-body.")
                                   'current-acl2-world wrld)
                          alist wrld
                          (not (global-val 'boot-strap-flg wrld)) ; safe-mode
                          gc-off nil nil)
                         (cond (erp
                                (er-cmp ctx
                                        "In the attempt to macroexpand the ~
                                         form ~x0, evaluation of the macro ~
                                         body caused the following ~
                                         error:~|~%~@1"
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

(defun acceptable-dcls-alist (state-vars)

; The declarations when (hons-enabledp state) have been found useful by Bob
; Boyer for the experimental hons version, but have not yet been carefully
; evaluated for soundness.

  (let ((hons-enabledp (access state-vars state-vars :hons-enabled)))
    `((let ignore ignorable type
           ,@(if hons-enabledp
                 '(dynamic-extent)
               nil))
      (mv-let ignore ignorable type)
      (flet ignore ignorable type) ; for each individual definition in the flet
      (defmacro ignore ignorable type xargs)
      (defuns ignore ignorable type optimize xargs
        ,@(if hons-enabledp
              '(inline notinline)
            nil)))))

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

  (let ((syms
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

(defun chk-dcl-lst (l vars binder ctx wrld state-vars)

; L is the list of expanded declares.  Vars is a list of variables
; bound in the immediately superior lexical environment.  Binder is
; a binder, as listed in acceptable-dcls-alist.

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
                   (temp (cdr (assoc-eq binder (acceptable-dcls-alist
                                                state-vars)))))
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
                         "Each element of a declartion must end in NIL but ~
                          ~x0 does not.  See :DOC declare." entry))
                (t
                 (case
                  dcl
                  ((dynamic-extent notinline inline)
                   (cond ((access state-vars state-vars :hons-enabled)

; should check we are binding a variable of a let

                          (value-cmp nil))
                         (t (er-cmp ctx
                                    "The declaration ~x0 is illegal except in ~
                                     a hons-enabled ACL2 executable.  See ~
                                     :DOC hons-and-memoization."
                                    dcl))))
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
                  ((ignore ignorable)
                   (cond ((subsetp (cdr entry) vars)
                          (value-cmp nil))
                         (t (er-cmp ctx
                                    "The variables of an ~x0 declaration must ~
                                     be introduced in the immediately ~
                                     superior lexical environment, but ~&1, ~
                                     which ~#1~[is~/are~] said to be ~
                                     ~#2~[ignored~/ignorable~] in ~x3, ~
                                     ~#1~[is~/are~] not bound immediately ~
                                     above the declaration.  See :DOC declare."
                                    dcl
                                    (set-difference-equal (cdr entry) vars)
                                    (if (eq dcl 'ignore) 0 1)
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

; The type-spec is (or t x).  There is an excellent change that this comes from
; (the type-spec ...); see the-fn.  So we change the error message a bit for
; this case.  Note that the error message is accurate, since (or t x) is
; illegal as a type-spec iff x is illegal.  And the message is reasonable
; because it is not misleading and it is likely to be only for THE, where the
; user did not use an explicit declaration (which was generated by us).

                       (er-cmp ctx
                               "~x0 fails to be a legal type-spec.  See ~
                                :MORE-DOC type-spec."
                               (caddr (cadr entry))))
                      ((weak-satisfies-type-spec-p (cadr entry))
                       (er-cmp ctx
                               "In the declaration ~x0, ~x1 fails to be a ~
                                legal type-spec because the symbol ~x2 is not ~
                                a known function symbol~@3.  See :MORE-DOC ~
                                type-spec."
                               entry (cadr entry) (cadr (cadr entry))
                               (if (eq (getprop (cadr (cadr entry)) 'macro-args
                                                t 'current-acl2-world wrld)
                                       t)
                                   ""
                                 "; rather, it is the name of a macro")))
                      (t
                       (er-cmp ctx
                               "In the declaration ~x0, ~x1 fails to be a ~
                                legal type-spec.  See :MORE-DOC type-spec."
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
                    (t (value-cmp nil))))
                  (otherwise
                   (mv t
                       (er hard! 'chk-dcl-lst
                           "Implementation error: A declaration, ~x0, is ~
                            mentioned in acceptable-dcls-alist but not in ~
                            chk-dcl-lst."
                           dcl))))))))))
       (chk-dcl-lst (cdr l) vars binder ctx wrld state-vars)))))

(defun number-of-strings (l)
  (cond ((null l) 0)
        ((stringp (car l))
         (1+ (number-of-strings (cdr l))))
        (t (number-of-strings (cdr l)))))

(defun remove-strings (l)
  (cond ((null l) nil)
        ((stringp (car l))
         (remove-strings (cdr l)))
        (t (cons (car l) (remove-strings (cdr l))))))

(defun get-string (l)
  (cond ((null l) nil)
        ((stringp (car l)) (list (car l)))
        (t (get-string (cdr l)))))

(defun collect-declarations-cmp (lst vars binder ctx wrld state-vars)

; Lst is a list of (DECLARE ...) forms, and/or documentation strings.
; We check that the elements are declarations of the types appropriate
; for binder, which is one of the names bound in
; acceptable-dcls-alist.  For IGNORE and TYPE declarations, which
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
          (er-progn-cmp (chk-dcl-lst dcls vars binder ctx wrld state-vars)
                        (value-cmp (append (get-string lst) dcls)))))))

(defun collect-declarations (lst vars binder state ctx)
  (cmp-to-error-triple (collect-declarations-cmp lst vars binder ctx
                                                 (w state)
                                                 (default-state-vars t))))

(defun listify (l)
  (cond ((null l) *nil*)
        (t (list 'cons (car l) (listify (cdr l))))))

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
               (and (nvariablep term)
                    (not (fquotep term))
                    (eq (ffn-symb term) 'if)
                    (equal (fargn term 1) *t*)
                    (equal (fargn term 2) *t*))))
         *t*)
        (t (fcons-term* 'if
                        (car term-lst)
                        (dcl-guardian (cdr term-lst))
                        '(illegal 'verify-guards
                                  '"Some TYPE declaration is violated."
                                  'nil)))))

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

(defabbrev translate-bind (x val bindings)

; Used only in translation.  Binds x to val on bindings.

  (cons (cons x val) bindings))

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

; Like er-cmp but returns 3 values, the additional one being the current value
; of bindings.  See also trans-er+ and trans-er+?.

  `(mv-let (ctx msg-or-val)
           (er-cmp ,@args)
           (mv ctx msg-or-val bindings)))

(defmacro trans-er+ (form ctx str &rest args)

; This macro is like trans-er, but it also prints the offending context, form,
; which could be the untranslated term or a surrounding term, etc.

  `(mv-let (ctx msg-or-val)
           (er-cmp ,ctx
                   "~@0  Note:  This error occurred in the context ~x1."
                   (msg ,str ,@args)
                   ,form)
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
; These were code on the property list in a somewhat optimized way
; involving the four properties FORMALS, STATE-IN, MULTIPLICITY, and
; STATE-OUT.  If STATE-IN was absent or NIL, then STATE was not a
; formal.  Otherwise, STATE-IN indicated the position (1-based) of
; STATE in the FORMALS.  If MULTIPLICITY was absent, it was implicitly
; 1.  If STATE-OUT was T then multiplicity was 1 and STATE was the
; single result.  We review these old characteristics because they were
; generalized when we introduced single-threaded objects, or ``stobjs''.

; Now, every function has four aspects to its syntactic character:
; * its arity
; * which of its inputs are stobjs
; * its multiplicity
; * which of its outputs are stobjs

; This is coded on the property list as follows.  First, a ``STOBJ
; flag'' is either NIL or the name of a stobj (including STATE).  A
; list of n STOBJ flags can thus indicate which elements of another
; list of length n are stobjs and which stobjs they are.

; FORMALS gives the list of formals.

; STOBJS-IN is a list of STOBJ flags that is interpreted in 1:1
; correspondence with the formals.  Every function symbol must have
; a STOBJS-IN property.  We do not support space-efficient coding
; of any special cases.

; STOBJS-OUT is a list of stobj flags indicating both the multiplicity
; and which outputs are which stobjs and which stobjs are returned.
; Every function must have a STOBJS-OUT property.  Note however that
; return-last effectively has no such property -- an error is caused
; if the function stobjs-out is applied to it -- as it always returns
; its last argument (possibly a multiple value) and should generally
; be considered as not having stobjs-out.

; During translation we generally have a stobj flag associated with
; the term we are translating, indicating the expected stobj, if any,
; produced by the term.  Consider a stobj flag, $s, that is non-nil,
; i.e., is a stobj name.  Then the term occupying the corresponding
; slot MUST be the stobj name $s.  We think of the stobj flags as
; meaning that the indicated stobj name is the only term that can be
; passed into that slot.

; But a function fn which takes in a stobj, $s, but which does not
; return a modified $s, may in fact be called on any object.  Our
; stobj primitives are all capable of computing on the logical objects
; that represent stobjs.  But they give special treatment to the live
; one.  There are two issues.  First, we do not want the live one ever
; to get into a non-stobj slot because the rest of the functions do
; not know how to handle it.  So if the actual is a stobj, the formal
; must be a stobj.  But if the actual is not a stobj, the formal may
; be a stobj...  Right?  Well, not quite.  The whole notion of
; single-threadedness depends on the determination that the stobj you
; get out is a modification of the stobj you put in and that the
; modifications were carried out by a given sequence of such function
; calls.  If a function returns a stobj, we INSIST that a stobj
; (indeed, ``the stobj'') was supplied.  But if a function does not
; return a stobj, then we don't care if the stobj went in or if some
; random object went in.  Well, we say that... but after Version_4.1 we
; eliminated the INCLP argument to functions in the translate11 nest.

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

; If name is supportive of a single-threaded object implementation, we
; return the name of the defstobj.  Otherwise, we return nil.  By
; "supportive" we mean name is the object name, the live var, a
; recognizer, accessor, updater, helper, resizer, or length function,
; or a constant introduced by the defstobj.

  (cond
   ((getprop name 'stobj nil 'current-acl2-world wrld)
    name)
   ((getprop name 'stobj-function nil 'current-acl2-world wrld))
   ((getprop name 'stobj-constant nil 'current-acl2-world wrld))
   (t (getprop name 'stobj-live-var nil 'current-acl2-world wrld))))

(defun stobj-creatorp (name wrld)

; Returns the name of the stobj that name creates, if name is a stobj creator;
; else returns nil.

; Keep the null test below in sync with the null test (and stobj-flag (null
; (cadr def))) near the top of oneify-cltl-code.

  (and (symbolp name)
       (null (getprop name 'formals t 'current-acl2-world wrld))
       (getprop name 'stobj-function nil 'current-acl2-world wrld)))

(defun defstobj-fnname (root key1 key2 renaming-alist)

; This has been moved from other-events.lisp, where other stobj-related
; functions are defined, because it is used in parse-with-local-stobj, which is
; used in translate11.

; This function generates the actual name we will use for a function generated
; by defstobj.  Root and renaming-alist are, respectively, a symbol and an
; alist.  Key1 describes which function name we are to generate and is one of
; :length, :resize, :recognizer, :accessor, :updater, or :creator.  Key2
; describes the ``type'' of root.  It is :top if root is the name of the live
; object (and hence, root starts with a $) and it is otherwise either :array or
; :non-array.  Note that if renaming-alist is nil, then this function returns
; the ``default'' name used.  If renaming-alist pairs some default name with an
; illegal name, the result is, of course, an illegal name.

  (let* ((default-fnname
           (case key1
             (:recognizer
              (case key2
                (:top
                 (packn-pos
                  (list (coerce (append (coerce (symbol-name root) 'list)
                                        '(#\P))
                                'string))
                  root))
                (otherwise (packn-pos (list root "P") root))))

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
                (otherwise root)))
             (:updater
              (case key2
                (:array (packn-pos (list "UPDATE-" root "I") root))
                (otherwise (packn-pos (list "UPDATE-" root) root))))
             (:creator
              (packn-pos (list "CREATE-" root) root))
             (otherwise
              (er hard 'defstobj-fnname
                  "Implementation error (bad case); please contact ACL2 ~
                   implementors."))))
         (temp (and default-fnname ; see comment above
                    (assoc-eq default-fnname renaming-alist))))
    (if temp (cadr temp) default-fnname)))

(defun parse-with-local-stobj (x)

; x is a with-local-stobj form.  We return (mv erp stobj-name mv-let-form
; creator-name).

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

(mutual-recursion

(defun ffnnamep (fn term)

; We determine whether the function fn (possibly a lambda-expression)
; is used as a function in term.

  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambda-applicationp term)
         (or (equal fn (ffn-symb term))
             (ffnnamep fn (lambda-body (ffn-symb term)))
             (ffnnamep-lst fn (fargs term))))
        ((eq (ffn-symb term) fn) t)
        (t (ffnnamep-lst fn (fargs term)))))

(defun ffnnamep-lst (fn l)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-listp l))))
  (if (null l)
      nil
    (or (ffnnamep fn (car l))
        (ffnnamep-lst fn (cdr l)))))

)

(defconst *synp-trans-err-string*
  "A synp term must take three quoted arguments, unlike ~x0.  Normally, a call ~
   to synp is the result of the macroexpansion of a call to syntaxp or ~
   bind-free, but this does not seem to be the case here.  If you believe this ~
   error message is itself in error please contact the maintainers of ACL2.")

(defconst *ttag-fns-and-macros*

; Each cdr is either nil or a msg.

  `((open-output-channel!)
    (progn!) ; protected because it is legal in books; it's OK to omit progn-fn
    (remove-untouchable-fn
     .
     ,(msg "  Note that the same restriction applies to the macro ~x0, whose ~
            expansions generate calls of ~x1."
           'remove-untouchable
           'remove-untouchable-fn))
    (set-raw-mode-on
     .
     ,(msg "  If you do not plan to certify books in this session, then ~
            instead you may want to call ~x0; see :DOC ~x0."
           'set-raw-mode-on!))
    (set-temp-touchable-fns)
    (set-temp-touchable-vars)
    (sys-call)
    ))

(defun ttag (wrld)

; This function returns nil if there is no active ttag.

  (declare (xargs :guard
                  (and (plist-worldp wrld)
                       (alistp (table-alist 'acl2-defaults-table wrld)))))
  (cdr (assoc-eq :ttag (table-alist 'acl2-defaults-table wrld))))

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

(defconst *oneify-primitives*

;;;; Some day we should perhaps remove consp and other such functions from this
;;;; list because of the "generalized Boolean" problem.

; Add to this list whenever we find a guardless function in #+acl2-loop-only.

  '(if equal cons not consp atom acl2-numberp characterp integerp rationalp
       stringp symbolp

; We want fmt-to-comment-window (which will arise upon macroexpanding calls of
; cw) to be executed always in raw Lisp, so we add it to this list in order to
; bypass its *1* function.

       fmt-to-comment-window

; When we oneify, we sometimes do so on code that was laid down for constrained
; functions.  Therefore, we put throw on the list.

       throw-raw-ev-fncall

; The next group may be important for the use of safe-mode.

       makunbound-global
       trans-eval ev ev-lst ev-fncall
;      fmt-to-comment-window ; already included above
       sys-call-status
;      pstack-fn
       untranslate
       untranslate-lst
       trace$-fn-general untrace$-fn-general untrace$-fn1 maybe-untrace$-fn
       memoize-on memoize-off ; especially relevant for #+hons
       set-w acl2-unwind-protect

; We know that calls of mv-list in function bodies are checked syntactically to
; satisfy arity and syntactic requirements, so it is safe to call it in raw
; Lisp rather than somehow considering its *1* function.  We considered adding
; return-last as well, but not only does return-last have a guard other than T,
; but indeed (return-last 'mbe1-raw exec logic) macroexpands in raw Lisp to
; exec, which isn't what we want in oneified code.

       mv-list
       ))

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
;   defdoc

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
                    being defined.  Thus, you cannot define ~&0 ~
                    simultaneously."
                   lst))))

(defun chk-no-duplicate-defuns (lst ctx state)
  (cmp-to-error-triple (chk-no-duplicate-defuns-cmp lst ctx))) 

(defun chk-state-ok-msg (wrld)

; We are in a context where 'state is a member of a list of formals.  Is this
; OK?

  (cond ((and (not (global-val 'boot-strap-flg wrld))
              (not (cdr (assoc-eq :state-ok
                                  (table-alist 'acl2-defaults-table
                                               wrld)))))
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
         (msg "The argument list to a function must be a true list but ~x0 is ~
               not."
              args))
        (t (mv-let (culprit explan)
                   (find-first-bad-arg args)
                   (msg "The argument list to a function must be a true list ~
                         of distinct, legal variable names.  ~x0 is not such ~
                         a list.  The element ~x1 violates the rules because ~
                         it ~@2."
                        args culprit explan)))))

(defun msg-to-cmp (ctx msg)

; Convert a given context and message to a corresponding context-message pair
; (see the Essay on Context-message Pairs).

  (assert$ ctx
           (cond (msg (mv ctx msg))
                 (t (mv nil nil)))))

(defun chk-arglist-cmp (args chk-state ctx wrld)
  (msg-to-cmp ctx (chk-arglist-msg args chk-state wrld)))

(defun chk-arglist (args chk-state ctx wrld state)
  (let ((msg (chk-arglist-msg args chk-state wrld)))
    (cond (msg (er soft ctx "~@0" msg))
          (t (value nil)))))

(defun logical-name-type (name wrld quietp)

; Given a logical-namep we determine what sort of logical object it is.

  (cond ((stringp name) 'package)
        ((function-symbolp name wrld) 'function)
        ((getprop name 'macro-body nil 'current-acl2-world wrld) 'macro)
        ((getprop name 'const nil 'current-acl2-world wrld) 'const)
        ((getprop name 'theorem nil 'current-acl2-world wrld) 'theorem)
        ((not (eq (getprop name 'theory t 'current-acl2-world wrld) t))
         'theory)
        ((getprop name 'label nil 'current-acl2-world wrld) 'label)
        ((getprop name 'stobj nil 'current-acl2-world wrld)

; Warning: Non-stobjs can have the stobj property, so do not move this cond
; clause upward!

         'stobj)
        ((getprop name 'stobj-live-var nil 'current-acl2-world wrld)
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
              (not (global-val 'boot-strap-flg w))
              (or

; Only definitions can be redefined from :program mode to :logic mode.

               (not (eq new-type 'function))
               (not (eq (logical-name-type name w t) 'function))))
         (er-cmp ctx
                 "Symbols in the main Lisp package, such as ~x0, may not be ~
                  defined or constrained."
                 name))
        (t (value-cmp nil))))

(defun chk-all-but-new-name (name ctx new-type w state)
  (cmp-to-error-triple (chk-all-but-new-name-cmp name ctx new-type w)))

(defun chk-defuns-tuples-cmp (lst local-p ctx wrld state-vars)
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
                      ctx wrld state-vars))
              (rst (chk-defuns-tuples-cmp (cdr lst) local-p ctx wrld
                                          state-vars)))
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
  (cmp-to-error-triple (chk-defuns-tuples-cmp lst local-p ctx wrld
                                              (default-state-vars t))))

(defun non-trivial-encapsulate-ee-entries (embedded-event-lst)
  (cond ((endp embedded-event-lst)
         nil)
        ((and (eq (caar embedded-event-lst) 'encapsulate)
              (cadar embedded-event-lst))
         (cons (car embedded-event-lst)
               (non-trivial-encapsulate-ee-entries (cdr embedded-event-lst))))
        (t (non-trivial-encapsulate-ee-entries (cdr embedded-event-lst)))))

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

(defun name-dropper (lst)

; This function builds a term that mentions each element of lst.  Provided the
; elements of list are translated terms, the output is a translated term.
; Provided every element of lst has a guard of t, the output has a guard of t.
; The intention here is that lst is a list of distinct variable names and
; name-dropper builds a translated term whose free-vars are those variables;
; futhermore, it is cheap to evaluate and always has a guard of T.
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
     ((getprop name 'predefined nil 'current-acl2-world wrld)
      (trans-er+ form ctx
                 "An FLET form has attempted to bind ~x0, which is predefined ~
                  in ACL2 hence may not be FLET-bound."
                 name))
     #-acl2-loop-only
     ((or (special-form-or-op-p name)
          (and (or (macro-function name)
                   (fboundp name))
               (not (getprop name 'macro-body nil 'current-acl2-world wrld))
               (eq (getprop name 'formals t 'current-acl2-world wrld) t)))
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
       (let ((stobjs-bound
              (collect-non-x nil (compute-stobj-flags bound-vars
                                                      known-stobjs
                                                      wrld)))
             (used-vars (union-eq (all-vars tbody)
                                  (all-vars1-lst tdcls nil)))
             (ignore-vars (ignore-vars edcls))
             (ignorable-vars (ignorable-vars edcls))
             (stobjs-out (translate-deref new-stobjs-out bindings)))
         (cond

; We skip the following case, where stobjs-out is not yet bound to a consp and
; some formal is a stobj, in favor of the next, which removes the stobj
; criterion.  But we leave this case here as a comment in case we ultimately
; find a way to eliminate the more sweeping case after it.

;         ((and (not (eq stobjs-out t))
;               stobjs-bound
;               (not (consp stobjs-out)))
;          (trans-er ctx
;                    "~@0"
;                    (unknown-binding-msg
;                     stobjs-bound
;                     (msg "the formals of an FLET binding for function ~x0"
;                          name)
;                     "the body of this FLET binding"
;                     "that body")))

          ((and (not (eq stobjs-out t))
                (not (consp stobjs-out)))

; Warning: Before changing this case, see the comment above about the
; commented-out preceding case.

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
          ((and (not (eq stobjs-out t))
                stobjs-bound
                (not (subsetp-eq stobjs-bound
                                 (collect-non-x nil stobjs-out))))
           (let ((stobjs-returned (collect-non-x nil stobjs-out)))
             (trans-er+ form ctx
                        "The single-threaded object~#0~[ ~&0 is a formal~/s ~
                         ~&0 are formals~] of an FLET-binding of ~x3.  It is ~
                         a requirement that ~#0~[this object~/these objects~] ~
                         be among the outputs of the body of that binding, ~
                         but ~#0~[it is~/they are~] not.  That body returns ~
                         ~#1~[no single-threaded objects~/the single-threaded ~
                         object ~&2~/the single-threaded objects ~&2~]."
                       (set-difference-eq stobjs-bound stobjs-returned)
                       (zero-one-or-more stobjs-returned)
                       stobjs-returned
                       name)))
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
                  (warning$-cmp ctx "Ignored-variables"
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
                       (delete-assoc-eq new-stobjs-out
                                        bindings))))))))))))))))))

(defun translate11-flet (x stobjs-out bindings known-stobjs flet-alist
                           ctx wrld state-vars)
  (cond
   ((not (eql (length x) 3))
    (trans-er ctx
              "An FLET form must have the form (flet bindings body), where ~
               bindings is a list of local function definitions, but ~x0 does ~
               not have this form.  See :DOC flet."
              x))
   (t
    (mv-let
     (erp fives)
     (chk-defuns-tuples-cmp (cadr x) t ctx wrld state-vars)
     (let ((names (strip-cars fives)))
       (mv-let
        (erp ignored-val)
        (if erp ; erp is a ctx and fives is a msg
            (mv erp fives)

; Note that we do not need to call chk-xargs-keywords, since
; acceptable-dcls-alist guarantees that xargs is illegal.

          (chk-no-duplicate-defuns-cmp names ctx))
        (declare (ignore ignored-val))
        (cond
         (erp (trans-er ctx
                        "The above error indicates a problem with the form ~p0."
                        x))
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
                     are~] thus illegal for ~&1.  See :DOC return-last-table."
                    'return-last
                    (intersection-eq
                     names
                     (strip-cars (table-alist 'return-last-table wrld)))))
         (t
          (trans-er-let*
           ((flet-alist (translate11-flet-alist x fives stobjs-out bindings
                                                known-stobjs flet-alist ctx wrld
                                                state-vars)))
           (translate11 (car (last x)) ; (nth 2 x) as of this writing
                        stobjs-out bindings known-stobjs flet-alist x
                        ctx wrld state-vars))))))))))

(defun translate11-mv-let (x stobjs-out bindings known-stobjs
                             local-stobj local-stobj-creator flet-alist
                             ctx wrld state-vars)

; X is a cons whose car is 'MV-LET.  This function is nothing more than the
; restriction of function translate11 to that case, except that if local-stobj
; is not nil, then we are in the process of translating
; (with-local-stobj local-stobj x local-stobj-creator), where we know that
; local-stobj-creator is the creator function for the stobj local-stobj.

; Warning:  If the final form of a translated mv-let is changed,
; be sure to reconsider translated-acl2-unwind-protectp.

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
           (producer-known-stobjs
            (if (and local-stobj (not (eq known-stobjs t)))
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
              stobjs-bound0))
           (body (car (last x))))
      (mv-let
       (erp edcls)
       (collect-declarations-cmp (butlast (cdddr x) 1)
                                 (cadr x) 'mv-let ctx wrld state-vars)
       (cond
        (erp (trans-er erp edcls))
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
                                     nil)          ;;; '(nil ... nil)
                                   bindings known-stobjs
                                   "in a DECLARE form in an MV-LET"
                                   flet-alist x ctx wrld state-vars))
           (tbody (translate11 body stobjs-out bindings
                               known-stobjs flet-alist x ctx wrld state-vars)))
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
              (trans-er+ x ctx
                         "~@0"
                         (unknown-binding-msg
                          stobjs-bound "an MV-LET" "the MV-LET" "the MV-LET")))
             ((and stobjs-bound
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
                     (warning$-cmp ctx "Ignored-variables"
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

(defun translate11-call (form fn args stobjs-out stobjs-out2 bindings
                              known-stobjs msg flet-alist ctx wrld state-vars)
  (let ((stobjs-in
         (if (consp fn)
             (compute-stobj-flags (lambda-formals fn)
                                  known-stobjs
                                  wrld)
           (stobjs-in fn wrld))))
    (cond
     ((consp stobjs-out)
      (cond
       ((consp stobjs-out2)
        (cond
         ((not (equal stobjs-out stobjs-out2))
          (trans-er+ form ctx
                     "It is illegal to invoke ~@0 here because of a signature ~
                      mismatch.  This function returns a result of shape ~x1 ~
                      where a result of shape ~x2 is required."
                     (if (consp fn) msg (msg "~x0" fn))
                     (prettyify-stobjs-out stobjs-out2)
                     (prettyify-stobjs-out stobjs-out)))
         (t (trans-er-let*

; We handle the special translation of wormhole-eval both here, when stobjs-out
; is known, and below, where it is not.  Of course, stobjs-out2 (for
; wormhole-eval) is fixed: (nil).  Keep this code in sync with that below.

; The odd treatment of wormhole-eval's first two arguments below is due to the
; fact that we actually don't want to translate them.  We will insist that they
; actually be quoted forms, not macro calls that expand to quoted forms.  So we
; put bogus nils in here and then swap back the untranslated args below.

             ((targs (translate11-lst (if (eq fn 'wormhole-eval)
                                          (list *nil* *nil* (nth 2 args))
                                          args)
                                      stobjs-in
                                      bindings
                                      known-stobjs
                                      msg flet-alist form ctx wrld
                                      state-vars)))
             (cond ((eq fn 'wormhole-eval)
                    (translate11-wormhole-eval (car args)
                                               (cadr args)
                                               (caddr targs)
                                               bindings flet-alist ctx wrld
                                               state-vars))
                   (t (trans-value (fcons-term fn targs))))))))
       (t
        (let ((bindings
               (translate-bind stobjs-out2 stobjs-out bindings)))
          (trans-er-let*
           ((args (translate11-lst args
                                   stobjs-in
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)))
           (trans-value (fcons-term fn args)))))))
     ((consp stobjs-out2)
      (let ((bindings
             (translate-bind stobjs-out stobjs-out2 bindings)))
        (trans-er-let*
         ((targs (translate11-lst (if (eq fn 'wormhole-eval)
                                      (list *nil* *nil* (nth 2 args))
                                      args)
                                  stobjs-in
                                  bindings known-stobjs
                                  msg flet-alist form ctx wrld state-vars)))
         (cond ((eq fn 'wormhole-eval)
                (translate11-wormhole-eval (car args)
                                           (cadr args)
                                           (caddr targs)
                                           bindings flet-alist ctx wrld
                                           state-vars))
               (t (trans-value (fcons-term fn targs)))))))
     (t (let ((bindings
               (translate-bind stobjs-out2 stobjs-out bindings)))
          (trans-er-let*
           ((args (translate11-lst args
                                   stobjs-in
                                   bindings known-stobjs
                                   msg flet-alist form ctx wrld state-vars)))
           (trans-value (fcons-term fn args))))))))

(defun translate11 (x stobjs-out bindings known-stobjs flet-alist
                      cform ctx wrld state-vars)

; Bindings is an alist binding symbols either to their corresponding
; STOBJS-OUT or to symbols.  The only symbols used are (about-to-be
; introduced) function symbols or the keyword :STOBJS-OUT.  When fn is
; bound to gn it means we have determined that the STOBJS-OUT of fn is
; that of gn.  We allow fn to be bound to itself -- indeed, it is
; required initially!  (This allows bindings to double as a recording
; of all the names currently being introduced.)

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
;                  body and allow DEFUN, IN-PACKAGE, etc.

; See the essay on STOBJS-IN and STOBJS-OUT, above.

; When stobjs-out is a symbol, it must be dereferenced through bindings
; before using it.  [One might think that we follow the convention of keeping
; it dereferenced, e.g., by using the new value whenever we bind it.
; But that is hard since the binding may come deep in some recursive
; call of translate.]

; T always deferences to t and nothing else dereferences to t.  So you
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
             ((eq stobjs-out t)              ;;; (1)
              (trans-value transx))
             ((consp stobjs-out)             ;;; (2)
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
             (t                              ;;; (3)
              (trans-value transx
                           (translate-bind
                            stobjs-out
                            (list (if (stobjp transx known-stobjs wrld)
                                      transx
                                    nil))
                            bindings)))))))))
   ((not (true-listp (cdr x)))
    (trans-er ctx
              "Function applications in ACL2 must end in NIL.  ~x0 is ~
               not of this form."
              x))
   ((not (symbolp (car x)))
    (cond ((or (not (consp (car x)))
               (not (eq (caar x) 'lambda)))
           (trans-er ctx
                     "Function applications in ACL2 must begin with a ~
                      symbol or LAMBDA expression.  ~x0 is not of ~
                      this form."
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
                        "It is illegal to return more than one ~
                         reference to a given single-threaded object ~
                         in an MV form.  The form ~x0 is thus illegal."
                        x))
             (t
              (trans-er-let*
               ((args
                 (translate11-lst (cdr x) new-stobjs-out
                                  bindings known-stobjs
                                  'mv flet-alist x ctx wrld state-vars)))
               (trans-value (listify args))))))))))
   ((eq (car x) 'mv-let)
    (translate11-mv-let x stobjs-out bindings known-stobjs
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
            (t
             (translate11-call x lambda-fn (cdr x) stobjs-out stobjs-out2
                               bindings known-stobjs
                               (msg "a call of FLET-bound function ~x0"
                                    (car x))
                               flet-alist ctx wrld state-vars)))))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member-eq (car x) '(defun defmacro in-package progn)))
    (trans-er+ x ctx
               "We do not permit the use of ~x0 inside of code to be executed ~
                by Common Lisp because its Common Lisp meaning differs from ~
                its ACL2 meaning."
               (car x)))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member-eq (car x)
                    '(defpkg defconst defstobj defthm defaxiom
                       deflabel defdoc deftheory
                       verify-guards
                       in-theory in-arithmetic-theory
                       push-untouchable remove-untouchable reset-prehistory
                       set-body table theory-invariant
                       include-book certify-book value-triple
                       local make-event with-output progn!)))
    (trans-er+ x ctx
               "We do not permit the use of ~x0 inside of code to be executed ~
                by Common Lisp because its Common Lisp runtime value and ~
                effect differs from its ACL2 meaning."
               (car x)))
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
                            (getprop (car form) 'macro-body nil
                                     'current-acl2-world
                                     wrld))
                       (list "  Note that ~x0 is a macro, not a function symbol."
                             (cons #\0 (car form)))
                     ""))))))
   ((eq (car x) 'translate-and-test)
    (cond ((not (equal (length x) 3))
           (trans-er+ x ctx
                      "TRANSLATE-AND-TEST requires exactly two arguments."))
          (t (trans-er-let*
              ((ans (translate11 (caddr x) stobjs-out bindings
                                 known-stobjs flet-alist x ctx wrld
                                 state-vars)))

; The next mv-let is spiritually just a continuation of the trans-er-let*
; above, as though to say "and let  test-term be (translate11 (list ...)...)"
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
                           (trans-er+ x ctx "~@0" msg))
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
             ((eq stobjs-out :stobjs-out)
              (trans-er ctx
                        "Calls of with-local-stobj, such as ~x0, cannot be ~
                         evaluated directly in the top-level loop.  ~
                         See :DOC with-local-stobj and see :DOC top-level."
                        x))
             ((and (eq st 'state)
                   (eq creator 'create-state)
                   (member-eq 'create-state
                              (global-val 'untouchable-fns wrld))
                   (not (eq (access state-vars state-vars :temp-touchable-fns)
                            t))
                   (not (member-eq 'create-state
                                   (access state-vars state-vars
                                           :temp-touchable-fns))))

; We provide a courtesy error here, rather than waiting to encounter
; create-state.

              (trans-er ctx
                        "Illegal with-local-stobj form, ~x0 (perhaps expanded ~
                         from a corresponding with-local-state form).  By ~
                         default, it is illegal to bind state using ~
                         with-local-stobj because it is generally dangerous ~
                         and unsound; see :DOC with-local-state, which ~
                         describes how to get around this restriction and ~
                         when it may be appropriate to do so."
                        x))
             ((and st
                   (if (eq st 'state)
                       (eq creator 'create-state)
                     (eq st (stobj-creatorp creator wrld))))
              (translate11-mv-let mv-let-form stobjs-out bindings
                                  known-stobjs st creator flet-alist ctx wrld
                                  state-vars))
             (t
              (trans-er ctx
                        "Illegal with-local-stobj form, ~x0.  The first ~
                         argument must be the name of a stobj and the third, ~
                         if supplied, must be its creator function.  See :DOC ~
                         with-local-stobj."
                        x)))))
   ((and (assoc-eq (car x) *ttag-fns-and-macros*)
         (not (ttag wrld)))
    (trans-er+ x ctx
               "The ~x0 ~s1 cannot be called unless a trust tag is in effect. ~
                ~ See :DOC defttag.~@2"
               (car x)
               (if (getprop (car x) 'macro-body nil 'current-acl2-world wrld)
                   "macro"
                 "function")
               (or (cdr (assoc-eq (car x) *ttag-fns-and-macros*))
                   "")))
   ((getprop (car x) 'macro-body nil 'current-acl2-world wrld)
    (cond
     ((and (eq stobjs-out :stobjs-out)
           (member-eq (car x) '(pand por pargs plet))
           (eq (access state-vars state-vars :parallel-evaluation-enabled)
               t))
      (trans-er ctx
                "Parallel evaluation is enabled, but is not implemented for ~
                 calls of parallelism primitives (~&0) made directly in the ~
                 ACL2 top-level loop, as opposed to being made inside a ~
                 function definition.  The call ~x1 is thus illegal.  To ~
                 allow such calls to be evaluated (but without parallelism), ~
                 either evaluate ~x2 or use the macro top-level.  See :DOC ~
                 parallelism-at-the-top-level and :DOC ~
                 set-parallel-evaluation."
                '(pand por pargs plet)
                x
                '(set-parallel-evaluation :bogus-parallelism-ok)))
     ((and (member-eq (car x) (global-val 'untouchable-fns wrld))
           (not (eq (access state-vars state-vars :temp-touchable-fns)
                    t))
           (not (member-eq (car x) (access state-vars state-vars
                                           :temp-touchable-fns))))

; If this error burns you during system maintenance, you can subvert our
; security by setting untouchables to nil in raw Lisp:

; (setf (cadr (assoc 'global-value 
;                    (get 'untouchable-fns *current-acl2-world-key*)))
;       nil)

      (trans-er+ x ctx
                 "It is illegal to call ~x0 because it has been placed on ~
                  untouchable-fns."
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

; Warning:  If the final form of a translated let is changed,
; be sure to reconsider translated-acl2-unwind-protectp.

; In translating LET and MV-LET we generate "open lambdas" as function
; symbols.  The main reason we did this was to prevent translate from
; exploding in our faces when presented with typical DEFUNs (e.g., our
; own code).  Note that such LAMBDAs can be expanded away.  However,
; expansion affects the guards.  Consider (let ((x (car 3))) t), which
; expands to ((lambda (x) t) (car 3)).

    (cond
     ((not (and (>= (length x) 3)
                (doubleton-list-p (cadr x))))
      (trans-er ctx
                "The proper form of a let is (let bindings dcl ... ~
                 dcl body), where bindings has the form ((v1 term) ~
                 ... (vn term)) and the vi are distinct variables, ~
                 not constants, and do not begin with an asterisk, ~
                 but ~x0 does not have this form."
                x))
     ((not (arglistp (strip-cars (cadr x))))
      (mv-let (culprit explan)
              (find-first-bad-arg (strip-cars (cadr x)))
              (trans-er ctx
                        "The form ~x0 is an improper let expression ~
                         because it attempts to bind ~x1, which ~@2."
                        x culprit explan)))
     ((and (not (eq stobjs-out t))
           (not (equal 1 (length (cadr x))))
           (not (all-nils (compute-stobj-flags (strip-cars (cadr x))
                                               known-stobjs
                                               wrld))))
      (trans-er ctx
                "A single-threaded object name, such as ~x0, may be ~
                 LET-bound only when it is the only binding in the ~
                 LET, but ~x1 binds more than one variable."
                (car
                 (collect-non-x nil
                  (compute-stobj-flags (strip-cars (cadr x))
                                       known-stobjs
                                       wrld)))
                x))
     (t (let* ((bound-vars (strip-cars (cadr x)))
               (stobjs-bound
                (collect-non-x nil (compute-stobj-flags bound-vars
                                                        known-stobjs
                                                        wrld)))
               (body (car (last x))))
          (mv-let
           (erp edcls)
           (collect-declarations-cmp (butlast (cddr x) 1)
                                     bound-vars 'let ctx wrld state-vars)
           (cond
            (erp (mv erp edcls bindings))
            (t
             (trans-er-let*
              ((value-forms
                (cond ((and (not (eq stobjs-out t))
                            stobjs-bound)

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
                                            nil)       ;;; '(nil ... nil)
                                          bindings known-stobjs
                                          "in a LET binding (or ~
                                           LAMBDA application)"
                                          flet-alist x ctx wrld state-vars))))
               (tbody
                (translate11 body stobjs-out bindings known-stobjs
                             flet-alist x ctx wrld state-vars))
               (tdcls (translate11-lst
                       (translate-dcl-lst edcls wrld)
                       (if (eq stobjs-out t)
                           t
                         nil)         ;;; '(nil ... nil)
                       bindings known-stobjs
                       "in a DECLARE form in a LET (or LAMBDA)"
                       flet-alist x ctx wrld state-vars)))
              (let ((used-vars (union-eq (all-vars tbody)
                                         (all-vars1-lst tdcls nil)))
                    (ignore-vars (ignore-vars edcls))
                    (ignorable-vars (ignorable-vars edcls))
                    (stobjs-out (translate-deref stobjs-out bindings)))
                (cond 
                 ((and (not (eq stobjs-out t))
                       stobjs-bound
                       (not (consp stobjs-out)))
                  (trans-er+ x ctx
                             "~@0"
                             (unknown-binding-msg
                              stobjs-bound "a LET" "the LET" "the LET")))
                 ((and (not (eq stobjs-out t))
                       stobjs-bound
                       (not (subsetp-eq stobjs-bound
                                        (collect-non-x nil stobjs-out))))
                  (let ((stobjs-returned (collect-non-x nil stobjs-out)))
                    (trans-er+ x ctx
                               "The single-threaded object~#0~[ ~&0 has~/s ~
                                ~&0 have~] been bound in a LET.  It is a ~
                                requirement that ~#0~[this object~/these ~
                                objects~] be among the outputs of the LET, ~
                                but ~#0~[it is~/they are~] not.  The LET ~
                                returns ~#1~[no single-threaded objects~/the ~
                                single-threaded object ~&2~/the ~
                                single-threaded objects ~&2~]."
                               (set-difference-eq stobjs-bound stobjs-returned)
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
                         (warning$-cmp ctx "Ignored-variables"
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
                                (t tbody)))
                              (body-vars (all-vars tbody))
                              (extra-body-vars (set-difference-eq
                                                body-vars
                                                bound-vars)))
                         (trans-value
                          (cons (make-lambda
                                 (append bound-vars extra-body-vars)
                                 tbody)

; See the analogous line in the handling of MV-LET for an explanation
; of hide-ignored-actuals.

                                (append
                                 (hide-ignored-actuals
                                  ignore-vars bound-vars value-forms)
                                 extra-body-vars)))))))))))))))))))
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
    (cond ((and (member-eq (car x) (global-val 'untouchable-fns wrld))
                (not (eq (access state-vars state-vars :temp-touchable-fns)
                         t))
                (not (member-eq (car x) (access state-vars state-vars
                                                :temp-touchable-fns))))
           (trans-er+ x ctx
                      "It is illegal to call ~x0 because it has been placed ~
                       on untouchable-fns."
                      (car x)))
          ((eq (car x) 'if)
           (cond ((stobjp (cadr x) known-stobjs wrld)
                  (trans-er+ x ctx
                             "It is illegal to test on a single-threaded ~
                              object such as ~x0."
                             (cadr x)))

; Because (cadr x) has not yet been translated, we do not really know it is not
; a stobj!  It could be a macro call that expands to a stobj.'  The error
; message above is just to be helpful.  An accurate check is made below.

                 (t (trans-er-let*
                     ((arg1 (translate11 (cadr x)
                                         (if (eq stobjs-out t)
                                             t
                                           '(nil))
                                         bindings known-stobjs
                                         flet-alist x ctx wrld state-vars))
                      (arg2 (translate11 (caddr x)
                                         stobjs-out bindings known-stobjs
                                         flet-alist x ctx wrld state-vars))
                      (arg3 (translate11 (cadddr x)
                                         stobjs-out bindings known-stobjs
                                         flet-alist x ctx wrld state-vars)))
                     (trans-value (fcons-term* 'if arg1 arg2 arg3))))))
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
; not change, stobjs.  If this is changed, change the referances to stobjs in
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
                                      x))))))
                 (t
                  (trans-er ctx
                            *synp-trans-err-string*
                            x))))
          ((and (eq (car x) 'mv-list)
                (not (eq stobjs-out t)))
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
          ((eq stobjs-out t)
           (trans-er-let*
            ((args (translate11-lst (cdr x) t bindings known-stobjs
                                    nil flet-alist x ctx wrld state-vars)))
            (trans-value (fcons-term (car x) args))))
          ((eq (car x) 'return-last) ; and stobjs-out is not t
           (let* ((arg1 (nth 1 x))
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
                          (nth 1 x)))
               ((eq key 'mbe1-raw)

; We need to know that the two arguments of mbe1 have the same signature.  If
; for example we have (mv-let (x y) (mbe1 <exec-form> <logic-form>)), but
; <exec-form> has signature *, then Common Lisp will get confused during
; evaluation.  This signature requirement is enforced by the trans-er-let*
; bindings below.

; At one time we disallowed the use of mbe inside a non-trivial encapsulate
; when translating for execution (stobjs-out not equal to t).  To see why, see
; the example in the comment near the top of (deflabel note-3-4 ...).  However,
; we subsequently disallowed guard verification for functions defined
; non-locally inside an encapsulate (see :DOC note-4-0), which is the proper
; fix for this issue.  What then is this issue?  The issue is that we need to
; be able to trust guard verification; evaluating the :exec branch of an mbe is
; just a special case.

                (trans-er-let*
                 ((targ2 (translate11 (nth 2 x)
                                      stobjs-out bindings known-stobjs
                                      flet-alist x ctx wrld state-vars)) 
                  (targ3 (translate11 (nth 3 x)
                                      stobjs-out bindings known-stobjs
                                      flet-alist x ctx wrld state-vars)))
                 (trans-value
                  (fcons-term* 'return-last targ1 targ2 targ3))))
               ((and (eq key 'ec-call1-raw)
                     (not (let* ((call (car (last x)))
                                 (fn (and (consp call)
                                          (car call))))
                            (and (symbolp fn)
                                 (not (member-eq fn *ec-call-bad-ops*))
                                 (function-symbolp fn wrld)))))
                (trans-er ctx
                          "A call of ~x0 (including macroexpansion of such a ~
                           call) must only be made on an argument of the form ~
                           (FN ...), where FN is a known function symbol of ~
                           the current ACL2 world not belonging to the list ~
                           that is the value of the constant ~x1.  The ~
                           argument ~x2 is thus illegal for ~x0, because ~@3."
                          'ec-call '*ec-call-bad-ops* (car (last x))
                          (let* ((call (car (last x)))
                                 (fn (and (consp call)
                                          (car call))))
                            (cond ((not (symbolp fn))
                                   (msg "~x0 is not a symbol" fn))
                                  ((member-eq fn *ec-call-bad-ops*)
                                   (msg "~x0 belongs to the above list" fn))
                                  ((atom call)
                                   (msg "~x0 does not have the form of a ~
                                          function call"
                                        call))
                                  ((eq (getprop fn 'macro-args t
                                                'current-acl2-world wrld)
                                       t)
                                   (assert$
                                    (not (function-symbolp fn wrld))
                                    (msg "~x0 is not a function symbol"
                                         fn)))
                                  (t (msg "~x0 is a macro, not a function ~
                                           symbol"
                                          fn))))))
               ((and keyp (not (return-last-lookup key wrld)))

; In an early implementation of return-last, we insisted that keyp be true.  But
; when we attempted to update the "GL" work of Sol Swords to use return-last,
; we encountered the creation of symbolic terms (presumably for some sort of
; meta reasoning) for which the first argument was not quoted.  Rather than try
; to understand whether this was necessary, we decided that others might also
; want to write meta-level functions that cons up return-last terms without a
; quoted first argument; and since it is easy to support that, we do so.

                (trans-er ctx
                          "The symbol ~x0 is specified in the first argument ~
                           of the form ~x1.  But ~x0 is not associated in the ~
                           table ~x2 with a non-nil symbol.  See :DOC ~
                           return-last."
                          key x 'return-last-table))
               (t
                (mv-let
                 (erp targ2 targ2-bindings)
                 (translate11 (nth 2 x)
                              '(nil) bindings known-stobjs
                              flet-alist x ctx wrld state-vars)
                 (declare (ignore targ2-bindings))
                 (cond
                  (erp (mv erp targ2 bindings))
                  (t
                   (trans-er-let*
                    ((targ3 (translate11
                             (nth 3 x)
                             stobjs-out bindings
                             known-stobjs ; for return-last call's last arg
                             flet-alist x ctx wrld state-vars)))
                    (cond
                     ((and (eq key 'ec-call1-raw)
                           keyp ; should always be true (but playing it safe)
                           (not (and (nvariablep targ3)
                                     (not (fquotep targ3))
                                     (symbolp (ffn-symb targ3))
                                     (function-symbolp (ffn-symb targ3) wrld))))
                      (trans-er ctx
                                "The argument of ~x0 must be a call of a ~
                                 known function symbol, but ~x1 is not."
                                'ec-call targ3))
                     (t (trans-value
                         (fcons-term* 'return-last
                                      targ1 targ2 targ3)))))))))))))
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
                      (always-boundp-global (cadr (cadr x))))))
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
                                                        (symbol-name (cadr (cadr x))))
                                           (cadr (cadr x)))))
                              (cond ((function-symbolp set-fn wrld)
                                     (msg "~|There is a function ~x0, which ~
                                           (from the name) may provide the ~
                                           functionality you desire."
                                          set-fn))
                                    (t "")))))
                 (t
                  (trans-er ctx
                            "Built-in state global variables may not be made ~
                             unbound, as in ~x1."
                            (cadr (cadr x))
                            x))))
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
              "~x0 takes ~#1~[no arguments~/1 argument~/~x2 ~
               arguments~] but in the call ~x3 it is given ~#4~[no ~
               arguments~/1 argument~/~x5 arguments~].   The formal ~
               parameters list for ~x0 is ~X67."
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
              "It is illegal to use DECLARE as a function symbol, as ~
               in ~x0.  DECLARE forms are permitted only in very ~
               special places, e.g., before the bodies of function ~
               definitions, LETs, and MV-LETs.  DECLARE forms are ~
               never permitted in places in which their ``values'' ~
               are relevant.  If you already knew this, it is likely ~
               you have made a typographical mistake, e.g., including ~
               the body in the DECLARE form or closing the superior ~
               form before typing the body."
              x))
   (t (trans-er+ x ctx
                 "The symbol ~x0 (in package ~x1) has neither a function nor ~
                  macro definition in ACL2.  ~#2~[Please define ~
                  it.~/Moreover, this symbol is in the main Lisp package; ~
                  hence, you cannot define it in ACL2.~]"
                 (car x)
                 (symbol-package-name (car x))
                 (if (equal (symbol-package-name (car x))
                            *main-lisp-package-name*)
                     1
                   0)))))

(defun translate11-lst (lst stobjs-out bindings known-stobjs
                            msg flet-alist cform ctx wrld state-vars)

; WARNING: This function's treatment of stobjs-out is unusual:
; (1) stobjs-out must be either t, nil, or list of stobjs flags.
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
                             (car lst) ctx wrld state-vars))
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
; :stobjs-out) to determine that we are not in a definition.  [Note: as this
; function recurs, bindings may grow because we add new bindings with cons; but
; in the case of :stobjs-out it will always contain just that one key.]

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
; bindings has been modified to bind every fn (ultimately) to a proper stobjs
; out setting.  Use translate-deref to recover the bindings.

  (translate11 x stobjs-out bindings known-stobjs nil x ctx w state-vars))

(defun translate1 (x stobjs-out bindings known-stobjs ctx w state)
  (mv-let (erp msg-or-val bindings)
          (translate1-cmp x stobjs-out bindings known-stobjs ctx w
                          (default-state-vars t))
          (cond (erp ; erp is a ctx and val is a msg
                 (mv-let (erp0 val state)
                         (er soft erp
                             "~@0"
                             msg-or-val)
                         (declare (ignore erp0 val))
                         (mv t nil bindings state)))
                (t (mv nil msg-or-val bindings state)))))

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
; function names occuring in the :exec part of an mbe.  Keep this in sync with
; all-fnnames1-exec.

  (cond (flg ; x is a list of terms
         (cond ((null x) acc)
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
                      (program-termp val w))
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

(defun translate (x stobjs-out logic-modep known-stobjs ctx w state)

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

  (cmp-to-error-triple
   (translate-cmp x stobjs-out logic-modep known-stobjs ctx w
                  (default-state-vars t))))

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
    (packn (list "REPLACED-" name))))

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

; Setting: A form has been evaluated, producing a state with alist1 as
; its user-stobj-alist.  The evaluation also produced some latches,
; which are alist2.  We wish to merge the latches into the
; user-stobj-alist of the state and this is the workhorse.  We know
; that the form returns at least one user stobj (and so, we know the
; form is not a DEFSTOBJ or its undo or redo).  Given this knowledge,
; we wish to store the new stobjs in latches back into the
; user-stobj-alist.

; Spec for this function: Both arguments are duplicate-free symbol
; alists.  For every (key . val) in alist2 we a put-assoc-eq of key
; and val into alist1.

  (cond ((endp alist2) alist1)

; The following clause is an optimization.  If alist1 and alist2 are
; equal and we continued as though this clause weren't here, then we
; would store each (key . val) pair of alist2 into an already
; identical pair of alist1, affecting no change of alist1.  So we can
; stop and return alist1 now.  (Note that if the two alists contained
; duplicate keys, this would not be an optimization: alist1 = alist2 =
; '((a . 1) (a . 2)) would yeild '((a . 1) (a . 2)) with this
; optimization in place but would yeild '((a . 2) (a . 2)) without
; this optimization.)  This optimization increases the efficiency of
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
            has been bound by with-local-stobj.  The reason is that those ~
            evaluators expect each stobj to match perfectly the corresponding ~
            global stobj that is stored in the ACL2 state.  The offending ~
            stobj name~#0~[ is~/s are~]:  ~&0."
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

(defun ev-for-trans-eval (trans vars stobjs-out ctx state aok)

; Trans is a translated term with the indicated stobjs-out, and vars is
; (all-vars term).  We return the result of evaluating trans as an error
; triple with possibly updated state, as described in trans-eval.

; This function is called by trans-eval, and is a suitable alternative to
; trans-eval when the term to be evaluated has already been translated by
; translate1 with stobjs-out = :stobjs-out.

  (let ((alist (cons (cons 'state 
                           (coerce-state-to-object state))
                     (user-stobj-alist-safe 'trans-eval vars state))))
    (mv-let
     (erp val latches)
     (ev trans alist state alist nil aok)

; The first state binding below is the state produced by the
; evaluation of the form.  The second state is the first, but with the
; user-stobj-alist of that state (possibly) updated to contain the
; modified latches.  Note that we don't bother to modify the
; user-stobj-alist if the form's output signature does not involve a
; user-defined stobj.  The particular forms we have in mind for this
; case are DEFSTOBJ forms and their ``undoers'' and ``re-doers''.
; They compute the state they mean and we shouldn't mess with the
; user-stobj-alist of their results, else we risk overturning
; carefully computed answers by restoring old stobjs.

     (let ((state
            (coerce-object-to-state (cdr (car latches)))))
       (let ((state
              (cond
               ((user-stobjsp stobjs-out)
                (update-user-stobj-alist
                 (put-assoc-eq-alist (user-stobj-alist state)
                                     (cdr latches))
                 state))
               (t state))))
         (cond
          (erp

; If ev caused an error, then val is a pair (str . alist) explaining
; the error.  We will process it here (as we have already processed the
; translate errors that might have arisen) so that all the errors that
; might be caused by this translation and evaluation are handled within
; this function.

           (error1 ctx (car val) (cdr val) state))
          (t (mv nil
                 (cons stobjs-out
                       (replace-stobjs stobjs-out val))
                 state))))))))

(defun trans-eval (form ctx state aok)

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

  (mv-let
   (erp trans bindings state)
   (translate1 form
               :stobjs-out '((:stobjs-out . :stobjs-out))
               t
               'top-level (w state) state)

; known-stobjs = t.  We expect trans-eval to be used only when the
; user is granted full access to the stobjs in state.  Of course, some
; applications of trans-eval, e.g., in eval-event-lst, first check
; that the form doesn't access stobjs or state.

   (cond
    (erp (mv t nil state))
    (t
     (let ((stobjs-out (translate-deref :stobjs-out bindings))
           (vars (all-vars trans)))
       (cond
        ((non-stobjps vars t (w state)) ;;; known-stobjs = t
         (er soft 'top-level
             "Global variables, such as ~&0, are not allowed. See ~
              :DOC ASSIGN and :DOC @."
             (non-stobjps vars t (w state)))) ;;; known-stobjs = t
        (t (ev-for-trans-eval trans vars stobjs-out ctx state aok))))))))

(defun simple-translate-and-eval (x alist ok-stobj-names msg ctx wrld state
                                    aok)

; A Note on the Reason this Function Exists:

; This function is a cousin of trans-eval that is much easier to use
; in simple cases.  Trans-eval can handle any well-formed term.  Thus,
; it must have a way to communicate to the caller how many results are
; being returned and what they are.  The obvious thing for trans-eval
; to do is to list the results.  But if one of them is STATE or some
; other stobj, it cannot.  So trans-eval has a rather complicated
; interface that permits the caller to determine the mulitplicity of
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
                        vars))
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
                              (cond
                               (erp (pprogn
                                     (error-fms nil ctx (car val) (cdr val)
                                                state)
                                     (er soft ctx
                                         "~@0 could not be evaluated."
                                         msg)))
                               (t (value (cons term val))))))))))

(defun tilde-*-alist-phrase1 (alist evisc-tuple level)
  (cond ((null alist) nil)
        (t (cons (msg "~t0~s1 : ~Y23~|" level (caar alist) (cdar alist) evisc-tuple)
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
; to translate.  Futhermore, proving interesting theorems about these
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
