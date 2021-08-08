; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
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

; When we are ready to verify termination in this and later files, we should
; consider changing null to endp in a number of functions.

(in-package "ACL2")

(defun enforce-redundancy-er-args (event-form-var wrld-var)
  (list "Enforce-redundancy is active; see :DOC set-enforce-redundancy and ~
         see :DOC redundant-events.  However, the following event ~@0:~|~%~x1"
        `(if (and (symbolp (cadr ,event-form-var))
                  (decode-logical-name (cadr ,event-form-var) ,wrld-var))
             "conflicts with an existing event of the same name"
           "is not redundant")
        event-form-var))

(defmacro enforce-redundancy (event-form ctx wrld form)
  (let ((var 'redun-check-var))
    `(let ((,var (and (not (eq (ld-skip-proofsp state)
                               'include-book))
                      (cdr (assoc-eq :enforce-redundancy
                                     (table-alist 'acl2-defaults-table
                                                  ,wrld))))))
       (cond ((eq ,var t)
              (check-vars-not-free
               (,var)
               (er soft ,ctx
                   ,@(enforce-redundancy-er-args
                      event-form wrld))))
             (t (pprogn (cond (,var (check-vars-not-free
                                     (,var)
                                     (warning$ ,ctx "Enforce-redundancy"
                                               ,@(enforce-redundancy-er-args
                                                  event-form wrld))))
                              (t state))
                        (check-vars-not-free
                         (,var)
                         ,form)))))))

(defun global-set (var val wrld)
  (declare (xargs :guard (and (symbolp var)
                              (plist-worldp wrld))))
  (putprop var 'global-value val wrld))

(defun tilde-@-illegal-variable-or-constant-name-phrase (name)

; Assume that legal-variable-or-constant-namep has failed on name.
; We return a phrase that when printed with ~@0 will complete the
; sentence "Variable names must ...".  Observe that the sentence
; could be "Constant names must ...".

  (cond ((not (symbolp name)) "be symbols")
        ((keywordp name) "not be in the KEYWORD package")
        ((and (legal-constantp1 name)
              (equal (symbol-package-name name) *main-lisp-package-name*))
         (cons "not be in the main Lisp package, ~x0"
               (list (cons #\0 *main-lisp-package-name*))))
        ((and (> (length (symbol-name name)) 0)
              (eql (char (symbol-name name) 0) #\&))
         "not start with ampersands")
        ((and (not (legal-constantp1 name))
              (member-eq name *common-lisp-specials-and-constants*))
         "not be among certain symbols from the main Lisp package, namely, the ~
          value of the list *common-lisp-specials-and-constants*")
        ((and (not (legal-constantp1 name))
              (equal (symbol-package-name name) *main-lisp-package-name*)
              (not (member-eq name *common-lisp-symbols-from-main-lisp-package*)))
         "either not be in the main Lisp package, or else must be among the ~
          imports into ACL2 from that package, namely, the list ~
          *common-lisp-symbols-from-main-lisp-package*")
        (t "be approved by LEGAL-VARIABLE-OR-CONSTANT-NAMEP and this ~
            one wasn't, even though it passes all the checks known to ~
            the diagnostic function ~
            TILDE-@-ILLEGAL-VARIABLE-OR-CONSTANT-NAME-PHRASE")))

(defun legal-constantp (name)

; A name may be declared as a constant if it has the syntax of a
; variable or constant (see legal-variable-or-constant-namep) and
; starts and ends with a *.

; WARNING: Do not confuse this function with defined-constant.

  (eq (legal-variable-or-constant-namep name) 'constant))

(defun genvar1 (pkg-witness char-lst avoid-lst cnt)

; This function generates a symbol in the same package as the symbol
; pkg-witness that is guaranteed to be a legal-variablep and not in avoid-lst.
; We form a symbol by concatenating char-lst and the decimal representation of
; the natural number cnt.  Observe the guard below.  Since guards are not
; checked in :program code, the user must ensure upon calling this
; function that pkg-witness is a symbol in some package other than the main
; lisp package or the keyword package and that char-lst is a list of characters
; not beginning with * or &.  Given that guard, there must exist a sufficiently
; large cnt to make our generated symbol be in the package of pkg-witness (a
; finite number of generated symbols might have been interned in one of the
; non-variable packages).

  (declare (xargs :guard (and (let ((p (symbol-package-name pkg-witness)))
                                (and (not (equal p "KEYWORD"))
                                     (not (equal p *main-lisp-package-name*))))
                              (consp char-lst)
                              (not (eql (car char-lst) #\*))
                              (not (eql (car char-lst) #\&)))))
  (let ((sym (intern-in-package-of-symbol
              (coerce
               (append char-lst
                       (explode-nonnegative-integer cnt 10 nil))
               'string)
              pkg-witness)))
    (cond ((or (member sym avoid-lst)

; The following call of legal-variablep could soundly be replaced by
; legal-variable-or-constant-namep, given the guard above, but we keep it
; as is for robustness.

               (not (legal-variablep sym)))
           (genvar1 pkg-witness char-lst avoid-lst (1+ cnt)))
          (t sym))))

(defun genvar (pkg-witness prefix n avoid-lst)

; This is THE function that ACL2 uses to generate new variable names.
; Prefix is a string and n is either nil or a natural number.  Together we
; call prefix and n the "root" of the variable we generate.

; We generate from prefix a legal variable symbol in the same package as
; pkg-witness that does not occur in avoid-lst.  If n is nil, we first try the
; symbol with symbol-name prefix first and otherwise suffix prefix with
; increasingly large naturals (starting from 0) to find a suitable variable.
; If n is non-nil it had better be a natural and we immediately begin trying
; suffixes from there.  Since no legal variable begins with #\* or #\&, we tack
; a #\V on the front of our prefix if prefix starts with one of those chars.
; If prefix is empty, we use "V".

; Note: This system will eventually contain a lot of code to generate
; "suggestive" variable names.  However, we make the convention that
; in the end every variable name generated is generated by this
; function.  Thus, all other code associated with variable name
; generation is heuristic if this one is correct.

  (let* ((pkg-witness (cond ((let ((p (symbol-package-name pkg-witness)))
                               (or (equal p "KEYWORD")
                                   (equal p *main-lisp-package-name*)))
; If pkg-witness is in an inappropriate package, we default it to the
; "ACL2" package.
                             'genvar)
                            (t pkg-witness)))
         (sym (if (null n) (intern-in-package-of-symbol prefix pkg-witness) nil))
         (cnt (if n n 0)))
    (cond ((and (null n)
                (legal-variablep sym)
                (not (member sym avoid-lst)))
           sym)
          (t (let ((prefix (coerce prefix 'list)))
               (cond ((null prefix) (genvar1 pkg-witness '(#\V) avoid-lst cnt))
                     ((and (consp prefix)
                           (or (eql (car prefix) #\*)
                               (eql (car prefix) #\&)))
                      (genvar1 pkg-witness (cons #\V prefix) avoid-lst cnt))
                     (t (genvar1 pkg-witness prefix avoid-lst cnt))))))))

(defun gen-formals-from-pretty-flags1 (pretty-flags i avoid)
  (cond ((endp pretty-flags) nil)
        ((and (symbolp (car pretty-flags))
              (equal (symbol-name (car pretty-flags)) "*"))
         (let ((xi (pack2 'x i)))
           (cond ((member-eq xi avoid)
                  (let ((new-var (genvar 'genvar ;;; ACL2 package
                                         "GENSYM"
                                         1
                                         avoid)))
                    (cons new-var
                          (gen-formals-from-pretty-flags1
                           (cdr pretty-flags)
                           (+ i 1)
                           (cons new-var avoid)))))
                 (t (cons xi
                          (gen-formals-from-pretty-flags1
                           (cdr pretty-flags)
                           (+ i 1)
                           avoid))))))
        (t (cons (car pretty-flags)
                 (gen-formals-from-pretty-flags1
                  (cdr pretty-flags)
                  (+ i 1)
                  avoid)))))

(defun gen-formals-from-pretty-flags (pretty-flags)

; Given a list of prettyified stobj flags, e.g., '(* * $S * STATE) we generate
; a proposed list of formals, e.g., '(X1 X2 $S X4 STATE).  We guarantee that
; the result is a list of symbols of the same length as pretty-flags.
; Furthermore, a non-* in pretty-flags is preserved in the same slot in the
; output.  Furthermore, the symbol generated for each * in pretty-flags is
; unique and not among the symbols in pretty-flags.  Finally, STATE is not
; among the symbols we generate.

  (gen-formals-from-pretty-flags1 pretty-flags 1 pretty-flags))

(defun collect-non-x (x lst)

; This function preserves possible duplications of non-x elements in lst.
; We use this fact when we check the legality of signatures.

  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((equal (car lst) x)
         (collect-non-x x (cdr lst)))
        (t (cons (car lst) (collect-non-x x (cdr lst))))))

(defun collect-non-* (lst)

; This variant of collect-symbol-name considers any symbol with name "*",
; regardless of the package.

  (declare (xargs :guard (symbol-listp lst)))
  (cond ((endp lst) nil)
        ((equal (symbol-name (car lst)) "*")
         (collect-non-* (cdr lst)))
        (t (cons (car lst) (collect-non-* (cdr lst))))))

(defun defstub-body-new (outputs)

; Turn the output part of a new-style signature into a term.  This is called to
; construct the body of the witness function that defstub passes to
; encapsulate, when the new style is used in defstub (otherwise,
; defstub-body-old is called).  This function never causes an error, even if
; outputs is ill-formed; what it returns in that case is irrelevant.  If
; outputs is well-formed, it converts each * to nil and every other symbol to
; itself, e.g., it converts (mv * s *) to (mv nil s nil), * to nil, and state
; to state.

  (cond ((atom outputs)
         (cond ((and (symbolp outputs)
                     (equal (symbol-name outputs) "*"))
                nil)
               (t outputs)))
        ((and (symbolp (car outputs))
              (equal (symbol-name (car outputs)) "*"))
         (cons nil (defstub-body-new (cdr outputs))))
        (t (cons (car outputs) (defstub-body-new (cdr outputs))))))

#+acl2-loop-only
(defmacro defproxy (name args-sig arrow body-sig)
  (cond
   ((not (and (symbol-listp args-sig)
              (symbolp arrow)
              (equal (symbol-name arrow) "=>")))
    (er hard 'defproxy
        "Defproxy must be of the form (proxy name args-sig => body-sig), ~
         where args-sig is a true-list of symbols.  See :DOC defproxy."))
   (t
    (let ((formals (gen-formals-from-pretty-flags args-sig))
          (body (defstub-body-new body-sig))
          (stobjs (collect-non-* args-sig)))
      `(defun ,name ,formals
         (declare (xargs :non-executable :program
                         :mode :program
                         ,@(and stobjs `(:stobjs ,stobjs)))
                  (ignorable ,@formals))

; The form of the body below is dictated by function throw-nonexec-error-p.
; Notice that we do not pass the formals to throw-nonexec-error as we do in
; defun-nx-fn, because if the formals contain a stobj then we would violate
; stobj restrictions, which are checked for non-executable :program mode
; functions.

         (prog2$ (throw-nonexec-error ',name nil)
                 ,body))))))

#-acl2-loop-only
(defmacro defproxy (name args-sig arrow body-sig)

; Note that a defproxy redefined using encapsulate can generate a warning in
; CLISP (see comment about CLISP in with-redefinition-suppressed), because
; indeed there are two definitions being made for the same name.  However, the
; definition generated for a function by encapsulate depends only on the
; function's signature, up to renaming of formals; see the #-acl2-loop-only
; definition of encapsulate.  So this redefinition is as benign as the
; redefinition that occurs in raw Lisp with a redundant defun.

  `(defstub ,name ,args-sig ,arrow ,body-sig))

; We now use encapsulate to implement defstub.  It is handy to do so here,
; rather than in other-events.lisp, since the raw Lisp definition of defproxy
; uses defstub.

(defun defstub-ignores (formals body)

; The test below is sufficient to ensure that the set-difference-equal
; used to compute the ignored vars will not cause an error.  We return
; a true list.  The formals and body will be checked thoroughly by the
; encapsulate, provided we generate it!  Provided they check out, the
; result returned is the list of ignored formals.

  (if (and (symbol-listp formals)
           (or (symbolp body)
               (and (consp body)
                    (symbol-listp (cdr body)))))
      (set-difference-equal
       formals
       (if (symbolp body)
           (list body)
         (cdr body)))
    nil))

(defun defstub-body-old-aux (outputs-without-mv stobjs)

; Helper of defstub-body-old; see that function.  This function processes the
; elements after mv.

  (declare (xargs :guard (symbol-listp stobjs)))
  (cond ((atom outputs-without-mv) nil)
        ((member-eq (car outputs-without-mv) stobjs)
         (cons (car outputs-without-mv)
               (defstub-body-old-aux (cdr outputs-without-mv) stobjs)))
        (t (cons nil ; could probably use t instead
                 (defstub-body-old-aux (cdr outputs-without-mv) stobjs)))))

(defun defstub-body-old (outputs stobjs)

; Turn the output part of an old-style signature into a term.  This is called
; to construct the body of the witness function that defstub passes to the
; encapsulate, when the old style is used in defstub (otherwise,
; defstub-body-new is called).  This function never causes an error, even if
; outputs is ill-formed; what it returns in that case is irrelevant.  If
; outputs is well-formed, it converts each non-stobj name to nil and each stobj
; name to itself, e.g., it converts (mv x s y) to (mv nil s nil), x to nil, and
; state to state.  Since stobjs other than state are not as evident in the old
; style as in the new style, the user-specified stobjs (as well as state, if
; present) are passed as an extra argument to this function; these stobjs are
; collected as explained in the comments in defstub-fn.

  (declare (xargs :guard (symbol-listp stobjs)))
  (cond ((atom outputs)
         (cond ((member-eq outputs stobjs) outputs)
               (t nil)))
        (t (cons (car outputs) (defstub-body-old-aux (cdr outputs) stobjs)))))

(defun defstub-fn1 (signatures name formals ign-dcl stobjs body outputs)
  `(with-output
     :off (:other-than error summary)
     :ctx '(defstub . ,name)
     :summary-off value
     (encapsulate
       ,signatures
       (with-output :off summary
         (logic))
       (with-output
         :summary-off (:other-than redundant)
         (local
          (defun ,name ,formals
            (declare ,ign-dcl
                     ,@(and stobjs `((xargs :stobjs ,stobjs))))
            ,body)))
       ,@(and (consp outputs)

; Note that if (car outputs) is not MV, then the signature will be illegal in
; the generated encapsulate below, so the user will see an error message that
; should be adequate.

              `((with-output :off summary
                  (defthm ,(packn-pos (list "TRUE-LISTP-" name)
                                      name)
                    (true-listp (,name ,@formals))
                    :rule-classes :type-prescription)))))))

(defun defstub-fn (name args)

; We cannot just "forward" the arguments of defstub to encapsulate and have
; encapsulate validate them, for two reasons.  First, the new-style syntax
; differs slightly in the two macros (e.g. (defstub f (*) => *) vs.
; (encapsulate (((f *) => *)) ...)) while the old-style syntax is the same
; (e.g. (defstub f (x) t) vs. (encapsulate ((f (x) t)) ...)), making it
; necessary to distinguish new style from old style to adapt slightly the
; syntax in the new style prior to passing the arguments to encapsulate.
; Second, the witness to pass to the encapsulate is constructed differently
; depending on whether the style is new or old.

; Here we are content to perform only a few validation checks, which at least
; suffice to let us pass the right data to encapsulate, which performs all
; remaining validation checks.

; In both styles, there must be at least two arguments following the name.  If
; this condition fails, it would not be clear what to pass to encapsulate.

  (let ((len-args (length args)))
    (cond
     ((not (and name (symbolp name)))
      `(er soft '(defstub . ,name)
           "The first argument of defstub must be a non-nil symbol.  The form ~
            ~x0 is thus illegal."
           '(defstub ,name ,@args)))
     ((< len-args 2)
      `(er soft '(defstub . ,name)
           "Defstub must be of the form (defstub name inputs => outputs ...) ~
            or (defstub name inputs outputs ...).  See :DOC defstub."))

; New and old style cannot be told apart just from the first argument after the
; name, which for example could be (state) in both styles.  New and old styles
; cannot be told apart just from the second argument after the name either,
; because for example (defstub f (x) =>) is valid in the old style, where => is
; (oddly) used as output variable.  We need to look past the second argument
; after the name: if there is no third argument, we must be in the old style,
; because the new style requires inputs, arrow, and outputs; if the third
; argument is a keyword, we must be in the old style, because the output part
; of the new style cannot be a keyword; if the third argument is not a keyword,
; we must be in the new style instead.

; We handle the old style first.

     ((or (= len-args 2)
          (keywordp (caddr args)))

; We keep the same syntax for the signature, including any options.  We use the
; inputs as the formals of the witness function.  If there is a :stobjs option
; (which may be a single stobj name or a list thereof) or the inputs include
; state, we declare the stobjs in the witness function (note that state may or
; may not be explicitly declared in the stobjs option of defstub).  If there
; are multiple outputs, we also generate an exported type prescription theorem
; saying that the function returns a true list.  The code below includes some
; checks on the arguments of defstub to ensure the absence of run-time errors
; (e.g. the options are checked to satisfy keyword-value-listp before calling
; assoc-keyword on them).

      (let* ((inputs (car args))
             (outputs (cadr args))
             (options (cddr args))
             (stobjs (and (keyword-value-listp options) ; assoc-keyword guard
                          (cadr (assoc-keyword :stobjs options))))
             (stobjs (cond ((symbol-listp stobjs) stobjs) ; covers nil case
                           ((symbolp stobjs) (list stobjs))
                           (t nil))) ; malformed :stobjs option
; Stobjs is a symbol-listp at this point.
             (stobjs (cond ((and (true-listp inputs) ; member-equal guard
                                 (member-eq 'state inputs))
                            (add-to-set-eq 'state stobjs))
                           (t stobjs)))

; If stobjs is ill-formed in any of the bindings above, then the signature will
; be illegal in the generated encapsulate, in which case the value of stobjs is
; irrelevant.

             (body (defstub-body-old outputs stobjs)))
        (defstub-fn1
          `((,name ,@args)) ; args includes inputs, outputs, and options
          name inputs
          `(ignorable ,@inputs)
          stobjs body outputs)))

; In the new style, we adapt the syntax of the signature, keeping all the
; options.  We derive the formals of the witness function by replacing the *s
; in the signature with distinct symbols.  We derive the stobjs of the witness
; function from the inputs of the signature, by collecting all the non-*s.  If
; there are multiple outputs, we also generate an exported type prescription
; theorem saying that the function returns a true list.  The code below
; includes some checks on the arguments of defstub to ensure the absence of
; run-time errors (e.g., the inputs are checked to satisfy symbol-listp before
; calling gen-formals-from-pretty-flags).

     (t (let* ((inputs (car args))
               (arrow

; We do not check here that arrow is a symbol with name "=>", as that check
; will be made when the signature is checked in the generated encapsulate.

                (cadr args))
               (outputs (caddr args))
               (options (cdddr args))
               (formals (and (symbol-listp inputs)

; Note that if inputs is not a symbol-listp, then the value of formals will be
; ignored because the generated encapsulate will immediately report a signature
; violation.

                             (gen-formals-from-pretty-flags inputs)))
               (body (defstub-body-new outputs))
               (ignores (defstub-ignores formals body))
               (stobjs (and (true-listp inputs) ; collect-non-x guard
                            (collect-non-* inputs))))
          (defstub-fn1
            `(((,name ,@inputs) ,arrow ,outputs ,@options))
            name formals `(ignore ,@ignores) stobjs body outputs))))))

(defmacro defstub (name &rest args)
  (defstub-fn name args))

;; Historical Comment from Ruben Gamboa:
;; I changed the primitive guard for the < function, and the
;; complex function.  Added the functions complexp, realp, and floor1.

;; Historical Comment from Ruben Gamboa:
;; I subsequently changed this to add the non-standard functions
;; standardp, standard-part and i-large-integer.  I had some
;; questions as to whether these functions should appear on this list
;; or not.  After considering carefully, I decided that was the right
;; course of action.  In addition to adding them to the list below, I
;; also add them to *non-standard-primitives* which is a special list
;; of non-standard primitives.  Functions in this list are considered
;; to be constrained.  Moreover, they are given the value t for the
;; property 'unsafe-induction so that recursion and induction are
;; turned off for terms built from these functions.

(defconst *primitive-formals-and-guards*

; Keep this in sync with ev-fncall-rec-logical and type-set-primitive, and with
; the documentation and "-completion" axioms of the primitives.  Also be sure
; to define a *1* function for each function in this list that is not a member
; of *oneify-primitives*.

; WARNING: for each primitive below, primordial-world puts a 'stobjs-in that is
; a list of nils of the same length as its formals, and a 'stobjs-out of
; '(nil).  Revisit that code if you add a primitive that involves stobjs!

; WARNING:  Just below you will find another list, *primitive-monadic-booleans*
; that lists the function names from this list that are monadic booleans.  The
; names must appear in the same order as here!

  '((acl2-numberp (x) 't)
    (bad-atom<= (x y) (if (bad-atom x) (bad-atom y) 'nil))
    (binary-* (x y) (if (acl2-numberp x) (acl2-numberp y) 'nil))
    (binary-+ (x y) (if (acl2-numberp x) (acl2-numberp y) 'nil))
    (unary-- (x) (acl2-numberp x))
    (unary-/ (x) (if (acl2-numberp x) (not (equal x '0)) 'nil))
    (< (x y)

; We avoid the temptation to use real/rationalp below, since it is a macro.

       (if #+:non-standard-analysis (realp x)
           #-:non-standard-analysis (rationalp x)
         #+:non-standard-analysis (realp y)
         #-:non-standard-analysis (rationalp y)
         'nil))
    (car (x) (if (consp x) 't (equal x 'nil)))
    (cdr (x) (if (consp x) 't (equal x 'nil)))
    (char-code (x) (characterp x))
    (characterp (x) 't)
    (code-char (x) (if (integerp x) (if (< x '0) 'nil (< x '256)) 'nil))
    (complex (x y)
             (if #+:non-standard-analysis (realp x)
                 #-:non-standard-analysis (rationalp x)
               #+:non-standard-analysis (realp y)
               #-:non-standard-analysis (rationalp y)
               'nil))
    (complex-rationalp (x) 't)
    #+:non-standard-analysis
    (complexp (x) 't)
    (coerce (x y)
            (if (equal y 'list)
                (stringp x)
                (if (equal y 'string)
                    (character-listp x)
                    'nil)))
    (cons (x y) 't)
    (consp (x) 't)
    (denominator (x) (rationalp x))
    (equal (x y) 't)
    #+:non-standard-analysis
    (floor1 (x) (realp x))
    (if (x y z) 't)
    (imagpart (x) (acl2-numberp x))
    (integerp (x) 't)
    (intern-in-package-of-symbol (str sym) (if (stringp str) (symbolp sym) 'nil))
    (numerator (x) (rationalp x))
    (pkg-imports (pkg) (stringp pkg))
    (pkg-witness (pkg) (if (stringp pkg) (not (equal pkg '"")) 'nil))
    (rationalp (x) 't)
    #+:non-standard-analysis
    (realp (x) 't)
    (realpart (x) (acl2-numberp x))
    (stringp (x) 't)
    (symbol-name (x) (symbolp x))
    (symbol-package-name (x) (symbolp x))
    (symbolp (x) 't)
    #+:non-standard-analysis
    (standardp (x) 't)
    #+:non-standard-analysis
    (standard-part (x) ; If (x) is changed here, change cons-term1-cases.
                   (acl2-numberp x))
    #+:non-standard-analysis
    (i-large-integer () 't)))

(defconst *primitive-monadic-booleans*

; This is the list of primitive monadic boolean function symbols.  Each
; function must be listed in *primitive-formals-and-guards* and they should
; appear in the same order.  (The reason order matters is simply to make it
; easier to check at the end of boot-strap that we have included all the
; monadic booleans.)

  '(acl2-numberp
    characterp
    complex-rationalp
    #+:non-standard-analysis
    complexp
    consp
    integerp
    rationalp
    #+:non-standard-analysis
    realp
    stringp
    symbolp
    #+:non-standard-analysis
    standardp))

#+:non-standard-analysis
(defconst *non-standard-primitives*
  '(standardp
    standard-part
    i-large-integer))

(defun cons-term1-cases (alist)

; Initially, alist is *primitive-formals-and-guards*.

  (cond ((endp alist) nil)
        ((member-eq (caar alist)
                    '(if ; IF is handled directly in cons-term1-body.
                         bad-atom<= pkg-imports pkg-witness))
         (cons-term1-cases (cdr alist)))
        (t (cons (let* ((trip (car alist))
                        (fn (car trip))
                        (formals (cadr trip))
                        (guard (caddr trip)))
                   (list
                    fn
                    (cond #+:non-standard-analysis
                          ((eq fn 'i-large-integer)
                           nil) ; fall through in cons-term1-body
                          #+:non-standard-analysis
                          ((eq fn 'standardp)
                           '(kwote t))
                          #+:non-standard-analysis
                          ((eq fn 'standard-part)
                           (assert$
                            (eq (car formals) 'x)
                            `(and ,guard ; a term in variable x
                                  (kwote ,@formals))))
                          ((equal guard *t*)
                           `(kwote (,fn ,@formals)))
                          ((or (equal formals '(x))
                               (equal formals '(x y)))
                           `(and ,guard
                                 (kwote (,fn ,@formals))))
                          (t (case-match formals
                               ((f1)
                                `(let ((,f1 x))
                                   (and ,guard
                                        (kwote (,fn ,@formals)))))
                               ((f1 f2)
                                `(let ((,f1 x)
                                       (,f2 y))
                                   (and ,guard
                                        (kwote (,fn ,@formals)))))
                               (& (er hard! 'cons-term1-cases
                                      "Unexpected formals, ~x0"
                                      formals)))))))
                 (cons-term1-cases (cdr alist))))))

(defconst *cons-term1-alist*
  (cons-term1-cases *primitive-formals-and-guards*))

(defmacro cons-term1-body ()
  `(let ((x (unquote (car args)))
         (y (unquote (cadr args))))
     (or (case fn
           ,@*cons-term1-alist*
           (if (kwote (if x y (unquote (caddr args)))))
           (not (kwote (not x))))
         (cons fn args))))

(defun quote-listp (l)
  (declare (xargs :guard (true-listp l)))
  (cond ((null l) t)
        (t (and (quotep (car l))
                (quote-listp (cdr l))))))

(defun cons-term1 (fn args)
  (declare (xargs :guard (and (pseudo-term-listp args)
                              (quote-listp args))))
  (cons-term1-body))

(defun cons-term (fn args)
  (declare (xargs :guard (pseudo-term-listp args)))
  (cond ((quote-listp args)
         (cons-term1 fn args))
        (t (cons fn args))))

(defmacro cons-term* (fn &rest args)
  `(cons-term ,fn (list ,@args)))

(defmacro mcons-term (fn args)

; The "m" in "mcons-term" is for "maybe fast".  Some calls of this macro can
; probably be replaced with fcons-term.

  `(cons-term ,fn ,args))

(defmacro mcons-term* (fn &rest args)

; The "m" in "mcons-term*" is for "maybe fast".  Some of calls of this macro
; can probably be replaced with fcons-term*.

  `(cons-term* ,fn ,@args))

(defmacro fcons-term (fn args)

; ; Start experimental code mod, to check that calls of fcons-term are legitimate
; ; shortcuts in place of the corresponding known-correct calls of cons-term.
;   #-acl2-loop-only
;   `(let* ((fn-used-only-in-fcons-term ,fn)
;           (args-used-only-in-fcons-term ,args)
;           (result (cons fn-used-only-in-fcons-term
;                         args-used-only-in-fcons-term)))
;      (assert$ (equal result (cons-term fn-used-only-in-fcons-term
;                                        args-used-only-in-fcons-term))
;               result))
;   #+acl2-loop-only
; ; End experimental code mod.

  (list 'cons fn args))

(defun cdr-nest (n v)
  (cond ((equal n 0) v)
        (t (fargn1 v n))))

(defun stobj-print-name (name)
  (coerce
   (cons #\<
         (append (string-downcase1 (coerce (symbol-name name) 'list))
                 '(#\>)))
   'string))

(defun evisceration-stobj-mark (name inputp)

; NAME is a stobj name.  We return an evisceration mark that prints as
; ``<name>''.  We make a special case out of STATE.

  (cond
   (inputp name)
   ((eq name 'STATE)
    *evisceration-state-mark*)
   (t
    (cons *evisceration-mark* (stobj-print-name name)))))

(defun evisceration-stobj-marks1 (stobjs-flags inputp)

; See the comment in eviscerate-stobjs, below.

  (cond ((null stobjs-flags) nil)
        ((car stobjs-flags)
         (cons (evisceration-stobj-mark (car stobjs-flags) inputp)
               (evisceration-stobj-marks1 (cdr stobjs-flags) inputp)))
        (t
         (cons nil
               (evisceration-stobj-marks1 (cdr stobjs-flags) inputp)))))

(defconst *error-triple-sig*
  '(nil nil state))

(defconst *cmp-sig*
  '(nil nil))

(defun evisceration-stobj-marks (stobjs-flags inputp)
  (cond ((equal stobjs-flags *error-triple-sig*)
         (if inputp
             *error-triple-sig*
           *evisceration-error-triple-marks*))
        ((equal stobjs-flags '(nil)) '(nil))
        (t (evisceration-stobj-marks1 stobjs-flags inputp))))

(defun eviscerate-stobjs1 (estobjs-out lst print-level print-length
                                       alist evisc-table hiding-cars
                                       iprint-alist
                                       iprint-fal-new iprint-fal-old eager-p)
  (cond
   ((null estobjs-out) (mv nil iprint-alist iprint-fal-new))
   ((car estobjs-out)
    (mv-let (rest iprint-alist iprint-fal-new)
      (eviscerate-stobjs1 (cdr estobjs-out) (cdr lst)
                          print-level print-length
                          alist evisc-table hiding-cars
                          iprint-alist iprint-fal-new iprint-fal-old eager-p)
      (mv (cons (car estobjs-out) rest)
          iprint-alist
          iprint-fal-new)))
   (t (mv-let (first iprint-alist iprint-fal-new)
        (eviscerate (car lst) print-level print-length
                    alist evisc-table hiding-cars iprint-alist
                    iprint-fal-new iprint-fal-old eager-p)
        (mv-let (rest iprint-alist iprint-fal-new)
          (eviscerate-stobjs1 (cdr estobjs-out) (cdr lst)
                              print-level print-length alist
                              evisc-table hiding-cars iprint-alist
                              iprint-fal-new iprint-fal-old eager-p)
          (mv (cons first rest) iprint-alist iprint-fal-new))))))

(defun eviscerate-stobjs (estobjs-out lst print-level print-length
                                      alist evisc-table hiding-cars
                                      iprint-alist iprint-fal-old eager-p)

; See also eviscerate-stobjs-top, which takes iprint-ar from the state and
; installs a new iprint-ar in the state.

; Warning: Right now, we abbreviate all stobjs with the <name> convention.  I
; have toyed with the idea of allowing the user to specify how a stobj is to be
; abbreviated on output.  This is awkward.  See the Essay on Abbreviating Live
; Stobjs below.

; We wish to eviscerate lst with the given print-level, etc., but respecting
; stobjs that we may find in lst.  Estobjs-out describes the shape of lst as a
; multiple value vector: if estobjs-out is of length 1, then lst is the single
; result; otherwise, lst is a list of as many elements as estobjs-out is long.
; The non-nil elements of stobjs name the stobjs in lst -- EXCEPT that unlike
; an ordinary ``stobjs-out'', the elements of estobjs-out are evisceration
; marks we are to ``print!''  For example corresponding to the stobjs-out
; setting of '(NIL $MY-STOBJ NIL STATE) is the estobjs-out

; '(NIL
;   (:EVISCERATION-MARK . "<$my-stobj>")
;   NIL
;   (:EVISCERATION-MARK . "<state>"))

; Here, we assume *evisceration-mark* is :EVISCERATION-MARK.

  (cond
   ((null estobjs-out)

; Lst is either a single non-stobj output or a list of n non-stobj outputs.  We
; eviscerate it without regard for stobjs.

    (eviscerate lst print-level print-length alist evisc-table hiding-cars
                iprint-alist nil iprint-fal-old eager-p))
   ((null (cdr estobjs-out))

; Lst is a single output, which is either a stobj or not depending on whether
; (car stobjs-out) is non-nil.

    (cond
     ((car estobjs-out)
      (mv (car estobjs-out) iprint-alist nil))
     (t (eviscerate lst print-level print-length alist evisc-table
                    hiding-cars iprint-alist nil iprint-fal-old eager-p))))
   (t (eviscerate-stobjs1 estobjs-out lst print-level print-length
                          alist evisc-table hiding-cars iprint-alist
                          nil iprint-fal-old eager-p))))

(defun eviscerate-stobjs-top (estobjs-out lst print-level print-length
                                          alist evisc-table hiding-cars
                                          state)

; See eviscerate-stobjs.

  (let ((iprint-fal-old (f-get-global 'iprint-fal state)))
    (mv-let (result iprint-alist iprint-fal-new)
      (eviscerate-stobjs estobjs-out lst print-level print-length alist
                         evisc-table hiding-cars
                         (and (iprint-enabledp state)
                              (iprint-last-index state))
                         iprint-fal-old
                         (iprint-eager-p iprint-fal-old))
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
         (mv result state))))))

; Essay on Abbreviating Live Stobjs

; Right now the live state is abbreviated as <state> when it is printed, and
; the user's live stobj $s is abbreviated as <$s>.  It would be cool if the
; user could specify how he or she wants a stobj displayed, e.g., by selecting
; key components for printing or by providing a function which maps the stobj
; to some non-stobj ``stand-in'' or eviscerated object for printing.

; I have given this matter several hours' thought and abandoned it for the
; moment.  I am not convinced it is worth the trouble.  It IS a lot of trouble.

; We eviscerate stobjs in the read-eval-print loop.  (Through Version_4.3, we
; also eviscerated stobjs in a very low-level place: ev-fncall-msg (and its
; more pervasive friend, ev-fncall-guard-er), used to print stobjs involved in
; calls of functions on args that violate a guard.)

; Every stobj must have some ``stand-in transformer'' function, fn.  We will
; typically be holding a stobj name, e.g., $S, and a live value, val, e.g.,
; (#(777) #(1 2 3 ...)), and wish to obtain some ACL2 object to print in place
; of the value.  This value is obtained by applying fn to val.  The two main
; issues I see are

; (a) where do we find fn?  The candidate places are state, world, and val
; itself.  But we do not have state available in the low-level code.

; (b) how do we apply fn to val?  The obvious thing is to call trans-eval or do
; an ev-fncall.  Again, we need state.  Furthermore, depending on how we do it,
; we have to fight a syntactic battle of ``casting'' an arbitrary object, val,
; to a stobj of type name, to apply a function which has a STOBJS-IN of (name).
; A more important problem is the one of order-of-definition.  Which is defined
; first: how to eviscerate a stobj or how to evaluate a form?  Stobj
; evisceration calls evaluation to apply fn, but evaluation calls stobj
; evisceration to report guard errors.

; Is user-specified stobj abbreviation really worth the trouble?

; One idea that presents itself is that val ``knows how to abbreviate itself.''
; I think this is akin to the idea of having a :program mode function, say
; stobj-standin, which syntactically takes a non-stobj and returns a non-stobj.
; Actually, stobj-standin would be called on val.  It is clear that I could
; define this function in raw lisp: look in *the-live-state* to determine how
; to abbreviate val and then just do it.  But what would be the logical
; definition of it?  We could leave it undefined, or defined to be an undefined
; function.  Until we admit the whole ACL2 system :logically, we could even
; define it in the logic to be t even though it really returned something else,
; since as a :program its logical definition is irrelevant.  But at the moment
; I don't think ACL2 has a precedent for such a function and I don't think
; user-specified stobj abbreviation is justification enough for doing it.

; End of Essay on Abbreviating Live Stobjs

(defmacro flambda-applicationp (term)

; Term is assumed to be nvariablep.

  `(consp (car ,term)))

(defabbrev lambda-applicationp (term)
  (and (consp term)
       (flambda-applicationp term)))

(defmacro flambdap (fn)

; Fn is assumed to be the fn-symb of some term.

  `(consp ,fn))

(defmacro lambda-formals (x) `(cadr ,x))

(defmacro lambda-body (x) `(caddr ,x))

(defmacro make-lambda (args body)
  `(list 'lambda ,args ,body))

(defmacro make-let (bindings body)
  `(list 'let ,bindings ,body))

(defun doublet-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (equal x nil))
        (t (and (true-listp (car x))
                (eql (length (car x)) 2)
                (doublet-listp (cdr x))))))

(defmacro er-let* (alist body)

; This macro introduces the variable er-let-star-use-nowhere-else.
; The user who uses that variable in his forms is likely to be
; disappointed by the fact that we rebind it.

; Keep in sync with er-let*@par.

  (declare (xargs :guard (and (doublet-listp alist)
                              (symbol-alistp alist))))
  (cond ((null alist)
         (list 'check-vars-not-free
               '(er-let-star-use-nowhere-else)
               body))
        (t (list 'mv-let
                 (list 'er-let-star-use-nowhere-else
                       (caar alist)
                       'state)
                 (cadar alist)
                 (list 'cond
                       (list 'er-let-star-use-nowhere-else
                             (list 'mv
                                   'er-let-star-use-nowhere-else
                                   (caar alist)
                                   'state))
                       (list t (list 'er-let* (cdr alist) body)))))))

#+acl2-par
(defmacro er-let*@par (alist body)

; Keep in sync with er-let*.

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
                       (list t (list 'er-let*@par (cdr alist) body)))))))

(defmacro match (x pat)
  (list 'case-match x (list pat t)))

(defmacro match! (x pat)
  (list 'or (list 'case-match x
                  (list pat '(value nil)))
        (list 'er 'soft nil
              "The form ~x0 was supposed to match the pattern ~x1."
              x (kwote pat))))

(defun def-basic-type-sets1 (lst i)
  (declare (xargs :guard (and (integerp i)
                              (true-listp lst))))
  (cond ((null lst) nil)
        (t (cons (list 'defconst (car lst) (list 'the-type-set (expt 2 i)))
                 (def-basic-type-sets1 (cdr lst) (+ i 1))))))

(defmacro def-basic-type-sets (&rest lst)
  (let ((n (length lst)))
    `(progn
       (defconst *actual-primitive-types* ',lst)
       (defconst *min-type-set* (- (expt 2 ,n)))
       (defconst *max-type-set* (- (expt 2 ,n) 1))
       (defmacro the-type-set (x)

; Warning: Keep this definition in sync with the type declaration in
; ts-subsetp0 and ts-subsetp.

         `(the (integer ,*min-type-set* ,*max-type-set*) ,x))
       ,@(def-basic-type-sets1 lst 0))))

(defun list-of-the-type-set (x)
  (cond ((consp x)
         (cons (list 'the-type-set (car x))
               (list-of-the-type-set (cdr x))))
        (t nil)))

(defmacro ts= (a b)
  (list '= (list 'the-type-set a) (list 'the-type-set b)))

; We'll create fancier versions of ts-complement0, ts-union0, and
; ts-intersection0 once we have defined the basic type sets.

(defmacro ts-complement0 (x)
  (list 'the-type-set (list 'lognot (list 'the-type-set x))))

(defmacro ts-complementp (x)
  (list 'minusp x))

(defun ts-union0-fn (x)
  (list 'the-type-set
        (cond ((null x) '*ts-empty*)
              ((null (cdr x)) (car x))
              (t (xxxjoin 'logior
                          (list-of-the-type-set x))))))

(defmacro ts-union0 (&rest x)
  (declare (xargs :guard (true-listp x)))
  (ts-union0-fn x))

(defmacro ts-intersection0 (&rest x)
  (list 'the-type-set
        (cons 'logand (list-of-the-type-set x))))

(defmacro ts-disjointp (&rest x)
  (list 'ts= (cons 'ts-intersection x) '*ts-empty*))

(defmacro ts-intersectp (&rest x)
  (list 'not (list 'ts= (cons 'ts-intersection x) '*ts-empty*)))

; We do not define ts-subsetp0, both because we don't need it and because if we
; do define it, we will be tempted to add the declaration found in ts-subsetp,
; yet we have not yet defined *min-type-set* or *max-type-set*.

(defun ts-builder-case-listp (x)

; A legal ts-builder case list is a list of the form
;    ((key1 val1 ...) (key2 val2 ...) ... (keyk valk ...))
; where none of the keys is 'otherwise or 't except possibly keyk and
; every key is a symbolp if keyk is 'otherwise or 't.

; This function returns t, nil, or 'otherwise.  A non-nil value means
; that x is a legal ts-builder case list.  If it returns 'otherwise,
; it means keyk is an 'otherwise or a 't clause.  That aspect of the
; function is not used outside of its definition, but it is used in
; the definition below.

; If keyk is an 'otherwise or 't then each of the other keys will
; occur twice in the expanded form of the ts-builder expression and
; hence those keys must all be symbols.

  (cond ((atom x) (eq x nil))
        ((and (consp (car x))
              (true-listp (car x))
              (not (null (cdr (car x)))))
         (cond ((or (eq t (car (car x)))
                    (eq 'otherwise (car (car x))))
                (cond ((null (cdr x)) 'otherwise)
                      (t nil)))
               (t (let ((ans (ts-builder-case-listp (cdr x))))
                    (cond ((eq ans 'otherwise)
                           (cond ((symbolp (car (car x)))
                                  'otherwise)
                                 (t nil)))
                          (t ans))))))
        (t nil)))

(defun ts-builder-macro1 (x case-lst seen)
  (declare (xargs :guard (and (symbolp x)
                              (ts-builder-case-listp case-lst))))
  (cond ((null case-lst) nil)
        ((or (eq (caar case-lst) t)
             (eq (caar case-lst) 'otherwise))
         (sublis (list (cons 'x x)
                       (cons 'seen seen)
                       (cons 'ts2 (cadr (car case-lst))))
                 '((cond ((ts-intersectp x (ts-complement0 (ts-union0 . seen)))
                          ts2)
                         (t *ts-empty*)))))
        (t (cons (sublis (list (cons 'x x)
                               (cons 'ts1 (caar case-lst))
                               (cons 'ts2 (cadr (car case-lst))))
                         '(cond ((ts-intersectp x ts1) ts2)
                                (t *ts-empty*)))
                 (ts-builder-macro1 x (cdr case-lst) (cons (caar case-lst)
                                                           seen))))))

(defun ts-builder-macro (x case-lst)
  (declare (xargs :guard (and (symbolp x)
                              (ts-builder-case-listp case-lst))))
  (cons 'ts-union
        (ts-builder-macro1 x case-lst nil)))

(defmacro ts-builder (&rest args)
; (declare (xargs :guard (and (consp args)
;                        (symbolp (car args))
;                        (ts-builder-case-listp (cdr args)))))
  (ts-builder-macro (car args) (cdr args)))

(defmacro ffn-symb-p (term sym)

; Term and sym should be expressions that evaluate to a pseudo-termp and a
; symbol, respectively.

  (cond
   ((symbolp term)
    `(and (nvariablep ,term)
;         (not (fquotep ,term))
          (eq (ffn-symb ,term) ,sym)))

; If we bind term then in general, we need to bind sym too, even though it only
; occurs once below.  Consider for example the expansion of (ffn-symb-p x (foo
; term)), where presumably term is bound above.  We need to avoid capturing the
; occurrence of term in (foo term), which is solved by binding sym here.  Of
; course, if sym is of the form (quote v) then this isn't an issue.

   ((and (consp sym)
         (eq (car sym) 'quote))
    `(let ((term ,term))
       (and (nvariablep term)
;           (not (fquotep term))
            (eq (ffn-symb term) ,sym))))
   (t
    `(let ((term ,term)
           (sym ,sym))
       (and (nvariablep term)
;           (not (fquotep term))
            (eq (ffn-symb term) sym))))))

(defabbrev strip-not (term)

; A typical use of this macro is:
; (mv-let (not-flg atm) (strip-not term)
;         ...body...)
; which has the effect of binding not-flg to T and atm to x if term
; is of the form (NOT x) and binding not-flg to NIL and atm to term
; otherwise.

  (cond ((ffn-symb-p term 'not)
         (mv t (fargn term 1)))
        (t (mv nil term))))

(defmacro equalityp (term)

; Note that the fquotep below is commented out.  This function violates
; our standard rules on the use of ffn-symb but is ok since we are looking
; for 'equal and not for 'quote or any constructor that might be hidden
; inside a quoted term.

  `(ffn-symb-p ,term 'equal))

(defmacro inequalityp (term)

; Note that the fquotep below is commented out.  This function violates
; our standard rules on the use of ffn-symb but is ok since we are looking
; for 'equal and not for 'quote or any constructor that might be hidden
; inside a quoted term.

  `(ffn-symb-p ,term '<))

(defmacro consityp (term)

; Consityp is to cons what equalityp is equal:  it recognizes terms
; that are non-evg cons expressions.

  `(ffn-symb-p ,term 'cons))

(defun print-current-idate (channel state)
  (mv-let (d state)
    (read-idate state)
    (print-idate d channel state)))

(defun skip-when-logic (str state)
  (pprogn
   (observation 'top-level
                "~s0 events are skipped when the default-defun-mode is ~x1."
                str
                (default-defun-mode-from-state state))
   (mv nil nil state)))

(defun chk-inhibit-output-lst (lst ctx state)
  (cond ((not (true-listp lst))
         (er soft ctx
             "The argument to set-inhibit-output-lst must evaluate to a ~
              true-listp, unlike ~x0."
             lst))
        ((not (subsetp-eq lst *valid-output-names*))
         (er soft ctx
             "The argument to set-inhibit-output-lst must evaluate to a ~
              subset of the list ~X01, but ~x2 contains ~&3."
             *valid-output-names*
             nil
             lst
             (set-difference-eq lst *valid-output-names*)))
        (t (let ((lst (if (member-eq 'warning! lst)
                          (add-to-set-eq 'warning lst)
                        lst)))
             (pprogn (cond ((and (member-eq 'prove lst)
                                 (not (member-eq 'proof-tree lst))
                                 (member-eq 'proof-tree
                                            (f-get-global 'inhibit-output-lst
                                                          state)))
                            (warning$ ctx nil
                                      "The printing of proof-trees is being ~
                                       enabled while the printing of proofs ~
                                       is being disabled.  You may want to ~
                                       execute :STOP-PROOF-TREE in order to ~
                                       inhibit proof-trees as well."))
                           (t state))
                     (value lst))))))

; With er defined, we may now define chk-ld-skip-proofsp.

(defconst *ld-special-error*
  "~x1 is an illegal value for the state global variable ~x0.  See ~
   :DOC ~x0.")

(defun chk-ld-skip-proofsp (val ctx state)
  (declare (xargs :mode :program))
  (cond ((member-eq val
                    '(t nil include-book
                        initialize-acl2 include-book-with-locals))
         (value nil))
        (t (er soft ctx
               *ld-special-error*
               'ld-skip-proofsp val))))

(defun set-ld-skip-proofsp (val state)
  (declare (xargs :mode :program))
  (er-progn
   (chk-ld-skip-proofsp val 'set-ld-skip-proofsp state)
   (pprogn
    (f-put-global 'ld-skip-proofsp val state)
    (value val))))

(defmacro set-ld-skip-proofs (val state)

; Usually the names of our set utilities do not end in "p".  We leave
; set-ld-skip-proofsp for backward compatibility, but we add this version
; for consistency.

  (declare (ignore state)) ; avoid a stobj problem
  `(set-ld-skip-proofsp ,val state))

(defun set-write-acl2x (val state)
  (declare (xargs :guard (state-p state)))
  (er-progn
   (cond ((member-eq val '(t nil)) (value nil))
         ((and (consp val) (null (cdr val)))
          (chk-ld-skip-proofsp (car val) 'set-write-acl2x state))
         (t (er soft 'set-write-acl2x
                "Illegal value for set-write-acl2x, ~x0.  See :DOC ~
                 set-write-acl2x."
                val)))
   (pprogn (f-put-global 'write-acl2x val state)
           (value val))))

;                             CHECKSUMS

; We begin by developing code to compute checksums for files, culminating in
; function check-sum.  (Later we will consider checksums for objects.)

; We can choose any two nonnegative integers for the following two
; constants and still have a checksum algorithm, provided, (a) that
; (< (* 127 *check-length-exclusive-maximum*) *check-sum-exclusive-maximum*)
; and provided (b) that (* 2 *check-sum-exclusive-maximum*) is of type
; (signed-byte 32).  The first condition assures that the intermediate
; sum we obtain by adding to a running checksum the product of a
; character code with the current location can be reduced modulo
; *check-sum-exclusive-maximum* by subtracting *check-sum-exclusive-maximum*.
; Choosing primes, as we do, may help avoid some loss of information
; due to cancellation.  Choosing primes that are smaller may lead to
; checksums with less information.

(defconst *check-sum-exclusive-maximum*

; 268435399 is the first prime below 2^28.  We use integers modulo this number
; as checksums.

  268435399)

(defconst *check-length-exclusive-maximum*

; 2097143 is the first prime below 2^21.  We use integers modulo this number as
; indices into the stream we are checksumming.

  2097143)

; We actually return checksums which are in (mod
; *check-sum-exclusive-maximum*).

(defconst *-check-sum-exclusive-maximum* (- *check-sum-exclusive-maximum*))

(defconst *1-check-length-exclusive-maximum*
  (1- *check-length-exclusive-maximum*))

(defun ascii-code! (x)
  (let ((y (char-code x)))
    (cond
     ((or (= y 0) (= y 128))
      1)
     ((< 127 y)
      (- y 128))
     (t y))))

(defun check-sum1 (sum len channel state)
  (declare (type (signed-byte 32) sum len))
  (let ((len (cond ((= len 0) *1-check-length-exclusive-maximum*)
                   (t (the (signed-byte 32) (1- len))))))
    (declare (type (signed-byte 32) len))
    (mv-let (x state)
      (read-char$ channel state)
      (cond ((not (characterp x)) (mv sum state))
            (t (let ((inc (ascii-code! x)))
                 (declare (type (unsigned-byte 7) inc))
                 (cond ((and (= inc 0)
                             (not (eql x #\Tab)))
                        (mv x state))
                       (t (let ((inc (the (unsigned-byte 7)
                                          (cond ((= inc 0) 9) (t inc)))))
                            (declare (type (unsigned-byte 7) inc))
                            (let ((sum (+ sum (the (signed-byte 32)
                                                   (* inc len)))))
                              (declare (type (signed-byte 32) sum))
                              (check-sum1
                               (cond ((>= sum *check-sum-exclusive-maximum*)
                                      (the (signed-byte 32)
                                       (+ sum *-check-sum-exclusive-maximum*)))
                                     (t sum))
                               len channel state)))))))))))

(defun check-sum (channel state)

; This function returns a checksum on the characters in a stream.
; This function also checks that every character read is either
; #\Newline, #\Tab, or #\Space, or a printing Ascii character.  If the
; first value returned is a character, that character was not legal.
; Otherwise, the first value returned is an integer, the checksum.

  (check-sum1 0 *1-check-length-exclusive-maximum* channel state))

; We now develop code for computing checksums of objects.  There are two
; separate algorithms, culminating respectively in functions old-check-sum-obj
; and fchecksum-obj.  The first development was used up through ACL2
; Version_3.4, which uses an algorithm similar to that of our file-based
; function, check-sum.  However, the #+hons version of ACL2 was being used on
; large cons trees with significant subtree sharing.  These "galactic" trees
; could have relatively few distinct cons cells but a huge naive node count.
; It was thus desirable to memoize the computation of checksums, which was
; impossible using the existing algorithm because it modified state.

; The second development was contributed by Jared Davis (and is now maintained
; by the ACL2 developers, who are responsible for any errors).  It is amenable
; to memoization and, indeed, fchecksum-obj is memoized in the #+hons version
; of ACL2.  We say more after developing the code for the first algorithm,
; culminating in function check-sum-obj1.

; We turn now to the first development (which is no longer used in ACL2).

(defun check-sum-inc (n state)
  (declare (type (unsigned-byte 7) n))
  (let ((top
         (32-bit-integer-stack-length state)))
    (declare (type (signed-byte 32) top))
    (let ((sum-loc (the (signed-byte 32) (+ top -1)))
          (len-loc (the (signed-byte 32) (+ top -2))))
      (declare (type (signed-byte 32) sum-loc len-loc))
      (let ((sum
             (aref-32-bit-integer-stack sum-loc state)))
        (declare (type (signed-byte 32) sum))
        (let ((len
               (aref-32-bit-integer-stack len-loc state)))
          (declare (type (signed-byte 32) len))
          (let ((len (cond ((= 0 len) *1-check-length-exclusive-maximum*)
                           (t (the (signed-byte 32) (+ len -1))))))
            (declare (type (signed-byte 32) len))
            (let ((state
                   (aset-32-bit-integer-stack len-loc len state)))
              (let ((new-sum
                     (the (signed-byte 32)
                      (+ sum (the (signed-byte 32) (* n len))))))
                (declare (type (signed-byte 32) new-sum))
                (let ((new-sum
                       (cond ((>= new-sum *check-sum-exclusive-maximum*)
                              (the (signed-byte 32)
                               (+ new-sum *-check-sum-exclusive-maximum*)))
                             (t new-sum))))
                  (declare (type (signed-byte 32) new-sum))
                  (aset-32-bit-integer-stack sum-loc new-sum state))))))))))

(defun check-sum-natural (n state)
  (declare (type unsigned-byte n))
  (cond ((<= n 127)
         (check-sum-inc (the (unsigned-byte 7) n) state))
        (t (pprogn (check-sum-inc (the (unsigned-byte 7) (rem n 127)) state)
                   (check-sum-natural (truncate n 127) state)))))

(defun check-sum-string1 (str i len state)
  (declare (type string str))
  (declare (type (signed-byte 32) i len))
  (cond ((= i len) state)
        (t (let ((chr (char str i)))
             (declare (type character chr))
             (let ((code (ascii-code! chr)))
               (declare (type (unsigned-byte 7) code))
               (cond ((> code 127)
                      (f-put-global
                       'check-sum-weirdness (cons str i) state))
                     (t (pprogn (check-sum-inc code state)
                                (check-sum-string1
                                 str
                                 (the (signed-byte 32) (1+ i))
                                 len
                                 state)))))))))

(defun check-sum-string2 (str i len state)

; This function serves the same purpose as check-sum-string1 except
; that no assumption is made that i or len fit into 32 bits.  It
; seems unlikely that this function will ever be called, since it
; seems unlikely that any Lisp will support strings of length 2 billion
; or more, but who knows.

  (declare (type string str))
  (cond ((= i len) state)
        (t (let ((chr (char str i)))
             (let ((code (ascii-code! chr)))
               (cond ((> code 127)
                      (f-put-global
                       'check-sum-weirdness (cons str i) state))
                     (t (pprogn (check-sum-inc code state)
                                (check-sum-string2
                                 str
                                 (1+ i)
                                 len
                                 state)))))))))

(defun check-sum-string (str state)
  (let ((len (the integer (length (the string str)))))
    (cond ((32-bit-integerp len)
           (check-sum-string1 str 0 (the (signed-byte 32) len) state))
          (t (check-sum-string2 str 0 len state)))))

(defun check-sum-obj1 (obj state)
  (cond ((symbolp obj)
         (pprogn (check-sum-inc 1 state)
                 (check-sum-string (symbol-name obj) state)))
        ((stringp obj)
         (pprogn (check-sum-inc 2 state)
                 (check-sum-string obj state)))
        ((rationalp obj)
         (cond ((integerp obj)
                (cond ((< obj 0)
                       (pprogn (check-sum-inc 3 state)
                               (check-sum-natural (- obj) state)))
                      (t (pprogn (check-sum-inc 4 state)
                                 (check-sum-natural obj state)))))
               (t (let ((n (numerator obj)))
                    (pprogn (check-sum-inc 5 state)
                            (check-sum-natural (if (< n 0) (1- (- n)) n) state)
                            (check-sum-natural (denominator obj) state))))))
        ((consp obj)
         (pprogn (check-sum-inc 6 state)
                 (check-sum-obj1 (car obj) state)
                 (cond ((atom (cdr obj))
                        (cond ((cdr obj)
                               (pprogn (check-sum-inc 7 state)
                                       (check-sum-obj1 (cdr obj) state)))
                              (t (check-sum-inc 8 state))))
                       (t (check-sum-obj1 (cdr obj) state)))))
        ((characterp obj)
         (pprogn (check-sum-inc 9 state)
                 (let ((n (ascii-code! obj)))
                   (cond ((< n 128)
                          (check-sum-inc (ascii-code! obj) state))
                         (t (f-put-global
                             'check-sum-weirdness obj state))))))
        ((complex-rationalp obj)
         (pprogn (check-sum-inc 14 state)
                 (check-sum-obj1 (realpart obj) state)
                 (check-sum-obj1 (imagpart obj) state)))
        (t (f-put-global
            'check-sum-weirdness obj state))))

(defun old-check-sum-obj (obj state)

; This function became obsolete after Version_3.4 but we include it in case
; there are situations where it becomes useful again.  It is the culmination of
; our first development of checksums for objects (as discussed above).

; We return a checksum on obj, using an algorithm similar to that of
; check-sum.  We return a non-integer as the first value if (and only if) the
; obj is not composed entirely of conses, symbols, strings, rationals, complex
; rationals, and characters. If the first value is not an integer, it is one of
; the offending objects encountered.

; We typically used this function to compute checksums for .cert files.

  (pprogn
   (extend-32-bit-integer-stack 2 0 state)
   (let ((top
          (32-bit-integer-stack-length state)))
     (let ((sum-loc (+ top -1))
           (len-loc (+ top -2)))
       (pprogn
        (aset-32-bit-integer-stack sum-loc 0 state)
        (aset-32-bit-integer-stack len-loc *1-check-length-exclusive-maximum*
                                   state)
        (f-put-global 'check-sum-weirdness nil state)
        (check-sum-obj1 obj state)
        (let ((ans (aref-32-bit-integer-stack sum-loc state)))
          (pprogn (shrink-32-bit-integer-stack 2 state)
                  (let ((x (f-get-global 'check-sum-weirdness state)))
                    (cond (x (pprogn (f-put-global
                                      'check-sum-weirdness nil state)
                                     (mv x state)))
                          (t (mv ans state)))))))))))

; We now develop code for the second checksum algorithm, contributed by Jared
; Davis (now maintained by the ACL2 developers, who are responsible for any
; errors).  See also the long comment after check-sum-obj, below.

; Our initial attempts however were a problem for GCL, which boxes fixnums
; unless one is careful.  A regression took about 44 or 45 minutes instead of
; 35 or 36 minutes, which is really significant considering that (probably)
; only the checksum code was changed, and one would expect checksums to take a
; trivial fraction of time during a regression.  Therefore, we developed code
; to avoid boxing fixnums in GCL during a common operation: multiplication mod
; M31 = #x7fffffff.  The code below is developed only for defining that
; operation, times-mod-m31; so we could conditionalize with #+gcl all
; definitions below up to times-mod-m31.  We believe that the following is a
; theorem, but we have not proved it (nor even admitted the relevant functions
; into :logic mode):

; (implies (and (natp x) (< x #x7fffffff)
;               (natp y) (< y #x7fffffff))
;          (equal (times-mod-m31 x y)
;                 (rem (* x y) #x7fffffff)))

; We considered using our fancy times-mod-m31 and its subfunctions for other
; than GCL.  The time loss for ACL2h built on CCL 1.2 (actually
; 1.2-r10991M-trunk) on DarwinX8664 was only about 3.2%, which seems worth the
; cost in order to avoid having Lisp-specific code.  However, regression runs
; with ACL2 built on Allegro CL exhibited intermittent checksumming errors.  We
; wonder about a possible compiler bug, since neither heavy addition of checks,
; nor running with safety 3 (both ACL2h on CCL and ACL2 on Allegro CL) showed
; any inappropriate type declarations in the code below, and there were no
; checksumming problems exhibited with CCL, GCL, or SBCL.  Moreover, Allegro CL
; showed significant slow down with the fancy times-mod-m31, not surprisingly
; since Allegro CL supports fixnums of less than 32 bits.  Therefore, we
; decided to use a much simpler times-mod-m31 for all Lisps except GCL.

(defun plus-mod-m31 (u v)

; Add u and v mod M31 = #x7fffffff.

  (declare (type (signed-byte 32) u v))
  (the (signed-byte 32)
       (let ((u (min u v))
             (v (max u v)))
         (declare (type (signed-byte 32) u v))
         (cond ((< u #x40000000) ; 2^30
                (cond ((< v #x40000000) ; 2^30
                       (the (signed-byte 32) (+ u v)))
                      (t
                       (let ((part (+ (the (signed-byte 32)
                                           (logand v #x3FFFFFFF)) ; v - 2^30
                                      u)))
                         (declare (type (signed-byte 32) part))
                         (cond ((< part #x3FFFFFFF)
                                (the (signed-byte 32)
                                     (logior part #x40000000)))
                               ((eql part #x3FFFFFFF)
                                0)
                               (t ; part + 2^30 = part' + 2^31
                                (the (signed-byte 32)
                                     (1+ (the (signed-byte 32)
                                              (logxor part #x40000000))))))))))
               (t (the (signed-byte 32)
                       (- #x7FFFFFFF
                          (the (signed-byte 32)
                               (+ (the (signed-byte 32)
                                       (- #x7FFFFFFF u))
                                  (the (signed-byte 32)
                                       (- #x7FFFFFFF v)))))))))))

(defun double-mod-m31 (x)

; This is an optimization of (plus-mod-m31 x x).

  (declare (type (signed-byte 32) x))
  (the (signed-byte 32)
       (cond ((< x #x40000000) ; 2^30
              (the (signed-byte 32) (ash x 1)))
             (t (the (signed-byte 32)
                     (- #x7FFFFFFF
                        (the (signed-byte 32)
                             (ash (the (signed-byte 32)
                                       (- #x7FFFFFFF x))
                                  1))))))))

(defun times-expt-2-16-mod-m31 (x)

; Given x < M31 = #x7fffffff, we compute 2^16*x mod M31.  The idea is to view x
; as the concatenation of 15-bit chunk H (high) to 16-bit chunk L (low), so
; that reasoning mod M31, 2^16*x = 2^32*H + 2^16*L = 2*H + 2^16*L.  Note that
; if L has its high (15th) bit set, then writing L# for the result of masking
; out that bit, we have [mod M31] 2^16*L = 2^16(2^15 + L#) = 2^31 + 2^16 * L#.
; = 1 + 2^16 * L#.

; We can test this function in CCL, in raw Lisp, as follows.  (It may be too
; slow to do this in GCL since some intermediate results might not be fixnums.)
; It took us about 3.5 minutes (late 2008).

;  (defun test ()
;    (loop for i from 0 to #x7ffffffe
;          when (not (eql (times-expt-2-16-mod-m31 i)
;                         (mod (* #x10000 i) #x7fffffff)))
;          do (return i)))
;  (test)

  (declare (type (signed-byte 32) x))
  (the (signed-byte 32)
       (let ((hi (ash x -16))
             (lo (logand x #x0000ffff)))
         (declare (type (signed-byte 32) hi lo))
         (cond ((eql 0
                     (the (signed-byte 32)
                          (logand lo #x8000))) ; logbitp in GCL seems to box!
                (the (signed-byte 32)
                     (plus-mod-m31 (double-mod-m31 hi)
                                   (the (signed-byte 32)
                                        (ash lo 16)))))
               (t
                (the (signed-byte 32)
                     (plus-mod-m31 (double-mod-m31 hi)
                                   (the (signed-byte 32)
                                        (logior
                                         #x1
                                         (the (signed-byte 32)
                                              (ash (the (signed-byte 32)
                                                        (logand lo #x7fff))
                                                   16)))))))))))

#+(and (not gcl) (not acl2-loop-only))
(declaim (inline times-mod-m31))

(defun times-mod-m31 (u v)

; Note that u or v (or both) can be #x7fffffff, not just less than that number;
; this code will still give the correct result, 0.

; See the comment above about "using our fancy times-mod-m31" for GCL only.

  (declare (type (signed-byte 32) u v))
  (the (signed-byte 32)
       #+(or (not gcl) acl2-loop-only)
       (rem (the (signed-byte 64) (* u v))
            #x7fffffff)
       #+(and gcl (not acl2-loop-only))

; We want to avoid boxing, where we have 32-bit fixnums u and v.  We compute as
; follows:

;   u * v
; = (2^16 u-hi + u-lo) * (2^16 v-hi + v-lo)
; = 2^32 u-hi v-hi + 2^16 u-hi v-lo + 2^16 u-lo v-hi + u-lo v-lo
; = [mod M31 = #x7fffffff]
;   2 u-hi v-hi + 2^16(u-hi*v-lo + u-lo*v-hi) + u-lo*v-lo

; Now u-hi and v-hi are less than 2^15, while u-lo and v-lo are less than
; 2^16.  So we need to be careful with the term u-lo*v-lo.

       (let ((u-hi (ash u -16))
             (u-lo (logand u #x0000ffff))
             (v-hi (ash v -16))
             (v-lo (logand v #x0000ffff)))
         (declare (type (signed-byte 32) u-hi u-lo v-hi v-lo))
         (let ((term1 (double-mod-m31 (the (signed-byte 32)
                                           (* u-hi v-hi))))
               (term2 (times-expt-2-16-mod-m31
                       (plus-mod-m31 (the (signed-byte 32) (* u-hi v-lo))
                                     (the (signed-byte 32) (* u-lo v-hi)))))
               (term3 (cond ((or (eql (the (signed-byte 32)
                                           (logand u-lo #x8000))
                                      0)
                                 (eql (the (signed-byte 32)
                                           (logand v-lo #x8000))
                                      0))
                             (the (signed-byte 32)
                                  (* u-lo v-lo)))
                            (t

; Let H = 2^15, and let u0 and v0 be the results of masking out the high bits
; of u-lo and v-lo, respectively.  So:

;   u-lo * v-lo
; = (H + u0) * (H + v0)
; = H^2 + H*(u0 + v0) + u0*v0

                             (let ((u0 (logand u #x7fff))
                                   (v0 (logand v #x7fff)))
                               (declare (type (signed-byte 32) u0 v0))
                               (plus-mod-m31 #x40000000 ; 2^30
                                             (plus-mod-m31
                                              (the (signed-byte 32)
                                                   (* #x8000 ; 2^15
                                                      (the (signed-byte 32)
                                                           (+ u0 v0))))
                                              (the (signed-byte 32)
                                                   (* u0 v0)))))))))
           (declare (type (signed-byte 32) term1 term2 term3))
           (plus-mod-m31 term1
                         (plus-mod-m31 term2 term3))))))

; Now we can include (our latest version of) Jared's code.

(defun fchecksum-natural-aux (n ans)

; A "functional" checksum for natural numbers.
;
;   N is the natural number we want to checksum.
;   ANS is the answer we have accumulated so far.
;
; Let M31 be 2^31 - 1.  This happens to be the largest representable 32-bit
; signed number using 2's complement arithmetic.  It is also a Mersenne prime.
; Furthermore, let P1 be 392894102, which is a nice, large primitive root of
; M31.  From number theory, we can construct a basic pseudorandom number
; generator as follows:
;
;   rnd0 = seed
;   rnd1 = (rnd0 * P1) mod M31
;   rnd2 = (rnd1 * P1) mod M31
;   ...
;
; And our numbers will not repeat until 2^31 - 1.  In fact, such a generator
; is found in the community book "misc/random."
;
; Our checksum algorithm uses this idea in a slightly different way.  Given a
; 31-bit natural number, K, think of (K * P1) mod M31 as a way to "shuffle" the
; bits of K around in a fairly random manner.  Then, to checksum a (potentially
; large) integer n, we break n up into 31-bit chunks, call them K1, K2, ...,
; Km.  We then compute (Ki * P1) mod M31 for each i, and xor the results all
; together to compute a new, 31-bit checksum.

; A couple of other notes.
;
;  - M31 may be written as #x7FFFFFFF.
;
;  - We recur using (ash n -31), but this computes the same thing as (truncate
;    n (expt 2 31)).
;
;  - We split n into Ki by using (logand n #x7FFFFFFF), which is the same as
;    (rem n (expt 2 31)).

  (declare (type (integer 0 *) n))
  (declare (type (signed-byte 32) ans))
  (the (signed-byte 32)
    (if (eql n 0)
        ans
      (fchecksum-natural-aux (the (integer 0 *) (ash n -31))
                             (the (signed-byte 32)
                               (logxor ans
                                       (the (signed-byte 32)
                                         (times-mod-m31
                                          (logand n #x7FFFFFFF)
                                          392894102))))))))

(defun fchecksum-natural (n)
  (declare (type (integer 0 *) n))
  (the (signed-byte 32)
    (fchecksum-natural-aux n 28371987)))

(defun fchecksum-string1 (str i len ans)

; A "functional" checksum for strings.
;
; This is similar to the case for natural numbers.
;
; We consider the string in 31-bit pieces; each character in the string has,
; associated with it, an 8-bit character code, so we can combine four of these
; codes together to create a 32 bit chunk.  We then simply drop the highest
; resulting bit (which should typically not matter because the character codes
; above 127 are so rarely used).  The remaining 31-bits are be treated just as
; the 31-bit chunks of integers are, but the only twist is that we will use a
; different primitive root so that we come up with different numbers.  In
; particular, we will use 506249751.

; WARNING: Keep this in sync with fchecksum-string2.

  (declare (type string str))
  (declare (type (signed-byte 32) i len ans))
  (the (signed-byte 32)
    (if (>= i len)
        ans
      (let* ((c0 (logand #x7F (the (signed-byte 32)
                                (char-code (the character (char str i))))))
             (i  (+ i 1))
             (c1 (if (>= i len)
                     0
                   (char-code (the character (char str i)))))
             (i  (+ i 1))
             (c2 (if (>= i len)
                     0
                   (char-code (the character (char str i)))))
             (i  (+ i 1))
             (c3 (if (>= i len)
                     0
                   (char-code (the character (char str i)))))
             (bits

; GCL 2.6.7 does needless boxing when we call logior on the four arguments,
; even when each of them is of the form (the (signed-byte 32) xxx).  So the
; code is a bit ugly below.

              (logior (the (signed-byte 32) (ash c0 24))
                      (the (signed-byte 32)
                           (logior (the (signed-byte 32) (ash c1 16))
                                   (the (signed-byte 32)
                                        (logior (the (signed-byte 32)
                                                     (ash c2 8))
                                                (the (signed-byte 32)
                                                     c3))))))))
        (declare (type (signed-byte 32) c0 i c1 c2 c3 bits))
        (fchecksum-string1
         str i len
         (the (signed-byte 32)
           (logxor ans
                   (the (signed-byte 32)
                     (times-mod-m31 bits 506249751)))))))))

(defun fchecksum-string2 (str i len ans)

; Same as above, but we don't assume i, len are (signed-byte 32)'s.

; WARNING: Keep this in sync with fchecksum-string1.

  (declare (type string str))
  (declare (type (signed-byte 32) ans))
  (declare (type (integer 0 *) i len))
  (the (signed-byte 32)
    (if (>= i len)
        ans
      (let* ((c0 (logand #x7F (the (signed-byte 32)
                                (char-code (the character (char str i))))))
             (i  (+ i 1))
             (c1 (if (>= i len)
                     0
                   (char-code (the character (char str i)))))
             (i  (+ i 1))
             (c2 (if (>= i len)
                     0
                   (char-code (the character (char str i)))))
             (i  (+ i 1))
             (c3 (if (>= i len)
                     0
                   (char-code (the character (char str i)))))
             (bits ; see comment in fchecksum-string1 about ugly code below
              (logior (the (signed-byte 32) (ash c0 24))
                      (the (signed-byte 32)
                           (logior (the (signed-byte 32) (ash c1 16))
                                   (the (signed-byte 32)
                                        (logior (the (signed-byte 32)
                                                     (ash c2 8))
                                                (the (signed-byte 32)
                                                     c3))))))))
        (declare (type (signed-byte 32) c0 c1 c2 c3 bits)
                 (type (integer 0 *) i))
        (fchecksum-string2
         str i len
         (the (signed-byte 32)
           (logxor ans
                   (the (signed-byte 32)
                     (times-mod-m31 bits 506249751)))))))))

(defun fchecksum-string (str)
  (declare (type string str))
  (the (signed-byte 32)
       (let ((length (length str)))
         (declare (type (integer 0 *) length))
         (cond ((< length 2147483647) ; so (+ 1 length) is (signed-byte 32)
                (fchecksum-string1 str 0 length

; We scramble the length in order to get a seed.  This number is just another
; primitive root.

                                   (times-mod-m31 (the (signed-byte 32)
                                                       (+ 1 length))
                                                  718273893)))
               (t
                (fchecksum-string2 str 0 length

; As above, but WARNING: Do not use times-mod-m31 here, because length need not
; be a fixnum.

                                   (rem (the integer (* (+ 1 length)
                                                        718273893))
                                        #x7FFFFFFF)))))))

#-(or acl2-loop-only hons)
(defvar *fchecksum-symbol-memo*
  nil)

(defun fchecksum-atom (x)

; X is any atom.  We compute a "functional checksum" of X.
;
; This is pretty straightforward.  For naturals and strings, we just call the
; functions we've developed above.  Otherwise, the object is composed out of
; naturals and strings.  We compute the component-checksums, then "scramble"
; them by multiplying with another primitive root.  Since it is easy to find
; primitive roots, it is easy to scramble in many different ways based on the
; different types we are looking at.

  (the (signed-byte 32)
    (cond ((natp x)
           (fchecksum-natural x))
          ((integerp x)

; It's not a natural, so it's negative.  We compute the code for the absolute
; value, then scramble it with yet another primitive root.

           (let ((abs-code (fchecksum-natural (- x))))
             (declare (type (signed-byte 32) abs-code))
             (times-mod-m31 abs-code 283748912)))
          ((symbolp x)
           (cond
            #-(or hons acl2-loop-only)
            ((and *fchecksum-symbol-memo*
                  (gethash x *fchecksum-symbol-memo*)))
            (t
             (let* ((pkg-code (fchecksum-string (symbol-package-name x)))
                    (sym-code (fchecksum-string (symbol-name x)))
                    (pkg-code-scramble

; We scramble the bits of pkg-code so that it matters that they are in order.
; To do this, we multiply by another primitive root and mod out by M31.

                     (times-mod-m31 pkg-code 938187814)))
               (declare (type (signed-byte 32)
                              pkg-code sym-code pkg-code-scramble))
               (cond #-(or hons acl2-loop-only)
                     (*fchecksum-symbol-memo*
                      (setf (gethash x *fchecksum-symbol-memo*)
                            (logxor pkg-code-scramble sym-code)))
                     (t (logxor pkg-code-scramble sym-code)))))))
          ((stringp x)
           (fchecksum-string x))
          ((characterp x) ; just scramble using another primitive root
           (times-mod-m31 (char-code x) 619823821))
          ((rationalp x)
           (let* ((num-code (fchecksum-atom (numerator x)))
                  (den-code (fchecksum-natural (denominator x)))
                  (num-scramble
                   (times-mod-m31 num-code 111298397))
                  (den-scramble
                   (times-mod-m31 den-code 391892127)))
             (declare (type (signed-byte 32)
                            num-code den-code num-scramble den-scramble))
             (logxor num-scramble den-scramble)))
          ((complex-rationalp x)
           (let* ((imag-code (fchecksum-atom (imagpart x)))
                  (real-code (fchecksum-atom (realpart x)))
                  (imag-scramble
                   (times-mod-m31 imag-code 18783723))
                  (real-scramble
                   (times-mod-m31 real-code 981827319)))
             (declare (type (signed-byte 32)
                            imag-code real-code imag-scramble real-scramble))
             (logxor imag-scramble real-scramble)))
          (t
           (prog2$ (er hard 'fchecksum-atom "Bad atom, ~x0"
                       x)
                   0)))))

(defconst *fchecksum-obj-stack-bound-init*

; This is a stack size bound used by fchecksum-obj and fchecksum-obj2.  It is
; somewhat arbitrary; feel free to change it.

  10000)

#-acl2-loop-only
(defvar *fchecksum-obj-stack-bound*
  *fchecksum-obj-stack-bound-init*)

(mutual-recursion

(defun fchecksum-obj2 (x)

; Warning: Keep this in sync with fchecksum-obj.

  (declare (xargs :guard t))
  (the (signed-byte 32)
       #+acl2-loop-only
       (fchecksum-obj x)
       #-acl2-loop-only
       (cond
        ((atom x)
         (fchecksum-atom x))
        ((zerop *fchecksum-obj-stack-bound*)
         (let* ((car-code (fchecksum-obj2 (car x)))
                (cdr-code (fchecksum-obj2 (cdr x)))
                (car-scramble
                 (times-mod-m31 car-code 627718124))
                (cdr-scramble
                 (times-mod-m31 cdr-code 278917287)))
           (declare (type (signed-byte 32)
                          car-code cdr-code car-scramble cdr-scramble))
           (logxor car-scramble cdr-scramble)))
        (t (let ((*fchecksum-obj-stack-bound*
                  (1- *fchecksum-obj-stack-bound*)))
             (fchecksum-obj x))))))

(defun fchecksum-obj (x)

; Warning: Keep this in sync with fchecksum-obj2 (see comment below).

; Finally, we just use the same idea to scramble cars and cdrs on conses.  To
; make this efficient on structure-shared objects, it ought to be memoized.  We
; do this explicitly in memoize-raw.lisp (for ACL2h).

; However, Keshav Kini has pointed out that community book
; books/centaur/aignet/rwlib.lisp fails to certify using checksums, because of
; a stack overflow.  We address this problem by introducing function
; fchecksum-obj2, which is essentially the same function but won't be memoized.
; Fchecksum-obj2 uses a special variable, *fchecksum-obj-stack-bound*, to
; determine whether to hop back to the memoized function (fchecksum-obj) or
; stay in the unmemoized function (fchecksum-obj2).

; We have considered making this partially tail-recursive, but this would ruin
; memoization.  If we find performance problems we could consider having such a
; version of fchecksum-obj, perhaps passing state into check-sum-obj to decide
; when to call it.

  (declare (xargs :guard t))
  (the (signed-byte 32)
       (cond
        ((atom x)
         (fchecksum-atom x))
        (t
         (let* ((car-code (fchecksum-obj2 (car x)))
                (cdr-code (fchecksum-obj2 (cdr x)))
                (car-scramble
                 (times-mod-m31 car-code 627718124))
                (cdr-scramble
                 (times-mod-m31 cdr-code 278917287)))
           (declare (type (signed-byte 32)
                          car-code cdr-code car-scramble cdr-scramble))
           (logxor car-scramble cdr-scramble))))))
)

#-acl2-loop-only
(declaim (notinline check-sum-obj)) ; see comment below for old code

(defun check-sum-obj (obj)
  (declare (xargs :guard t))
  #-acl2-loop-only
  (setq *fchecksum-obj-stack-bound* *fchecksum-obj-stack-bound-init*)
  (fchecksum-obj obj))

; ; To use old check-sum-obj code, but then add check-sum-obj to
; ; *INITIAL-PROGRAM-FNS-WITH-RAW-CODE* if doing this for a build:
; (defun check-sum-obj (obj)
;   #-acl2-loop-only
;   (return-from check-sum-obj
;                (mv-let (val state)
;                        (old-check-sum-obj obj *the-live-state*)
;                        (declare (ignore state))
;                        val))
;   #+acl2-loop-only
;   (declare (ignore obj))
;   (er hard 'check-sum-obj "ran *1* code for check-sum-obj"))

; Here are some examples.  Warning: in raw Lisp, set
; *fchecksum-obj-stack-bound* to a very large value (say, 10000000) before
; running these examples.
;
;  (fchecksum-obj 0)
;  (fchecksum-obj 19)
;  (fchecksum-obj 1892)
;  (fchecksum-obj "foo")
;  (fchecksum-obj "bfdkja")
;  (fchecksum-obj #\a)
;  (fchecksum-obj "a")
;  (fchecksum-obj #\b)
;  (fchecksum-obj #\c)
;  (fchecksum-obj 189)
;  (fchecksum-obj -189)
;  (fchecksum-obj -19189)
;  (fchecksum-obj -19283/188901)
;  (fchecksum-obj 19283/188901)
;  (fchecksum-obj 19283/2)
;  (fchecksum-obj 2/19283)
;  (fchecksum-obj 19283)
;  (fchecksum-obj #c(19283 198))
;  (fchecksum-obj #c(198 19283))
;  (fchecksum-obj #c(-19283/1238 198))
;
;  (fchecksum-obj 3)
;  (fchecksum-obj '(3 . nil))
;  (fchecksum-obj '(nil . 3))
;
;  (fchecksum-obj nil)
;  (fchecksum-obj '(nil))
;  (fchecksum-obj '(nil nil))
;  (fchecksum-obj '(nil nil nil))
;  (fchecksum-obj '(nil nil nil nil))
;
; ; And here are some additional comments.  If you want to generate more
; ; primitive roots, or verify that the ones we have picked are primitive roots,
; ; try this:
;
;  (include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system)
;  (include-book "std/testing/assert-bang" :dir :system)
;
; ; Here we establish that the factors of M31-1 are 2, 3, 7, 11, 31, 151, and
; ; 331.
;
;  (assert! (equal (- #x7FFFFFFF 1)
;                  (* 2 3 3 7 11 31 151 331)))
;
; ;; And so the following is sufficient to establish that n is a primitive
; ;; root.
;
; (defund primitive-root-p (n)
;   (let* ((m31   #x7FFFFFFF)
;          (m31-1 (- m31 1)))
;     (and (not (equal (mod-expt-fast n (/ m31-1 2) m31) 1))
;          (not (equal (mod-expt-fast n (/ m31-1 3) m31) 1))
;          (not (equal (mod-expt-fast n (/ m31-1 7) m31) 1))
;          (not (equal (mod-expt-fast n (/ m31-1 11) m31) 1))
;          (not (equal (mod-expt-fast n (/ m31-1 31) m31) 1))
;          (not (equal (mod-expt-fast n (/ m31-1 151) m31) 1))
;          (not (equal (mod-expt-fast n (/ m31-1 331) m31) 1)))))
;
; ; And here are some primitive roots that we found.  There are lots of
; ; them.  If you want a new one, just pick a number and start incrementing
; ; or decrementing until it says T.
;
;  (primitive-root-p 506249751)
;  (primitive-root-p 392894102)
;  (primitive-root-p 938187814)
;  (primitive-root-p 718273893)
;  (primitive-root-p 619823821)
;  (primitive-root-p 283748912)
;  (primitive-root-p 111298397)
;  (primitive-root-p 391892127)
;  (primitive-root-p 18783723)
;  (primitive-root-p 981827319)
;
;  (primitive-root-p 627718124)
;  (primitive-root-p 278917287)
;
; ; At one point I [Jared] used this function to analyze different
; ; implementations of fchecksum-natural.  You might find it useful if you want
; ; to write an alternate implementation.  You want to produce a fast routine
; ; that doesn't have many collisions.
;
; (defun analyze-fchecksum-natural (n)
;   (let (table ones twos more)
;     ;; Table is a mapping from sums to the number of times they are hit.
;     (setq table (make-hash-table))
;     (loop for i from 1 to n do
;           (let ((sum (fchecksum-natural i)))
;             (setf (gethash sum table)
;                   (+ 1 (nfix (gethash sum table))))))
;     ;; Now we will walk the table and see how many sums are hit once,
;     ;; twice, or more often than that.
;     (setq ones 0)
;     (setq twos 0)
;     (setq more 0)
;     (maphash (lambda (key val)
;                (declare (ignore key))
;                (cond ((= val 1) (incf ones val))
;                      ((= val 2) (incf twos val))
;                      (t         (incf more val))))
;              table)
;     (format t "~a~%" (list ones twos more))
;     (format t "Unique mappings: ~5,2F%~%"
;             (* 100 (/ (coerce ones 'float) n)))
;     (format t "2-ary collisions: ~5,2F%~%"
;             (* 100 (/ (coerce twos 'float) n)))
;     (format t "3+-ary collisions: ~5,2F%~%"
;             (* 100 (/ (coerce more 'float) n)))))
;
;  (analyze-fchecksum-natural 1000)
;  (analyze-fchecksum-natural 10000)
;  (analyze-fchecksum-natural 100000)
;  (analyze-fchecksum-natural 1000000)
;  (analyze-fchecksum-natural 10000000)

; End of checksum code.

(defun read-file-iterate (channel acc state)
  (mv-let (eof obj state)
    (read-object channel state)
    (cond (eof
           (mv (reverse acc) state))
          (t (read-file-iterate channel (cons obj acc) state)))))

(defun read-file (name state)
  (mv-let (channel state)
    (open-input-channel name :object state)
    (cond (channel
           (mv-let (ans state)
             (read-file-iterate channel nil state)
             (pprogn (close-input-channel channel state)
                     (mv nil ans state))))
          (t (er soft 'read-file "No file found ~x0." name)))))

(defun formals (fn w)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp w))))
  (let ((temp (getpropc fn 'formals t w)))
    (cond ((eq temp t)
           (er hard? 'formals
               "Every function symbol is supposed to have a 'FORMALS property ~
                but ~x0 does not!"
               fn))
          (t temp))))

(defun plist-worldp-with-formals (alist)

; This function is like the system function PLIST-WORLDP except that here we
; additionally require that every FORMALS property have either a true-list or
; *ACL2-PROPERTY-UNBOUND* as its value.  This is used in the guards for ARITY
; and TERMP.  We expect this function to hold on (w state).

  (declare (xargs :guard t))
  (cond ((atom alist) (eq alist nil))
        (t (and (consp (car alist))
                (symbolp (car (car alist)))
                (consp (cdr (car alist)))
                (symbolp (cadr (car alist)))
                (or (not (eq (cadr (car alist)) 'FORMALS))
                    (eq (cddr (car alist)) *ACL2-PROPERTY-UNBOUND*)
                    (true-listp (cddr (car alist))))
                (plist-worldp-with-formals (cdr alist))))))

(defun arity (fn w)
  (declare (xargs :guard (and (or (and (consp fn)
                                       (consp (cdr fn))
                                       (true-listp (cadr fn)))
                                  (symbolp fn))
                              (plist-worldp-with-formals w))))
  (cond ((flambdap fn) (length (lambda-formals fn)))
        (t (let ((temp (getpropc fn 'formals t w)))
             (cond ((eq temp t) nil)
                   (t (length temp)))))))

(defun symbol-class (sym wrld)

; The symbol-class of a symbol is one of three keywords:

; :program               - not defined within the logic
; :ideal                 - defined in the logic but not known to be CL compliant
; :common-lisp-compliant - defined in the logic and known to be compliant with
;                          Common Lisp

; Convention: We never print the symbol-classes to the user.  We would prefer
; the user not to think about these classes per se.  It encourages a certain
; confusion, we think, because users want everything to be
; common-lisp-compliant and start thinking of it as a mode, sort of like "super
; :logic" or something.  So we are keeping these names to ourselves by not
; using them in error messages and documentation.  Typically used English
; phrases are such and such is "compliant with Common Lisp" or "is not known to
; be compliant with Common Lisp."

; Historical Note: :Program function symbols were once called "red", :ideal
; symbols were once called "blue", and :common-lisp-compliant symbols were once
; called "gold."

; Before we describe the storage scheme, let us make a few observations.
; First, most function symbols have the :program symbol-class, because until
; ACL2 is admitted into the logic, the overwhelming majority of the function
; symbols will be system functions.  Second, all :logic function symbols have
; symbol-class :ideal or :common-lisp-compliant.  Third, this function,
; symbol-class, is most often applied to :logic function symbols, because most
; often we use it to sweep through the function symbols in a term before
; verify-guards.  Finally, theorem names are very rarely of interest here but
; they are always either :ideal or (very rarely) :common-lisp-compliant.

; Therefore, our storage scheme is that every :logic function will have a
; symbol-class property that is either :ideal or :common-lisp-compliant.  We
; will not store a symbol-class property for :program but just rely on the
; absence of the property (and the fact that the symbol is recognized as a
; function symbol) to default its symbol-class to :program.  Thus, system
; functions take no space but are slow to answer.  Finally, theorems will
; generally have no stored symbol-class (so it will default to :ideal for them)
; but when it is stored it will be :common-lisp-compliant.

; Note that the defun-mode of a symbol is actually determined by looking at its
; symbol-class.  We only store the symbol-class.  That is more often the
; property we need to look at.  But we believe it is simpler for the user to
; think in terms of :mode and :verify-guards.

  (declare (xargs :guard (and (symbolp sym)
                              (plist-worldp wrld))))
  (if (eq sym 'cons) ; optimization
      :COMMON-LISP-COMPLIANT
    (or (getpropc sym 'symbol-class nil wrld)
        (if (getpropc sym 'theorem nil wrld)
            :ideal
          :program))))

(defmacro fdefun-mode (fn wrld)

; Fn must be a symbol and a function-symbol of wrld.

  `(if (eq (symbol-class ,fn ,wrld) :program)
       :program
       :logic))

(defun defun-mode (name wrld)

; Only function symbols have defun-modes.  For all other kinds of names
; e.g., package names and macro names, the "defun-mode" is nil.

; Implementation Note:  We do not store the defun-mode of a symbol on the
; property list of the symbol.  We compute the defun-mode from the symbol-class.

  (declare (xargs :guard (plist-worldp wrld)))
  (cond ((and (symbolp name)
              (function-symbolp name wrld))
         (fdefun-mode name wrld))
        (t nil)))

(defun arities-okp (user-table w)
  (declare (xargs :guard (and (symbol-alistp user-table)
                              (plist-worldp-with-formals w))))
  (cond
   ((endp user-table) t)
   (t (and (equal (arity (car (car user-table)) w)
                  (cdr (car user-table)))
           (logicp (car (car user-table)) w)
           (arities-okp (cdr user-table) w)))))

(table user-defined-functions-table nil nil
       :guard
       (and (symbolp val)
            (case key
              ((untranslate untranslate-lst)
               (equal (length (getpropc val 'formals nil world))
                      (length (getpropc key 'formals nil world))))
              (untranslate-preprocess
               (equal (length (getpropc val 'formals nil world))
                      2))
              (otherwise nil))
            (equal (getpropc val 'stobjs-out '(nil) world)
                   '(nil))))

(defrec def-body

; Use the 'recursivep property, not this :recursivep field, when referring to
; the original definition, as is necessary for verify-guards,
; verify-termination, and handling of *1* functions.

  ((nume
    hyp ; nil if there are no hypotheses
    .
    concl)
   equiv
   .
   (recursivep formals rune . controller-alist))
  t)

(defun latest-body (fncall hyp concl)
  (if hyp
      (fcons-term* 'if hyp concl
                   (fcons-term* 'hide fncall))
    concl))

(defun def-body (fn wrld)
  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp wrld)
                              (true-listp (getpropc fn 'def-bodies nil wrld)))))
  (car (getpropc fn 'def-bodies nil wrld)))

(defun body (fn normalp w)

; WARNING: Fn can be either a function symbol of w or a lambda, but in the
; former case fn should in :logic mode.  The requirement is actually a bit
; looser: fn can be a :program mode function symbol if fn is not built-in and
; normalp is nil.  But if fn is a built-in :program mode function symbol, we do
; not store even its 'unnormalized-body property; when we tried modifying
; defuns-fn-short-cut to store that property even when boot-strap-flg is true,
; we saw nearly a 9% increase in image size for SBCL, and nearly 13% for CCL.
; Consider using cltl-def-from-name or related functions if fn is in :program
; mode.

; The safe way to call this function is with normalp = nil, which yields the
; actual original body of fn.  The normalized body is provably equal to the
; unnormalized body, but that is not a strong enough property in some cases.
; Consider for example the following definition: (defun foo () (car 3)).  Then
; (body 'foo nil (w state)) is (CAR '3), so guard verification for foo will
; fail, as it should.  But (body 'foo t (w state)) is 'NIL, so we had better
; scan the unnormalized body when generating the guard conjecture rather than
; the normalized body.  Functional instantiation may also be problematic if
; constraints are gathered using the normalized body, although we do not yet
; have an example showing that this is critical.

; WARNING: If normalp is non-nil, then we are getting the most recent body
; installed by a :definition rule with non-nil :install-body value.  Be careful
; that this is really what is desired; and if so, be aware that we are not
; returning the corresponding def-body rune.

  (cond ((flambdap fn)
         (lambda-body fn))
        (normalp (let ((def-body (def-body fn w)))
                   (cond
                    ((not (eq (access def-body def-body :equiv)
                              'equal))

; The application of fn to its formals can fail to be equal to its body in all
; such cases, so we revert to the unnormalized body.  An alternative could be
; to define the function def-body to find the most recent body that has 'equal
; as its :equal, rather than the recent body unconditionally.  But then, since
; we want :expand hints to use the latest body even if :equiv is not 'equal, we
; could have three different bodies in use at a given time (unnormalized,
; latest normalized, and latest normalized with :equiv = equal), and that just
; seems potentially too confusing.  Instead, our story will be that the body is
; always either the latest body or the (original) unnormalized body.

                     (getpropc fn 'unnormalized-body nil w))
                    (t (latest-body (fcons-term fn
                                                (access def-body def-body
                                                        :formals))
                                    (access def-body def-body :hyp)
                                    (access def-body def-body :concl))))))
        (t (getpropc fn 'unnormalized-body nil w))))

; Rockwell Addition: Consider the guard conjectures for a stobj-using
; function.  Every accessor and updater application will generate the
; obligation to prove (stp st), where stp is the recognizer for the
; stobj st.  But this is guaranteed to be true for bodies that have
; been translated as defuns, because of the syntactic restrictions on
; stobjs.  So in this code we are concerned with optimizing these
; stobj recognizer expressions away, by replacing them with T.

(defun get-stobj-recognizer (stobj wrld)

; If stobj is a stobj name, return the name of its recognizer; else nil.  The
; value of the 'stobj property is always (*the-live-var* recognizer creator
; ...), for all user defined stobj names.  The value is '(*the-live-state*) for
; STATE and is nil for all other names.

  (cond ((eq stobj 'state)
         'state-p)
        (t (cadr (getpropc stobj 'stobj nil wrld)))))

(defun stobj-recognizer-terms (known-stobjs wrld)

; Given a list of stobjs, return the list of recognizer applications.
; E.g., given (STATE MY-ST) we return ((STATE-P STATE) (MY-STP MY-ST)).

  (cond ((endp known-stobjs) nil)
        (t (cons (fcons-term* (get-stobj-recognizer (car known-stobjs) wrld)
                              (car known-stobjs))
                 (stobj-recognizer-terms (cdr known-stobjs) wrld)))))

(defun mcons-term-smart (fn args)

; The following function is guaranteed to create a term provably equal to (cons
; fn args).  If we find other optimizations to make here, we should feel free
; to do so.

  (if (and (eq fn 'if)
           (equal (car args) *t*))
      (cadr args)
    (cons-term fn args)))

(mutual-recursion

(defun optimize-stobj-recognizers1 (known-stobjs recog-terms term)
  (cond
   ((variablep term) term)
   ((fquotep term) term)
   ((flambda-applicationp term)

; We optimize the stobj recognizers in the body of the lambda.  We do
; not have to watch out of variable name changes, since if a stobj
; name is passed into a lambda it is passed into a local of the same
; name.  We need not optimize the body if no stobj name is used as a
; formal.  But we have to optimize the args in either case.

    (let ((formals (lambda-formals (ffn-symb term)))
          (body (lambda-body (ffn-symb term))))
      (cond
       ((intersectp-eq known-stobjs formals)
        (fcons-term
         (make-lambda formals
                      (optimize-stobj-recognizers1
                       known-stobjs
                       recog-terms
                       body))
         (optimize-stobj-recognizers1-lst known-stobjs
                                          recog-terms
                                          (fargs term))))
       (t (fcons-term (ffn-symb term)
                      (optimize-stobj-recognizers1-lst known-stobjs
                                                       recog-terms
                                                       (fargs term)))))))
   ((and (null (cdr (fargs term)))
         (member-equal term recog-terms))

; If the term is a recognizer call, e.g., (MY-STP MY-ST), we replace
; it by T.  The first conjunct above is just a quick test: If the term
; has 2 or more args, then don't bother to do the member-equal.  If
; the term has 1 or 0 (!) args we do.  We won't find it if it has 0
; args.

    *t*)
   (t (mcons-term-smart (ffn-symb term)
                        (optimize-stobj-recognizers1-lst known-stobjs
                                                         recog-terms
                                                         (fargs term))))))

(defun optimize-stobj-recognizers1-lst (known-stobjs recog-terms lst)
  (cond
   ((endp lst) nil)
   (t (cons (optimize-stobj-recognizers1 known-stobjs recog-terms (car lst))
            (optimize-stobj-recognizers1-lst known-stobjs
                                             recog-terms
                                             (cdr lst)))))))

(defun optimize-stobj-recognizers (known-stobjs term wrld)

; Term is a term.  We scan it and find every call of the form (st-p
; st) where st is a member of known-stobjs and st-p is the stobj
; recognizer function for st.  We replace each such call by T.  The
; idea is that we have simplified term under the assumption that each
; (st-p st) is non-nil.  This simplification preserves equivalence
; with term PROVIDED all stobj recognizers are Boolean valued!

  (cond
   ((null known-stobjs) term)
   (t (optimize-stobj-recognizers1
       known-stobjs
       (stobj-recognizer-terms known-stobjs wrld)
       term))))

; Rockwell Addition: The new flag, stobj-optp, determines whether the
; returned guard has had all the stobj recognizers optimized away.  Of
; course, whether you should call this with stobj-optp t or nil
; depends on the expression you're exploring: if it has been suitably
; translated, you can use t, else you must use nil.  Every call of
; guard (and all the functions that call those) has been changed to
; pass down this flag.  I won't mark every such place, but they'll
; show up in the compare-windows.

(defun guard (fn stobj-optp w)

; This function is just the standard way to obtain the guard of fn in
; world w.

; If stobj-optp is t, we optimize the returned term, simplifying it
; under the assumption that every stobj recognizer in it is true.  If
; fn traffics in stobjs, then it was translated under the stobj
; syntactic restrictions.  Let st be a known stobj for fn (i.e.,
; mentioned in its stobjs-in) and let st-p be the corresponding
; recognizer.  This function should only be called with stobj-optp = t
; if you know (st-p st) to be true in the context of that call.

; The documentation string below addresses the general notion of
; guards in ACL2, rather than explaining this function.

  (cond ((flambdap fn) *t*)
        ((or (not stobj-optp)
             (all-nils (stobjs-in fn w)) )
         (getpropc fn 'guard *t* w))
        (t

; If we have been told to optimize the stobj recognizers (stobj-optp =
; t) and there are stobjs among the arguments of fn, then fn was
; translated with the stobj syntactic restrictions enforced for those
; names.  That means we can optimize the guard of the function
; appropriately.

         (optimize-stobj-recognizers
          (collect-non-x 'nil (stobjs-in fn w))
          (or (getpropc fn 'guard *t* w)

; Once upon a time we found a guard of nil, and it took awhile to track down
; the source of the ensuing error.

              (illegal 'guard "Found a nil guard for ~x0."
                       (list (cons #\0 fn))))
          w))))

(defun guard-lst (fns stobj-optp w)
  (cond ((null fns) nil)
        (t (cons (guard (car fns) stobj-optp w)
                 (guard-lst (cdr fns) stobj-optp w)))))

(defmacro equivalence-relationp (fn w)

; See the Essay on Equivalence, Refinements, and Congruence-based
; Rewriting.

; (Note: At the moment, the fact that fn is an equivalence relation is
; encoded merely by existence of a non-nil 'coarsenings property.  No
; :equivalence rune explaining why fn is an equivalence relation is to
; be found there -- though such a rune does exist and is indeed found
; among the 'congruences of fn itself.  We do not track the use of
; equivalence relations, we just use them anonymously.  It would be
; good to track them and report them.  When we do that, read the Note
; on Tracking Equivalence Runes in subst-type-alist1.)

  `(let ((fn ,fn))

; While both equal and iff have non-nil coarsenings properties, we make
; special cases of them here because they are common and we wish to avoid
; the getprop.

     (or (eq fn 'equal)
         (eq fn 'iff)
         (and (not (flambdap fn))
              (getpropc fn 'coarsenings nil ,w)))))

(defun >=-len (x n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (= n 0)
      t
      (if (atom x)
          nil
          (>=-len (cdr x) (1- n)))))

(defun all->=-len (lst n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (atom lst)
      (eq lst nil)
      (and (>=-len (car lst) n)
           (all->=-len (cdr lst) n))))

(defun strip-cadrs (x)
  (declare (xargs :guard (all->=-len x 2)))
  (cond ((endp x) nil)
        (t (cons (cadar x) (strip-cadrs (cdr x))))))

; Rockwell Addition: Just moved from other-events.lisp

(defun strip-cddrs (x)
  (declare (xargs :guard (all->=-len x 2)))
  (cond ((endp x) nil)
        (t (cons (cddar x) (strip-cddrs (cdr x))))))

(defun global-set-lst (alist wrld)
  (cond ((null alist) wrld)
        (t (global-set-lst (cdr alist)
                           (global-set (caar alist)
                                       (cadar alist)
                                       wrld)))))

(defmacro cons-term1-body-mv2 ()
  `(let ((x (unquote (car args)))
         (y (unquote (cadr args))))
     (let ((evg (case fn
                  ,@*cons-term1-alist*
                  (if (kwote (if x y (unquote (caddr args)))))
                  (not (kwote (not x))))))
       (cond (evg (mv t evg))
             (t (mv nil form))))))

(defun cons-term1-mv2 (fn args form)
  (declare (xargs :guard (and (pseudo-term-listp args)
                              (quote-listp args))))
  (cons-term1-body-mv2))

(mutual-recursion

(defun sublis-var1 (alist form)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-term-listp (strip-cdrs alist))
                              (pseudo-termp form))))
  (cond ((variablep form)
         (let ((a (assoc-eq form alist)))
           (cond (a (mv (not (eq form (cdr a)))
                        (cdr a)))
                 (t (mv nil form)))))
        ((fquotep form)
         (mv nil form))
        (t (mv-let (changedp lst)
                   (sublis-var1-lst alist (fargs form))
                   (let ((fn (ffn-symb form)))
                     (cond (changedp (mv t (cons-term fn lst)))
                           ((and (symbolp fn) ; optimization
                                 (quote-listp lst))
                            (cons-term1-mv2 fn lst form))
                           (t (mv nil form))))))))

(defun sublis-var1-lst (alist l)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-term-listp (strip-cdrs alist))
                              (pseudo-term-listp l))))
  (cond ((endp l)
         (mv nil l))
        (t (mv-let (changedp1 term)
                   (sublis-var1 alist (car l))
                   (mv-let (changedp2 lst)
                           (sublis-var1-lst alist (cdr l))
                           (cond ((or changedp1 changedp2)
                                  (mv t (cons term lst)))
                                 (t (mv nil l))))))))
)

(defun sublis-var (alist form)

; If you are tempted to call this function with alist = nil to put form into
; quote-normal form, consider calling quote-normal-form instead.

  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-term-listp (strip-cdrs alist))
                              (pseudo-termp form))))
  (mv-let (changedp val)
          (sublis-var1 alist form)
          (declare (ignore changedp))
          val))

(defun sublis-var-lst (alist l)
  (declare (xargs :guard (and (symbol-alistp alist)
                              (pseudo-term-listp (strip-cdrs alist))
                              (pseudo-term-listp l))))
  (mv-let (changedp val)
          (sublis-var1-lst alist l)
          (declare (ignore changedp))
          val))

(defun subcor-var1 (vars terms var)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-term-listp terms)
                              (equal (length vars) (length terms))
                              (variablep var))))
  (cond ((endp vars) var)
        ((eq var (car vars)) (car terms))
        (t (subcor-var1 (cdr vars) (cdr terms) var))))

(mutual-recursion

(defun subcor-var (vars terms form)

; "Subcor" stands for "substitute corresponding elements".  Vars and terms are
; in 1:1 correspondence, and we substitute terms for corresponding vars into
; form.  This function was called sub-pair-var in nqthm.

  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-term-listp terms)
                              (equal (length vars) (length terms))
                              (pseudo-termp form))))
  (cond ((variablep form)
         (subcor-var1 vars terms form))
        ((fquotep form) form)
        (t (cons-term (ffn-symb form)
                      (subcor-var-lst vars terms (fargs form))))))

(defun subcor-var-lst (vars terms forms)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-term-listp terms)
                              (equal (length vars) (length terms))
                              (pseudo-term-listp forms))))
  (cond ((endp forms) nil)
        (t (cons (subcor-var vars terms (car forms))
                 (subcor-var-lst vars terms (cdr forms))))))

)

; We now develop the code to take a translated term and "untranslate"
; it into something more pleasant to read.

(defun make-reversed-ad-list (term ans)

; We treat term as a CAR/CDR nest around some ``base'' and return (mv ad-lst
; base), where ad-lst is the reversed list of #\A and #\D characters and base
; is the base of the CAR/CDR nest.  Thus, (CADDR B) into (mv '(#\D #\D #\A) B).
; If term is not a CAR/CDR nest, adr-lst is nil.

  (cond ((variablep term)
         (mv ans term))
        ((fquotep term)
         (mv ans term))
        ((eq (ffn-symb term) 'CAR)
         (make-reversed-ad-list (fargn term 1) (cons '#\A ans)))
        ((eq (ffn-symb term) 'CDR)
         (make-reversed-ad-list (fargn term 1) (cons '#\D ans)))
        (t (mv ans term))))

(defun car-cdr-abbrev-name (adr-lst)

; Given an adr-lst we turn it into one of the CAR/CDR abbreviation names.  We
; assume the adr-lst corresponds to a legal name, e.g., its length is no
; greater than five (counting the #\R).

  (intern (coerce (cons #\C adr-lst) 'string) "ACL2"))

(defun pretty-parse-ad-list (ad-list dr-list n base)
  (cond
   ((eql n 5)
    (pretty-parse-ad-list ad-list '(#\R) 1
                          (list (car-cdr-abbrev-name dr-list) base)))
   ((endp ad-list)
    (cond ((eql n 1) base)
          (t (list (car-cdr-abbrev-name dr-list) base))))
   ((eql (car ad-list) #\A)
    (pretty-parse-ad-list (cdr ad-list) '(#\R) 1
                          (list (car-cdr-abbrev-name (cons #\A dr-list)) base)))
   (t ; (eql (car ad-list) '#\D)
    (pretty-parse-ad-list (cdr ad-list) (cons #\D dr-list) (+ 1 n) base))))

(defun untranslate-car-cdr-nest (term)

; This function is not actually used, but it illustrates how car-cdr nests are
; untranslated.  See community book books/system/untranslate-car-cdr.lisp for
; documentation and a correctness proof.

; Examples:
; (untranslate-car-cdr-nest '(car (cdr (car b))))
; ==> (CADR (CAR B))
; (untranslate-car-cdr-nest '(car (cdr (cdr b))))
; ==> (CADDR B)
; (untranslate-car-cdr-nest '(car (car (cdr (cdr b)))))
; ==> (CAR (CADDR B))

  (mv-let (ad-list base)
          (make-reversed-ad-list term nil)
          (cond
           ((null ad-list) base)
           (t (pretty-parse-ad-list ad-list '(#\R) 1 base)))))

(defun collect-non-trivial-bindings (vars vals)
  (cond ((null vars) nil)
        ((eq (car vars) (car vals))
         (collect-non-trivial-bindings (cdr vars) (cdr vals)))
        (t (cons (list (car vars) (car vals))
                 (collect-non-trivial-bindings (cdr vars) (cdr vals))))))

(defun untranslate-and (p q iff-flg)

; The following theorem illustrates the theorem:

; (thm (equal (and p (and q1 q2)) (and p q1 q2)))

; We formerly also gave special treatment corresponding to the cases (equal
; (and t q) q) and (iff (and p t) p).  But we stopped doing so after
; Version_8.2, when Stephen Westfold pointed out the confusion arising in the
; proof-builder after rewriting a subterm, tst, to t, in a term (and tst x2),
; i.e., (if tst x2 'nil).  A similar problem occurs for (and x2 tst).

; Warning: Keep this in sync with and-addr.

  (declare (ignore iff-flg))
  (cond ((and (consp q)
              (eq (car q) 'and))
         (cons 'and (cons p (cdr q))))
        (t (list 'and p q))))

(defun untranslate-or (p q)

; The following theorem illustrates the various cases:
; (thm (equal (or p (or q1 q2)) (or p q1 q2))))

  (cond ((and (consp q)
              (eq (car q) 'or))
         (cons 'or (cons p (cdr q))))
        (t (list 'or p q))))

(defun case-length (key term)

; Key is either nil or a variablep symbol.  Term is a term.  We are
; imagining printing term as a case on key.  How long is the case
; statement?  Note that every term can be printed as (case key
; (otherwise term)) -- a case of length 1.  If key is nil we choose it
; towards extending the case-length.

  (case-match term
              (('if ('equal key1 ('quote val)) & y)
               (cond ((and (if (null key)
                               (variablep key1)
                             (eq key key1))
                           (eqlablep val))
                      (1+ (case-length key1 y)))
                     (t 1)))
              (('if ('eql key1 ('quote val)) & y)
               (cond ((and (if (null key)
                               (variablep key1)
                             (eq key key1))
                           (eqlablep val))
                      (1+ (case-length key1 y)))
                     (t 1)))
              (('if ('member key1 ('quote val)) & y)
               (cond ((and (if (null key)
                               (variablep key1)
                             (eq key key1))
                           (eqlable-listp val))
                      (1+ (case-length key1 y)))
                     (t 1)))
              (& 1)))

; And we do a similar thing for cond...

(defun cond-length (term)
  (case-match term
              (('if & & z) (1+ (cond-length z)))
              (& 1)))

; In general the following list should be set to contain all the boot-strap
; functions that have boolean type set.

(defconst *untranslate-boolean-primitives*
  '(equal))

(defun right-associated-args (fn term)

; Fn is a function symbol of two arguments.  Term is a call of fn.
; E.g., fn might be 'BINARY-+ and term might be '(BINARY-+ A (BINARY-+
; B C)).  We return the list of arguments in the right-associated fn
; nest, e.g., '(A B C).

  (let ((arg2 (fargn term 2)))
    (cond ((and (nvariablep arg2)
                (not (fquotep arg2))
                (eq fn (ffn-symb arg2)))
           (cons (fargn term 1) (right-associated-args fn arg2)))
          (t (fargs term)))))

(defun dumb-negate-lit (term)
  (declare (xargs :guard (pseudo-termp term)))
  (cond ((variablep term)
         (fcons-term* 'not term))
        ((fquotep term)
         (cond ((equal term *nil*) *t*)
               (t *nil*)))
        ((eq (ffn-symb term) 'not)
         (fargn term 1))
        ((and (eq (ffn-symb term) 'equal)
              (or (equal (fargn term 2) *nil*)
                  (equal (fargn term 1) *nil*)))
         (if (equal (fargn term 2) *nil*)
             (fargn term 1)
             (fargn term 2)))
        (t (fcons-term* 'not term))))

(defun dumb-negate-lit-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (dumb-negate-lit (car lst))
                 (dumb-negate-lit-lst (cdr lst))))))

(mutual-recursion

(defun term-stobjs-out-alist (vars args alist wrld)
  (if (endp vars)
      nil
    (let ((st (term-stobjs-out (car args) alist wrld))
          (rest (term-stobjs-out-alist (cdr vars) (cdr args) alist wrld)))
      (if (and st (symbolp st))
          (acons (car vars) st rest)
        rest))))

(defun term-stobjs-out (term alist wrld)

; Warning: This function currently has heuristic application only.  We need to
; think harder about it if we are to rely on it for soundness.

  (cond
   ((variablep term)
    (or (cdr (assoc term alist))
        (and (getpropc term 'stobj nil wrld)
             term)))
   ((fquotep term)
    nil)
   ((eq (ffn-symb term) 'return-last)
    (term-stobjs-out (car (last (fargs term))) alist wrld))
   (t (let ((fn (ffn-symb term)))
        (cond
         ((member-eq fn '(nth mv-nth))
          (let* ((arg1 (fargn term 1))
                 (n (and (quotep arg1) (cadr arg1))))
            (and (integerp n)
                 (<= 0 n)
                 (let ((term-stobjs-out
                        (term-stobjs-out (fargn term 2) alist wrld)))
                   (and (consp term-stobjs-out)
                        (nth n term-stobjs-out))))))
         ((eq fn 'update-nth)
          (term-stobjs-out (fargn term 3) alist wrld))
         ((flambdap fn) ; (fn args) = ((lambda vars body) args)
          (let ((vars (lambda-formals fn))
                (body (lambda-body fn)))
            (term-stobjs-out body
                             (term-stobjs-out-alist vars (fargs term) alist wrld)
                             wrld)))
         ((eq fn 'if)
          (or (term-stobjs-out (fargn term 2) alist wrld)
              (term-stobjs-out (fargn term 3) alist wrld)))
         (t
          (let ((lst (stobjs-out fn wrld)))
            (cond ((and (consp lst) (null (cdr lst)))
                   (car lst))
                  (t lst)))))))))
)

(defun accessor-root (n term wrld)

; When term is a stobj name, say st, ac is the accessor function for st defined
; to return (nth n st), then untranslate maps (nth n st) to (nth *ac* st).
; The truth is that the 'accessor-names property of st is used to carry this
; out.  Update-nth gets similar consideration.

; But what about (nth 0 (run st n)), where run returns a stobj st?  Presumably
; we would like to print that as (nth *b* (run st n)) where b is the 0th field
; accessor function for st.  We would also like to handle terms such as (nth 1
; (mv-nth 3 (run st n))).  These more general cases are likely to be important
; to making stobj proofs palatable.  There is yet another consideration, which
; is that during proofs, the user may use variable names other than stobj names
; to refer to stobjs.  For example, there may be a theorem of the form
; (... st st0 ...), which could generate a term (nth n st0) during a proof that
; the user would prefer to see printed as (nth *b* st0).

; The present function returns the field name to be returned in place of n when
; untranslating (nth n term) or (update-nth n val term).  Wrld is, of course,
; an ACL2 world.

  (let ((st (term-stobjs-out term
                             (table-alist 'nth-aliases-table wrld)
                             wrld)))
    (and st
         (symbolp st)
         (let ((accessor-names
                (getpropc st 'accessor-names nil wrld)))
           (and accessor-names
                (< n (car (dimensions st accessor-names)))
                (aref1 st accessor-names n))))))

; We define progn! here so that it is available before its call in redef+.  But
; first we define observe-raw-mode-setting, a call of which is laid down by the
; use of f-put-global on 'acl2-raw-mode-p in the definition of progn!.

#-acl2-loop-only
(defun observe-raw-mode-setting (v state)

; We are about to set state global 'acl2-raw-mode-p to v.  We go through some
; lengths here to maintain the values of state globals
; 'raw-include-book-dir-alist and 'raw-include-book-dir!-alist, and warn when
; the value of either of these variables is discarded as we leave raw mode.  We
; are thus violating the semantics of put-global, by sometimes setting these
; two variables when only 'acl2-raw-mode-p is to be set -- but all bets are off
; when using raw mode, so this violation is tolerable.

  (let ((old-raw-mode (f-get-global 'acl2-raw-mode-p state))
        (old-raw-include-book-dir-alist
         (f-get-global 'raw-include-book-dir-alist state))
        (old-raw-include-book-dir!-alist
         (f-get-global 'raw-include-book-dir!-alist state))
        (ctx 'observe-raw-mode-setting))
    (cond
     ((or (iff v old-raw-mode)

; If we are executing a raw-Lisp include-book on behalf of include-book-fn,
; then a change in the status of raw mode is not important, as we will continue
; to maintain and use the values of state globals 'raw-include-book-dir-alist
; and 'raw-include-book-dir!-alist to compute the value of function
; include-book-dir.  The former state global is bound by state-global-let* in
; load-compiled-book, which in turn is called by include-book under
; include-book-fn.  The latter state global is set to an alist value (i.e., not
; :ignore) in include-book-raw-top, which in turn is called when doing early
; loads of compiled files by include-book-top, under include-book-fn, under
; include-book.

          *load-compiled-stack*)
      state)
     ((eq (not old-raw-mode)
          (raw-include-book-dir-p state))

; Clearly the two arguments of iff can't both be nil, since the value of
; 'raw-include-book-dir-alist is not ignored (it is never :ignore) in raw-mode.
; Can they both be t?  Assuming old-raw-mode is nil, then since (iff v
; old-raw-mode) is false, we are about to go into raw mode.  Also, since we are
; not in the previous case, we are not currently under include-book-fn.  But
; since we are currently not in raw mode and not under include-book-fn, we
; expect old-raw-include-book-dir-alist to be :ignore, as per the Essay on
; Include-book-dir-alist: "We maintain the invariant that :ignore is the value
; [of 'include-book-dir-alist] except when in raw-mode or during evaluation of
; include-book-fn."

      (prog2$ (er hard! ctx
                  "Implementation error: Transitioning from ~x0 = ~x1 and yet ~
                   the value of state global variable ~x2 is ~x3!  ~
                   Implementors should see the comment just above this ~
                   message in observe-raw-mode-setting."
                  'acl2-raw-mode-p
                  old-raw-mode
                  'raw-include-book-dir-alist
                  old-raw-include-book-dir-alist)
              state))
     (t
      (let* ((wrld (w state))
             (old-table-include-book-dir-alist
              (cdr (assoc-eq :include-book-dir-alist
                             (table-alist 'acl2-defaults-table wrld))))
             (old-table-include-book-dir!-alist
              (table-alist 'include-book-dir!-table wrld)))
        (pprogn
         (cond
          ((and
            old-raw-mode

; The warning below is probably irrelevant for a context such that
; acl2-defaults-table will ultimately be discarded, because even without
; raw-mode we will be discarding include-book-dir-alist changes.

            (not (acl2-defaults-table-local-ctx-p state))
            (or (not (equal old-raw-include-book-dir-alist
                            old-table-include-book-dir-alist))
                (not (equal old-raw-include-book-dir!-alist
                            old-table-include-book-dir!-alist))))
           (warning$ ctx "Raw-mode"
                     "The set of legal values for the :DIR argument of ~
                      include-book and ld appears to have changed when ~v0 ~
                      was executed in raw-mode.  Changes are being discarded ~
                      as we exit raw-mode."
                     (append
                      (and (not (equal old-table-include-book-dir-alist
                                       old-raw-include-book-dir-alist))
                           '(add-include-book-dir
                             delete-include-book-dir))
                      (and (not (equal old-table-include-book-dir!-alist
                                       old-raw-include-book-dir!-alist))
                           '(add-include-book-dir!
                             delete-include-book-dir!)))))
          (t state))
         (without-interrupts

; By using without-interrupts, we intend to preserve the invariant that the two
; state globals beingn set here are either both :ignore or else neither is
; :ignore.

          (f-put-global 'raw-include-book-dir-alist
                        (cond (old-raw-mode

; We are leaving raw-mode and are not under include-book-fn.

                               :ignore)
                              (t old-table-include-book-dir-alist))
                        state)
          (f-put-global 'raw-include-book-dir!-alist
                        (cond (old-raw-mode

; We are leaving raw-mode and are not under include-book-fn.

                               :ignore)
                              (t old-table-include-book-dir!-alist))
                        state))))))))

#+acl2-loop-only
(defmacro progn! (&rest r)
  (declare (xargs :guard (or (not (symbolp (car r)))
                             (eq (car r) :state-global-bindings))))
  (cond
   ((and (consp r)
         (eq (car r) :state-global-bindings))
    `(state-global-let* ,(cadr r)
                        (progn!-fn ',(cddr r) ',(cadr r) state)))
    (t `(progn!-fn ',r nil state))))

#-acl2-loop-only
(defmacro progn! (&rest r)
  (let ((sym (gensym)))
    `(let ((state *the-live-state*)
           (,sym (f-get-global 'acl2-raw-mode-p *the-live-state*)))
       (declare (ignorable state))
       (unwind-protect
           (progn
             ,@(cond ((eq (car r) :state-global-bindings)
                      (cddr r))
                     (t r)))

; Notice that we don't need to use state-global-let* to protect against the
; possibility that the resetting of acl2-raw-mode-p never gets executed below.
; There are two reasons.  First, ACL2's unwind protection mechanism doesn't
; work except inside the ACL2 loop, and although it may be that we always
; execute progn! forms from (ultimately) inside the ACL2 loop, it is preferable
; not to rely on that assumption.  The other reason is that we assume that
; there are no errors during the execution of r in raw Lisp, since presumably
; the progn! form was already admitted in the loop.  There are flaws in this
; assumption, of course: the user may abort or may be submitting the progn! in
; raw mode (in which case progn!-fn was not executed first).  So we may want to
; revisit the resetting of acl2-raw-mode-p, but in that case we need to
; consider whether we need our solution to work outside the ACL2 loop, and if
; so, then whether it actually does work.

         (f-put-global 'acl2-raw-mode-p ,sym state)))))

; The LD Specials

; The function LD will "bind" some state globals in the sense that it will
; smash their global values and then restore the old values upon completion.
; These state globals are called "LD specials".  The LD read-eval-print loop
; will reference these globals.  The user is permitted to set these globals
; with commands executed in LD -- with the understanding that the values are
; lost when LD is exited and the pop occurs.

; To make it easy to reference them and to ensure that they are set to legal
; values, we will define access and update functions for them.  We define the
; functions here rather than in ld.lisp so that we may use them freely in our
; code.

(defun ld-redefinition-action (state)
  (f-get-global 'ld-redefinition-action state))

(defun chk-ld-redefinition-action (val ctx state)
  (cond ((or (null val)
             (and (consp val)
                  (member-eq (car val) '(:query :warn :doit :warn! :doit!))
                  (member-eq (cdr val) '(:erase :overwrite))))
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-redefinition-action val))))

(defun set-ld-redefinition-action (val state)
  (er-progn
   (chk-ld-redefinition-action val 'set-ld-redefinition-action state)
   (pprogn
    (f-put-global 'ld-redefinition-action val state)
    (value val))))

(defmacro redef nil
 '(set-ld-redefinition-action '(:query . :overwrite) state))

(defmacro redef! nil
 '(set-ld-redefinition-action '(:warn! . :overwrite) state))

(defmacro redef+ nil

; WARNING: Keep this in sync with redef-.

  #-acl2-loop-only
  nil
  #+acl2-loop-only
  `(with-output
    :off (summary event)
    (progn
      (defttag :redef+)
      (progn!
       (set-ld-redefinition-action '(:warn! . :overwrite)
                                   state)
       (program)
       (set-temp-touchable-vars t state)
       (set-temp-touchable-fns t state)
       (f-put-global 'redundant-with-raw-code-okp t state)
       (set-state-ok t)))))

(defmacro redef- nil

; WARNING: Keep this in sync with redef+.

  #-acl2-loop-only
  nil
  #+acl2-loop-only
  `(with-output
    :off (summary event)
    (progn
      (redef+) ; to allow forms below
      (progn! (f-put-global 'redundant-with-raw-code-okp nil state)
              (set-temp-touchable-vars nil state)
              (set-temp-touchable-fns nil state)
              (defttag nil)
              (logic)
              (set-ld-redefinition-action nil state)
              (set-state-ok nil)))))

(defun chk-current-package (val ctx state)
  (cond ((find-non-hidden-package-entry val (known-package-alist state))
         (value nil))
        (t (er soft ctx *ld-special-error* 'current-package val))))

(defun set-current-package (val state)

; This function is equivalent to in-package-fn except for the
; error message generated.

  (er-progn
   (chk-current-package val 'set-current-package state)
   (pprogn
    (f-put-global 'current-package val state)
    (value val))))

(defun defun-for-state-name (name)
  (add-suffix name "-STATE"))

(defmacro error-free-triple-to-state (ctx form)
  (declare (xargs :guard ; really (quotep ctx), but we don't check pseudo-termp
                  (and (consp ctx)
                       (eq (car ctx) 'quote))))
  `(mv-let (erp val state)
     ,form
     (declare (ignore val))
     (prog2$ (and erp (er hard ,ctx
                          "Unexpected error.  An error message may have been ~
                           printed above."))
             state)))

(defmacro defun-for-state (name args)
  `(defun ,(defun-for-state-name name)
       ,args
     (error-free-triple-to-state
      ',name
      (,name ,@args))))

(defun-for-state set-current-package (val state))

(defun standard-oi (state)
  (f-get-global 'standard-oi state))

(defun read-standard-oi (state)

; We let LD take a true-listp as the "input file" and so we here implement
; the generalized version of (read-object (standard-oi state) state).

  (let ((standard-oi (standard-oi state)))
    (cond ((consp standard-oi)
           (let ((state (f-put-global 'standard-oi (cdr standard-oi) state)))
             (mv nil (car standard-oi) state)))
          ((null standard-oi)
           (mv t nil state))
          (t (read-object standard-oi state)))))

(defun chk-standard-oi (val ctx state)
  (cond
   ((and (symbolp val)
         (open-input-channel-p val :object state))
    (value nil))
   ((true-listp val)
    (value nil))
   ((and (consp val)
         (symbolp (cdr (last val)))
         (open-input-channel-p (cdr (last val)) :object state))
    (value nil))
   (t (er soft ctx *ld-special-error* 'standard-oi val))))

(defun set-standard-oi (val state)
  (er-progn (chk-standard-oi val 'set-standard-oi state)
            (pprogn
             (f-put-global 'standard-oi val state)
             (value val))))

(defun chk-standard-co (val ctx state)
  (cond
   ((and (symbolp val)
         (open-output-channel-p val :character state))
    (value nil))
   (t (er soft ctx *ld-special-error* 'standard-co val))))

(defun set-standard-co (val state)
  (er-progn
   (chk-standard-co val 'set-standard-co state)
   (pprogn
    (f-put-global 'standard-co val state)
    (value val))))

(defun proofs-co (state)
  (f-get-global 'proofs-co state))

(defun chk-proofs-co (val ctx state)
  (cond
   ((and (symbolp val)
         (open-output-channel-p val :character state))
    (value nil))
   (t (er soft ctx *ld-special-error* 'proofs-co val))))

(defun set-proofs-co (val state)
  (er-progn
   (chk-proofs-co val 'set-proofs-co state)
   (pprogn
    (f-put-global 'proofs-co val state)
    (value val))))

(defun illegal-state-ld-prompt (channel state)

; See the Essay on Illegal-states.

; Since ACL2 doesn't allow lower-case characters in package names, the
; following is distinguishable from the prompts in legal states.  We indicate
; the ld-level just as is done by default-print-prompt.

  (fmt1 "[Illegal-State] ~*0"
        (list (cons #\0 (list "" ">" ">" ">"
                              (make-list-ac (f-get-global 'ld-level state)
                                            nil nil))))
        0 channel state nil))

(defun ld-pre-eval-filter (state)
  (f-get-global 'ld-pre-eval-filter state))

(defun illegal-state-p (state)
  (eq (ld-pre-eval-filter state)
      :illegal-state))

(defun ld-prompt (state)
  (cond ((illegal-state-p state) 'illegal-state-ld-prompt)
        (t (f-get-global 'ld-prompt state))))

(defun chk-ld-prompt (val ctx state)
  (cond ((or (null val)
             (eq val t))
         (value nil))
        (t (let ((wrld (w state)))
             (cond ((and (symbolp val)
                         (equal (arity val wrld) 2)
                         (equal (stobjs-in val wrld) '(nil state))
                         (equal (stobjs-out val wrld) '(nil state)))
                    (cond ((or (eq val 'brr-prompt)
                               (ttag wrld))
                           (value nil))
                          (t (er soft ctx
                                 "It is illegal to set the ld-prompt to ~x0 ~
                                  unless there is an active trust ttag.  See ~
                                  :DOC ~x1."
                                 val 'ld-prompt))))
                   (t (er soft ctx *ld-special-error* 'ld-prompt val)))))))

(defun set-ld-prompt (val state)
  (er-progn
   (chk-ld-prompt val 'set-ld-prompt state)
   (pprogn
    (f-put-global 'ld-prompt val state)
    (value val))))

(defun ld-keyword-aliases (state)
  (table-alist 'ld-keyword-aliases (w state)))

(defun ld-keyword-aliasesp (key val wrld)
  (and (keywordp key)
       (true-listp val)
       (int= (length val) 2)
       (let ((n (car val))
             (fn (cadr val)))
         (and (natp n)
              (cond
               ((and (symbolp fn)
                     (function-symbolp fn wrld))
                (equal (arity fn wrld) n))
               ((and (symbolp fn)
                     (getpropc fn 'macro-body nil wrld))
                t)
               (t (and (true-listp fn)
                       (>= (length fn) 3)
                       (<= (length fn) 4)
                       (eq (car fn) 'lambda)
                       (arglistp (cadr fn))
                       (int= (length (cadr fn)) n))))))))

(table ld-keyword-aliases nil nil
       :guard
       (ld-keyword-aliasesp key val world))

#+acl2-loop-only
(defmacro add-ld-keyword-alias! (key val)
  `(with-output
     :off (event summary)
     (progn (table ld-keyword-aliases ,key ,val)
            (table ld-keyword-aliases))))

#-acl2-loop-only
(defmacro add-ld-keyword-alias! (key val)
  (declare (ignore key val))
  nil)

(defmacro add-ld-keyword-alias (key val)
  `(local (add-ld-keyword-alias! ,key ,val)))

#+acl2-loop-only
(defmacro set-ld-keyword-aliases! (alist)
  `(with-output
     :off (event summary)
     (progn (table ld-keyword-aliases nil ',alist :clear)
            (table ld-keyword-aliases))))

#-acl2-loop-only
(defmacro set-ld-keyword-aliases! (alist)
  (declare (ignore alist))
  nil)

(defmacro set-ld-keyword-aliases (alist &optional state)

; We add state (optionally) just for backwards compatibility through
; Version_6.2.  We might eliminate it after Version_6.3.

  (declare (ignore state))
  `(local (set-ld-keyword-aliases! ,alist)))

(defun ld-missing-input-ok (state)
  (f-get-global 'ld-missing-input-ok state))

(defun chk-ld-missing-input-ok (val ctx state)
  (cond ((or (member-eq val '(t nil :warn))
             (msgp val) ; admittedly, a weak check
             )
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-missing-input-ok val))))

(defun set-ld-missing-input-ok (val state)
  (er-progn
   (chk-ld-missing-input-ok val 'set-ld-missing-input-ok state)
   (pprogn
    (f-put-global 'ld-missing-input-ok val state)
    (value val))))

(defun new-namep (name wrld)

; We determine if name has properties on world wrld.  Once upon a time
; this was equivalent to just (not (assoc-eq name wrld)).  However, we
; have decided to ignore certain properties:
; * 'global-value - names with this property are just global variables
;                   in our code; we permit the user to define functions
;                   with those names.
; * 'table-alist - names with this property are being used as tables
; * 'table-guard - names with this property are being used as tables

; WARNING: If this list of properties is changed, change renew-name/erase.

; Additionally, if name has a non-nil 'redefined property name is treated as
; new if all of its other properties are as set by renew-name/erase or
; renew-name/overwrite, as appropriate.  The 'redefined property is set by
; renew-name to be (renewal-mode .  old-sig) where renewal-mode is :erase,
; :overwrite, or :reclassifying-overwrite.

  (let ((redefined (getpropc name 'redefined nil wrld)))
    (cond
     ((and (consp redefined)
           (eq (car redefined) :erase))

; If we erased the properties of name and they are still erased, then we
; will find no non-nil properties except for those left by
; renew-name/erase and renew-name.

      (not (has-propsp name
                       '(REDEFINED
                         GLOBAL-VALUE
                         TABLE-ALIST
                         TABLE-GUARD)
                       'current-acl2-world
                       wrld
                       nil)))
     ((and (consp redefined)
           (or (eq (car redefined) :overwrite)
               (eq (car redefined) :reclassifying-overwrite)))

; We make a check analogous to that for erasure, allowing arbitrary non-nil
; values on all the properties untouched by renew-name/overwrite and insisting
; that all the properties erased by that function are still gone.  Technically
; we should confirm that the lemmas property has been cleansed of all
; introductory rules, but in fact we allow it to have an arbitrary non-nil
; value.  This is correct because if 'formals is gone then we cleansed 'lemmas
; and nothing could have been put back there since name is not yet a function
; symbol again.

      (not (has-propsp name
                       '(REDEFINED

                         LEMMAS

                         GLOBAL-VALUE
                         LABEL
                         LINEAR-LEMMAS
                         FORWARD-CHAINING-RULES
                         ELIMINATE-DESTRUCTORS-RULE
                         COARSENINGS
                         CONGRUENCES
                         PEQUIVS
                         INDUCTION-RULES
                         THEOREM
                         UNTRANSLATED-THEOREM
                         CLASSES
                         CONST
                         THEORY
                         TABLE-GUARD
                         TABLE-ALIST
                         MACRO-BODY
                         MACRO-ARGS
                         PREDEFINED
                         TAU-PAIR
                         POS-IMPLICANTS
                         NEG-IMPLICANTS
                         UNEVALABLE-BUT-KNOWN
                         SIGNATURE-RULES-FORM-1
                         SIGNATURE-RULES-FORM-2
                         BIG-SWITCH
                         TAU-BOUNDERS-FORM-1
                         TAU-BOUNDERS-FORM-2
                         )
                       'current-acl2-world
                       wrld
                       nil)))
     (t (not (has-propsp name
                         '(GLOBAL-VALUE
                           TABLE-ALIST
                           TABLE-GUARD)
                         'current-acl2-world
                         wrld
                         nil))))))

(defun chk-ld-pre-eval-filter (val ctx state)
  (cond ((or (member-eq val '(:all :query :illegal-state))
             (and (symbolp val)
                  (not (keywordp val))
                  (not (equal (symbol-package-name val)
                              *main-lisp-package-name*))
                  (new-namep val (w state))))
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-pre-eval-filter val))))

(defun set-ld-pre-eval-filter (val state)
  (er-progn
   (chk-ld-pre-eval-filter val 'set-ld-pre-eval-filter state)
   (pprogn
    (f-put-global 'ld-pre-eval-filter val state)
    (value val))))

(defun ld-pre-eval-print (state)
  (f-get-global 'ld-pre-eval-print state))

(defun chk-ld-pre-eval-print (val ctx state)
  (cond ((member-eq val '(nil t :never))
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-pre-eval-print val))))

(defun set-ld-pre-eval-print (val state)
  (er-progn
   (chk-ld-pre-eval-print val 'set-ld-pre-eval-print state)
   (pprogn
    (f-put-global 'ld-pre-eval-print val state)
    (value val))))

(defun ld-post-eval-print (state)
  (f-get-global 'ld-post-eval-print state))

(defun chk-ld-post-eval-print (val ctx state)
  (cond ((member-eq val '(nil t :command-conventions))
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-post-eval-print val))))

(defun set-ld-post-eval-print (val state)
  (er-progn
   (chk-ld-post-eval-print val 'set-ld-post-eval-print state)
   (pprogn
    (f-put-global 'ld-post-eval-print val state)
    (value val))))

(defun ld-error-triples (state)
  (f-get-global 'ld-error-triples state))

(defun chk-ld-error-triples (val ctx state)
  (cond ((member-eq val '(nil t))
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-error-triples val))))

(defun set-ld-error-triples (val state)
  (er-progn
   (chk-ld-error-triples val 'set-ld-error-triples state)
   (pprogn
    (f-put-global 'ld-error-triples val state)
    (value val))))

(defun ld-error-action (state)
  (f-get-global 'ld-error-action state))

(defun chk-ld-error-action (val ctx state)
  (cond ((member-eq val '(:continue :return :return! :error))
         (value nil))
        ((and (consp val)
              (eq (car val) :exit)
              (consp (cdr val))
              (natp (cadr val))
              (null (cddr val)))
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-error-action val))))

(defun set-ld-error-action (val state)
  (er-progn
   (chk-ld-error-action val 'set-ld-error-action state)
   (pprogn
    (f-put-global 'ld-error-action val state)
    (value val))))

(defun ld-query-control-alist (state)
  (f-get-global 'ld-query-control-alist state))

(defun ld-query-control-alistp (val)
  (cond ((atom val) (or (eq val nil)
                        (eq val t)))
        ((and (consp (car val))
              (symbolp (caar val))
              (or (eq (cdar val) nil)
                  (eq (cdar val) t)
                  (keywordp (cdar val))
                  (and (consp (cdar val))
                       (keywordp (cadar val))
                       (null (cddar val)))))
         (ld-query-control-alistp (cdr val)))
        (t nil)))

(defun cdr-assoc-query-id (id alist)
  (cond ((atom alist) alist)
        ((eq id (caar alist)) (cdar alist))
        (t (cdr-assoc-query-id id (cdr alist)))))

(defun chk-ld-query-control-alist (val ctx state)
  (cond
   ((ld-query-control-alistp val)
    (value nil))
   (t (er soft ctx *ld-special-error* 'ld-query-control-alist val))))

(defun set-ld-query-control-alist (val state)
  (er-progn
   (chk-ld-query-control-alist val 'set-ld-query-control-alist state)
   (pprogn
    (f-put-global 'ld-query-control-alist val state)
    (value val))))

(defun ld-verbose (state)
  (f-get-global 'ld-verbose state))

(defun chk-ld-verbose (val ctx state)
  (cond ((or (stringp val)
             (and (consp val)
                  (stringp (car val))))
         (value nil))
        ((member-eq val '(nil t))
         (value nil))
        (t (er soft ctx *ld-special-error* 'ld-verbose val))))

(defun set-ld-verbose (val state)
  (er-progn
   (chk-ld-verbose val 'set-ld-verbose state)
   (pprogn
    (f-put-global 'ld-verbose val state)
    (value val))))

(defun chk-ld-user-stobjs-modified-warning (val ctx state)
  (cond ((member-eq val '(nil t :same))
         (value nil))
        (t (er soft ctx *ld-special-error*
               'ld-user-stobjs-modified-warning val))))

(defun set-ld-user-stobjs-modified-warning (val state)
  (er-progn
   (chk-ld-user-stobjs-modified-warning val
                                        'set-ld-user-stobjs-modified-warning
                                        state)
   (pprogn
    (f-put-global 'ld-user-stobjs-modified-warning val state)
    (value val))))

(defconst *nqthm-to-acl2-primitives*

; Keep this list in sync with documentation for nqthm-to-acl2.

  '((ADD1 1+)
    (ADD-TO-SET ADD-TO-SET-EQUAL ADD-TO-SET-EQ)
    (AND AND)
    (APPEND APPEND BINARY-APPEND)
    (APPLY-SUBR .   "Doesn't correspond to anything in ACL2, really.
                     See the documentation for DEFEVALUATOR and META.")
    (APPLY$ .       "See the documentation for DEFEVALUATOR and META.")
    (ASSOC ASSOC-EQUAL ASSOC ASSOC-EQ)
    (BODY .         "See the documentation for DEFEVALUATOR and META.")
    (CAR CAR)
    (CDR CDR)
    (CONS CONS)
    (COUNT ACL2-COUNT)
    (DIFFERENCE -)
    (EQUAL EQUAL EQ EQL =)
    (EVAL$ .        "See the documentation for DEFEVALUATOR and META.")
    (FALSE .        "Nqthm's F corresponds to the ACL2 symbol NIL.")
    (FALSEP NOT NULL)
    ;;(FIX)
    ;;(FIX-COST)
    ;;(FOR)
    (FORMALS .      "See the documentation for DEFEVALUATOR and META.")
    (GEQ >=)
    (GREATERP >)
    (IDENTITY IDENTITY)
    (IF IF)
    (IFF IFF)
    (IMPLIES IMPLIES)
    (LEQ <=)
    (LESSP <)
    (LISTP CONSP)
    (LITATOM SYMBOLP)
    (MAX MAX)
    (MEMBER MEMBER-EQUAL MEMBER MEMBER-EQ)
    (MINUS - UNARY--)
    (NEGATIVEP MINUSP)
    (NEGATIVE-GUTS ABS)
    (NLISTP ATOM)
    (NOT NOT)
    (NUMBERP ACL2-NUMBERP INTEGERP RATIONALP)
    (OR OR)
    (ORDINALP O-P)
    (ORD-LESSP O<)
    (PACK .         "See INTERN and COERCE.")
    (PAIRLIST PAIRLIS$)
    (PLUS + BINARY-+)
    ;;(QUANTIFIER-INITIAL-VALUE)
    ;;(QUANTIFIER-OPERATION)
    (QUOTIENT /)
    (REMAINDER REM MOD)
    (STRIP-CARS STRIP-CARS)
    (SUB1 1-)
    ;;(SUBRP)
    ;;(SUM-CDRS)
    (TIMES * BINARY-*)
    (TRUE . "The symbol T.")
    ;;(TRUEP)
    (UNION UNION-EQUAL UNION-EQ)
    (UNPACK .       "See SYMBOL-NAME and COERCE.")
    (V&C$ .         "See the documentation for DEFEVALUATOR and META.")
    (V&C-APPLY$ .   "See the documentation for DEFEVALUATOR and META.")
    (ZERO .         "The number 0.")
    (ZEROP ZEROP)))

(defconst *nqthm-to-acl2-commands*

; Keep this list in sync with documentation for nqthm-to-acl2.

  '((ACCUMULATED-PERSISTENCE ACCUMULATED-PERSISTENCE)
    (ADD-AXIOM DEFAXIOM)
    (ADD-SHELL .    "There is no shell principle in ACL2.")
    (AXIOM DEFAXIOM)
    (BACKQUOTE-SETTING .
                    "Backquote is supported in ACL2, but not
                     currently documented.")
    (BOOT-STRAP GROUND-ZERO)
    (BREAK-LEMMA MONITOR)
    (BREAK-REWRITE BREAK-REWRITE)
    (CH PBT .       "See also :DOC history.")
    (CHRONOLOGY PBT .
                    "See also :DOC history.")
    (COMMENT DEFLABEL)
    (COMPILE-UNCOMPILED-DEFNS COMP)
    (CONSTRAIN .    "See :DOC encapsulate and :DOC local.")
    (DATA-BASE .    "Perhaps the closest ACL2 analogue of DATA-BASE
                     is PROPS.  But see :DOC history for a collection
                     of commands for querying the ACL2 database
                     (``world'').  Note that the notions of
                     supporters and dependents are not supported in
                     ACL2.")
    (DCL DEFSTUB)
    (DEFN DEFUN DEFMACRO)
    (DEFTHEORY DEFTHEORY)
    (DISABLE DISABLE)
    (DISABLE-THEORY .
                    "See :DOC theories.  The Nqthm command
                     (DISABLE-THEORY FOO) corresponds roughly to the
                     ACL2 command
                     (in-theory (set-difference-theories
                                  (current-theory :here)
                                  (theory 'foo))).")
    (DO-EVENTS LD)
    (DO-FILE LD)
    (ELIM ELIM)
    (ENABLE ENABLE)
    (ENABLE-THEORY .
                    "See :DOC theories.  The Nqthm command
                     (ENABLE-THEORY FOO) corresponds roughly to the
                     ACL2 command
                     (in-theory (union-theories
                                  (theory 'foo)
                                  (current-theory :here))).")
    (EVENTS-SINCE PBT)
    (FUNCTIONALLY-INSTANTIATE .
                    "ACL2 provides a form of the :USE hint that
                     corresponds roughly to the
                     FUNCTIONALLY-INSTANTIATE event of Nqthm. See
                     :DOC lemma-instance.")
    (GENERALIZE GENERALIZE)
    (HINTS HINTS)
    (LEMMA DEFTHM)
    (MAINTAIN-REWRITE-PATH BRR)
    (MAKE-LIB .     "There is no direct analogue of Nqthm's notion of
                     ``library.''  See :DOC books for a description
                     of ACL2's mechanism for creating and saving
                     collections of events.")
    (META META)
    (NAMES NAME)
    (NOTE-LIB INCLUDE-BOOK)
    (PPE PE)
    (PROVE THM)
    (PROVEALL .     "See :DOC ld and :DOC certify-book.  The latter
                     corresponds to Nqthm's PROVE-FILE,which may be
                     what you're interested in, really.")
    (PROVE-FILE CERTIFY-BOOK)
    (PROVE-FILE-OUT CERTIFY-BOOK)
    (PROVE-LEMMA DEFTHM .
                    "See also :DOC hints.")
    (R-LOOP .       "The top-level ACL2 loop is an evaluation loop as
                     well, so no analogue of R-LOOP is necessary.")
    (REWRITE REWRITE)
    (RULE-CLASSES RULE-CLASSES)
    (SET-STATUS IN-THEORY)
    (SKIM-FILE LD-SKIP-PROOFSP)
    (TOGGLE IN-THEORY)
    (TOGGLE-DEFINED-FUNCTIONS EXECUTABLE-COUNTERPART-THEORY)
    (TRANSLATE TRANS TRANS1)
    (UBT UBT U)
    (UNBREAK-LEMMA UNMONITOR)
    (UNDO-BACK-THROUGH UBT)
    (UNDO-NAME .    "See :DOC ubt.  There is no way to undo names in
                     ACL2 without undoing back through such names.
                     However, see :DOC ld-skip-proofsp for
                     information about how to quickly recover the
                     state.")))

(defun nqthm-to-acl2-fn (name state)
  (declare (xargs :guard (symbolp name)))
  (io? temporary nil (mv erp val state)
       (name)
       (let ((prims (cdr (assoc-eq name *nqthm-to-acl2-primitives*)))
             (comms (cdr (assoc-eq name *nqthm-to-acl2-commands*))))
         (pprogn
          (cond
           (prims
            (let ((syms (fix-true-list prims))
                  (info (if (consp prims) (cdr (last prims)) prims)))
              (pprogn
               (if syms
                   (fms "Related ACL2 primitives (use :PE or see documentation ~
                         to learn more):  ~&0.~%"
                        (list (cons #\0 syms))
                        *standard-co*
                        state
                        nil)
                 state)
               (if info
                   (pprogn (fms info
                                (list (cons #\0 syms))
                                *standard-co*
                                state
                                nil)
                           (newline *standard-co* state))
                 state))))
           (t state))
          (cond
           (comms
            (let ((syms (fix-true-list comms))
                  (info (if (consp comms) (cdr (last comms)) comms)))
              (pprogn
               (if syms
                   (fms "Related ACL2 commands (use :PE or see documentation ~
                         to learn more):  ~&0.~%"
                        (list (cons #\0 syms))
                        *standard-co*
                        state
                        nil)
                 state)
               (if info
                   (pprogn (fms info
                                (list (cons #\0 syms))
                                *standard-co*
                                state
                                nil)
                           (newline *standard-co* state))
                 state))))
           (t state))
          (if (or prims comms)
              (value :invisible)
            (pprogn
             (fms "Sorry, but there seems to be no ACL2 notion corresponding ~
                   to the alleged Nqthm notion ~x0.~%"
                  (list (cons #\0 name))
                  *standard-co*
                  state
                  nil)
             (value :invisible)))))))

; Here are functions that can be defined to print out the last part of the
; documentation string for nqthm-to-acl2, using (print-nqthm-to-acl2-doc
; state).

; (defun print-nqthm-to-acl2-doc1 (alist state)
;   (cond
;    ((null alist) state)
;    (t (let* ((x (fix-true-list (cdar alist)))
;              (s (if (atom (cdar alist))
;                     (cdar alist)
;                   (cdr (last (cdar alist))))))
;         (mv-let
;          (col state)
;          (fmt1 "  ~x0~t1--> "
;                (list (cons #\0 (caar alist))
;                      (cons #\1 16))
;                0 *standard-co* state nil)
;          (declare (ignore col))
;          (mv-let
;           (col state)
;           (fmt1 " ~&0"
;                 (list (cons #\0 x))
;                 0 *standard-co* state nil)
;           (declare (ignore col))
;           (pprogn
;            (if (or (null x) (null s))
;                state
;              (fms "~t0" (list (cons #\0 21)) *standard-co* state nil))
;            (if s
;                (mv-let
;                 (col state)
;                 (fmt1 "~@0~%" ; Here % was vertical bar, but emacs 19 has trouble...
;                       (list (cons #\0 s)) 0 *standard-co* state nil)
;                 (declare (ignore col))
;                 state)
;              (newline *standard-co* state))
;            (print-nqthm-to-acl2-doc1 (cdr alist) state))))))))
;
; (defun print-nqthm-to-acl2-doc (state)
;   (pprogn
;    (princ$ "  ~bv[]" *standard-co* state)
;    (fms "  Nqthm functions  -->     ACL2"
;         nil *standard-co* state nil)
;    (fms "  ----------------------------------------~%"
;         nil *standard-co* state nil)
;    (print-nqthm-to-acl2-doc1 *nqthm-to-acl2-primitives* state)
;    (fms "  ========================================~%"
;         nil *standard-co* state nil)
;    (fms "  Nqthm commands   -->     ACL2"
;         nil *standard-co* state nil)
;    (fms "  ----------------------------------------~%"
;         nil *standard-co* state nil)
;    (print-nqthm-to-acl2-doc1 *nqthm-to-acl2-commands* state)
;    (princ$ "  ~ev[]" *standard-co* state)
;    (newline *standard-co* state)
;    (value :invisible)))

(defmacro nqthm-to-acl2 (x)

; Keep documentation for this function in sync with *nqthm-to-acl2-primitives*
; and *nqthm-to-acl2-commands*.  See comment above for how some of this
; documentation was generated.

  (declare (xargs :guard (and (true-listp x)
                              (equal (length x) 2)
                              (eq (car x) 'quote)
                              (symbolp (cadr x)))))
  `(nqthm-to-acl2-fn ,x state))

#+(and gcl (not acl2-loop-only))
(progn
  (defvar *current-allocated-fixnum-lo* 0)
  (defvar *current-allocated-fixnum-hi* 0))

(defun allocate-fixnum-range (fixnum-lo fixnum-hi)
  (declare (xargs :guard (and (integerp fixnum-lo)
                              (integerp fixnum-hi)
                              (>= fixnum-hi fixnum-lo)))
           (type (signed-byte 30) fixnum-lo fixnum-hi))

; This function is simply NIL in the logic but allocates a range of fixnums
; (from fixnum-lo to fixnum-hi) in GCL as a side effect (a side effect which
; should only affect the speed with which ACL2 computes a value, but not the
; value itself up to EQUALity).  In GCL, there is a range of pre-allocated
; fixnums which are fixed to be -1024 to +1023.

  (let ((tmp (- fixnum-hi fixnum-lo)))
    (declare (ignore tmp))
    #+(and gcl (not acl2-loop-only))
    (cond ((or (> fixnum-hi *current-allocated-fixnum-hi*)
               (< fixnum-lo *current-allocated-fixnum-lo*))
           (fms "NOTE:  Allocating bigger fixnum table in GCL.~|"
                nil (standard-co *the-live-state*) *the-live-state*
                nil)
           (system::allocate-bigger-fixnum-range fixnum-lo (1+ fixnum-hi))
           (setq *current-allocated-fixnum-lo* fixnum-lo)
           (setq *current-allocated-fixnum-hi* fixnum-hi))
          (t
           (fms "No further fixnum allocation done:~|  Previous fixnum table ~
                 encompasses desired allocation.~|"
                nil (standard-co *the-live-state*) *the-live-state*
                nil)))
    #+(and (not gcl) (not acl2-loop-only))
    (fms "Fixnum allocation is only performed in GCL.~|"
         nil (standard-co *the-live-state*) *the-live-state*
         nil)
    nil))

; It has been found useful to allocate new space very gradually in Allegro CL
; 6.1 for at least one unusually large job on a version of RedHat Linux (over
; 600MB without this caused GC error; with this call, the corresponding image
; size was cut by very roughly one third and there was no GC error).  However,
; the problem seems to disappear in Allegro CL 6.2.  So we won't advertise
; (document) this utility.

#+allegro
(defmacro allegro-allocate-slowly (&key (free-bytes-new-other '1024)
                                        (free-bytes-new-pages '1024)
                                        (free-percent-new '3)
                                        (expansion-free-percent-old '3)
                                        (expansion-free-percent-new '3))
  `(allegro-allocate-slowly-fn ,free-bytes-new-other ,free-bytes-new-pages
                               ,free-percent-new ,expansion-free-percent-old
                               ,expansion-free-percent-new))

(defun allegro-allocate-slowly-fn (free-bytes-new-other
                                   free-bytes-new-pages
                                   free-percent-new
                                   expansion-free-percent-old
                                   expansion-free-percent-new)

  #-(and allegro (not acl2-loop-only))
  (declare (ignore free-bytes-new-other free-bytes-new-pages free-percent-new
                   expansion-free-percent-old expansion-free-percent-new))
  #+(and allegro (not acl2-loop-only))
  (progn
    (setf (sys:gsgc-parameter :free-bytes-new-other) free-bytes-new-other)
    (setf (sys:gsgc-parameter :free-bytes-new-pages) free-bytes-new-pages)
    (setf (sys:gsgc-parameter :free-percent-new) free-percent-new)
    (setf (sys:gsgc-parameter :expansion-free-percent-old)
          expansion-free-percent-old)
    (setf (sys:gsgc-parameter :expansion-free-percent-new)
          expansion-free-percent-new))
  nil)

; All code for the pstack feature occurs immediately below.  When a form is
; wrapped in (pstk form), form will be pushed onto *pstk-stack* during its
; evaluation.  The stack can be evaluated (during a break or after an
; interrupted proof) by evaluating the form (pstack), and it is
; initialized at the beginning of each new proof attempt (in prove-loop, since
; that is the prover's entry point under both prove and pc-prove).

#-acl2-loop-only
(progn
  (defparameter *pstk-stack* nil)
  (defvar *verbose-pstk* nil)

; The following are only of interest when *verbose-pstk* is true.

  (defparameter *pstk-level* 1)
  (defparameter *pstk-start-time-stack* nil))

(defmacro clear-pstk ()
  #+acl2-loop-only nil
  #-acl2-loop-only
  '(progn (setq *pstk-stack* nil)
          (setq *pstk-level* 1)
          (setq *pstk-start-time-stack* nil)))

(defconst *pstk-vars*
  '(pstk-var-0
    pstk-var-1
    pstk-var-2
    pstk-var-3
    pstk-var-4
    pstk-var-5
    pstk-var-6
    pstk-var-7
    pstk-var-8
    pstk-var-9
    pstk-var-10
    pstk-var-11
    pstk-var-12))

(defun pstk-bindings-and-args (args vars)

; We return (mv bindings new-args fake-args).  Here new-args is a symbol-listp
; and of the same length as args, where each element of args is either a symbol
; or is the value of the corresponding element of new-args in bindings.
; Fake-args is the same as new-args except that state has been replaced by
; <state>.

  (cond
   ((endp args)
    (mv nil nil nil))
   ((endp vars)
    (mv (er hard 'pstk-bindings-and-args
            "The ACL2 sources need *pstk-vars* to be extended.")
        nil nil))
   (t
    (mv-let (bindings rest-args fake-args)
      (pstk-bindings-and-args (cdr args) (cdr vars))
      (cond
       ((eq (car args) 'state)
        (mv bindings
            (cons (car args) rest-args)
            (cons ''<state> rest-args)))
       ((symbolp (car args))
        (mv bindings
            (cons (car args) rest-args)
            (cons (car args) fake-args)))
       (t
        (mv (cons (list (car vars) (car args)) bindings)
            (cons (car vars) rest-args)
            (cons (car vars) fake-args))))))))

(defmacro pstk (form)
  (declare (xargs :guard (consp form)))
  #+acl2-loop-only
  `(check-vars-not-free
    ,*pstk-vars*
    ,form)
  #-acl2-loop-only
  (mv-let (bindings args fake-args)
    (pstk-bindings-and-args (cdr form) *pstk-vars*)
    `(let ,bindings
       (setq *pstk-stack*
             (cons ,(list* 'list (kwote (car form)) fake-args)
                   *pstk-stack*))
       (dmr-display)
       (when (and *verbose-pstk*
                  (or (eq *verbose-pstk* t)
                      (not (member-eq ',(car form) *verbose-pstk*))))
         (setq *pstk-start-time-stack*
               (cons (get-internal-time) *pstk-start-time-stack*))
         (format t "~V@TCP~D> ~S~%"
                 (* 2 *pstk-level*)
                 *pstk-level*
                 ',(car form))
         (setq *pstk-level* (1+ *pstk-level*)))
       (our-multiple-value-prog1
        ,(cons (car form) args)

; Careful!  We must be careful not to smash any mv-ref value in the forms
; below, in case form returns a multiple value.  So, for example, we use format
; rather than fmt1.

        (when (and *verbose-pstk*
                   (or (eq *verbose-pstk* t)
                       (not (member-eq ',(car form) *verbose-pstk*))))
          (setq *pstk-level* (1- *pstk-level*))
          (format t "~V@TCP~D< ~S [~,2F seconds]~%"
                  (* 2 *pstk-level*)
                  *pstk-level*
                  ',(car form)
                  (/ (- (get-internal-time)
                        (pop *pstk-start-time-stack*))
                     (float internal-time-units-per-second))))
        (setq *pstk-stack* (cdr *pstk-stack*))
        ,@(and (not (eq (car form) 'ev-fncall-meta)) ; overkill in that case
               '((dmr-display)))
        ,@(and (eq (car form) 'rewrite-atm)
               '((setq *deep-gstack* nil)))))))

(defun pstack-fn (allp state)
  #+acl2-loop-only
  (declare (ignore allp))
  #-acl2-loop-only
  (cond ((and allp (not (eq allp :all)))
         (fmt-abbrev "~%~p0"
                     (list (cons #\0 (if allp
                                         *pstk-stack*
                                       (strip-cars *pstk-stack*))))
                     0 *standard-co* state "~|"))
        (t
         (fms "~p0~|"
              (list (cons #\0 (if allp *pstk-stack* (strip-cars *pstk-stack*))))
              *standard-co*
              state
              (and allp ; (eq allp :all)
                   (cons (world-evisceration-alist state nil)
                         '(nil nil nil))))))
  #-acl2-loop-only
  (if (assoc-eq 'preprocess-clause *pstk-stack*)
      (cw "NOTE:  You may find the hint :DO-NOT '(PREPROCESS) helpful.~|"))
  (value :invisible))

(defmacro pstack (&optional allp)
  `(pstack-fn ,allp state))

(defun verbose-pstack (flg-or-list)
  (declare (xargs :guard (or (eq flg-or-list t)
                             (eq flg-or-list nil)
                             (symbol-listp flg-or-list))))
  #+acl2-loop-only
  flg-or-list
  #-acl2-loop-only
  (setq *verbose-pstk* flg-or-list))

; End of pstack code.

; The following two functions could go in axioms.lisp, but it seems not worth
; putting them in :logic mode so we might as well put them here.

(defmacro set-print-clause-ids (flg)
  (declare (xargs :guard (member-equal flg '(t 't nil 'nil))))
  (let ((flg (if (atom flg)
                 (list 'quote flg)
               flg)))
    `(f-put-global 'print-clause-ids ,flg state)))

(defun set-saved-output-token-lst (save-flg state)
  (declare (xargs :stobjs state))
  (cond ((member-eq save-flg '(t :all))
         (f-put-global 'saved-output-token-lst :all state))
        ((null save-flg)
         (f-put-global 'saved-output-token-lst nil state))
        ((true-listp save-flg)
         (f-put-global 'saved-output-token-lst save-flg state))
        (t (prog2$ (er hard 'set-saved-output
                       "Illegal first argument to set-saved-output-token-lst ~
                        (must be ~x0 or a true-listp): ~x1."
                       t save-flg)
                   state))))

(defun set-gag-mode-fn (action state)

; Warning: Keep this in sync with with-output-fn, in particular with respect to
; the legal values for action and for the state-global-let* generated there.

  (let ((action (if (and (consp action)
                         (consp (cdr action))
                         (eq (car action) 'quote))
                    (cadr action)
                  action)))
    (pprogn
     (case action
       ((t)
        (pprogn (set-saved-output-token-lst t state)
                (set-print-clause-ids nil)))
       (:goals
        (pprogn (set-saved-output-token-lst t state)
                (set-print-clause-ids t)))
       ((nil)
        (pprogn (set-saved-output-token-lst nil state)
                (set-print-clause-ids nil)))
       (otherwise
        (prog2$ (er hard 'set-gag-mode
                    "Unknown set-gag-mode argument, ~x0"
                    action)
                state))) ; to allow set-saved-output
     (f-put-global 'gag-mode action state))))

(defmacro set-gag-mode (action)
  `(set-gag-mode-fn ,action state))

(defun pop-inhibit-output-lst-stack (state)
  (let ((stk (f-get-global 'inhibit-output-lst-stack state)))
    (cond ((null stk) state)
          (t (pprogn (f-put-global 'inhibit-output-lst
                                   (caar stk)
                                   state)
                     (set-gag-mode (cdar stk))
                     (f-put-global 'inhibit-output-lst-stack
                                   (cdr stk)
                                   state))))))

(defun push-inhibit-output-lst-stack (state)
  (f-put-global 'inhibit-output-lst-stack
                (cons (cons (f-get-global 'inhibit-output-lst state)
                            (f-get-global 'gag-mode state))
                      (f-get-global 'inhibit-output-lst-stack state))
                state))

(defun set-gc-threshold$-fn (new-threshold verbose-p)

; This function is used to manage garbage collection in a way that is friendly
; to ACL2(p).  As suggested by its name, it sets (in supported Lisps), to
; new-threshold, the number of bytes to be allocated before the next garbage
; collection.  It may set other gc-related behavior as well.

  (declare (ignorable verbose-p))
  (let ((ctx 'set-gc-threshold$))
    (cond
     ((not (posp new-threshold))
      (er hard ctx
          "The argument to set-gc-threshold$ must be a positive integer, so ~
           the value ~x0 is illegal."
          new-threshold))
     (t
      #-acl2-loop-only
      (progn
        #+ccl
        (ccl:set-lisp-heap-gc-threshold ; CCL requires a fixnum.
         (cond ((> new-threshold most-positive-fixnum)
                (progn (cw "Requested value for set-gc-threshold$ must be a ~
                            fixnum in CCL, but ~x0 is greater than ~
                            most-positive-fixnum (which is ~x1). Setting to ~
                            most-positive-fixnum instead.~|"
                           new-threshold most-positive-fixnum)
                       most-positive-fixnum))
               (t new-threshold)))
        #+(and ccl acl2-par)
        (progn (cw "Disabling the CCL Ephemeral GC for ACL2(p)~%")
               (ccl:egc nil))
        #+sbcl
        (setf (sb-ext:bytes-consed-between-gcs) (1- new-threshold))
        #+(and lispworks lispworks-64bit)
        (let

; In the case of 64-bit LispWorks, we set the threshold to at least 2^20 (1 MB)
; for generation 3, since we believe that any smaller might not provide good
; performance, and we set proportionally smaller thresholds for generations 1
; and 2.

            ((gen0-threshold

; For generation 0, we want to reduce the generation-3 threshold by a factor
; off 2^10.  The corresponding value for dividing the minimum new-threshold of
; 2^20 would thus be 2^20/2^10 = 2^10.  However, LispWorks requires a larger
; minimum value for system:set-gen-num-gc-threshold; since 2^13 was even too
; small, we have chosen 2^14.  But we still attempt to divide new-threshold by
; 2^10.

              (max (expt 2 14) (floor new-threshold (expt 2 10))))
             (gen1-threshold
              (max (expt 2 17) (floor new-threshold (expt 2 3))))
             (gen2-threshold
              (max (expt 2 18) (floor new-threshold (expt 2 2))))
             (gen3-threshold
              (max (expt 2 20) new-threshold)))

          (when (< new-threshold (expt 2 20))
            (let ((state *the-live-state*))

; Avoid warning$-cw, since this function is called by LP outside the loop.

              (warning$ 'set-gc-threshold$ nil
                        "Using default thresholds that are greater than the ~
                         requested value ~x0, as follows for generations 0, ~
                         1, 2 and 3, respectively: ~&1."
                        new-threshold
                        (list gen0-threshold
                              gen1-threshold
                              gen2-threshold
                              gen3-threshold))))

; Calling set-gen-num-gc-threshold sets the GC threshold for the given
; generation of garbage.

          (system:set-gen-num-gc-threshold 0 gen0-threshold)
          (system:set-gen-num-gc-threshold 1 gen1-threshold)
          (system:set-gen-num-gc-threshold 2 gen2-threshold)

; This call to set-blocking-gen-num accomplishes two things: (1) It sets the
; third generation as the "final" generation -- nothing can be promoted to
; generation four or higher.  (2) It sets the GC threshold for generation 3.

          (system:set-blocking-gen-num 3 :gc-threshold gen3-threshold))
        #-(or ccl sbcl (and lispworks lispworks-64bit))
        (when verbose-p
          (let ((state *the-live-state*))

; Avoid warning$-cw, since this function is called by LP outside the loop.

            (warning$ 'set-gc-threshold$ nil
                      "We have not yet implemented setting the garbage ~
                       collection threshold for this Lisp.  Contact the ACL2 ~
                       implementors to request such an implementation."))))
      t))))

(defmacro set-gc-threshold$ (new-threshold &optional (verbose-p 't))

; See comments in set-gc-threshold$-fn.

  `(set-gc-threshold$-fn ,new-threshold ,verbose-p))
