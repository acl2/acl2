(in-package "ACL2")

;; Contact: Sol Swords <sswords@cs.utexas.edu>

;; This book contains the macro b*, which acts like let* with certain
;; extensions.  Some of its features:
;; - Can bind single values and MVs within the same let*-like sequence
;; of assignments, without nesting
;; - Can bind variables using user-defined pattern-matching idioms
;; - Eliminates ignore and ignorable declarations

(defdoc b* ":DOC-SECTION B*
Flexible let*-like macro for variable bindings~/
Usage:
~bv[]
 (b* ;; let*-like binding to a single variable:
     ((x (cons 'a 'b))

     ;; mv binding
      ((mv y z) (return-two-values x x))

     ;; No binding: expression evaluated for side effects
      (- (cw \"Hello\")) ;; prints \"Hello\"

     ;; Binding with type declaration:
      ((the (integer 0 100) n) (foo z))

     ;; MV which ignores a value:
      ((mv & a) (return-garbage-in-first-mv y z))

     ;; Binds value 0 to C and value 1 to D,
     ;; declares (ignorable C) and (ignore D)
      ((mv ?c ?!d) (another-mv a z))

     ;; Bind V to the middle value of an error triple,
     ;; quitting if there is an error condition (a la er-let*)
      ((er v) (trans-eval '(len (list 'a 1 2 3)) 'foo state))

     ;; The WHEN, IF, and UNLESS constructs insert an IF in the
     ;; binding stream.  The WHEN and IF constructs are equivalent.
      ((when v) (finish-early-because-of v))
      ((if v)   (finish-early-because-of v))
      ((unless c) (finish-early-unless c))

     ;; Pattern-based binding using cons, where D is ignorable
      ((cons (cons b c) ?d) (must-return-nested-conses a))

     ;; Alternate form of pattern binding with cons nests, where G is
     ;; ignored and f has a type declaration:
      (`(,e (,(the (signed-byte 8) f) . ,?!g))
       (makes-a-list-of-conses b))

     ;; LIST and LIST* are also supported:
      ((list a b) '((1 2) (3 4)))
      ((list* a (the string b) c) '((1 2) \"foo\" 5 6 7))

     ;; Pattern with user-defined constructor:
      ((my-tuple foo bar hum) (something-of-type-my-tuple e c g))

     ;; Don't-cares with pattern bindings:
      ((my-tuple & (cons carbar &) hum) (something-else foo f hum))

     ;; Pattern inside an mv:
      ((mv a (cons & c)) (make-mv-with-cons)))
   (some-expression .....))
~ev[]
~/

B* is a macro for binding variables in sequence, like let*.  However, it
contains some additional features to allow it to bind multi-values, error
triples, and subtrees of CONS structures, run forms for side-effects, ignore
variables or declare them ignorable.  It can also be extended by the user to
support more binding constructs.

Its syntax is
 (b* <list-of-bindings> . <list-of-result-forms>)
where a result form is any ACL2 term, and a binding is
 (<binder-form> [<expression>]).  See below for discussion of binder forms.
Depending on the binder form, it may be that multiple expressions are allowed
or only a single one.

B* expands to multiple nestings of another macro PATBIND, analogously to how
LET* expands to multiple nestings of LET.

-- Basic let*-like usage --

B* can be used exactly like LET*, except that it does not yet support DECLARE
forms.  However, IGNORE or IGNORABLE declarations are inserted by B* according
to the syntax of the variables bound\; see below.  B* also supports multiple
result expressions after the binding list\; these are run in sequence and the
result of the last such form is returned.

-- Binder Forms --

The following binder forms are supported by this book alone, but support may
be added by the user for other binding forms.  In most cases, these binding
forms may be nested.  See ~il[b*-binders] for a comprehensive list of available
binder forms.

 ~c[(mv a b ...)] produces an MV-LET binding

 ~c[(cons a b)] produces a binding of the CAR and CDR of the corresponding expression

 ~c[(er a)] produces an ER-LET* binding

 ~c[(list a b ...)] produces a binding of (car val), (cadr val), etc, where val
is the result of the corresponding expression

 ~c[(nths a b ...)] produces a binding of (nth 0 val), (nth 1 val), etc, where val
is the result of the corresponding expression

 ~c[(list* a b)], ~c[`(,a . ,b)] are alternatives to the CONS binder.

 ~c[(the type-spec var)] produces a binding of var to the result of the
corresponding expression, and a declaration that var is of the given
type-spec.  A THE pattern may be nested inside other patterns, but VAR must
itself be a symbol and not a nested pattern, and type-spec must be a type-spec.

 ~c[(if test)], ~c[(when test)], and ~c[(unless test)] don't actually produce bindings at
all.  Instead, they insert an IF where one branch is the rest of the B* form and
the other is the \"bound\" expression.  For example,
~bv[]
 (b* (((if (atom a)) 0)
      (rest (of-bindings)))
   final-expr)
~ev[]
expands to something like this:
~bv[]
 (if (atom a)
     0
   (b* ((rest (of-bindings)))
     final-expr))
~ev[]
These forms also create an \"implicit progn\" with multiple expressions, like
this:
~bv[]
 (b* (((if (atom a)) (cw \"a is an atom, returning 0\") 0)
      ...)
   ...)
~ev[]

-- Nesting Binders --

The CONS, LIST, LIST*, and backtick binders may be nested arbitrarily inside
other binders.  Often user-defined binders may also be arbitrarily nested.  For
example,

~c[((mv (list `(,a . ,b)) (cons c d)) <form>)]

will result in the following (logical) bindings:

~c[a] bound to ~c[(car (nth 0 (mv-nth 0 <form>)))]

~c[b] bound to ~c[(cdr (nth 0 (mv-nth 0 <form>)))]

~c[c] bound to ~c[(car (mv-nth 1 <form>))]

~c[d] bound to ~c[(cdr (mv-nth 1 <form>))].

-- Ignore, Ignorable, and Side-effect Only Bindings --

The following constructs may be used in place of variables:

Dash (-), used as a top-level binding form, will run the corresponding
expressions (in an implicit progn) for side-effects without binding its value.
Used as a lower-level binding form, it will cause the binding to be ignored or
not created.

Ampersand (&), used as a top-level binding form, will cause the corresponding
expression to be ignored and not run at all.  Used as a lower-level binding
form, it will cause the binding to be ignored or not created.

Any symbol beginning with ?! works similarly to the & form.  It is ignored
or not evaluated at all.

Any symbol beginning with ? but not ?! will make a binding of the symbol
obtained by removing the ?, and will make an IGNORABLE declaration for this
variable.

-- User-Defined Binders --

A new binder form may be created by defining a macro named PATBIND-<name>.  We
discuss the detailed interface of user-defined binders below.  First,
DEF-PATBIND-MACRO provides a simple way to define certain user binders.  For
example, this form is used to define the binder for CONS:
~bv[]
 (def-patbind-macro cons (car cdr))
~ev[]
This defines a binder macro ~c[PATBIND-CONS] which enables ~c[(cons a b)] to be used as
a binder form.  This binder form must take two arguments since two destructor
functions (car cdr) are given to def-patbind-macro.  The destructor functions
are each applied to the form to produce the bindings for the corresponding
arguments of the binder.

There are many cases in which DEF-PATBIND-MACRO is not powerful enough.  For
example, a binder produced by DEF-PATBIND-MACRO may only take a fixed number of
arguments.  More flexible operations may be defined by hand-defining the binder
macro using the form DEF-B*-BINDER; see ~il[DEF-B*-BINDER].

A binder macro PATBIND-<NAME> must take three arguments ARGS, FORMS,
and REST-EXPR.  The form
~bv[]
 (b* (((binder arg1 arg2) binding1 binding2))
    expr)
~ev[]
translates to a macro call
~bv[]
 (patbind-binder (arg1 arg2) (binding1 binding2) expr).
~ev[]
That is, ARGS is the list of arguments given to the binder form, BINDINGS is
the list of expressions bound to them, and EXPR is the result expression to be
run once the bindings are in place.  The definition of the patbind-binder macro
determines how this gets further expanded.  Some informative examples of these
binder macros may be found in bstar.lisp\; simply search for uses of
DEF-B*-BINDER. Here are some notes on defining binder macros.

Often the simplest way to accomplish the intended effect of a patbind macro is
to have it construct another B* form to be recursively expanded, or to call
other patbind macros.  See, for example, the definition of PATBIND-LIST.

Patbind macros for forms that are truly creating bindings should indeed use B*
 (or PATBIND, which is what B* expands to) to create these bindings, so that
ignores and nestings are dealt with uniformly.  See, for example, the
definition of PATBIND-NTHS.

In order to get good performance, destructuring binders such as are produced by
DEF-PATBIND-MACRO bind a variable to any binding that isn't already a variable
or quoted constant.  This is important so that in the following form,
~c[(foo x y)] is run only once:
~bv[]
 (b* (((cons a b) (foo x y))) ...)
~ev[]
In these cases, it is good discipline to check the new variables introduced
using the macro CHECK-VARS-NOT-FREE\; since ACL2 does not have gensym, this is
the best option we have. See any definition produced by DEF-PATBIND-MACRO for
examples, and additionally PATBIND-NTHS, PATBIND-ER, and so forth.
")



(include-book "pack")
(include-book "progndollar")

(defun macro-name-for-patbind (binder)
  (intern-in-package-of-symbol
   (concatenate 'string
                "PATBIND-"
                (symbol-name binder))
   (if (equal (symbol-package-name binder) "COMMON-LISP")
       'acl2::foo
     binder)))

(defconst *patbind-special-syms* '(t nil & -))

(defun int-string (n)
  (coerce (explode-nonnegative-integer n 10 nil) 'string))

(defun str-num-sym (str n)
  (intern (concatenate 'string str (int-string n)) "ACL2"))

(defun ignore-var-name (n)
  (str-num-sym "IGNORE-" n))


(defun debuggable-binder-list-p (x)
  (declare (xargs :guard t))
  (cond ((atom x) 
         (or (equal x nil)
             (cw "; Not a binder list; ends with ~x0, instead of nil.~%" x)))
        ;; This used to check that the cdar was also a cons and a true-list,
        ;; but this can be left up to the individual binders.
        ((consp (car x))
         (debuggable-binder-list-p (cdr x)))
        (t
         (cw "; Not a binder list; first bad entry is ~x0.~%" (car x)))))

(defun debuggable-binders-p (x)
  (declare (xargs :guard t))
  (cond ((atom x) 
         (or (equal x nil)
             (cw "; Not a binder list; ends with ~x0, instead of nil.~%" x)))
        ;; This used to check that the cdar was also a cons and a true-list,
        ;; but this can be left up to the individual binders.
        ((consp (car x)) t)
        (t
         (cw "; Not a binder list; first bad entry is ~x0.~%" (car x)))))

(defun decode-varname-for-patbind (pattern)
  (let* ((name (symbol-name pattern))
         (len (length name))
         (?p (and (<= 1 len)
                  (eql (char name 0) #\?)))
         (?!p (and ?p
                   (<= 2 len)
                   (eql (char name 1) #\!)))
         (sym (cond 
               (?!p (intern-in-package-of-symbol
                     (subseq name 2 nil) pattern))
               (?p (intern-in-package-of-symbol
                    (subseq name 1 nil) pattern))
               (t pattern)))
         (ignorep (cond
                   (?!p 'ignore)
                   (?p 'ignorable))))
    (mv sym ignorep)))



(defun patbindfn (pattern assign-exprs nested-expr)
  (cond ((eq pattern '-)
         ;; A dash means "run this for side effects."  In this case we allow
         ;; multiple terms; these form an implicit progn, in the common-lisp sense.
         `(prog2$ (progn$ . ,assign-exprs)
                  ,nested-expr))
        ((member pattern *patbind-special-syms*)
         ;; &, T, NIL mean "don't bother evaluating this."
         nested-expr)
        ((atom pattern)
         ;; A binding to a single variable.  Here we don't allow multiple
         ;; expressions; we believe it's more readable to use - to run things
         ;; for side effects, and this might catch some paren errors.
         (if (cdr assign-exprs)
             (er hard 'b* "~
The B* binding of ~x0 to ~x1 isn't allowed because the binding of a variable must be a
single term." pattern assign-exprs)
           (mv-let (sym ignorep)
             (decode-varname-for-patbind pattern)
             ;; Can we just refuse to bind a variable marked ignored?
             (if (eq ignorep 'ignore)
                 nested-expr
               `(let ((,sym ,(car assign-exprs)))
                  ,@(and ignorep `((declare (,ignorep ,sym))))
                  ,nested-expr)))))
        ((eq (car pattern) 'quote)
         ;; same idea as &, t, nil
         nested-expr)
        (t ;; Binding macro call.
         (let* ((binder (car pattern))
                (patbind-macro (macro-name-for-patbind binder))
                (args (cdr pattern)))
           `(,patbind-macro ,args ,assign-exprs ,nested-expr)))))
             
        

         
         
(defmacro patbind (pattern assign-exprs nested-expr)
  (patbindfn pattern assign-exprs nested-expr))


;; (defun b*-fn1 (bindlist expr)
;;   (declare (xargs :guard (debuggable-binders-p bindlist)))
;;   (if (atom bindlist)
;;       expr
;;     `(patbind ,(caar bindlist) ,(cdar bindlist)
;;               ,(b*-fn1 (cdr bindlist) expr))))

;; (defun b*-fn (bindlist exprs)
;;   (declare (xargs :guard (and (debuggable-binders-p bindlist)
;;                               (consp exprs))))
;;   (b*-fn1 bindlist `(progn$ . ,exprs)))

(defun b*-fn (bindlist exprs)
  (declare (xargs :guard (and (debuggable-binders-p bindlist)
                              (consp exprs))))
  (if (atom bindlist)
      (cons 'progn$ exprs)
    `(patbind ,(caar bindlist) ,(cdar bindlist)
              (b* ,(cdr bindlist) . ,exprs))))

(defmacro b* (bindlist expr &rest exprs)
  (declare (xargs :guard (debuggable-binders-p bindlist)))
  (b*-fn bindlist (cons expr exprs)))


(defdoc b*-binders ":Doc-section b*
B*-BINDERS: List of the available directives usable in B*.~/
~/~/")


(defmacro def-b*-binder (name &rest rest)
  (let* ((macro-name (macro-name-for-patbind name))
         (decls-and-doc (butlast rest 1))
         (body (car (last rest)))
         (decls (remove-strings decls-and-doc))
         (doc (car (get-string decls-and-doc)))
         (doc-sectionp (and doc 
                            (equal (string-upcase (subseq doc 0 12))
                                   ":DOC-SECTION"))))
    `(progn
       (defmacro ,macro-name (args forms rest-expr)
         ,(if doc
              (if doc-sectionp
                  doc
                (concatenate 'string ":DOC-SECTION ACL2::B*-BINDERS
" doc))
            (concatenate 'string
                         ":DOC-SECTION ACL2::B*-BINDERS
B* binder form " (symbol-name name) "~/
 (placeholder)~/~/"))
         ,@decls
         ,body)
       (table b*-binder-table ',name ',macro-name))))


(defdoc def-b*-binder
  ":doc-section b*
DEF-B*-BINDER: Introduce a new form usable inside B*.~/
Usage:
~bv[]
 (def-b*-binder <name> <declare> <doc> <body>)
~ev[]
Introduces a B* binder form of the given name.  The given body, which may use
the variables args, forms, and rest-expr, is used to
macroexpand a form like the following:
~bv[]
 (b* (((<name> . <args>) . <forms>)) <rest-expr>)
~ev[]
The documentation string and declaration forms are optional\; a placeholder doc
string will be produced under :doc-section B*-BINDERS if none is provided.  It
is recommended that the string use that :doc-section, since this provides a
single location where the user may see all of the available binder forms.  If
no doc-section is provided, B*-BINDERS will be used.~/

This works by introducing a macro named PATBIND-<name>.  See ~il[b*] for more
details.~/")









(defmacro destructure-guard (binder args bindings len)
  `(and (or (and (true-listp ,args)
                 . ,(and len `((= (length ,args) ,len))))
            (cw "~%~%**** ERROR ****
Pattern constructor ~x0 needs a true-list of ~@1arguments, but was given ~x2~%~%"
                ',binder ,(if len `(msg "~x0 " ,len) "")
                ,args))
        (or (and (consp ,bindings)
                 (eq (cdr ,bindings) nil))
            (cw "~%~%**** ERROR ****
Pattern constructor ~x0 needs exactly one binding expression, but was given ~x1~%~%"
                ',binder ,bindings))))



(defun destructor-binding-list (args destructors binding)
  (if (atom args)
      nil
    (cons (list (car args) (list (car destructors) binding))
          (destructor-binding-list (cdr args) (cdr destructors) binding))))

(defmacro def-patbind-macro (binder destructors &rest rst)
  (let ((len (length destructors))
        (doc (get-string rst)))
    `(def-b*-binder ,binder ,@doc
       (declare (xargs :guard
                       (destructure-guard ,binder args forms ,len)))
       (let* ((binding (car forms))
              (computedp (or (atom binding)
                             (eq (car binding) 'quote)))
              (bexpr (if computedp binding (pack binding)))
              (binders (destructor-binding-list args ',destructors bexpr)))
         (if computedp
             `(b* ,binders ,rest-expr)
           `(let ((,bexpr ,binding))
              (declare (ignorable ,bexpr))
              (b* ,binders
                (check-vars-not-free (,bexpr) ,rest-expr))))))))

;; The arg might be a plain variable, an ignored or ignorable variable, or a
;; binding expression.
(defun var-ignore-list-for-patbind-mv (args igcount mv-vars binders ignores ignorables freshvars)
  (if (atom args)
      (mv (reverse mv-vars)
          (reverse binders)
          (reverse ignores)
          (reverse ignorables)
          (reverse freshvars))
    (mv-let (mv-var binder freshp ignorep)
      (cond ((or (member (car args) *patbind-special-syms*)
                 (quotep (car args))
                 (and (atom (car args)) (not (symbolp (car args)))))
             (let ((var (ignore-var-name igcount)))
               (mv var nil nil 'ignore)))
            ((symbolp (car args))
             (mv-let (sym ignorep)
               (decode-varname-for-patbind (car args))
               (case ignorep
                 (ignore (mv sym nil nil 'ignore))
                 (ignorable (mv sym nil nil 'ignorable))
                 (t (mv sym nil nil nil)))))
            (t ;; (and (consp (car args))
             ;;                   (not (eq (caar args) 'quote)))
             (let ((var (pack (car args))))
               (mv var (list (car args) var) t nil))))
      (var-ignore-list-for-patbind-mv
       (cdr args)
       (if (eq ignorep 'ignore) (1+ igcount) igcount)
       (cons mv-var mv-vars)
       (if binder (cons binder binders) binders)
       (if (eq ignorep 'ignore) (cons mv-var ignores) ignores)
       (if (eq ignorep 'ignorable) (cons mv-var ignorables) ignorables)
       (if freshp (cons mv-var freshvars) freshvars)))))
          


(def-b*-binder mv
  " B* binder for multiple values~/
Usage example:
~bv[]
 (b* (((mv a b c) (form-returning-three-values)))
    form)
~ev[]
is equivalent to
~bv[]
 (mv-let (a b c) (form-returning-three-values)
   form).
~ev[]

~l[B*] for background.

The MV binder only makes sense as a top-level binding, but each of its
arguments may be a recursive binding.~/~/"
  (declare (xargs :guard (destructure-guard mv args forms nil)))
  (mv-let (vars binders ignores ignorables freshvars)
    (var-ignore-list-for-patbind-mv args 0 nil nil nil nil nil)
    `(mv-let ,vars ,(car forms)
       (declare (ignore . ,ignores))
       (declare (ignorable . ,ignorables))
       (check-vars-not-free
        ,ignores
        (b* ,binders
          (check-vars-not-free ,freshvars ,rest-expr))))))

(def-patbind-macro cons (car cdr)
  "B* binder for CONS decomposition using CAR/CDR~/
Usage:
~bv[]
 (b* (((cons a b) (binding-form))) (result-form))
~ev[]
is equivalent to
~bv[]
 (let* ((tmp (binding-form))
        (a (car tmp))
        (b (cdr tmp)))
    (result-form))
~ev[]

~l[B*] for background.

Each of the arguments to the CONS binder may be a recursive binder, and CONS
may be nested inside other bindings.~/~/")

(defun nths-binding-list (args n form)
  (if (atom args)
      nil
    (cons (list (car args) `(nth ,n ,form))
          (nths-binding-list (cdr args) (1+ n) form))))


(def-b*-binder nths
  "B* binder for list decomposition using NTH~/
Usage:
~bv[]
 (b* (((nths a b c) lst)) form)
~ev[]
is equivalent to
~bv[]
 (b* ((a (nth 0 lst))
      (b (nth 1 lst))
      (c (nth 2 lst)))
   form).
~ev[]

~l[B*] for background.

Each of the arguments to the NTHS binder may be a recursive binder, and NTHS
may be nested inside other bindings.~/~/"
  (declare (xargs :guard (destructure-guard nths args forms nil)))
  (let* ((binding (car forms))
         (evaledp (or (atom binding) (eq (car binding) 'quote)))
         (form (if evaledp binding (pack binding)))
         (binders (nths-binding-list args 0 form)))
    (if evaledp
        `(b* ,binders ,rest-expr)
      `(let ((,form ,binding))
         (declare (ignorable ,form))
         (b* ,binders
           (check-vars-not-free (,form) ,rest-expr))))))



(def-b*-binder nths*
  "B* binder for list decomposition using NTH, with one final NTHCDR~/
Usage:
~bv[]
 (b* (((nths* a b c d) lst)) form)
~ev[]
is equivalent to
~bv[]
 (b* ((a (nth 0 lst))
      (b (nth 1 lst))
      (c (nth 2 lst))
      (d (nthcdr 3 lst)))
   form).
~ev[]

~l[B*] for background.

Each of the arguments to the NTHS binder may be a recursive binder, and NTHS
may be nested inside other bindings.~/~/"
  (declare (xargs :guard (and (destructure-guard nths args forms nil)
                              (< 0 (len args)))))
  (let* ((binding (car forms))
         (evaledp (or (atom binding) (eq (car binding) 'quote)))
         (form (if evaledp binding (pack binding)))
         (binders (append (nths-binding-list (butlast args 1) 0 form)
                          `((,(car (last args)) (nthcdr ,(1- (len args)) ,form))))))
    (if evaledp
        `(b* ,binders ,rest-expr)
      `(let ((,form ,binding))
         (declare (ignorable ,form))
         (b* ,binders
           (check-vars-not-free (,form) ,rest-expr))))))
  




(def-b*-binder list
  "B* binder for list decomposition using CAR/CDR~/
Usage:
~bv[]
 (b* (((list a b c) lst)) form)
~ev[]
is equivalent to
~bv[]
 (b* ((a (car lst))
      (tmp1 (cdr lst))
      (b (car tmp1))
      (tmp2 (cdr tmp1))
      (c (car tmp2)))
   form).
~ev[]

~l[B*] for background.

Each of the arguments to the LIST binder may be a recursive binder, and LIST
may be nested inside other bindings.~/~/"
  (declare (xargs :guard (destructure-guard list args forms nil)))
  (if (atom args)
      rest-expr
    `(patbind-cons (,(car args) (list . ,(cdr args))) ,forms ,rest-expr)))

(def-b*-binder list*
  "B* binder for list* decomposition using CAR/CDR~/
Usage:
~bv[]
 (b* (((list* a b c) lst)) form)
~ev[]
is equivalent to
~bv[]
 (b* ((a (car lst))
      (tmp1 (cdr lst))
      (b (car tmp1))
      (c (cdr tmp1)))
   form).
~ev[]

~l[B*] for background.

Each of the arguments to the LIST* binder may be a recursive binder, and LIST*
may be nested inside other bindings.~/~/"
  (declare (xargs :guard (and (consp args)
                              (destructure-guard list* args forms nil))))
  (if (atom (cdr args))
      `(patbind ,(car args) ,forms ,rest-expr)
    `(patbind-cons (,(car args) (list* . ,(cdr args))) ,forms ,rest-expr)))



(defun assigns-for-assocs (args alist)
  (if (atom args)
      nil
    (cons (if (consp (car args))
              `(,(caar args) (cdr (assoc ,(cadar args) ,alist)))
            (mv-let (sym ign)
              (decode-varname-for-patbind (car args))
              (declare (ignore ign))
              `(,(car args) (cdr (assoc ',sym ,alist)))))
          (assigns-for-assocs (cdr args) alist))))

(def-b*-binder assocs
  "B* binder for alist values~/
Usage:
~bv[]
 (b* (((assocs (a akey) b (c 'foo)) alst)) form)
~ev[]
is equivalent to
~bv[]
 (b* ((a (cdr (assoc akey alst)))
      (b (cdr (assoc 'b alst)))
      (c (cdr (assoc 'foo alst))))
   form).
~ev[]

~l[B*] for background.

The arguments to the ASSOCS binder should be either single symbols or pairs
~c[(VAR KEY)].  In the pair form, ~c[VAR] is assigned to the associated value
of ~c[KEY] in the bound object, which should be an alist.  Note that ~c[KEY]
does not get quoted; it may itself be some expression.  An argument consisting
of the single symbol ~c[VAR] is equivalent to the pair ~c[(VAR 'VAR)].

Each of the arguments in the ~c[VAR] position of the pair form may be a
recursive binder, and ASSOCS may be nested inside other bindings.~/~/"
  (mv-let (pre-bindings name rest)
    (if (and (consp (car forms))
             (not (eq (caar forms) 'quote)))
        (mv `((?tmp-for-assocs ,(car forms)))
            'tmp-for-assocs
            `(check-vars-not-free (tmp-for-assocs)
                            ,rest-expr))
      (mv nil (car forms) rest-expr))
    `(b* (,@pre-bindings
          . ,(assigns-for-assocs args name))
       ,rest)))


(def-b*-binder er
  "B* binder for error triples~/
Usage:
~bv[]
 (b* (((er x) (error-triple-form))) (result-form))
~ev[]
is equivalent to
~bv[]
 (er-let* ((x (error-triple-form))) (result-form)),
~ev[]
which itself is approximately equivalent to
~bv[]
 (mv-let (erp x state)
         (error-triple-form)
     (if erp
         (mv erp x state)
       (result-form)))
~ev[]

~l[B*] for background.

The ER binder only makes sense as a top-level binding, but its argument may be
a recursive binding.~/~/"
  (declare (xargs :guard (destructure-guard er args forms 1)))
  `(mv-let (patbind-er-fresh-variable-for-erp
            patbind-er-fresh-variable-for-val
            state)
     ,(car forms)
     (if patbind-er-fresh-variable-for-erp
         (mv patbind-er-fresh-variable-for-erp
             patbind-er-fresh-variable-for-val
             state)
       (patbind ,(car args)
                (patbind-er-fresh-variable-for-val)
                (check-vars-not-free
                 (patbind-er-fresh-variable-for-val
                  patbind-er-fresh-variable-for-erp)
                 ,rest-expr)))))

(def-b*-binder state-global
  "B* binder for state globals~/
Usage:
~bv[]
 (b* (((state-global x) (value-form))) (result-form))
~ev[]
is equivalent to
~bv[]
 (state-global-let* ((x (value-form))) (result-form)).
~ev[]

~l[B*] for background.~/~/"
  (declare (xargs :guard
                  (and (destructure-guard
                        state-global args forms 1)
                       (or (symbolp (car args))
                           (cw "~%~%**** ERROR ****
Pattern constructor ~x0 needs a single argument which is a symbol, but got ~x1~%~%"
                               'state-global args)))))
  `(state-global-let*
    ((,(car args) ,(car forms)))
    ,rest-expr))


(def-b*-binder when
  "B* control flow operator~/
Usage:
~bv[]
 (b* (((when (condition-form))
        (early-form1) ... (early-formN))
      ... rest of bindings ...)
   (late-result-form))
~ev[]
is equivalent to
~bv[]
 (if (condition-form)
     (progn$ (early-form1) ... (early-formN))
   (b* (... rest of bindings ...)
     (late-result-form)))
~ev[]

~l[B*] for background.

Effectively, this provides a way to exit early from the sequence of
computations represented by a list of B* binders.

In the special case where no early-forms are provided, the condition itself is
returned.  I.e.,
~bv[]
 (b* (((when (condition-form)))
      ... rest of bindings)
    (late-result-form))
~ev[]
is equivalent to
~bv[]
 (or (condition-form)
     (b* (... rest of bindings ...)
        (late-result-form)))
~ev[]
~/~/"
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  (if forms
      `(if ,(car args)
           (progn$ . , forms)
         ,rest-expr)
    `(or ,(car args) ,rest-expr)))

(def-b*-binder if
  "B* control flow operator~/
The B* binders IF and WHEN are exactly equivalent.  ~l[PATBIND-WHEN].~/~/"
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       (progn$ . ,forms)
     ,rest-expr))

(def-b*-binder unless
  "B* control flow operator~/
The B* binder UNLESS is exactly like WHEN, but negates the condition so that
the early exit is taken when the condition is false.  ~l[PATBIND-WHEN].~/~/"
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       ,rest-expr
     (progn$ . ,forms)))
  
(def-b*-binder run-when
  "B* conditional execution operator~/
Usage:
~bv[]
 (b* (((run-when (condition-form)) (run-form1) ... (run-formn)))
   (result-form))
~ev[]
is equivalent to
~bv[]
 (prog2$ (and (condition-form)
              (progn$ (run-form1) ... (run-formn)))
         (result-form)).
~ev[]

~l[B*] for background.~/~/"
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(prog2$ (and ,(car args)
               (progn$ . , forms))
           ,rest-expr))

(def-b*-binder run-if
  "B* conditional execution operator~/
The B* binders RUN-IF and RUN-WHEN are exactly equivalent.
~l[PATBIND-RUN-WHEN].~/~/"
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(prog2$ (and ,(car args)
                (progn$ . ,forms))
           ,rest-expr))

(def-b*-binder run-unless
  "B* control flow operator~/
The B* binder RUN-UNLESS is exactly like RUN-WHEN, but negates the condition so
that the extra forms are run when the condition is false.
~l[PATBIND-RUN-WHEN].~/~/"
  (declare (Xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(prog2$ (or ,(car args)
               (progn$ . ,forms))
           ,rest-expr))

(def-b*-binder the
  "B* type declaration operator~/
Usage:
~bv[]
 (b* (((the integer x) (form))) (result-form))
~ev[]
is equivalent to
~bv[]
 (let ((x (form)))
   (declare (type integer x))
   (result-form))
~ev[]

~l[B*] for background.

The THE binder form only makes sense on variables, though those variables may
be prefixed with the ? or ?! operators to make them ignorable or ignored.
However, it may be nested within other binder forms.~/~/"
  (declare (xargs :guard
                  (and (destructure-guard the args forms 2)
                       (or (translate-declaration-to-guard
                            (car args) 'var nil)
                           (cw "~%~%**** ERROR ****
The first argument to pattern constructor ~x0 must be a type-spec, but is ~x1~%~%"
                               'the (car args)))
                       (or (symbolp (cadr args))
                           (cw "~%~%**** ERROR ****
The second argument to pattern constructor ~x0 must be a symbol, but is ~x1~%~%"
                               'the (cadr args))))))
  (mv-let (sym ignorep)
    (decode-varname-for-patbind (cadr args))
    (if (eq ignorep 'ignore)
        rest-expr
      `(let ((,sym ,(car forms)))
         ,@(and ignorep `((declare (ignorable ,sym))))
         (declare (type ,(car args) ,sym))
         ,rest-expr))))
      

      



(set-state-ok t)

(with-output 
 :off warning
 (local
  (progn
    (defun return-two-values (a b)
      (mv a b))

    (defun transl-equal-tests-fn (tests)
      (if (atom tests)
          `(mv nil state)
        `(mv-let (err val state)
           (transl-equal ',(caar tests) ',(cadar tests))
           (if (or err (not val))
               (mv ',(car tests) state)
             ,(transl-equal-tests-fn (cdr tests))))))

    (defmacro transl-equal-tests (&rest tests)
      (transl-equal-tests-fn tests))


    (defun patbind-tests-fn (tests state)
      (declare (xargs :mode :program))
      (if (atom tests)
          (value '(value-triple :invisible))
        (mv-let (erp val state)
          (thm-fn `(equal ,(caar tests) ,(cadar tests))
                  state '(("goal" :in-theory nil)) nil nil)
          (if erp
              (mv (msg "~% ****** ERROR ******~%~
Testing of the patbind macro failed on expression ~x0~%~%" (car tests))
                  val state)
            (patbind-tests-fn (cdr tests) state)))))

    (defmacro patbind-run-tests (&rest tests)
      `(make-event
        (patbind-tests-fn ',tests state)))
    ;;        (mv-let (err val state)
    ;;          (transl-equal-tests ,@tests)
    ;;          (declare (ignore val))
    ;;          (if err
    ;;              (mv t
    ;;                  (er hard? 'patbind-run-tests
    ;;                      "~% ****** ERROR ******~%~
    ;; Testing of the patbind macro failed on expression ~x0~%~%" err)
    ;;                  state)
    ;;            (value (prog2$ (cw "
    ;; Testing of the patbind macro passed.~%")
    ;;                           `(value-triple 'tests-ok)))))
    ;;        :check-expansion (value-triple 'tests-ok)))


    (patbind-run-tests
     ;; TEST CASES

     ((patbind (cons (cons a b) c) (x) (list a b c))
      (let* ((|(CAR X)| (car x))
             (c (cdr x)))
        (let* ((a (car |(CAR X)|))
               (b (cdr |(CAR X)|)))
          (list a b c))))

     ((patbind x ((cons 'a 'b)) x)
      (let ((x (cons 'a 'b))) x))

     ((patbind (mv a b) ((mv 'a 'b)) (list a b))
      (mv-let (a b) (mv 'a 'b) (list a b)))

     ((patbind & ((cw "Hello")) nil)
      nil)

     ((patbind - ((cw "Hello")) nil)
      (prog2$ (cw "Hello")
              nil))

     ((patbind (cons a &) ('(a b)) a)
      (let ((a (car '(a b))))
        a))

     ((patbind (cons (cons a b) c) (x)
               (list a b c))
      (let ((|(CONS A B)| (car x))
            (c (cdr x)))
        (let ((a (car |(CONS A B)|))
              (b (cdr |(CONS A B)|)))
          (list a b c))))

     ((patbind (cons (cons a b) c) ((cons x y))
               (list a b c))
      (let ((|(CONS (CONS A B) C)| (cons x y)))
        (let ((|(CONS A B)| (car |(CONS (CONS A B) C)|))
              (c (cdr |(CONS (CONS A B) C)|)))
          (let ((a (car |(CONS A B)|))
                (b (cdr |(CONS A B)|)))
            (list a b c)))))

     ((patbind (cons (cons & b) c) ((cons x y))
               (list b c))
      (let ((|(CONS (CONS & B) C)| (cons x y)))
        (let ((|(CONS & B)| (car |(CONS (CONS & B) C)|))
              (c (cdr |(CONS (CONS & B) C)|)))
          (let ((b (cdr |(CONS & B)|)))
            (list b c)))))

     ((patbind (cons (cons a &) c) ((cons x y))
               (list a c))
      (let ((|(CONS (CONS A &) C)| (cons x y)))
        (let ((|(CONS A &)| (car |(CONS (CONS A &) C)|))
              (c (cdr |(CONS (CONS A &) C)|)))
          (let ((a (car |(CONS A &)|)))
            (list a c)))))


     ((patbind (mv (cons a (cons b c)) d)
               ((return-two-values x y))
               (list a b c d))
      (mv-let (|(CONS A (CONS B C))| d)
        (return-two-values x y)
        (let ((a (car |(CONS A (CONS B C))|))
              (|(CONS B C)| 
               (cdr |(CONS A (CONS B C))|)))
          (let ((b (car |(CONS B C)|))
                (c (cdr |(CONS B C)|)))
            (list a b c d)))))

     ((patbind (mv (cons a (cons b c)) &)
               ((return-two-values x y))
               (list a b c d))
      (mv-let (|(CONS A (CONS B C))| ignore-0)
        (return-two-values x y)
        (declare (ignore ignore-0))
        (let ((a (car |(CONS A (CONS B C))|))
              (|(CONS B C)| 
               (cdr |(CONS A (CONS B C))|)))
          (let ((b (car |(CONS B C)|))
                (c (cdr |(CONS B C)|)))
            (list a b c d)))))

     ((patbind (mv (cons a (cons & c)) &)
               ((return-two-values x y))
               (list a c d))
      (mv-let (|(CONS A (CONS & C))| ignore-0)
        (return-two-values x y)
        (declare (ignore ignore-0))
        (let ((a (car |(CONS A (CONS & C))|))
              (|(CONS & C)| 
               (cdr |(CONS A (CONS & C))|)))
          (let ((c (cdr |(CONS & C)|)))
            (list a c d)))))
 
     ((patbind `(,a ,b) ((cons x y)) (list a b))
      (let ((|(CONS A (CONS B (QUOTE NIL)))| (cons x y)))
        (let ((a (car |(CONS A (CONS B (QUOTE NIL)))|))
              (|(CONS B (QUOTE NIL))|
               (cdr |(CONS A (CONS B (QUOTE NIL)))|)))
          (let ((b (car |(CONS B (QUOTE NIL))|)))
            (list a b)))))

     ))))
