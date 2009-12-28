(in-package "ACL2")

;; Contact: Sol Swords <sswords@cs.utexas.edu>

;; This book contains the macro b*, which acts like let* with certain
;; extensions.  Some of its features:
;; - Can bind single values and MVs within the same let*-like sequence
;; of assignments, without nesting
;; - Can bind variables using user-defined pattern-matching idioms
;; - Eliminates ignore and ignorable declarations

(defdoc b* ":DOC-SECTION Programming
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
forms may be nested.

(mv a b ...) produces an MV-LET binding

(cons a b) produces a binding of the CAR and CDR of the corresponding expression

(er a) produces an ER-LET* binding

(list a b ...) produces a binding of (car val), (cadr val), etc, where val
is the result of the corresponding expression

(nths a b ...) produces a binding of (nth 0 val), (nth 1 val), etc, where val
is the result of the corresponding expression

(list* a b), `(,a . ,b) are alternatives to the CONS binder.

(the type-spec var) produces a binding of var to the result of the
corresponding expression, and a declaration that var is of the given
type-spec.  A THE pattern may be nested inside other patterns, but VAR must
itself be a symbol and not a nested pattern, and type-spec must be a type-spec.

(if test), (when test), and (unless test) don't actually produce bindings at
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
((mv (list `(,a . ,b)) (cons c d)) <form>)
will result in the following (logical) bindings:
a bound to (car (nth 0 (mv-nth 0 <form>)))
b bound to (cdr (nth 0 (mv-nth 0 <form>)))
c bound to (car (mv-nth 1 <form>))
d bound to (cdr (mv-nth 1 <form>)).

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
(def-patbind-macro cons (car cdr))
This defines a binder macro PATBIND-CONS which enables (cons a b) to be used as
a binder form.  This binder form must take two arguments since two destructor
functions (car cdr) are given to def-patbind-macro.  The destructor functions
are each applied to the form to produce the bindings for the corresponding
arguments of the binder.

There are many cases in which DEF-PATBIND-MACRO is not powerful enough.  For
example, a binder produced by DEF-PATBIND-MACRO may only take a fixed number of
arguments.  To more flexibly create binders, one must define binder macros by
hand.

A binder macro PATBIND-<NAME> must take three arguments ARGS, BINDINGS,
and EXPR.  The form
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
binder macros may be found in bstar.lisp\; simply search for macro declarations
whose names begin with PATBIND-.  Here are some notes on defining binder macros.

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
        ((and (consp (car x))
              (consp (cdar x))
              (true-listp (cddar x)))
         (debuggable-binder-list-p (cdr x)))
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


(defun b*-fn1 (bindlist expr)
  (declare (xargs :guard (debuggable-binder-list-p bindlist)))
  (if (atom bindlist)
      expr
    `(patbind ,(caar bindlist) ,(cdar bindlist)
              ,(b*-fn1 (cdr bindlist) expr))))

(defun b*-fn (bindlist exprs)
  (declare (xargs :guard (and (debuggable-binder-list-p bindlist)
                              (consp exprs))))
  (b*-fn1 bindlist `(progn$ . ,exprs)))

(defmacro b* (bindlist expr &rest exprs)
  (declare (xargs :guard (debuggable-binder-list-p bindlist)))
  (b*-fn bindlist (cons expr exprs)))





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

(defmacro def-patbind-macro (binder destructors)
  (let ((len (length destructors)))
    `(defmacro ,(macro-name-for-patbind binder) (args bindings expr)
       (declare (xargs :guard
                       (destructure-guard ,binder args bindings ,len)))
       (let* ((binding (car bindings))
              (computedp (or (atom binding)
                             (eq (car binding) 'quote)))
              (bexpr (if computedp binding (pack binding)))
              (binders (destructor-binding-list args ',destructors bexpr)))
         (if computedp
             `(b* ,binders ,expr)
           `(let ((,bexpr ,binding))
              (declare (ignorable ,bexpr))
              (b* ,binders
                (check-vars-not-free (,bexpr) ,expr))))))))

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
          


(defmacro patbind-mv (args bindings expr)
  (declare (xargs :guard (destructure-guard mv args bindings nil)))
  (mv-let (vars binders ignores ignorables freshvars)
    (var-ignore-list-for-patbind-mv args 0 nil nil nil nil nil)
    `(mv-let ,vars ,(car bindings)
       (declare (ignore . ,ignores))
       (declare (ignorable . ,ignorables))
       (check-vars-not-free
        ,ignores
        (b* ,binders
          (check-vars-not-free ,freshvars ,expr))))))

(def-patbind-macro cons (car cdr))

(defun nths-binding-list (args n form)
  (if (atom args)
      nil
    (cons (list (car args) `(nth ,n ,form))
          (nths-binding-list (cdr args) (1+ n) form))))


(defmacro patbind-nths (args bindings expr)
  (declare (xargs :guard (destructure-guard nths args bindings nil)))
  (let* ((binding (car bindings))
         (evaledp (or (atom binding) (eq (car binding) 'quote)))
         (form (if evaledp binding (pack binding)))
         (binders (nths-binding-list args 0 form)))
    (if evaledp
        `(b* ,binders ,expr)
      `(let ((,form ,binding))
         (declare (ignorable ,form))
         (b* ,binders
           (check-vars-not-free (,form) ,expr))))))
  




(defmacro patbind-list (args bindings expr)
  (declare (xargs :guard (destructure-guard list args bindings nil)))
  (if (atom args)
      expr
    `(patbind-cons (,(car args) (list . ,(cdr args))) ,bindings ,expr)))

(defmacro patbind-list* (args bindings expr)
  (declare (xargs :guard (and (consp args)
                              (destructure-guard list* args bindings nil))))
  (if (atom (cdr args))
      `(patbind ,(car args) ,bindings ,expr)
    `(patbind-cons (,(car args) (list* . ,(cdr args))) ,bindings ,expr)))

(defmacro patbind-er (args bindings expr)
  (declare (xargs :guard (destructure-guard er args bindings 1)))
  `(mv-let (patbind-er-fresh-variable-for-erp
            patbind-er-fresh-variable-for-val
            state)
     ,(car bindings)
     (if patbind-er-fresh-variable-for-erp
         (mv patbind-er-fresh-variable-for-erp
             patbind-er-fresh-variable-for-val
             state)
       (patbind ,(car args)
                (patbind-er-fresh-variable-for-val)
                (check-vars-not-free
                 (patbind-er-fresh-variable-for-val
                  patbind-er-fresh-variable-for-erp)
                 ,expr)))))

(defmacro patbind-state-global (args bindings expr)
  (declare (xargs :guard
                  (and (destructure-guard
                        state-global args bindings 1)
                       (or (symbolp (car args))
                           (cw "~%~%**** ERROR ****
Pattern constructor ~x0 needs a single argument which is a symbol, but got ~x1~%~%"
                               'state-global args)))))
  `(state-global-let*
    ((,(car args) ,(car bindings)))
    ,expr))


(defmacro patbind-when (args bindings expr)
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       (progn$ . , bindings)
     ,expr))

(defmacro patbind-if (args bindings expr)
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       (progn$ . ,bindings)
     ,expr))

(defmacro patbind-unless (args bindings expr)
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       ,expr
     (progn$ . ,bindings)))
  
(defmacro patbind-the (args bindings expr)
  (declare (xargs :guard
                  (and (destructure-guard the args bindings 2)
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
        expr
      `(let ((,sym ,(car bindings)))
         ,@(and ignorep `((declare (ignorable ,sym))))
         (declare (type ,(car args) ,sym))
         ,expr))))
      



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
