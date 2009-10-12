(in-package "ACL2")

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
     ;; ignored:
     (`(,e (,f . ,?!g)) (makes-a-list-of-conses b))

     ;; LIST and LIST* are also supported:
     ((list a b) '((1 2) (3 4)))
     ((list* a b c) '((1 2) (3 4) 5 6 7))

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
(<binder-form> <expression>).  See below for discussion of binder forms.


-- Basic let*-like usage --
B* can be used exactly like LET*, except that it does not yet support DECLARE
forms.  However, IGNORE or IGNORABLE declarations are inserted by B* according
to the syntax of the variables bound; see below.  B* also supports multiple
result expressions after the binding list; these are run in sequence and the
result of the last such form is returned.

-- Binder Forms --
The following binder forms are supported by this book alone, but support may
be added by the user for other binding forms.  In most cases, these binding
forms may be nested.

(mv a b ...) produces an MV-LET binding

(cons a b) produces a binding of the CAR and CDR of the corresponding expression

(er a) produces an ER-LET* binding

(list a b ...) produces a binding of (NTH 0 val), (NTH 1 val), etc, where val
is the result of the corresponding expression

(list* a b), `(,a . ,b) are alternatives to the CONS binder.

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
expression for side-effects without binding its value.  Used as a lower-level
binding form, it will cause the binding to be ignored or not created.  

Ampersand (&), used as a top-level binding form, will cause the corresponding
expression to be ignored and not run at all.  Used as a lower-level binding
form, it will cause the binding to be ignored or not created.

Any symbol beginning with ?! works similarly to the & form.  It is ignored
or not evaluated at all.

Any symbol beginning with ? but not ?! will make a binding of the symbol
obtained by removing the ?, and will make an IGNORABLE declaration for this
variable.

-- User-Defined Binders --
A new binder form may be created by defining a macro named PATBIND-<name>, in
the ACL2 package.  We discuss the detailed interface of user-defined binders
below.  First, DEF-PATBIND-MACRO provides a simple way to define certain user
binders.  For example, this form is used to define the binder for CONS:
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

A binder macro PATBIND-<NAME> must take four arguments ARGS, BINDING, IGNORES,
and EXPR.  EXPR is the result expression to be run once the bindings are in
place.  BINDING is the term to be decomposed and bound to ARGS, which are
variables corresponding to the arguments given to the binder form.  Finally,
IGNORES is a list of the same length as ARGS each element of which is either
NIL or one of the symbols IGNORE (meaning the corresponding argument is an
ignored variable) or IGNORABLE (meaning the corresponding argument is an
ignorable variable.

The binder macro must produce a form that performs the bindings of ARGS to the
appropriate forms involving BINDING, makes declarations appropriate for
IGNORES, and finally runs EXPR.  For examples of this, see the definitions of
binder macros PATBIND-LIST and PATBIND-LIST*.

The default behavior on each binder is to first bind a variable to the result
of computing the form.  When the form returns multiple values, this is the
wrong behavior.  The MV and ER binders are treated specially for this purpose.
User binders are treated this way if they end in the character +.
")



;; Here are some examples of how it can be used:
#||
(b* ;; let*-like binding to a single variable:
    ((x (cons 'a 'b))
     ;; mv binding
     ((mv y z) (return-two-values x x))
     ;; No binding: expression evaluated for side effects
     (- (cw "Hello")) ;; prints "Hello"
     ;; Dont-care: expression not evaluated at all
     ;; (why do we want this? see below.)
     (& (cw "Hello")) ;; does not print "Hello"
     ;; MV which ignores a value:
     ((mv & a) (return-garbage-in-first-mv y z))
     ;; Pattern-based binding using cons:
     ((cons (cons b c) d) (must-return-nested-conses a))
     ;; Alternate form of pattern binding with cons nests:
     (`(,e (,f . ,g)) (makes-a-list-of-conses b))
     ;; Pattern with user-defined constructor:
     ((my-tuple foo bar hum) (something-of-type-my-tuple e c g))
     ;; Don't-cares with pattern bindings:
     ((my-tuple & (cons carbar &) hum) (something-else foo f hum))
     ;; Pattern inside an mv:
     ((mv a (cons & c)) (make-mv-with-cons)))
  (some-expression ....))
||#
;; Syntax of b*:
;; (b* <binder-list> <expr>) where
;; 
;; binder-list: ([(<pattern> <expr>)])
;;
;; pattern: <varname-symbol> | & | - | nil | (quote <expr>)
;;          | (<pattern-constructor> [<pattern>])
;;
;; pattern-constructor: mv | cons | <user-defined-constructor>
;;
;;
;; Pattern constructors can be defined using the macro
;; def-patbind-macro, as in (def-patbind-macro cons (car cdr)), where
;; the first argument is the constructor symbol and the second is a
;; list of field accessor functions.




;; Technical details:
;;
;; b* is based on another macro, patbind, much like let* is based on let;
;; a call to b* expands to one or more nested calls to patbind.
;; Specifically, as with let* and let, each item in the binder list
;; results in one call to patbind, so that variables bound in the list
;; are available for use in the next binding expression.
;;
;; Each binding is specified by a pattern and an expression.  The
;; expression is evaluated and the pattern is then matched against its
;; value recursively, splitting into the following cases:
;;
;; Pattern is a variable symbol:  the variable is simply bound to the
;; expression using let.
;;
;; Pattern is the - wildcard:  The expression is evaluated for side
;; effects and not bound.
;;
;; Pattern is the & wildcard, a quoted constant, or the symbol nil or
;; t:  The binding is ignored and the expression is never evaluated.
;;
;; Otherwise, the pattern must be a constructor expression, a cons
;; where the car is a symbol with associated macro named
;; patbind-<symbol>, and the cdr is a list of patterns.  The cdr, or
;; argument list, is processed as follows to produce a variable list
;; and an ignore list, as follows.
;;
;; - Each variable symbol is added to the variable list.
;;
;; - Each wildcard, boolean symbol, and quoted constant has a variable
;; name created for it which is added to the variable and ignore lists.
;;
;; - Each constructor call has a variable name created for it which is
;; added to the variable list.
;;
;; The inner expression is then augmented with surrounding calls to
;; patbind for each pair (pattern, variable) from the argument list and
;; the variable list.  This expression is passed, along with the
;; variable list, assigned expression, and ignore list, to the macro
;; patbind-<symbol>, which is user-defined.  In sane cases, the action of the
;; macro is to surround the augmented inner expression with a binding
;; for each of the variables in the variable list.
;; 
;; Here are some examples of how patbind expands:
;; (patbind (cons a (cons & b)) (some-function-call) (the-answer))
;; Since the pattern (cons a (cons & b)) is a constructor call and the
;; assigned expression is not evaluated, we first bind its result to a
;; variable.  The variable name chosen is the pattern itself read into
;; a symbol, which we would not expect to conflict with any other
;; variable name.
;; (let ((|(CONS A (CONS & B))| (some-function-call)))
;;   (patbind (cons a (cons & b)) |(CONS A (CONS & B))| (the-answer)))
;; The inner patbind has its assigned expression already evaluated, and
;; its pattern is a constructor call; the constructor is CONS and the
;; argument list is (A (CONS & B)).  The variable list for this is (A
;; |(CONS & B)|) and the ignore list is empty.  The inner expression
;; is augmented by binding the patterns to the variables, although
;; binding a to itself is skipped:
;; (patbind (cons & b) |(CONS & B)| (the-answer))
;; and this augmented inner expression is passed to the PATBIND-CONS
;; macro with the variable list, assigned expression, and ignore list:
;; (patbind-cons (a |(CONS & B)|) |(CONS A (CONS & B))| nil
;;   (patbind (cons & b) |(CONS & B)| (the-answer)))
;; The patbind-cons macro forms a let expression binding the first
;; variable in the list to the car of the assigned expression and the
;; second to the cdr:
;; (let ((a (car |(CONS A (CONS & B))|))
;;       (|(CONS & B)| (cdr |(CONS A (CONS & B))|)))
;;   (patbind (cons & b) |(CONS & B)| (the-answer)))
;; The inner patbind also has a cons constructor call as its pattern
;; which is processed as follows: The argument list is (& b), so the
;; variable list is (ignore-0 b) and the ignore list is (ignore-0).
;; The augmented inner expression is
;; (patbind & ignore-0 (the-answer))
;; and the patbind-cons call is
;; (patbind-cons (ignore-0 b) |(CONS & B)| (ignore-0)
;;   (patbind & ignore-0 (the-answer)))
;; The patbind-cons macro simply removes variables in the ignore list
;; from its let binding, so the result of this expansion is
;; (let ((b (cdr |(CONS & B)|)))
;;   (patbind & ignore-0 (the-answer)))
;; The inner patbind call has the wildcard symbol & as its pattern, so it
;; ignores the binding altogether and expands to (the-answer).
;; So the full expansion is equivalent to
;; (let ((|(CONS A (CONS & B))| (some-function-call)))
;;   (let ((a (car |(CONS A (CONS & B))|))
;;         (|(CONS & B)| (cdr |(CONS A (CONS & B))|)))
;;     (let ((b (cdr |(CONS & B)|)))
;;       (the-answer)))).





(include-book "pack")

(defun patbind-macro-name (binder)
  (intern (concatenate 'string
                       "PATBIND-"
                       (symbol-name binder))
          "ACL2"))

(defconst *patbind-special-syms* '(t nil & -))

(defun int-string (n)
  (coerce (explode-nonnegative-integer n 10 nil) 'string))

(defun str-num-sym (str n)
  (intern (concatenate 'string str (int-string n)) "ACL2"))

(defun ignore-var-name (n)
  (str-num-sym "IGNORE-" n))



(verify-termination doubleton-list-p)
(verify-guards doubleton-list-p)


(defun debuggable-doubleton-list-p (x)
  (declare (xargs :guard t))
  (mbe :logic (doubleton-list-p x)
       :exec (cond ((atom x) 
                    (or (equal x nil)
                        (cw "; Not a doubleton-list-p: ends with ~x0, instead of nil.~%" x)))
                   ((and (true-listp (car x))
                         (eql (length (car x)) 2))
                    (debuggable-doubleton-list-p (cdr x)))
                   (t
                    (cw "; Not a doubleton-list-p: first bad entry is ~x0.~%" (car x))))))

(defun patbind-decode-varname (pattern)
  (let* ((name (symbol-name pattern))
         (?p (and (<= 1 (length name))
                  (eql (char name 0) #\?)))
         (?!p (and ?p
                   (<= 2 (length name))
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

(defun patbind-nest (args vars expr)
  (if (atom args)
      expr
    (if (atom (car args))
        (patbind-nest (cdr args) (cdr vars) expr)
      `(patbind ,(car args) ,(car vars)
                ,(patbind-nest (cdr args) (cdr vars) expr)))))


(defun patbind-find-ignores (ignore-or-ignorable vars ignores acc)
  (if (atom vars)
      acc
    (patbind-find-ignores
     ignore-or-ignorable
     (cdr vars) (cdr ignores)
     (if (eq ignore-or-ignorable (car ignores))
         (cons (car vars) acc)
       acc))))

(defun patbind-var-ignore-list (args vars igcount ignores)
  (if (atom args)
      (mv (reverse vars) (reverse ignores))
    (mv-let (sym ignorep)
      (cond ((or (member (car args) *patbind-special-syms*)
                 (quotep (car args))
                 (and (atom (car args)) (not (symbolp (car args)))))
             (let ((var (ignore-var-name igcount)))
               (mv var 'ignore)))
            ((symbolp (car args))
             (patbind-decode-varname (car args)))
            (t (mv (pack (car args)) nil)))
      (patbind-var-ignore-list (cdr args) (cons sym vars)
                               (if (eql ignorep 'ignore)
                                   (1+ igcount)
                                 igcount)
                               (cons ignorep ignores)))))



(defun patbindfn (pattern assign-expr nested-expr)
  (cond ((and (consp assign-expr) (not (eq (car assign-expr) 'quote))
              (consp pattern)
              (not (member (car pattern) '(mv er when unless if)))
              (not (and (symbolp (car pattern))
                        (let ((str (symbol-name (car pattern))))
                          (and (not (equal str ""))
                               (eql (char str (1- (length str))) #\+))))))
         (let ((var (pack pattern)))
           `(let ((,var ,assign-expr))
              (patbind ,pattern ,var ,nested-expr))))
        ((eq pattern '-)
         `(prog2$ ,assign-expr
                  ,nested-expr))
        ((member pattern *patbind-special-syms*)
         nested-expr)
        ((atom pattern)
         (mv-let (sym ignorep)
           (patbind-decode-varname pattern)
           `(let ((,sym ,assign-expr))
              ,@(and ignorep `((declare (,ignorep ,sym))))
              ,nested-expr)))
        ((eq (car pattern) 'quote)
         nested-expr)
        ((member (car pattern) '(when unless if))
         (let* ((binder (car pattern))
                (patbind-macro (patbind-macro-name binder))
                (args (cdr pattern)))
           `(,patbind-macro ,args ,assign-expr nil
                            ,nested-expr)))
        (t (let* ((binder (car pattern))
                  (patbind-macro (patbind-macro-name binder))
                  (args (cdr pattern)))
             (mv-let 
              (vars ignores)
              (patbind-var-ignore-list args nil 0 nil)
              `(,patbind-macro ,vars ,assign-expr ,ignores
                               ,(patbind-nest args vars nested-expr)))))))
             
        

(defun mk-prog2$-nest (exprs)
  (declare (xargs :guard (consp exprs)))
  (if (atom (cdr exprs))
      (car exprs)
    `(prog2$ ,(car exprs)
             ,(mk-prog2$-nest (cdr exprs)))))
         
         
(defmacro patbind (pattern assign-expr nested-expr)
  (patbindfn pattern assign-expr nested-expr))


(defun b*-fn1 (bindlist expr)
  (declare (xargs :guard (debuggable-doubleton-list-p bindlist)))
  (if (atom bindlist)
      expr
    `(patbind ,(caar bindlist) ,(cadar bindlist)
              ,(b*-fn1 (cdr bindlist) expr))))

(defun b*-fn (bindlist exprs)
  (declare (xargs :guard (and (debuggable-doubleton-list-p bindlist)
                              (consp exprs))))
  (b*-fn1 bindlist (mk-prog2$-nest exprs)))

(defmacro b* (bindlist expr &rest exprs)
  (declare (xargs :guard (debuggable-doubleton-list-p bindlist)))
  (b*-fn bindlist (cons expr exprs)))




(defun binding-list (args bindings ignores)
  (if (atom args)
      nil
    (if (eql (car ignores) 'ignore)
        (binding-list (cdr args) (cdr bindings) (cdr ignores))
      (cons (list (car args) (car bindings))
            (binding-list (cdr args) (cdr bindings) (cdr ignores))))))


(defun destructor-binding-list (destructors)
  (if (atom destructors)
      nil
    ``((,',(car destructors) ,binding) .
       ,,(destructor-binding-list (cdr destructors)))))

(defmacro def-patbind-macro (binder destructors)
  (let ((binding-list (destructor-binding-list destructors))
        (len (length destructors)))
  `(defmacro ,(patbind-macro-name binder) (args binding ignores expr)
     (declare (xargs :guard (and (true-listp args)
                                 (= (length args) ,len))))
     (let ((ignorable (patbind-find-ignores 'ignorable args ignores nil)))
     `(let ,(binding-list args ,binding-list ignores)
        ,@(and ignorable `((declare (ignorable . ,ignorable))))
        ,expr)))))



(defmacro patbind-mv (args binding ignores expr)
  (let ((ignore (patbind-find-ignores 'ignore args ignores nil))
        (ignorable (patbind-find-ignores 'ignorable args ignores nil)))
    `(mv-let ,args ,binding 
       ,@(and (or ignore ignorable)
              `((declare ,@(and ignore `((ignore . ,ignore)))
                         . ,(and ignorable `((ignorable . ,ignorable))))))
       ,expr)))

(def-patbind-macro cons (car cdr))

(defun list-binding-list (args n form ignores)
  (if (atom args)
      nil
    (if (eql (car ignores) 'ignore)
        (list-binding-list (cdr args) (1+ n) form (cdr ignores))
      (cons (list (car args) `(nth ,n ,form))
            (list-binding-list (cdr args) (1+ n) form (cdr ignores))))))


(defun list*-binding-list (args form ignores)
  (if (atom (cdr args))
      (if (eql (car ignores) 'ignore)
          nil
        (list (list (car args) form)))
    (if (eql (car ignores) 'ignore)
        (list*-binding-list (cdr args) `(cdr ,form) (cdr ignores))
      (cons (list (car args) `(car ,form))
            (list*-binding-list (cdr args) `(cdr ,form) (cdr ignores))))))


(defmacro patbind-list (args binding ignores expr)
  (declare (xargs :guard (true-listp args)))
  (let ((ignorable (patbind-find-ignores 'ignorable args ignores nil)))
    `(let ,(list-binding-list args 0 binding ignores)
       ,@(and ignorable `((declare (ignorable . ,ignorable))))
       ,expr)))


(defmacro patbind-list* (args binding ignores expr)
  (declare (xargs :guard (true-listp args)))
  (let ((ignorable (patbind-find-ignores 'ignorable args ignores nil)))
    `(let ,(list*-binding-list args binding ignores)
       ,@(and ignorable `((declare (ignorable . ,ignorable))))
       ,expr)))

(defmacro patbind-er (args binding ignores expr)
  (declare (xargs :guard (and (consp args) (eq (cdr args) nil))))
  (case (car ignores)
    (ignore `(er-progn ,binding ,expr))
    (ignorable `(er-let* ((,(car args) ,binding))
                         (let ((,(car args) ,(car args)))
                           (declare (ignorable ,(car args)))
                         ,expr)))
    (otherwise `(er-let* ((,(car args) ,binding))
                         ,expr))))

(defmacro patbind-state-global (args binding ignores expr)
  (declare (ignorable ignores))
  `(state-global-let*
    ((,(car args) ,binding))
    ,expr))


(defmacro patbind-when (args bindings ignores expr)
  (declare (ignore ignores)
           (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       ,bindings
     ,expr))

(defmacro patbind-if (args bindings ignores expr)
  (declare (ignore ignores)
           (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       ,bindings
     ,expr))

(defmacro patbind-unless (args bindings ignores expr)
  (declare (ignore ignores)
           (xargs :guard (and (consp args) (eq (cdr args) nil))))
  `(if ,(car args)
       ,expr
     ,bindings))
  


(local
 (progn
   (defmacro transl-equal (x y)
     `(mv-let (flgx valx bindings state)
        (translate1 ,x :stobjs-out
                    '((:stobjs-out . :stobjs-out))
                    t :top-level (w state) state)
        (declare (ignore bindings))
        (mv-let (flgy valy bindings state)
          (translate1 ,y :stobjs-out
                      '((:stobjs-out . :stobjs-out))
                      t :top-level (w state) state)
          (declare (ignore bindings))
          (mv (and flgx flgy) (equal valx valy) state))))


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


   (defmacro patbind-run-tests (&rest tests)
     `(make-event
       (mv-let (err state)
         (transl-equal-tests ,@tests)
         (if err
             (mv t
                 (er hard? 'patbind-run-tests
                     "~% ****** ERROR ******~%~
Testing of the patbind macro failed on expression ~x0~%~%" err)
                 state)
           (value (prog2$ (cw "
Testing of the patbind macro passed.~%")
                          `(value-triple 'tests-ok)))))
       :check-expansion (value-triple 'tests-ok)))


   (patbind-run-tests
;; TEST CASES

    ((patbind (cons (cons a b) c) x (list a b c))
     (let ((|(CONS A B)| (car x))
           (c (cdr x)))
       (let ((a (car |(CONS A B)|))
             (b (cdr |(CONS A B)|)))
         (list a b c))))

    ((patbind x (cons 'a 'b) x)
     (let ((x (cons 'a 'b))) x))

    ((patbind (mv a b) (mv 'a 'b) (list a b))
     (mv-let (a b) (mv 'a 'b) (list a b)))

    ((patbind & (cw "Hello") nil)
     nil)

    ((patbind - (cw "Hello") nil)
     (prog2$ (cw "Hello")
             nil))

    ((patbind (cons a &) '(a b) a)
     (let ((a (car '(a b))))
       a))

    ((patbind (cons (cons a b) c) x
              (list a b c))
     (let ((|(CONS A B)| (car x))
           (c (cdr x)))
       (let ((a (car |(CONS A B)|))
             (b (cdr |(CONS A B)|)))
         (list a b c))))

    ((patbind (cons (cons a b) c) (cons x y)
              (list a b c))
     (let ((|(CONS (CONS A B) C)| (cons x y)))
       (let ((|(CONS A B)| (car |(CONS (CONS A B) C)|))
             (c (cdr |(CONS (CONS A B) C)|)))
         (let ((a (car |(CONS A B)|))
               (b (cdr |(CONS A B)|)))
           (list a b c)))))

    ((patbind (cons (cons & b) c) (cons x y)
              (list b c))
     (let ((|(CONS (CONS & B) C)| (cons x y)))
       (let ((|(CONS & B)| (car |(CONS (CONS & B) C)|))
             (c (cdr |(CONS (CONS & B) C)|)))
         (let ((b (cdr |(CONS & B)|)))
           (list b c)))))

    ((patbind (cons (cons a &) c) (cons x y)
              (list a c))
     (let ((|(CONS (CONS A &) C)| (cons x y)))
       (let ((|(CONS A &)| (car |(CONS (CONS A &) C)|))
             (c (cdr |(CONS (CONS A &) C)|)))
         (let ((a (car |(CONS A &)|)))
           (list a c)))))


    ((patbind (mv (cons a (cons b c)) d)
              (return-two-values x y)
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
              (return-two-values x y)
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
              (return-two-values x y)
              (list a c d))
     (mv-let (|(CONS A (CONS & C))| ignore-0)
       (return-two-values x y)
       (declare (ignore ignore-0))
       (let ((a (car |(CONS A (CONS & C))|))
             (|(CONS & C)| 
              (cdr |(CONS A (CONS & C))|)))
         (let ((c (cdr |(CONS & C)|)))
           (list a c d)))))
 
    ((patbind `(,a ,b) (cons x y) (list a b))
     (let ((|(CONS A (CONS B (QUOTE NIL)))| (cons x y)))
       (let ((a (car |(CONS A (CONS B (QUOTE NIL)))|))
             (|(CONS B (QUOTE NIL))|
              (cdr |(CONS A (CONS B (QUOTE NIL)))|)))
         (let ((b (car |(CONS B (QUOTE NIL))|)))
           (list a b)))))

    )))
