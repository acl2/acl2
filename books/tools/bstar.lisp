
;; This book contains the macro b*, which acts like let* with certain
;; extensions.  Some of its features:
;; - Can bind single values and MVs within the same let*-like sequence
;; of assignments, without nesting
;; - Can bind variables using user-defined pattern-matching idioms
;; - Eliminates ignore declarations

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


(in-package "ACL2")


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

(defun patbind-var-ignore-list (args vars ignores)
  (if (atom args)
      (mv (reverse vars) ignores)
    (if (or (member (car args) *patbind-special-syms*)
            (quotep (car args)))
        (let ((var (ignore-var-name (length ignores))))
          (patbind-var-ignore-list (cdr args) (cons var vars)
                                  (cons var ignores)))
      (patbind-var-ignore-list (cdr args) (cons (pack (car args)) vars)
                              ignores))))


(defun patbind-nest (args vars expr)
  (if (atom args)
      expr
    (if (eq (car args) (car vars))
        (patbind-nest (cdr args) (cdr vars) expr)
      `(patbind ,(car args) ,(car vars)
             ,(patbind-nest (cdr args) (cdr vars) expr)))))

                       

(defun patbindfn (pattern assign-expr nested-expr)
  (cond ((and (consp assign-expr) (not (eq (car assign-expr) 'quote))
              (consp pattern) (not (eq (car pattern) 'mv))
              (not (eq (car pattern) 'er)))
         (let ((var (pack pattern))) 
           `(let ((,var ,assign-expr))
              (patbind ,pattern ,var ,nested-expr))))
        ((eq pattern '-)
         `(let ((ign ,assign-expr))
            (declare (ignore ign))
            ,nested-expr))
        ((member pattern *patbind-special-syms*)
         nested-expr)
        ((atom pattern)
         `(let ((,pattern ,assign-expr))
            ,nested-expr))
        ((eq (car pattern) 'quote)
         nested-expr)
        (t (let* ((binder (car pattern))
                  (patbind-macro (patbind-macro-name binder))
                  (args (cdr pattern)))
             (mv-let 
              (vars ignores)
              (patbind-var-ignore-list args nil nil)
              `(,patbind-macro ,vars ,assign-expr ,ignores
                              ,(patbind-nest args vars nested-expr)))))))
             
        
         
         
(defmacro patbind (pattern assign-expr nested-expr)
  (patbindfn pattern assign-expr nested-expr))


(defun b*-fn (bindlist expr)
  (if (atom bindlist)
      expr
    `(patbind ,(caar bindlist) ,(cadar bindlist)
           ,(b*-fn (cdr bindlist) expr))))

(defmacro b* (bindlist expr)
  (b*-fn bindlist expr))




(defun binding-list (args bindings ignores)
  (if (atom args)
      nil
    (if (member (car args) ignores)
        (binding-list (cdr args) (cdr bindings) ignores)
      (cons (list (car args) (car bindings))
            (binding-list (cdr args) (cdr bindings) ignores)))))


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
     `(let ,(binding-list args ,binding-list ignores)
        ,expr))))



(defmacro patbind-mv (args binding ignores expr)
  `(mv-let ,args ,binding 
           ,@(if ignores
                 `((declare (ignore ,@ignores)))
               nil)
           ,expr))

(def-patbind-macro cons (car cdr))

(defun list-binding-list (args n form ignores)
  (if (atom args)
      nil
    (if (member (car args) ignores)
        (list-binding-list (cdr args) (1+ n) form ignores)
      (cons (list (car args) `(nth ,n ,form))
            (list-binding-list (cdr args) (1+ n) form ignores)))))


(defun list*-binding-list (args form ignores)
  (if (atom (cdr args))
      (if (member (car args) ignores)
          nil
        (list (list (car args) form)))
    (if (member (car args) ignores)
        (list*-binding-list (cdr args) form ignores)
      (cons (list (car args) `(car ,form))
            (list*-binding-list (cdr args) `(cdr ,form) ignores)))))


(defmacro patbind-list (args binding ignores expr)
  (declare (xargs :guard (true-listp args)))
  `(let ,(list-binding-list args 0 binding ignores)
     ,expr))


(defmacro patbind-list* (args binding ignores expr)
  (declare (xargs :guard (true-listp args)))
  `(let ,(list*-binding-list args binding ignores)
     ,expr))

(defmacro patbind-er (args binding ignores expr)
  `(er-let* ((,(car args) ,binding))
            ,@(if ignores
                  `((declare (ignore . ,ignores)))
                nil)
            ,expr))

(defmacro patbind-state-global (args binding ignores expr)
  (declare (ignorable ignores))
  `(state-global-let*
    ((,(car args) ,binding))
    ,expr))


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
           (value (prog2$ (cw "~%Testing of the patbind macro ~
passed.~%")
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
     (let ((ign (cw "Hello")))
       (declare (ignore ign))
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
