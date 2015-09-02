(in-package "ACL2")

; ============================================================

; Exercise 5.1

#|

Define the macro cadn so that

(cadn 0 x) <==> (car x)
(cadn 1 x) <==> (car (cdr x))
(cadn 2 x) <==> (car (cdr (cdr x)))
etc.

This macro does not require ampersand markers.  You might consider defining a
recursive function first.

|#

(defun cadn-fn (n x)
  (if (zp n)
      `(car ,x)
    (cadn-fn (- n 1) `(cdr ,x))))

(defmacro cadn (n x)
  (cadn-fn n x))

; ============================================================

; Exercise 5.2

#|

What expression does (cadn t x) abbreviate?  What expression does (cadn i x)
abbreviate?  In many solutions, these expressions expand to (car x) because the
first argument to cadn is not a natural number.  Suppose you wished to write
the cadn macro so that an error is caused if its first argument is not an
explicitly given natural.  How can you do that?  Hint: Macros can have guards
(see guard) and they are evaluated after the macro formals are bound and before
the macro body is evaluated.

|#

; Answer to first two questions above: (car x).
; (Try :set-guard-checking nil, followed by :trans (cadn t x).)

(defmacro cadn-guarded (n x)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (cadn-fn n x))

; ============================================================

; Exercise 5.3

#|

Define the macro ffix so that (ffix expr) <==> (fix expr) unless expr is an
application of +, *, or fix, in which case (ffix expr) <==> expr.  Hint: This
macro does not require ampersand markers.

|#

(defmacro ffix (x)
  (cond ((and (consp x)
              (member (car x) '(+ * fix)))
         x)
        (t (list 'fix x))))

; ============================================================

; Exercise 5.4

#|

Suppose you must frequently pair some computed object with itself.  You write
the macro

(defmacro pairit (x)
  `(cons ,x ,x)).

Why is this a poor design for this macro?  Hint: Consider the time it takes to
compute the value of (pairit (fact 100)).

|#

; Answer:  The argument of pairit is evaluated twice.

; ============================================================

; Exercise 5.5

#|

The following defmacro is intended to provide the abbreviation (if-nzp x expr_1
expr_2 expr_3) so that expr_1 is evaluated and returned if the value of x is
negative, expr_2 is evaluated and returned if the value of x is zero, and
expr_3 is evaluated and returned otherwise.

(defmacro if-nzp (x expr1 expr2 expr3)
  `(let ((val ,x))
     (cond ((< val 0) ,expr1)
           ((equal val 0) ,expr2)
           (t ,expr3))))

The definition cleverly avoids the re-evaluation of its first argument.  What
is wrong with this expansion scheme?  How can you avoid the problem?  Hint:
Consider the variables that occur freely in the expri.  ACL2 does not support
the Common Lisp ``function'' gensym.  The best we can do is to insure that
certain symbols do not occur freely in other forms.  See the macro
check-vars-not-free in the ACL2 sources.

|#

; Answer to first question:  What is wrong is that val may occur in expr1,
; expr2, or expr3, but the binding of val in the body of if-nzp will hide the
; binding of val in the enclosing environment.  Consider the following example,
; where the expected answer is 'negative, but -1 is returned (if first you
; execute (set-ignore-ok t) in order to avoid an error).

; (let ((val 'negative))
;   (if-nzp -1 val 'zero 'positive))

; Here is a safe definition.

(defmacro if-nzp (x expr1 expr2 expr3)
  `(let ((val ,x))
     (cond ((< val 0) (check-vars-not-free (val) ,expr1))
           ((equal val 0) (check-vars-not-free (val) ,expr2))
           (t (check-vars-not-free (val) ,expr3)))))

; ============================================================

; Exercise 5.6

#|

Define (type-case x :type_1 expr_1 ... :type_n expr_n) to evaluate and return
expr_i, where type_i is the first type listed describing x.  The form should
return nil if no type listed describes x.  The expected type_i are integer,
rational, string, symbol, cons, Boolean, and other.  For example,

(type-case (car x)
  :integer  (+ 1 i)
  :rational (+ 2 i)
  :symbol   (+ 3 i)
  :other    (+ 4 i))

should evaluate and return (+ 1 i), if the value of (car x) is an integer, (+ 2
i), if the value of (car x) is not an integer but is a rational, etc.

|#

(defun type-case-keyword-alistp (x)
  (cond ((endp x) t)
        ((endp (cdr x)) nil)
        (t (and (member (car x) '(:integer :rational :string :symbol :cons
                                           :boolean :other))
                (type-case-keyword-alistp (cddr x))))))

(defun type-case-type (args)
  (cond ((endp args) nil)
        (t (cons (case (car args)
                   (:integer '((integerp x) :integer))
                   (:rational '((rationalp x) :rational))
                   (:string '((stringp x) :string))
                   (:symbol '((symbolp x) :symbol))
                   (:cons '((consp x) :cons))
                   (:boolean '((consp x) :boolean))
                   (:other '(t :other))
                   (otherwise nil))
                 (type-case-type (cddr args))))))

(defun type-case-clauses (args)
  (cond ((endp args) nil)
        (t (cons (list (car args)
                       (cadr args))
                 (type-case-clauses (cddr args))))))

(defmacro type-case (x &rest args)
  (declare (xargs :guard (type-case-keyword-alistp args)))
  `(case (let ((x ,x))
           (cond ,@(type-case-type args)))
     ,@(type-case-clauses args)
     (otherwise nil)))

; ============================================================

; Exercise 5.7

#|

Suppose you have a lot of functions that take s as an argument and return a
``new value'' of s as a result.  Here we are thinking of s as a ``state'' and
these functions as state transformers.  For example, (do-f x s) might return a
``new'' state and (do-g x y s) might return a ``new'' state.  You will
frequently need to create sequential compositions of these functions, e.g.,
(do-f x (do-g i2 j2 (do-g i1 j1 s))).  To avoid writing such compositions
define the macro do-sequentially so that

(do-sequentially (do-g i1 j1 s)
                 (do-g i2 j2 s)
                 (do-f x s))

evaluates to the same thing as the composition above.

|#

(defmacro do-sequentially (&rest args)
  (cond ((endp args) 's)
        (t `(let ((s ,(car args))) (do-sequentially ,@(cdr args))))))

; ============================================================
