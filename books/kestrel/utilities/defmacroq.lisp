; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc defmacroq
  :parents (macros defmacro kestrel-utilities)
  :short "Define a macro that quotes arguments not wrapped in @(':eval')"
  :long "<p>@('Defmacroq') has the same general form as @('defmacro') (see
 @(see defmacro)), that is:</p>

 @({
 (defmacro name macro-args doc-string dcl ... dcl body)
 })

 <p>However, for any subsequent call of @('name'), and for each variable
 @('var') introduced by @(tsee macro-args) that is bound to a corresponding
 value @('val') from the call, @('var') is instead bound to @('(quote val)')
 with one exception: if @('val') is of the form @('(:eval x)'), then @('var')
 is bound to the expression @('x').  The following example shows how this
 works.</p>

 @({
 ACL2 !>(defmacroq mac2 (x y)
          `(list ,x ,y))

 Summary
 Form:  ( DEFMACRO MAC2 ...)
 Rules: NIL
 Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
  MAC2
 ACL2 !>:trans1 (mac2 (a b) (:eval (append '(c d) '(e f))))
  (LIST '(A B) (APPEND '(C D) '(E F)))
 ACL2 !>(mac2 (a b) (:eval (append '(c d) '(e f))))
 ((A B) (C D E F))
 ACL2 !>
 })

 <p>Thus, if we ignore the role of @(':eval'), the macro definition above is
 equivalent to the following.</p>

 @({
 (defmacro mac2 (x y)
   `(list ',x ',y))
 })")

(defun defmacroq-binding (arg)
  (declare (xargs :guard (symbolp arg)))
  `(,arg (if (and (consp ,arg)
                  (consp (cdr ,arg))
                  (null (cddr ,arg))
                  (eq (car ,arg) :eval))
             (cadr ,arg)
           (list 'quote ,arg))))

(defun defmacroq-bindings (args)
  (declare (xargs :guard (symbol-listp args)))
  (cond ((endp args) nil)
        (t (cons (defmacroq-binding (car args))
                 (defmacroq-bindings (cdr args))))))

(defmacro defmacroq (fn args &rest rest)

; TODO: Perhaps Propagate ignore and ignorable declarations into the generated
; LET.

  (let* ((vars (macro-vars args))
         (bindings (defmacroq-bindings vars))
         (dcls (butlast rest 1))
         (body (car (last rest))))
    (cond ((member-eq 'state vars)
           (er hard 'defmacroq
               "It is illegal to supply STATE as an argument of DEFMACROQ."))
          (t `(defmacro ,fn ,args
                ,@dcls
                (let ,bindings
                  ,body))))))

;;; tests

(local (progn

(defmacroq mac4 (x y z w)
  `(list ,x ,y ,z ,w (f-boundp-global 'boot-strap-flg state)))

(defun f (a state b)
  (declare (xargs :stobjs state))
  (cons 17 (mac4 c (:eval (cons a b)) b (:eval (expt 2 3)))))

(assert-event (equal (f (expt 4 1) state (reverse '(i j k)))
                     '(17 C (4 K J I) B 8 T)))

))
