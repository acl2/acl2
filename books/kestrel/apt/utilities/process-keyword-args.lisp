; Support for processing keyword arguments
;
; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file defines the macro (bind-** args form), which is intended to support
; the use of mutual-recursion in transformations.  The example displayed below
; illustrates its use; you might want to read that first, rather than the
; following dry description.

; First, some terminology.  The "clique" of a function symbol fn is its
; 'recursivep property, which is a list of all function symbols defined
; together with fn (including fn itself).  Note that fn is defined by
; mutual-recursion if and only if its clique has at least two elements.  For a
; symbol A, we write A** to denote the symbol in the same package as A whose
; name has "**" suffixed to the end of its symbol-name.

; Bind-** may only be called in a lexical environment where the symbols FN,
; CLIQUE, and CTX are bound, where CLIQUE is the clique of FN, and STATE is
; bound to the ACL2 state.  CTX is a context.  We refer to FN and CLIQUE below.

; Each member of the list, args, is either a symbol or a list containing a
; single symbol.  If the symbol A is in args, then we bind a corresponding
; symbol A** to a list of the same length as CLIQUE.  Normally each value in
; that list is the value V of A, but if V is of the form (:map . X), then X
; should be an alist whose strip-cars is CLIQUE.  In that case A** is bound to
; the list of values from X (its strip-cadrs), which is in one-one
; correspondence with CLIQUE.  Form is a form that should evaluate to an error
; triple (mv nil val state) under the bindings of symbols A** as described
; above.  If (A) is in args, then A** is not bound; instead, it is checked that
; the value of A is not of the form (:map . X), else an error is returned.

; Here is an example.  In this case, the list args discussed above is the list
; (arg1 (arg2) arg3), which indicates that we are to bind arg1** and arg3** but
; not arg2**; moreover, arg2** is checked not to be a :map expression.

#||
ACL2 !>:trans1 (bind-**
		(arg1 (arg2) arg3)
		(value (list arg1** arg2 arg3**)))
 (ER-PROGN (BIND-**-CHECK ARG2 CTX STATE)
           (ER-LET* ((ARG1** (MAKE-** ARG1 FN CLIQUE CTX STATE))
                     (ARG3** (MAKE-** ARG3 FN CLIQUE CTX STATE)))
                    (VALUE (LIST ARG1** ARG2 ARG3**))))
ACL2 !>(let* ((fn 'pseudo-termp)
	      (clique (recursivep fn nil (w state)))
	      (ctx 'top)
	      (arg1 23)
	      (arg2 'hello)
	      (arg3 '(:map (pseudo-termp aa) (pseudo-term-listp bb))))
	 (bind-**
	  (arg1 (arg2) arg3)
	  (value (list arg1** arg2 arg3**))))
 ((23 23) HELLO (AA BB))
ACL2 !>(let* ((fn 'pseudo-termp)
	      (clique (recursivep fn nil (w state)))
	      (ctx 'top)
	      (arg1 23)
	      (arg2 '(:map (pseudo-termp xx) (pseudo-term-listp yy)))
	      (arg3 '(:map (pseudo-termp aa) (pseudo-term-listp bb))))
	 (bind-**
	  (arg1 (arg2) arg3)
	  (value (list arg1** arg2 arg3**))))


ACL2 Error in TOP:  It is illegal to use the (:map ...) construct for
the keyword argument, :ARG2.

ACL2 !>
||#

; TO DO:
; - For (:map (f1 v1) ... (fk vk)), eliminate the requirement that the clique
;   of the given function is exactly (f1 ... fk), in that order.
; - Support (:map ... ((fn1 ... fnk) val) ...).
; - Support (:map ... (:otherwise val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "option-parsing")

(program)
(set-state-ok t)

(defun make-** (arg option-name clique ctx state)
  (let ((map-p (and (consp arg)
                    (eq (car arg) :map))))
    (cond (map-p
           (er-let* ((alist
                      (elaborate-mut-rec-option-with-state
                       arg
                       (intern (symbol-name option-name) "KEYWORD")
                       clique ctx state)))
             (value (strip-cdrs alist))))
          ((null arg) ; optimization
           (value nil))
          ((cdr clique) ; and not map-p
           (value (make-list (length clique) :initial-element arg)))
          (t (value (list arg))))))

(defun bind-**-check (sym val ctx state)
  (cond ((and (consp val)
              (eq (car val) :map))
         (er soft ctx
             "It is illegal to use the (:map ...) construct for the keyword ~
              argument, ~x0."
             (intern (symbol-name sym) "KEYWORD")))
        (t (value nil))))

(defun bind-**-bindings (args bindings checks)
  (cond ((endp args)
         (mv (reverse bindings)
             (reverse checks)))
        ((consp (car args))
         (bind-**-bindings
          (cdr args)
          bindings
          (cons `(bind-**-check ',(caar args) ,(caar args) ctx state)
                checks)))
        (t (bind-**-bindings
            (cdr args)
            (cons `(,(add-suffix (car args) "**")
                    (make-** ,(car args) ',(car args) clique ctx state))
                  bindings)
            checks))))

(defmacro bind-** (args form)
  (mv-let (bindings checks)
    (bind-**-bindings args nil nil)
    `(er-progn ,@checks
               (er-let* ,bindings
                 ,form))))
