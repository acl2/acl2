; Copyright (C) 2018, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; We consider the general problem of how to generate a defun form that is then
; used for doing an efficient computation, without leaving the defun form in
; the world.

; In this book we illustrate how to solve by working a specific example: we
; generate custom code for membership of a given element in a list.

; (Note: I wonder if this could be done more simply!  I found this a bit
; confusing myself, but I hope that the comments below will be helpful in
; understanding my solution.)

; Let's start by doing this manually in a specific example, which is to search
; for the symbol A in a list:

#||
(defun my-mem (lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((eq (car lst) 'a) t)
        (t (my-mem (cdr lst)))))

Example evaluations:
ACL2 !>(my-mem '(x y a z))
T
ACL2 !>(my-mem '(x y z))
NIL
ACL2 !>
||#

; Here is a first attempt to generate code that searches for the symbol A in a
; given list, in this case, (append '(x y z) '(a b c)).

#||
(with-output
  :off :all
  :on error
  (make-event
   (let ((L (append '(x y z) '(a b c))))
     (er-progn (defun my-mem (lst)
                 (declare (xargs :guard (true-listp lst)))
                 (cond ((endp lst) nil)
                       ((eq (car lst) 'a) t)
                       (t (my-mem (cdr lst)))))
               (value `(value-triple (my-mem ',L)))))))
||#

; But this doesn't work, because the er-progn call evaluates to
;   (VALUE-TRIPLE (MY-MEM '(X Y Z A B C)))
; so that's the make-event expansion; but after expansion, the definition of
; my-mem is gone, so this call of my-mem cannot be evaluated.

; A standard sort of workaround is to replace er-progn by progn, since progn
; does not require its forms to be translated before evaluation starts --
; rather, each form is evaluated in term, so the definition of my-mem would be
; available when evaluating the value-triple form.  So perhaps we want
; something like the following.

#||
(with-output
  :off :all
  :on error
  (make-event
   (let ((L (append '(x y z) '(a b c))))
     (progn (defun my-mem (lst)
              (declare (xargs :guard (true-listp lst)))
              (cond ((endp lst) nil)
                    ((eq (car lst) 'a) t)
                    (t (my-mem (cdr lst)))))
            (value-triple `(value-triple (my-mem ',L)))))))
||#

; Notice that VALUE has been replaced by VALUE-TRIPLE, because PROGN requires
; each form to be a legal event form.  But then this fails to work, because the
; occurrence of L inside the outer VALUE-TRIPLE call is not related to the
; LET-bound variable, L -- there are no free variables recognized by
; VALUE-TRIPLE.  This point is perhaps confusing but made more clear by seeing
; what we have when the backquote is removed.

#||
ACL2 !>'(value-triple `(value-triple (my-mem ',L)))
(VALUE-TRIPLE (CONS 'VALUE-TRIPLE
                    (CONS (CONS 'MY-MEM
                                (CONS (CONS 'QUOTE (CONS L 'NIL)) 'NIL))
                          'NIL)))
ACL2 !>
||#

; We see a form (value-triple ... L ...) with L free, which makes no sense
; since free variables in value-triple forms are simply errors.

; So what we actually generate is more complex than suggested by the two tries
; above.  First, here is code that generates a make-event call that is designed
; to return

;   (mv nil (list 'value-triple expr) state)

; after evaluating the given definition.  Note that the definition is evaluated
; only during make-event expansion, and thus does not leave the definition in
; the world.

(defun run-def-form (def expr)
  `(make-event
    (progn ,def
           (value-triple (list 'value-triple (list 'quote ,expr))))))

; Let's see how things work with run-def-form; an explanation follows this log.

#||
ACL2 !>(run-def-form '(defun foo (x y) (cons y x))
                     '(foo 3 4))
(MAKE-EVENT (PROGN (DEFUN FOO (X Y) (CONS Y X))
                   (VALUE-TRIPLE (LIST 'VALUE-TRIPLE
                                       (LIST 'QUOTE (FOO 3 4))))))
ACL2 !>(with-output
	 :off :all
	 (MAKE-EVENT (PROGN (DEFUN FOO (X Y) (CONS Y X))
			    (VALUE-TRIPLE (LIST 'VALUE-TRIPLE
						 (LIST 'QUOTE (FOO 3 4)))))))
 (4 . 3)
ACL2 !>
||#

; What happened?  The resulting make-event form produced an expansion of
; (VALUE-TRIPLE (QUOTE (4 . 3))), and that expansion was submitted, producing
; the error triple (mv nil (4 . 3) state), which is printed as " (4 . 3)".
; (See :DOC error-triple.)

; Now we take advantage of run-def-form to generate our solution.  The outer
; make-event produces its expansion by evaluating the indicated run-def-form,
; which returns (as the expansion) an inner make-event call like the one
; displayed above.  That inner make-event call then produces the desired
; error-triple (mv nil val state), as illustrated above.

(defun search-list-fn (elt x)
  (declare (xargs :guard t))
  `(with-output ; inhibit output
     :off :all ; all output is inhibited except:
     :on error ; allow error output
     (make-event
      (let ((elt ,elt)
            (x ,x))
        (let ((eq-fn (cond ((symbolp elt) 'eq)
                           ((eqlablep elt) 'eql)
                           (t 'equal))))
          (run-def-form `(defun my-mem (lst)
                           (declare (xargs :guard (true-listp lst)))
                           (cond ((endp lst) nil)
                                 ((,eq-fn (car lst) ',elt) t)
                                 (t (my-mem (cdr lst)))))
                        `(my-mem ',x)))))))

(defmacro search-list (elt x)
  (search-list-fn elt x))

; Now, (search-list elt x) will evaluate elt and x and return

;   (mv nil val state)

; where val is t or nil, depending on whether or not (the value of elt) occurs
; in (the value of) x.  Here are some examples.  You might find it helpful to
; evaluate (trace$ run-def-form) first, to help with understanding what is
; happening.

#||
ACL2 !>(search-list 'a (append '(x y z) '(b c)))
 NIL
ACL2 !>(search-list 'a (append '(x y z) '(a b c)))
 T
ACL2 !>(search-list '(a b) '((c d) (a b)))
 T
ACL2 !>(search-list '(a b) '((c d) (a b e)))
 NIL
ACL2 !>
||#

; Examples of use in code:
#||
ACL2 !>(er-let* ((x (search-list '(a b) '((c d) (a b e)))))
	 (value x))
 NIL
ACL2 !>(er-let* ((x (search-list '(a b) '((c d) (a b)))))
	 (value x))
 T
ACL2 !>
||#
