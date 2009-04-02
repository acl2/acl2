; This variant of basic.lisp uses :check-expansion t.  If you care to look in
; basic-check.cert, you'll see that the expansions saved for test1 (position 1
; in this file) and test2 (position 2 in this file) are of the form
; (record-expansion original-form new-form), where original-form is as below
; and new-form is similar but with the :check-expansion filled in with the
; result of expanding the argument of make-event.

(in-package "ACL2")

; Here's something fun to try interactively.
#|
(make-event
 (er-progn (assign saved-len (length (w state)))
           (value '(value-triple nil))))

; Defines (foo x) to be x.
(make-event
 (if (equal (length (w state)) (@ saved-len))
     '(defun foo (x) x)
   '(defun foo (x) (cons x x))))

:pe foo

; Causes a redefinition error.
(make-event
 (if (equal (length (w state)) (@ saved-len))
     '(defun foo (x) x)
   '(defun foo (x) (cons x x))))

; Works but defines (bar x) to be (cons x x).
(make-event
 (if (equal (length (w state)) (@ saved-len))
     '(defun bar (x) x)
   '(defun bar (x) (cons x x))))

:ubt 1

; This time (bar x) is x.
(make-event
 (if (equal (length (w state)) (@ saved-len))
     '(defun bar (x) x)
   '(defun bar (x) (cons x x))))

|# ; |

(make-event
 '(defun test1 (x)
    (cons x x))
 :check-expansion t)

(make-event
 (value '(defun test2 (x)
           (cons x x)))
 :check-expansion t)

(defun bar (x)
  (cons (test1 x) (test2 x)))

(defthm bar-prop
  (equal (bar x)
         (cons (cons x x)
               (cons x x))))
