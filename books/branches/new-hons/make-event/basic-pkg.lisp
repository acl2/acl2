; This book is similar to (part of) basic.lisp, but is in package "FOO" and
; hence must be certified in a world where package "FOO" has been defined (see
; basic-pkg.acl2).

(in-package "FOO")

(make-event
 '(defun test1 (x)
    (list x x)))

(make-event
 (value '(defun test2 (x)
           (cons x x))))

(defun bar (x)
  (cons (test1 x) (test2 x)))

(defthm bar-prop
  (equal (bar x)
         (cons (list x x)
               (cons x x))))
