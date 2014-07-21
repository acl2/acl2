; Copyright (C) 2014, Regents of the University of Texas
; Original author: Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; See book-thms.lisp.  This is an example that tests the utilities contained in
; that book.


(include-book "book-thms")



; Example:

(logic)

(local (encapsulate-then-new-info
        my-name
        (defthm foo
          (equal (car (cons x y)) x))
        (defun f1 (x y) (<= x y))
        (defthm bar
          (< (acl2-count x) (acl2-count (cons x y))))
        (defun-sk exists-x-f1 (y)
          (exists x (f1 x y)))

        (encapsulate ((f (x) t)
                      (h (x) t))
          (local (defun f (x) x))
          (defun g (x) (f x))
          (local (defun h (x) x))
          (defthm my-thm
            (equal (f x) (h (g x)))))
        (defchoose my-ch (x) (y)
          (f1 x (cons 0 y)))
        ))

(local
 (assert-event
  (equal (my-name)
         '((FOO :THEOREM (EQUAL (CAR (CONS X Y)) X))
           (F1 :DEF (EQUAL (F1 X Y) (<= X Y)))
           (BAR :THEOREM (< (ACL2-COUNT X)
                            (ACL2-COUNT (CONS X Y))))
           (EXISTS-X-F1-SUFF :THEOREM (IMPLIES (F1 X Y) (EXISTS-X-F1 Y)))
           ((EXISTS-X-F1 EXISTS-X-F1-WITNESS)
            :CONSTRAINT
            (AND (EQUAL (EXISTS-X-F1 Y)
                        (LET ((X (EXISTS-X-F1-WITNESS Y)))
                             (F1 X Y)))
                 (IMPLIES (F1 X Y) (EXISTS-X-F1 Y))))
           (MY-THM :THEOREM (EQUAL (F X) (H (G X))))
           ((G F H)
            :CONSTRAINT
            (AND (EQUAL (G X) (F X))
                 (EQUAL (F X) (H (G X)))))
           (MY-CH :DEFCHOOSE (IMPLIES (F1 X (CONS 0 Y))
                                      (LET ((X (MY-CH Y)))
                                           (F1 X (CONS 0 Y)))))))))
