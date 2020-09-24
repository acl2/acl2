(in-package "ACL2")
(include-book "find-lemmas")
(include-book "std/lists/sets" :dir :system)

(local (defun p (x) x))
(local (defun q (x) (p x)))
(local (defthm foo (equal (p x) x)))
(local (defthm bar (equal (q x) (p x))))

(assert-event (set-equiv (find-lemmas '(p))
                         '((defthm foo (equal (p x) x))
                           (defthm bar (equal (q x) (p x))))))

(assert-event (set-equiv (find-lemmas '(q))
                         '((defthm bar (equal (q x) (p x))))))

(assert-event (set-equiv (find-funs '(p))
                         '((defun p (x) x) (defun q (x) (p x)))))
