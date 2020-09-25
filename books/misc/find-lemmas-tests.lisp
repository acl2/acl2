(in-package "ACL2")
(include-book "find-lemmas")
(include-book "std/lists/sets" :dir :system)

(defconst *p-def* '(defun p (x) x))
(defconst *q-def* '(defun q (x) (p x)))
(defconst *foo-def* '(defthm foo (equal (p x) x)))
(defconst *bar-def* '(defthm bar (equal (q x) (p x))))

(local (make-event *p-def*))
(local (make-event *q-def*))
(local (make-event *foo-def*))
(local (make-event *bar-def*))

(assert-event (set-equiv (find-lemmas '(p)) (list *foo-def* *bar-def*)))
(assert-event (set-equiv (find-lemmas '(q)) (list *bar-def*)))
(assert-event (set-equiv (find-funs '(p)) (list *p-def* *q-def*)))
