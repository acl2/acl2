;; Copyright (C) 2020, Regents of the University of Texas
;; Written by Mihir Mehta
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

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
(local (mutual-recursion
        (defun evenlp (x)
          (if (consp x) (oddlp (cdr x)) t))
        (defun oddlp (x)
          (if (consp x) (evenlp (cdr x)) nil))))

(assert-event (set-equiv (find-lemmas '(p))
                         (list *foo-def* *bar-def*)))
(assert-event (set-equiv (find-lemmas '(q))
                         (list *bar-def*)))
(assert-event
 (member-equal
  'nth-update-nth
  (strip-cars (strip-cdrs (find-lemmas '(update-nth) nil)))))
(assert-event
 (not
  (member-equal
   'nth-update-nth
   (strip-cars (strip-cdrs (find-lemmas '(update-nth)))))))

(assert-event (set-equiv (find-defs '(p))
                         (list *p-def* *q-def*)))

(assert-event
 (set-equiv (find-events '(p))
            (list *p-def* *q-def* *foo-def* *bar-def*)))
