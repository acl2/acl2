; Tests for the deque book.
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Aakash Koneru

(in-package "DATA")

(include-book "deque")

(assert-event (equal (deque->list (empty-deque)) nil))
(assert-event (deque-emptyp (empty-deque)))
(assert-event (equal (deque-size (empty-deque)) 0))

(local (defconst *dq* (push-back 3 (push-front 1 (push-front 2 (empty-deque))))))

(assert-event (equal (deque->list *dq*) '(1 2 3)))
(assert-event (dequep *dq*))
(assert-event (not (deque-emptyp *dq*)))
(assert-event (equal (deque-size *dq*) 3))
(assert-event (equal (front *dq*) 1))
(assert-event (equal (back *dq*) 3))

(assert-event (equal (deque->list (pop-front *dq*)) '(2 3)))
(assert-event (equal (deque->list (pop-back *dq*)) '(1 2)))
(assert-event (equal (front (push-front 0 *dq*)) 0))
(assert-event (equal (back (push-back 4 *dq*)) 4))

(assert-event (equal (deque->list (list->deque '(a b c d e))) '(a b c d e)))
(assert-event (equal (deque-size (list->deque '(a b c d e))) 5))
(assert-event (dequep (list->deque '(1 2 3 4 5 6 7 8 9))))
