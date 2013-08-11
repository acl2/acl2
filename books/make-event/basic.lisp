; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here are some simple examples intended to illustrate the basics of
; make-event, with a focus on make-event-debug.

(in-package "ACL2")

; Very simple example: generates the indicated defun.
(make-event
 '(defun test1 (x)
    (cons x x)))

; The setting of make-event-debug takes place after expansion begins, so we
; should NOT see debug information for expansion.  However, since
; make-event-debug is not in the list *protected-state-globals-for-make-event*,
; its setting will cause debug information to be printed for later events.
(make-event
 (pprogn
  (f-put-global 'make-event-debug t state)
  (value '(defun test2 (x)
            x))))

; Should now see debug output for make-event expansion (see comment above).
(make-event
 (value '(defun test3 (x)
           (list x x))))

; Should still see debug output, because make-event-debug is t when expansion
; is entered.  Moreover, we should see debug output later because of the
; state-global-let*.
(make-event
 (state-global-let*
  ((make-event-debug nil))
  (value '(defun test4 (x)
            x))))

; Should still see debug output.
(make-event
 (value '(defun test5 (x)
           x)))

; Should still see debug output, because the value of 'make-event-debug is t
; when expansion begins.
(make-event
 (pprogn
  (f-put-global 'make-event-debug nil state)
  (value '(defun test6 (x)
            x))))

; Should not see debug output, because the value of 'make-event-debug was set
; to nil just above.
(make-event
 (value '(defun test7 (x)
           x)))

; Let's check that we really did complete the definitions of test1, test2, and
; test3.

(defun bar (x)
  (list (test1 x) (test2 x) (test3 x)))

(defthm bar-prop
  (equal (bar x)
         (list (cons x x)
               x
               (list x x))))
