; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book illustrates a workaround, as promised in :DOC loop$, for the case
; that a function's measure's depends on a warrant.  We show that the resulting
; function can be executed in the ACL2 loop without calling the warrant, and we
; illustrate some reasoning about the resulting definition given that its body
; depends on a warrant.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defun$ cons-count (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ 1 (cons-count (car x)) (cons-count (cdr x)))
    0))

(defun$ cons-count-lst (lst)
  (declare (xargs :guard t))
  (loop$ for x in (true-list-fix lst)
         sum
         (1+ (cons-count x))))

(must-fail
; fails (needs warrant):
(defun count-numeric-leaves (x)
  (declare (xargs :guard t
                  :measure (cons-count-lst x)))
  (cond ((consp x)
         (if (atom (car x))
             (if (acl2-numberp (car x))
                 (1+ (count-numeric-leaves (cdr x)))
               (count-numeric-leaves (cdr x)))
           (+ (count-numeric-leaves (caar x))
              (count-numeric-leaves (cdar x))
              (count-numeric-leaves (cdr x)))))
        ((acl2-numberp x) 1)
        (t 0)))
)

; succeeds with warrant:
(defun count-numeric-leaves (x)
  (declare (xargs :guard (eq (warrant cons-count) t)
                  :measure (if (warrant cons-count)
                               (cons-count-lst x)
                             0)))
  (if (mbt (warrant cons-count))
      (cond ((consp x)
             (if (atom (car x))
                 (if (acl2-numberp (car x))
                     (1+ (count-numeric-leaves (cdr x)))
                   (count-numeric-leaves (cdr x)))
               (+ (count-numeric-leaves (caar x))
                  (count-numeric-leaves (cdar x))
                  (count-numeric-leaves (cdr x)))))
            ((acl2-numberp x) 1)
            (t 0))
    0))

(assert-event (equal (count-numeric-leaves '(3 (4 . 5) 6))
                     4))

(must-fail
; fails (needs warrant):
 (thm (equal (count-numeric-leaves '(3 (4 . 5) 6))
             4)
      :hints (("Goal" :in-theory (disable (:e count-numeric-leaves)))))
 )

; succeeds with warrant:
(thm (implies (warrant cons-count)
              (equal (count-numeric-leaves '(3 (4 . 5) 6))
                     4))
     :hints (("Goal" :in-theory (disable (:e count-numeric-leaves)))))
