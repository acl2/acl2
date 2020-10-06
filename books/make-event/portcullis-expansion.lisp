; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we do a bunch of tests that have generally already been recorded in the
; certification world.

(in-package "ACL2")

(set-enforce-redundancy t)

(defun test1 (x)
  (cons x x))

(defun test2 (x)
  x)

(defun test3 (x)
  x)

(encapsulate
 ((foo (x) t))
 (local (make-event '(defun foo (x) (cons x x))))
 (defthm foo-prop
   (consp (foo x))))

(encapsulate
 ((foo2 (x) t))
 (local (make-event '(defun foo2 (x) (cons x x))
                    :check-expansion t))
 (defthm foo2-prop
   (consp (foo2 x))))

(encapsulate
 ((foo3 (x) t))
 (local (make-event '(defun foo3 (x) (cons x x))
                    :check-expansion
                    (defun foo3 (x) (cons x x))))
 (defthm foo3-prop
   (consp (foo3 x))))

(defun bar (x) (cons x x))

(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identical with original event, so should succeed.
(encapsulate
 ()
 (make-event '(defun bar (x) (cons x x)))
 (defthm bar-prop
   (consp (bar x))))

; Succeeds because component events are redundant.
(encapsulate
 ()
 (defun bar (x) (cons x x))
 (defthm bar-prop
   (consp (bar x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identical with original encapsulate, so succeeds.
(encapsulate
 ()
 (make-event '(defun bar2 (x) (cons x x))
             :check-expansion t)
 (defthm bar2-prop
   (consp (bar2 x))))

; Not identical with original encapsulate, but succeeds because component
; events are redundant.
(encapsulate
 ()
 (make-event '(defun bar2 (x) (cons x x))
             :check-expansion
             (defun bar2 (x) (cons x x)))
 (defthm bar2-prop
   (consp (bar2 x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identical with original encapsulate, so succeeds.
(encapsulate
 ()
 (make-event '(defun bar3 (x) (cons x x))
             :check-expansion
             (defun bar3 (x) (cons x x)))
 (defthm bar3-prop
   (consp (bar3 x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Identical with original encapsulate, so succeeds.
(encapsulate
 ((local-fn (x) t))
 (local (defun local-fn (x) x))
 (make-event '(defun bar4 (x) (cons x x))
             :check-expansion nil)
 (defthm bar4-prop
   (consp (bar4 x))))

; The following doesn't help the failures below, because of non-trivial
; signature in each case.
(set-enforce-redundancy nil)

; Not identical with original encapsulate, so fails (even though actual
; :check-expansion is the same).
(must-fail
 (encapsulate
  ((local-fn (x) t))
  (local (defun local-fn (x) x))
  (make-event '(defun bar4 (x) (cons x x)))
  (defthm bar4-prop
    (consp (bar4 x)))))

; Not identical with original encapsulate, so fails.
(must-fail
 (encapsulate
  ((local-fn (x) t))
  (local (defun local-fn (x) x))
  (make-event '(defun bar4 (x) (cons x x))
              :check-expansion t)
  (defthm bar4-prop
    (consp (bar4 x)))))

; Not identical with original encapsulate, so fails.
(must-fail
 (encapsulate
  ((local-fn (x) t))
  (local (defun local-fn (x) x))
  (make-event '(defun bar4 (x) (cons x x))
              :check-expansion
              (defun bar4 (x) (cons x x)))
  (defthm bar4-prop
    (consp (bar4 x)))))

(defmacro my-id (x) x)

; Not identical with original encapsulate even though my-id is the identity
; macro, so fails.
(must-fail
 (encapsulate
  ((local-fn (x) t))
  (local (defun local-fn (x) x))
  (my-id (make-event '(defun bar4 (x) (cons x x))
                     :check-expansion nil))
  (defthm bar4-prop
    (consp (bar4 x)))))
