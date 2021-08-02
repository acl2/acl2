; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2006)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "prove-dollar")

(include-book "std/testing/assert-bang-stobj" :dir :system)
(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defmacro must-succeed-pi (form) ; prove-dollar version of must-succeed
  `(local (must-eval-to-t ,form)))

(defmacro must-fail-pi (form) ; prove-dollar version of must-succeed
  `(local (must-fail (must-eval-to-t ,form))))

; Returns (mv nil t state).
(must-succeed-pi (prove$ '(equal x x)))

; Returns (mv nil nil state).  Notice that unlike the other arguments, the
; :with-output argument is not evaluated.
(must-fail-pi
 (prove$ '(equal x y)
         :with-output (:off summary)))

; Returns (mv nil nil state).
(must-fail-pi
 (prove$ '(equal (append (append x y) x y x y x y x y)
                 (append x y x y x y x y x y))
         :time-limit 5/4))

(must-fail-pi
 (prove$ '(equal (append (append x y) x y x y x y x y)
                 (append x y x y x y x y x y))
         :step-limit 1000))

; ; Returns (mv nil nil state); all options are used.
(must-fail-pi
 (prove$ '(and (equal (append (append x y) x y x y x y x y)
                      (append x y x y x y x y x y))
               (equal (append (append x y) x y x y x)
                      (append x y x y x y x y x)))
         :otf-flg t
         :hints '(("Goal" :use ((:theorem (equal x x)))))
         :time-limit 3
         :with-output nil))

; :pso ; displays the proof

; Use prove$ in a function.
(defun first-success-time (termlist time-limit state)
  (declare (xargs :mode :program :stobjs state))
  (cond ((endp termlist) (value nil))
        (t (er-let* ((result (prove$ (car termlist) :time-limit time-limit)))
             (cond (result (value (car termlist)))
                   (t (first-success-time (cdr termlist) time-limit state)))))))

; Returns (mv nil (equal (append (append x y) z) (append x y z)) state):
(local (must-eval-to
        (first-success-time '((equal x y)
                              (equal (append (append x y) x y x y x y x y)
                                     (append x y x y x y x y x y))
                              (equal (append (append x y) z)
                                     (append x y z))
                              (equal u u))
                            2 ; I've measured about 1/100 as sufficient.
                            state)
        '(equal (append (append x y) z) (append x y z))))

; Use prove$ in a function.
(defun first-success-step (termlist step-limit state)
  (declare (xargs :mode :program :stobjs state))
  (cond ((endp termlist) (value nil))
        (t (er-let* ((result (prove$ (car termlist) :step-limit step-limit)))
             (cond (result (value (car termlist)))
                   (t (first-success-step (cdr termlist) step-limit state)))))))

(local (must-eval-to
        (first-success-step '((equal x y)
                              (equal (append (append x y) x y x y x y x y)
                                     (append x y x y x y x y x y))
                              (equal (append (append x y) z)
                                     (append x y z))
                              (equal u u))
                            1000 ; 435 should suffice
                            state)
        '(equal (append (append x y) z) (append x y z))))
