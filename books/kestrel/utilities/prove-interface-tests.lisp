; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2006)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "prove-interface")

(include-book "std/testing/eval" :dir :system) ; for assert!-stobj

(defmacro must-succeed-pi (form) ; prove-interface version of must-succeed
  `(local (must-eval-to-t ,form)))

(defmacro must-fail-pi (form) ; prove-interface version of must-succeed
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
(defun first-success (termlist time-limit state)
  (declare (xargs :mode :program :stobjs state))
  (cond ((endp termlist) (value nil))
        (t (er-let* ((result (prove$ (car termlist) :time-limit time-limit)))
             (cond (result (value (car termlist)))
                   (t (first-success (cdr termlist) time-limit state)))))))

; Returns (mv nil (equal (append (append x y) z) (append x y z)) state):
#+skip
(local (must-eval-to
        (first-success '((equal x y)
                         (equal (append (append x y) x y x y x y x y)
                                (append x y x y x y x y x y))
                         (equal (append (append x y) z)
                                (append x y z))
                         (equal u u))
                       2
                       state)
        '(equal (append (append x y) z) (append x y z))))
