(in-package "ACL2")

; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann and Eric Smith
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Tests for verify-guards-program

(include-book "verify-guards-program")
(include-book "std/testing/must-fail" :dir :system)

(defun f1p (x) (declare (xargs :mode :program)) x)
(defun f2p (x)
  (declare (xargs :mode :program))
  (if (consp x) (f2p (cdr x)) x))
(defun f3 (x) x)
(defun f4p (x)
  (declare (xargs :mode :program))
  (list (f1p x) (f2p x) (f3 x)))
(verify-guards-program f4p :print t)

(defun f5p (x y)
  (declare (xargs :mode :program))
  (if (consp x)
      (f5p (cdr x) y)
    (if (consp y)
        (f5p x (cdr y))
      (list x y))))
(defun f6p (x y)
  (declare (xargs :mode :program))
  (list (f4p x) (f5p x y)))

; No measure guessed:
(verify-guards-program f6p :print t)

; Guard verification fails for f7p:
(defun f7p (x)
  (declare (xargs :mode :program))
  (car (f1p x)))
(must-fail (verify-guards-program f7p :print t))

; Fails (tests that verify-termination doesn't do guard
; verification under skip-proofs):
(defun f8p (x)
  (declare (xargs :mode :program :guard (not (acl2-numberp x))))
  (car (f1p x)))
(must-fail (verify-guards-program f8p))

; Succeeds
(defun f9p (x)
  (declare (xargs :mode :program :guard (consp x)))
  (car (f1p x)))
(verify-guards-program f9p)

;; Fails because f0 does not exist
(must-fail (verify-guards-program f0))

;;; A test with :hints:

(defun foo (x)
  (declare (xargs :mode :program
                  :guard (natp (car x))))
  x)
(defun bar (x)
  (declare (xargs :mode :program
                  :guard (natp x)))
  (foo (cons x nil)))
(in-theory (disable car-cons)) ;to make the proof fail without hints
;; fails without the hints:
(must-fail (verify-guards-program bar))
(verify-guards-program bar :hints (("Goal" :in-theory (enable car-cons))))
;Also test :otf-flg
(verify-guards-program bar :otf-flg t
                       :hints (("Goal" :in-theory (enable car-cons))))
