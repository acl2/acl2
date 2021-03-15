; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book certifies, even if the local event just below is commented out.
; But without the local event, a subsequent include-book then fails.  The
; reason the local event saves us is that it causes the include-book phase of
; certify-book to roll back the world all the way to ground-zero before
; including the book, and that way it can see that the symbol-function of
; ttag-f at the end doesn't match the symbol-function that was stored in the
; *hcomp-fn-ht* by add-trip (via install-for-add-trip-hcomp-build) when ttag-f
; was admitted.  Without that rollback, *hcomp-fn-ht* gets the wrong entry (via
; hcomp-build-from-state) -- i.e., the final symbol-function -- and that final
; eq check succeeds, so ttag-f is considered qualified.

(in-package "ACL2")

(local (defun loc (x) x))

; This is basically assert!, except for the :check-expansion, which causes the
; check to take place even at include-book time.
(defmacro chk (x)
  `(make-event (if ,x
                   '(value-triple :success)
                 (er soft 'chk "Failure for ~x0" ',x))
               :check-expansion t))

(defun ttag-f (x)
  (declare (xargs :guard t))
  x)

(defttag :ttag-test)

; The following is fine during certify-book but not during include-book.
(chk (equal (ttag-f 3) 3))

(progn!
 (set-raw-mode t)
 (defun ttag-f (x) (cons x x)))
