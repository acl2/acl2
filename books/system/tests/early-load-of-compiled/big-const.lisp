; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book has taken twice as long to include as to certify, because *c*
; wasn't qualified.  This was fixed in mid-February 2021; now, include-book is
; as fast as certify-book and is as fast as when providing include-book with
; :load-compiled-file nil.  The relevant change is to eliminate the "oldp" part
; of install-for-add-trip-hcomp-build, by removing the call of
; install-for-add-trip in the attachment case of add-trip.

(in-package "ACL2")

; The following is necessary for fixing the include-book slow-down before
; mid-February 2021, by causing roll-back when certifying.

; (local (defun loc (x) x))

(defun big-c (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) nil)
        (t (let ((x (big-c (1- n))))
             (cons x x)))))

(defconst *c* (acl2-count (big-c 27)))
