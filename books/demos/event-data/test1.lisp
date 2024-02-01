; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


; Portcullis command (see test1.acl2):
#|
(defthm true-listp-reverse
  (implies (true-listp x)
           (true-listp (reverse x)))
  :rule-classes :type-prescription)
|#

; To demonstrate runes-diff:
; (1) Certify test1, which uses .acl2 file to generate
;     .sys/test1@event-data.lsp.
; (2) In ACL2:
;     (saving-event-data (ld "test1.lisp"))
;     which fails because .acl2 file wasn't loaded.
; (3) (runes-diff "test1.lisp")

(in-package "ACL2")

(defun bar (x) (declare (xargs :guard t)) x)

(in-theory (disable reverse))

(defun foo (x)
  (declare (xargs :guard (alistp x) :verify-guards nil))
  (append (reverse x) x))

; Fails when we ld this file.
(verify-guards foo)

(defun h (x) x)
