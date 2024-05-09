; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


; Portcullis command (see test1a.acl2):
#|
(defthm true-listp-reverse
  (implies (true-listp x)
           (true-listp (reverse x)))
  :rule-classes :type-prescription)
|#

; To demonstrate runes-diff:
; (1) Certify test1a, which uses .acl2 file to generate
;     .sys/test1a@event-data.lsp.
; (2) In ACL2:
;     (saving-event-data (ld "test1a.lisp"))
;     which fails because .acl2 file wasn't loaded.
; (3) (runes-diff "test1a.lisp")

(in-package "ACL2")

(defun bar (x) (declare (xargs :guard t)) x)

(in-theory (disable reverse))

(defun foo (x)
  (declare (xargs :guard (alistp x) :verify-guards nil))
  (append (reverse x) x))

; Fails when we ld this file.  This is the proof obligation from (verify-guards
; foo) in test1.lisp, but our initial implementation had special handling for
; verify-guards (in source function event-data-name) that allowed the
; runes-diff call in test1a-input.lsp to work.  It didn't work here, but now it
; does.
(defthm foo-guard-obligation
  (implies (alistp x)
           (true-listp (reverse x))))

(defun h (x) x)
