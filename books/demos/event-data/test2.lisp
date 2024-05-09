; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


; To demonstrate runes-diff:
; (1) Certify test2, which uses .acl2 file to generate
;     .sys/test1@event-data.lsp.
; (2) In ACL2
;     (in-theory (disable reverse))
;     (saving-event-data (ld "test2.lisp"))
; (3) We see in the following that (:definition reverse)
;     is in the old runes (from the certification) but
;     not in the new runes (from the ld):
;     (runes-diff "test2.lisp")
; Now we disable the type-prescription for binary-append, which doesn't cause
; the thm to fail but does cause its runes to change.
; (5) (in-theory (disable (:t append)))
; (6) (saving-event-data (ld "test2.lisp"))
; (7) We see that (:TYPE-PRESCRIPTION BINARY-APPEND) is a rule from the proof
;     when certifying the book but not from the latest ld, and we see that an
;     elim rule was used in the new proof attempt (from that ld).
;     Notice the use of :name nil, since there is no name associated with a
;     thm.
;     (runes-diff "test2.lisp" :name nil)

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

(thm (implies (consp (append y x)) (consp (append x y))))

(define foo ((x true-listp))
  :verify-guards nil
  (append (reverse x) x)
  ///
  (verify-guards foo))

(defun h (x) x)
