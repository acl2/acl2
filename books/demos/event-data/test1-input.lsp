; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree))
(set-gag-mode nil)

; Fails because file test1.acl2 isn't loaded here:
(saving-event-data (ld "test1.lisp"))

; Then the following produces differences as shown below.
(runes-diff "test1.lisp")

; The following shows the result from the runes-diff call above and relevant
; output that explains it.

; Result from runes-diff:
#|
 ((:OLD ((:TYPE-PRESCRIPTION TRUE-LISTP-REVERSE)))
  (:NEW ((:DEFINITION ALISTP)
         (:DEFINITION ATOM)
         (:DEFINITION NOT)
         (:DEFINITION TRUE-LISTP)
         (:ELIM CAR-CDR-ELIM)
         (:EXECUTABLE-COUNTERPART CONSP)
         (:EXECUTABLE-COUNTERPART NOT)
         (:EXECUTABLE-COUNTERPART REVERSE)
         (:FAKE-RUNE-FOR-TYPE-SET NIL)
         (:INDUCTION ALISTP))))
|#

; From summary in test1.cert.out:
#|
Rules: ((:FORWARD-CHAINING ALISTP-FORWARD-TO-TRUE-LISTP)
        (:TYPE-PRESCRIPTION ALISTP)
        (:TYPE-PRESCRIPTION REVERSE)
        (:TYPE-PRESCRIPTION TRUE-LISTP-REVERSE))
|#

; From corresponding summary in the ld call above:
#|
Rules: ((:DEFINITION ALISTP)
        (:DEFINITION ATOM)
        (:DEFINITION NOT)
        (:DEFINITION TRUE-LISTP)
        (:ELIM CAR-CDR-ELIM)
        (:EXECUTABLE-COUNTERPART CONSP)
        (:EXECUTABLE-COUNTERPART NOT)
        (:EXECUTABLE-COUNTERPART REVERSE)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:FORWARD-CHAINING ALISTP-FORWARD-TO-TRUE-LISTP)
        (:INDUCTION ALISTP)
        (:TYPE-PRESCRIPTION ALISTP)
        (:TYPE-PRESCRIPTION REVERSE))
|#
