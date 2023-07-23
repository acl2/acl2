; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree))
(set-gag-mode nil)

(in-theory (disable reverse))

; Fails because of the disable above:
(saving-event-data (ld "test2.lisp"))

; Then the following produces differences as shown below.
(runes-diff "test1.lisp")

(in-theory (disable (:t append)))

; Fails as before, but with a different proof for the thm:
(saving-event-data (ld "test2.lisp"))

; See rune differences for the thm:
(runes-diff "test2.lisp" :name nil)

; The following shows the result from the runes-diff call above and relevant
; output that explains it.

; Result from runes-diff:
#|
 ((:OLD ((:TYPE-PRESCRIPTION BINARY-APPEND)))
  (:NEW ((:ELIM CAR-CDR-ELIM))))
|#

; From summary for the THM in test2.cert.out:
#|
Rules: ((:DEFINITION BINARY-APPEND)
        (:DEFINITION ENDP)
        (:DEFINITION NOT)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:INDUCTION BINARY-APPEND)
        (:TYPE-PRESCRIPTION BINARY-APPEND))
|#

; From summary for the second attempt for the THM in test2-log.out:
#|
Rules: ((:DEFINITION BINARY-APPEND)
        (:DEFINITION ENDP)
        (:DEFINITION NOT)
        (:ELIM CAR-CDR-ELIM)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:INDUCTION BINARY-APPEND))
|#
