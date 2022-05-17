; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Small test of including a book built on local portcullis events.

(in-package "ACL2")

; I'll use no_port on the next line just to keep the test "pure".
(include-book "local-port") ; no_port

; F2 is defined only locally in the portcullis commands of local-port.lisp:
(assert-event (eq (getpropc 'f2 'formals t) t))

(value-triple (equal (g 3) '(3 . 3))
              :on-skip-proofs t)
