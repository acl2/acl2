; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")


; If the invariant holds, it does not break during evaluation.
(include-book "inv-proof")

; If the invariant holds, there will be no deadlock.
(include-book "termination")

; TODO: show (create-wtree n) satisfies the invariant.
; - the result of create-wtree has a root by construction
; - and that root has a rightmost child,  with index equal to n
;   also by construction.
; - So, if inv holds for root, and if root terminated,
;   it will contain sum((1- n)).