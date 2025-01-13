; Copyright (C) 2024, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.txt for an overview of this example.

(in-package "ACL2")

; Introduce the implementation stobj, mem{ht}.
(include-book "mem_ht")

; Prepare to attach mem{ht} to the stobj, mem, when mem is introduced as an
; attachable stobj.
(attach-stobj mem mem{ht})

; Introduce the attachable stobj, mem, to which mem{ht} is to be attached (see
; above).
(include-book "mem")

; This little test at certification time is skipped by include-book:
(value-triple (update 3 'three mem)
              :stobjs-out '(mem))

; This little test at certification time is skipped by include-book:
(assert-event (equal (lookup 3 mem)
                     'three))

; See demo-input.lsp for evaluation examples, including expected output.
