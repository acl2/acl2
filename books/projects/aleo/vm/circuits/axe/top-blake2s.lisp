; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "support-blake2s")
(include-book "add-plus-3")
(include-book "blake2s-r1cs")
(include-book "blake2s-one-round-r1cs")
(include-book "blake2s1round")
(include-book "blake2s-one-round-spec-openers")
(include-book "blake2s-one-round-proof")
(include-book "blake2s-one-round-proof2")
;(include-book "blake2s-spec-openers") ;conflict on number of rounds in the spec
;(include-book "blake2s-proof2") ;; works but takes several hours, conflict on *r*
