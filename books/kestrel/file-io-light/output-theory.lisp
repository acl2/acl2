; A book that loads a theory useful for guard-verified, logic mode file output.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "open-output-channel-p")
(include-book "open-output-channel")
(in-theory (enable open-output-channel-p1-becomes-open-output-channel-p))

(include-book "close-output-channel")

(include-book "princ-dollar")
(include-book "prin1-dollar")

; See output-theory-doc.lisp
; for xdoc definition.
