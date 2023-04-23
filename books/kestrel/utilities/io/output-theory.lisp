; A book that loads a theory useful for guard-verified, logic mode file output.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/open-output-channel-p" :dir :system)
(include-book "kestrel/file-io-light/open-output-channel" :dir :system)
(in-theory (enable open-output-channel-p1-becomes-open-output-channel-p))

(include-book "kestrel/file-io-light/close-output-channel" :dir :system)

(include-book "kestrel/file-io-light/princ-dollar" :dir :system)
(include-book "kestrel/file-io-light/prin1-dollar" :dir :system)

; See output-theory-doc.lisp
; for xdoc definition.
