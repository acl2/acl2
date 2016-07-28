; Kestrel Utilities
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides a collection of utilities contributed by Kestrel Institute.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "applicability-conditions")
(include-book "auto-termination")
(include-book "defchoose-queries")
(include-book "define-sk")
(include-book "defun-sk-queries")
(include-book "directed-untranslate")
(include-book "event-forms")
(include-book "fresh-names")
(include-book "install-not-norm-event")
(include-book "minimize-ruler-extenders")
(include-book "numbered-names")
(include-book "prove-interface")
(include-book "terms")
(include-book "testing")
(include-book "types")
(include-book "ubi")
(include-book "user-interface")
(include-book "verify-guards-program")
(include-book "world-queries")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-utilities

  :parents (kestrel-books)

  :short "A collection of utilities contributed by Kestrel Institute.")
