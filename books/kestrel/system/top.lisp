; System Utilities
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides some system utilities.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "auto-termination")
(include-book "defun-sk-queries")
(include-book "directed-untranslate")
(include-book "event-forms")
(include-book "fresh-names")
(include-book "install-not-norm-event")
(include-book "minimize-ruler-extenders")
(include-book "prove-interface")
(include-book "terms")
(include-book "ubi")
(include-book "verify-guards-program")
(include-book "world-queries")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-system-utilities

  :parents (kestrel-books)

  :short "Some system utilities.")
