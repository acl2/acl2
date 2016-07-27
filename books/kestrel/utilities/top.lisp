; Kestrel Utilities
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides utilities in the Kestrel Books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../general/auto-termination")
(include-book "../general/define-sk")
(include-book "../general/testing")
(include-book "../general/types")
(include-book "../general/ubi")

(include-book "../system/applicability-conditions")
(include-book "../system/defchoose-queries")
(include-book "../system/defun-sk-queries")
(include-book "../system/directed-untranslate")
(include-book "../system/event-forms")
(include-book "../system/fresh-names")
(include-book "../system/install-not-norm-event")
(include-book "../system/minimize-ruler-extenders")
(include-book "../system/numbered-names")
(include-book "../system/prove-interface")
(include-book "../system/terms")
(include-book "../system/user-interface")
(include-book "../system/verify-guards-program")
(include-book "../system/world-queries")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-utilities

  :parents (kestrel-books)

  :short
  "Utilities in the <see topic='@(url kestrel-books)'>Kestrel Books</see>.")
