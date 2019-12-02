; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fresh-namep")
(include-book "function-name-listp")
(include-book "function-namep")
(include-book "function-symbol-listp")
(include-book "function-symbolp")
(include-book "logic-function-namep")
(include-book "logical-name-listp")
(include-book "macro-name-listp")
(include-book "macro-namep")
(include-book "macro-symbol-listp")
(include-book "macro-symbolp")
(include-book "theorem-name-listp")
(include-book "theorem-namep")
(include-book "theorem-symbol-listp")
(include-book "theorem-symbolp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/event-name-queries
  :parents (std/system)
  :short "Utilities to query names of events in the @(see world).")
