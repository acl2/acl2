; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macro-args-plus")
(include-book "macro-keyword-args")
(include-book "macro-keyword-args-plus")
(include-book "macro-required-args")
(include-book "macro-required-args-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/macro-queries
  :parents (std/system)
  :short "Utilities to query macros."
  :long
  (xdoc::topstring-p
   "These utilities retrieve properties of macros in the @(see world)."))
