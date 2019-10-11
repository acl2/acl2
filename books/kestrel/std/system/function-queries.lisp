; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arity-plus")
(include-book "definedp")
(include-book "definedp-plus")
(include-book "formals-plus")
(include-book "primitivep")
(include-book "primitivep-plus")
(include-book "pure-raw-p")
(include-book "rawp")
(include-book "stobjs-in-plus")
(include-book "stobjs-out-plus")
(include-book "ubody")
(include-book "ubody-plus")
(include-book "uguard")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/function-queries
  :parents (std/system)
  :short "Utilities to query functions."
  :long
  (xdoc::topstring-p
   "These utilities are mostly for named functions in the @(see world),
    but some utilities also work on lambda expressions."))
