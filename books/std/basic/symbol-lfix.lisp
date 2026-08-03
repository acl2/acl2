; Standard Basic Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-lfix ((x symbolp))
  :returns (x-fixed symbolp)
  :parents (std/basic symbol-fix)
  :short "Fixer for @(tsee symbolp) that is the identity in execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is logically @(tsee symbol-fix),
     but the @(tsee symbolp) guard allows execution as a no-op."))
  (mbe :logic (symbol-fix x)
       :exec x)
  :no-function t
  :hooks (:fix))
