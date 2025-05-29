; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "ubyte3-ihs-theorems")
(include-book "ubyte5-ihs-theorems")
(include-book "ubyte6-ihs-theorems")
(include-book "ubyte7-ihs-theorems")
(include-book "ubyte8-ihs-theorems")
(include-book "ubyte12-ihs-theorems")
(include-book "ubyte16-ihs-theorems")
(include-book "ubyte32-ihs-theorems")
(include-book "ubyte64-ihs-theorems")
(include-book "ubyte128-ihs-theorems")

(include-book "sbyte8-ihs-theorems")
(include-book "sbyte16-ihs-theorems")
(include-book "sbyte32-ihs-theorems")
(include-book "sbyte64-ihs-theorems")
(include-book "sbyte128-ihs-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbyte-standard-instances-ihs-theorems
  :parents (defbyte-standard-instances)
  :short (xdoc::topstring
          "Theorems about @(tsee defbyte) standard instances and "
          (xdoc::seetopic "acl2::ihs" "IHS") " functions."))
