; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ubyte64")

(include-book "defbyte-ihs-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ubyte64-ihs-theorems
  :parents (ubyte64 fty::defbyte-standard-instances-ihs-theorems)
  :short (xdoc::topstring "Theorems about @(tsee ubyte64) and "
                          (xdoc::seetopic "ihs" "IHS") " functions.")

  (fty::defbyte-ihs-theorems ubyte64))
