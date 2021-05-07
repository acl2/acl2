; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ubyte16")

(include-book "defbyte-ihs-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ubyte16-ihs-theorems
  :parents (ubyte16 fty::defbyte-standard-instances-ihs-theorems)
  :short (xdoc::topstring "Theorems about @(tsee ubyte16) and "
                          (xdoc::seetopic "ihs" "IHS") " functions.")

  (fty::defbyte-ihs-theorems ubyte16))
