; FTY -- Fixtype of (Unsigned 8-bit) Bytes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/defbyte" :dir :system)

; to use the BYTEP recognizer in Std:
(include-book "std/basic/bytep" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defbyte byte
  :size 8
  :pred bytep
  :parents (fty::fty-extensions fty::specific-types bytep)
  :short
  (xdoc::topstring
   "A "
   (xdoc::seetopic "fty::fty" "fixtype")
   " of "
   (xdoc::seetopic "bytep" "(unsigned 8-bit) bytes")
   ".")
  :long
  (xdoc::topstring-p
   "We use @(tsee fty::defbyte) to generate this fixtype,
    along with the recognizer, fixer, and equivalence.
    The recognizer is identical to @(tsee bytep)."))
