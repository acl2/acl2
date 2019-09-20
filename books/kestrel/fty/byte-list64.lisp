; FTY -- Fixtype of True Lists of 64 (Unsigned 8-bit) Bytes
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/deflist-of-len" :dir :system)

(include-book "byte-list")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist-of-len byte-list64
  :list-type byte-list
  :length 64
  :pred byte-list64p
  :parents (fty::fty-extensions fty::specific-types byte-list)
  :short
  (xdoc::topstring
   "A "
   (xdoc::seetopic "fty::fty" "fixtype")
   " of true lists of "
   (xdoc::seetopic "bytep" "(unsigned 8-bit) bytes")
   " of length 64."))
