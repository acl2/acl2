; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "../bit-vectors/bitops-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "u32"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (u32-fix
          u32-equal$inline
          u32-equal
          u32-plus
          u32-minus
          u32-uminus
          u32-and
          u32-or
          u32-xor
          u32-not
          u32-shl
          u32-shr
          ))

(defequiv u32-equal)
