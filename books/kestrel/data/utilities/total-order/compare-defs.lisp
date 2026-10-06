; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "../fixed-size-words/fixnum")
(include-book "total-order-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "compare"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (atom-type-rank$inline
          atom-type-rank
          fast-acl2-number-compare-<<
          fast-symbol-compare-<<
          fast-eqlable-compare-<<
          fast-compare-<<
          compare-<<$inline
          compare-<<
          acl2-number-compare-<<$inline
          acl2-number-compare-<<
          symbol-compare-<<$inline
          symbol-compare-<<
          eqlable-compare-<<$inline
          eqlable-compare-<<))
