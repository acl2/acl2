; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HASH")

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)

(include-book "kestrel/data/utilities/bit-vectors/bitops-defs" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(local (include-book "std/util/defredundant" :dir :system))

(local (include-book "to-bytes"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (*tag-cons*
          *tag-symbol*
          *tag-string*
          *tag-character*
          *tag-integer*
          *tag-rational*
          *tag-complex*
          *tag-bad-atom*
          nat-to-bytes
          nat-to-leb128-groups
          integer-contents-to-bytes
          integer-to-bytes
          rational-contents-to-bytes
          rational-to-bytes
          complex-rational-to-bytes
          acl2-number-to-bytes
          character-contents-to-bytes
          character-to-bytes
          characters-to-bytes
          string-contents-to-bytes
          string-to-bytes
          symbol-to-bytes
          atom-to-bytes
          to-bytes
          no-bad-atoms-p
          ))
