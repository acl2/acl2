; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HASH")

(include-book "to-bytes-defs")

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)

(include-book "kestrel/data/utilities/fixed-size-words/fixnum" :dir :system)
(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(local (include-book "std/util/defredundant" :dir :system))

(local (include-book "jenkins"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (jenkins-acc-byte
          jenkins-acc-bytes
          jenkins-acc-leb128-small
          jenkins-acc-leb128-groups-small
          jenkins-acc-leb128-groups
          jenkins-acc-nat
          jenkins-acc-integer-contents
          jenkins-acc-integer
          jenkins-acc-rational-contents
          jenkins-acc-rational
          jenkins-acc-complex-rational
          jenkins-acc-acl2-number
          jenkins-acc-character-contents
          jenkins-acc-character
          jenkins-acc-string-index
          jenkins-acc-string-contents
          jenkins-acc-string
          jenkins-acc-symbol
          jenkins-acc-atom
          jenkins-acc
          jenkins-finalize
          jenkins-bytes
          jenkins
          acl2-number-jenkins
          symbol-jenkins
          eqlable-jenkins
          ))
