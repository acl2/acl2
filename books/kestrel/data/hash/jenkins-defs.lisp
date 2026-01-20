; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HASH")

(include-book "kestrel/data/utilities/fixed-size-words/fixnum" :dir :system)
(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(local (include-book "std/util/defredundant" :dir :system))

(local (include-book "jenkins"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (jenkins-acc-byte
          jenkins-acc-character
          jenkins-acc-string-fixnum-index
          jenkins-acc-string-nonfixnum-index
          jenkins-acc-string
          jenkins-acc-nat
          jenkins-acc-integer
          jenkins-acc-rational
          jenkins-acc-complex-rational
          jenkins-acc-acl2-number
          jenkins-acc-symbol
          jenkins-acc-atom
          jenkins-acc
          jenkins
          acl2-number-jenkins
          symbol-jenkins
          eqlable-jenkins
          ))
