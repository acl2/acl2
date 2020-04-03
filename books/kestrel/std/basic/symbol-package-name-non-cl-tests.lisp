; Standard Basic Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-package-name-non-cl")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (symbol-package-name-non-cl 'symbol-listp)
              "ACL2")

(assert-equal (symbol-package-name-non-cl 'std::define)
              "ACL2")


(assert-equal (symbol-package-name-non-cl 'std::deflist)
              "STD")

(assert-equal (symbol-package-name-non-cl 'cons)
              "ACL2")
