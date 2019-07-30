; Symbol Utilities -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbols")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (symbol-package-name-safe 'symbol-listp)
              "ACL2")

(assert-equal (symbol-package-name-safe 'std::define)
              "ACL2")


(assert-equal (symbol-package-name-safe 'std::deflist)
              "STD")

(assert-equal (symbol-package-name-safe 'cons)
              "ACL2")
