; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/system/flatten-ands-in-lit
  :parents (std/system/term-transformations)
  :short (xdoc::topstring "Theorems about "
                          (xdoc::seetopic "system-utilities"
                                          "@('flatten-ands-in-lit')")
                          ".")

  (defthm pseudo-term-listp-of-flatten-ands-in-lit
    (implies (pseudo-termp term)
             (pseudo-term-listp (flatten-ands-in-lit term)))))

(in-theory (disable flatten-ands-in-lit))
