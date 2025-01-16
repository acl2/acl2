; Standard Typed Alists Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/typed-alists/symbol-alistp
  :parents (std/typed-alists)
  :short "Theorems about the built-in @(tsee symbol-alistp)."

  (defthm symbol-alistp-of-append
    (equal (symbol-alistp (append x y))
           (and (symbol-alistp (true-list-fix x))
                (symbol-alistp y))))

  (defthmd alistp-when-symbol-alistp
    (implies (symbol-alistp x)
             (alistp x)))

  (defthmd symbol-listp-of-strip-cars-when-symbol-alistp
    (implies (symbol-alistp alist)
             (symbol-listp (strip-cars alist)))))
