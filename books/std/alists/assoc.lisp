; Standard Association Lists Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/alists/assoc-equal
  :parents (std/alists assoc)
  :short "Theorems about @(tsee assoc-equal)
          in the @(see std/alists) library."

  (defthm consp-of-assoc-equal
    (implies (alistp alist)
             (iff (consp (assoc-equal key alist))
                  (assoc-equal key alist)))))
