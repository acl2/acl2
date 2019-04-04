; Alist Utilities -- Theorems about REMOVE-ASSOC-EQUAL
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection remove-assoc-equal-theorems
  :parents (alist-utilities remove-assoc)
  :short "Some theorems about the built-in function @(tsee remove-assoc)."

  (defthm alistp-of-remove-assoc-equal
    (implies (alistp x)
             (alistp (remove-assoc-equal key x)))))
