; Standard Association Lists Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Mihir Mehta (mihir@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection std/alists/remove-assoc-equal
  :parents (std/alists remove-assoc)
  :short "Theorems about @(tsee remove-assoc-equal)
          in the @(see std/alists) library."

  (defthm alistp-of-remove-assoc-equal
    (implies (alistp x)
             (alistp (remove-assoc-equal a x))))

  (defthm acl2-count-of-remove-assoc-equal-upper-bound
    (<= (acl2-count (remove-assoc-equal a x))
        (acl2-count x))
    :rule-classes :linear)

  (defthm symbol-alistp-of-remove-assoc-equal
    (implies (symbol-alistp x)
             (symbol-alistp (remove-assoc-equal a x))))

  (defthm eqlable-alistp-of-remove-assoc-equal
    (implies (eqlable-alistp x)
             (eqlable-alistp (remove-assoc-equal a x))))

  (defthm strip-cars-of-remove-assoc-equal
    (equal (strip-cars (remove-assoc-equal a x))
           (remove-equal a (strip-cars x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable remove-assoc-equal))
