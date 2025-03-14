; Standard System Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "classes")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (classes 'car-cdr-elim (w state)) '((:elim)))

(must-succeed*
 (defthm th (acl2-numberp (- x)))
 (assert-equal (classes 'th (w state)) '((:rewrite))))

(must-succeed*
 (defthm th (booleanp (if x t nil)) :rule-classes :type-prescription)
 (assert-equal (classes 'th (w state))
               '((:type-prescription :typed-term (if x 't 'nil)))))
