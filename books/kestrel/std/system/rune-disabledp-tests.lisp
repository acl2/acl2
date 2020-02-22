; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rune-disabledp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (rune-disabledp '(:rewrite cons-car-cdr) state)))

(must-succeed*
 (defthmd th (acl2-numberp (+ x y)))
 (assert! (rune-disabledp '(:rewrite th) state)))

(must-succeed*
 (defthm th (acl2-numberp (+ x y)))
 (assert! (not (rune-disabledp '(:rewrite th) state))))

(must-succeed*
 (defthmd th (acl2-numberp (+ x y)) :rule-classes :type-prescription)
 (assert! (rune-disabledp '(:type-prescription th) state)))

(must-succeed*
 (defthmd th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert! (rune-disabledp '(:rewrite th . 1) state))
 (assert! (rune-disabledp '(:rewrite th . 2) state)))

(must-succeed*
 (defthm th
   (acl2-numberp (+ x y))
   :rule-classes ((:rewrite :corollary (acl2-numberp (+ x y)))
                  (:rewrite :corollary (acl2-numberp (+ y x)))))
 (assert! (not (rune-disabledp '(:rewrite th . 1) state)))
 (assert! (not (rune-disabledp '(:rewrite th . 2) state))))
