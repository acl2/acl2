; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "INTERVAL")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following contains extensions to noninterval arithmetic
;; functions. Namely, maybe-rationalp and maybe-rational-fix (but also bringing
;; in kestrel/utilities/arith-fix-and-equiv).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled maybe-rationalp-when-rationalp
  (implies (rationalp x)
           (maybe-rationalp x))
  :enable maybe-rationalp)

(defrule maybe-rationalp-when-rationalp-cheap
  (implies (rationalp x)
           (maybe-rationalp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by maybe-rationalp-when-rationalp)

(defruled maybe-rationalp-when-not
  (implies (not (double-rewrite x))
           (maybe-rationalp x))
  :enable maybe-rationalp)

(defrule maybe-rationalp-when-not-cheap
  (implies (not x)
           (maybe-rationalp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :use maybe-rationalp-when-not)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule rationalp-of-maybe-rational-fix
  (equal (rationalp (maybe-rational-fix x))
         (and x t))
  :enable maybe-rational-fix)

(defruled maybe-rational-fix-when-arg
  (implies x
           (equal (maybe-rational-fix x)
                  (rfix x)))
  :enable maybe-rational-fix)

(defrule maybe-rational-fix-when-arg-cheap
  (implies x
           (equal (maybe-rational-fix x)
                  (rfix x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by maybe-rational-fix-when-arg)

(defrule maybe-rational-fix-under-iff
  (iff (maybe-rational-fix x)
       x)
  :enable maybe-rational-fix)
