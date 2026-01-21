; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "core")
(include-book "with-fixing-theorems")
(include-book "assoc")
(include-book "submap")
(include-book "extensionality")
(include-book "compatiblep")
(include-book "delete")
(include-book "update")
(include-book "from-alist")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-of-car-of-from-lists
  (equal (assoc (car keys) (from-lists keys vals))
         (if (consp keys)
             (cons (car keys) (car vals))
           nil))
  :enable from-lists)

(defrule assoc-of-car-of-from-lists-when-consp
  (implies (consp keys)
           (equal (assoc (car keys) (from-lists keys vals))
                  (cons (car keys) (car vals))))
  :by assoc-of-car-of-from-lists)

(defrule assoc-of-from-lists-under-iff
  (iff (assoc key (from-lists keys vals))
       (member-equal key keys))
  :induct t
  :enable (from-lists
           member-equal))

(defrule assoc-of-from-lists-when-not-member-equal-cheap
  (implies (not (member-equal key keys))
           (not (assoc key (from-lists keys vals))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))
