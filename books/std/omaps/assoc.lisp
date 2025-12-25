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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-of-head-key
  (equal (assoc (mv-nth 0 (head map)) map)
         (if (emptyp map)
             nil
           (cons (mv-nth 0 (head map))
                 (mv-nth 1 (head map)))))
  :enable assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-when-assoc-of-tail
  (implies (assoc key (tail map))
           (equal (assoc key map)
                  (assoc key (tail map))))
  :by assoc-of-tail-when-assoc-of-tail)

(theory-invariant (incompatible! (:rewrite assoc-of-tail-when-assoc-of-tail)
                                 (:rewrite assoc-when-assoc-of-tail)))

(defrule assoc-when-assoc-of-tail-cheap
  (implies (assoc key (tail map))
           (equal (assoc key map)
                  (assoc key (tail map))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by assoc-when-assoc-of-tail)

(theory-invariant (incompatible! (:rewrite assoc-of-tail-when-assoc-of-tail)
                                 (:rewrite assoc-when-assoc-of-tail-cheap)))
