; Ordered Maps (Omaps) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OMAP")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "core")
(include-book "with-fixing-theorems")
(include-book "assoc")
(include-book "submap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled compatiblep-of-tail-when-compatiblep
  (implies (compatiblep map0 map1)
           (compatiblep (tail map0) map1))
  :enable compatiblep)

(defrule compatiblep-of-tail-when-compatiblep-cheap
  (implies (compatiblep map0 map1)
           (compatiblep (tail map0) map1))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by compatiblep-of-tail-when-compatiblep)

(defruled compatiblep-of-arg1-and-tail-when-compatiblep
  (implies (compatiblep map0 map1)
           (compatiblep map0 (tail map1)))
  :induct t
  :enable compatiblep)

(defrule compatiblep-of-arg1-and-tail-when-compatiblep-cheap
  (implies (compatiblep map0 map1)
           (compatiblep map0 (tail map1)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by compatiblep-of-arg1-and-tail-when-compatiblep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled assoc-when-compatiblep-and-assoc
  (implies (and (compatiblep map0 map1)
                (assoc key map0)
                (assoc key map1))
           (equal (assoc key map0)
                  (assoc key map1)))
  :induct t
  :enable compatiblep
  :prep-lemmas
  ((defrule equal-of-assoc-and-cons
     (equal (equal (assoc key0 map)
                   (cons key1 val))
            (and (assoc key0 map)
                 (equal key0 key1)
                 (equal (cdr (assoc key0 map)) val)))
     :induct t
     :enable assoc)))

(defrule assoc-when-compatiblep-and-assoc-syntaxp
  (implies (and (compatiblep map0 map1)
                (syntaxp (<< map1 map0))
                (assoc key map0)
                (assoc key map1))
           (equal (assoc key map0)
                  (assoc key map1)))
  :by assoc-when-compatiblep-and-assoc)

(defrule equal-of-assoc-assoc-when-compatiblep
  (implies (compatiblep map0 map1)
           (equal (equal (assoc key map0) (assoc key map1))
                  (iff (assoc key map0) (assoc key map1))))
  :use assoc-when-compatiblep-and-assoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule compatiblep-when-submap
  (implies (submap sub sup)
           (compatiblep sub sup))
  :induct t
  :enable (compatiblep
           submap))

(defrule reflexivity-of-compatiblep
  (compatiblep map map))

(defruled symmetry-of-compatiblep-weak
  (implies (compatiblep map1 map0)
           (compatiblep map0 map1))
  :induct (compatiblep map0 map1)
  :enable compatiblep)

(defrule symmetry-of-compatiblep
  (equal (compatiblep map1 map0)
         (compatiblep map0 map1))
  :use (symmetry-of-compatiblep-weak
        (:instance symmetry-of-compatiblep-weak
                   (map0 map1)
                   (map1 map0))))

(defrule compatiblep-when-submap-2
  (implies (submap sub sup)
           (compatiblep sup sub)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule compatiblep-weaken-arg2
  (implies (and (compatiblep map sup)
                (submap sub sup))
           (compatiblep map sub))
  :induct (compatiblep map sub)
  :enable (compatiblep
           assoc-when-submap-and-assoc))

(defrule compatiblep-weaken-arg1
  (implies (and (compatiblep sup map)
                (submap sub sup))
           (compatiblep sub map)))
