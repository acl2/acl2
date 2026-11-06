; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "kestrel/data/treemap/defunion" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The sum of two bags adds the occurrences of each element, so it is the
;; union of their maps which adds the values of a shared key. A sum of
;; positive values is positive, so the union of two bags' maps is a bag's map.

(treemap::defunion map-sum
  :combine (lambda (key x y)
             (declare (ignore key))
             (+ (nfix x) (nfix y)))
  :val-pred posp
  :val-set-pred set-all-posp
  :combine-hints (("Goal" :in-theory (enable nfix))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-posp-of-map-sum
  (implies (and (map-values-all-posp x)
                (map-values-all-posp y))
           (map-values-all-posp (map-sum x y)))
  :enable map-values-all-posp)
