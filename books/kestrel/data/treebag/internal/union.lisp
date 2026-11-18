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

;; The union of two bags takes the greater count of each element, so it is the
;; union of their maps which takes the greater value of a shared key. The
;; greater of two positive values is positive, so the union of two bags' maps
;; is a bag's map.

(treemap::defunion map-union
  :combine (lambda (key x y)
             (declare (ignore key))
             (acl2::max (nfix x) (nfix y)))
  :val-pred posp
  :val-set-pred set-all-posp
  :combine-hints (("Goal" :in-theory (enable nfix))))

;;;;;;;;;;;;;;;;;;;;

(defrule map-values-all-posp-of-map-union
  (implies (and (map-values-all-posp x)
                (map-values-all-posp y))
           (map-values-all-posp (map-union x y)))
  :enable map-values-all-posp)
