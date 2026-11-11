; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "step"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (stepp
          irr-step
          step-fix
          step-equiv
          step->to
          step->label
          step
          step-listp
          step-list-fix
          step-list-equiv
          steps-end
          ))

(defequiv step-equiv)
(defequiv step-list-equiv)
