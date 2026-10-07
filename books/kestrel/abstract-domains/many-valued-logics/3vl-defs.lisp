; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "3vl"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (3p
          3fix
          3equiv
          3info<
          3info<=
          binary-3join$inline
          3join
          3not
          binary-3and$inline
          3and
          binary-3or$inline
          3or
          binary-3xor$inline
          3xor
          3implies
          binary-3iff$inline
          3iff
          3possibly
          3definitely
          3truth<
          3truth<=
          binary-3and$
          3and$
          binary-3or$
          3or$
          3implies$
          ))

(defequiv 3equiv)