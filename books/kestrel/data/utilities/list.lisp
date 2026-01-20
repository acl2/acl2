; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "std/lists/equiv" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "std/util/defredundant" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-fix ((list true-listp))
  (mbe :logic (true-list-fix list)
       :exec (the list list))
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (list-equiv))

(define list-equal
  ((x true-listp)
   (y true-listp))
  (declare (xargs :split-types t)
           (type list x y))
  :returns (yes/no booleanp :rule-classes (:rewrite :type-prescription))
  (mbe :logic (list-equiv x y)
       :exec (if (endp x)
                 (endp y)
               (and (not (endp y))
                    (equal (first (the cons x)) (first (the cons y)))
                    (list-equal (rest (the cons x)) (rest (the cons y))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable endp
                                           list-equal))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t list-equal)))

(defequiv list-equiv
  :package :equiv)
