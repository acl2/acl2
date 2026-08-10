; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "map-defs")
(include-book "size-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "update-defs")
(include-book "delete-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "kestrel/data/treeset/cardinality" :dir :system))
(local (include-book "kestrel/data/treeset/delete" :dir :system))
(local (include-book "kestrel/data/treeset/min-max" :dir :system))

(local (include-book "map"))
(local (include-book "keys"))
(local (include-book "size"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "update"))
(local (include-book "delete"))
(local (include-book "submap"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc inductions
  :parents (treemap)
  :short "Induction schemes for @(see treemap)s.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head-delete-induction (map)
  :parents (inductions)
  (or (emptyp map)
      (head-delete-induction (delete (head-key map) map)))
  :measure (size map)
  :verify-guards nil

  ///
  (in-theory (enable (:i head-delete-induction))))

;;;;;;;;;;;;;;;;;;;;

(define head-delete-bi-induction (x y)
  :parents (inductions)
  (or (emptyp x)
      (emptyp y)
      (head-delete-bi-induction (delete (head-key x) x)
                                (delete (head-key y) y)))
  :measure (size x)
  :verify-guards nil

  ///
  (in-theory (enable (:i head-delete-bi-induction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-delete-induction (map)
  :parents (inductions)
  (or (emptyp map)
      (min-delete-induction (delete (min-key map) map)))
  :measure (size map)
  :verify-guards nil

  ///
  (in-theory (enable (:i min-delete-induction))))

;;;;;;;;;;;;;;;;;;;;

(define max-delete-induction (map)
  :parents (inductions)
  (or (emptyp map)
      (max-delete-induction (delete (max-key map) map)))
  :measure (size map)
  :verify-guards nil

  ///
  (in-theory (enable (:i max-delete-induction))))
