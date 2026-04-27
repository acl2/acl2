; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "insert-defs")
(include-book "delete-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "set"))
(local (include-book "cardinality"))
(local (include-book "in"))
(local (include-book "min-max"))
(local (include-book "insert"))
(local (include-book "delete"))
(local (include-book "subset"))
(local (include-book "extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc inductions
  :parents (treeset)
  :short "Induction schemes for @(see treeset)s.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: is this a good destructor elimination rule?
(defrule head-tail-elim
  (implies (not (emptyp set))
           (equal (insert (head set) (tail set))
                  set))
  :rule-classes :elim
  :enable extensionality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head-tail-induction (set)
  :parents (inductions)
  (or (emptyp set)
      (head-tail-induction (delete (head set) set)))
  :measure (cardinality set)
  :verify-guards nil

  ///
  (in-theory (enable (:i head-tail-induction))))

;;;;;;;;;;;;;;;;;;;;

(define head-tail-bi-induction (x y)
  (or (emptyp x)
      (emptyp y)
      (head-tail-bi-induction (delete (head x) x)
                              (delete (head y) y)))
  :measure (cardinality x)
  :verify-guards nil

  ///
  (in-theory (enable (:i head-tail-bi-induction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define min-delete-induction (set)
  :parents (inductions)
  (or (emptyp set)
      (min-delete-induction (delete (min set) set)))
  :measure (cardinality set)
  :verify-guards nil

  ///
  (in-theory (enable (:i min-delete-induction))))

;;;;;;;;;;;;;;;;;;;;

(define max-delete-induction (set)
  :parents (inductions)
  (or (emptyp set)
      (max-delete-induction (delete (max set) set)))
  :measure (cardinality set)
  :verify-guards nil

  ///
  (in-theory (enable (:i max-delete-induction))))
