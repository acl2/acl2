; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "../set-defs")
(include-book "../cardinality-defs")
(include-book "../delete-defs")
(include-book "../min-max-defs")
(include-book "../iter-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(local (include-book "../set"))
(local (include-book "../cardinality"))
(local (include-book "../delete"))
(local (include-book "../min-max"))
(local (include-book "../iter"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iter-any-evenp ((iter iterp))
  (and (has-valuep iter)
       (or (evenp (nfix (value iter)))
           (iter-any-evenp (next iter))))
  :measure (nexts iter))

(defrule iter-any-evenp-when-iter-equiv-congruence
  (implies (iter-equiv iter0 iter1)
           (equal (iter-any-evenp iter0)
                  (iter-any-evenp iter1)))
  :rule-classes :congruence
  :induct (iter-any-evenp iter0)
  :enable iter-any-evenp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define any-evenp ((set setp))
  (mbe :logic (and (not (emptyp set))
                   (or (evenp (nfix (min set)))
                       (any-evenp (delete (min set) set))))
       :exec (iter-any-evenp (iter-min set)))
  :measure (cardinality set)
  :verify-guards nil ;; Verified below
  ///

  (defrule iter-any-evenp-becomes-any-evenp
    (equal (iter-any-evenp iter)
           (and (has-valuep iter)
                (or (evenp (nfix (value iter)))
                    (any-evenp (after iter)))))
    :induct t
    :enable (iter-any-evenp
             any-evenp))

  (verify-guards any-evenp))

(defrule any-evenp-when-equiv-congruence
  (implies (equiv set0 set1)
           (equal (any-evenp set0)
                  (any-evenp set1)))
  :rule-classes :congruence
  :induct (any-evenp set0)
  :enable any-evenp)

