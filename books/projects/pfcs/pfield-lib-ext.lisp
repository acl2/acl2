; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/list-fix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prime fields library extensions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfield::pow-0-equiv
  (implies (and (primep p)
                (integerp x))
           (equal (equal (pfield::pow x n p) 0)
                  (and (not (zp n))
                       (equal (mod x p) 0))))
  :induct t
  :enable pfield::pow)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-append
  (equal (fe-listp (append x y) p)
         (and (fe-listp (true-list-fix x) p)
              (fe-listp y p)))
  :induct t
  :enable append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-repeat
  (iff (fe-listp (repeat n x) p)
       (or (zp n) (fep x p)))
  :induct t
  :enable repeat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-last
  (implies (fe-listp x p)
           (fe-listp (last x) p))
  :induct t
  :enable last)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-take
  (implies (fe-listp x p)
           (iff (fe-listp (take n x) p)
                (or (fep nil p)
                    (<= (nfix n) (len x)))))
  :induct t
  :enable (take nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-butlast
  (implies (fe-listp x p)
           (fe-listp (butlast x n) p))
  :enable (butlast nfix fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fep-of-nth-when-fe-listp
  (implies (fe-listp x p)
           (iff (fep (nth n x) p)
                (< (nfix n) (len x))))
  :induct t
  :enable (nth nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-update-nth
  (implies (fe-listp x p)
           (iff (fe-listp (update-nth n y x) p)
                (and (fep y p)
                     (or (<= (nfix n) (len x))
                         (fep nil p)))))
  :induct t
  :enable (update-nth nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-rev
  (equal (pfield::fe-listp (rev x) prime)
         (pfield::fe-listp (true-list-fix x) prime))
  :induct t
  :enable rev)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfield::nat-listp-when-fe-listp
  (implies (fe-listp x p)
           (nat-listp x))
  :induct t
  :enable nat-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-fw-to-nat-listp
  (implies (fe-listp x p)
           (nat-listp x))
  :rule-classes :forward-chaining
  :induct t
  :enable nat-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist pfield::fe-list-listp (pfield::x p)
  :guard (primep p)
  (fe-listp pfield::x p)
  :true-listp t
  :elementp-of-nil t
  ///

  (defruled pfield::true-list-listp-when-fe-list-listp
    (implies (fe-list-listp x p)
             (true-list-listp x))
    :induct t
    :enable true-list-listp))
