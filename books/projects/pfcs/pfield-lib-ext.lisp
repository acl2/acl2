; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2024 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2024 Aleo Systems Inc. (https://www.aleo.org)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/lists/list-fix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prime fields library extensions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-append
  (equal (fe-listp (append x y) p)
         (and (fe-listp (true-list-fix x) p)
              (fe-listp y p)))
  :induct t
  :enable append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfield::nat-listp-when-fe-listp
  (implies (fe-listp x p)
           (nat-listp x))
  :induct t
  :enable nat-listp)

(defrule pfield::fe-listp-fw-to-nat-listp
  (implies (fe-listp x p)
           (nat-listp x))
  :rule-classes :forward-chaining
  :induct t
  :enable nat-listp)
