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

(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::not-difference-when-subset
  (implies (set::subset a b)
           (not (set::difference a b)))
  :use (:instance set::subset-difference (x a) (y b))
  :disable set::subset-difference
  :enable set::emptyp)
