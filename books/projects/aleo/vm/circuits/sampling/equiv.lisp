; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file defines R1CS equivalences.
; There are many things that can be done here, but we take the approach now
; of only adding what we need.
; 1. boolean ternary and field ternary yield different orders
;    of the addends.  The snarkvm circuit-generating code looks the same,
;    but the field ternary comes out as
;      (x)*(y + -z) = (w + -z)
;    and the boolean ternary comes out as
;      (x)(-z + y) = (-z + w).
;    So the very first equivalence predicate simply tries permuting
;    any linear combinations of length two.  No normalization function yet.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)

(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)

(include-book "std/strings/decimal" :dir :system)

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note, the equiv functions must be total (and binary) in order to use defequiv.

(acl2::define equiv-1-comm-2--lc (lc1 lc2)
  :returns (y/n booleanp)
  (or (equal lc1 lc2)
      (and (true-listp lc1)
           (true-listp lc2)
           (equal (len lc1) 2)
           (equal (len lc2) 2)
           (equal lc1 (reverse lc2)))))

(acl2::defequiv EQUIV-1-COMM-2--LC :hints (("Goal" :in-theory (enable EQUIV-1-COMM-2--LC))))
; => EQUIV-1-COMM-2--LC-IS-AN-EQUIVALENCE

(acl2::define equiv-1-comm-2--constraint (constraint1 constraint2)
  :returns (y/n booleanp)
  (or (equal constraint1 constraint2)
      (and (r1cs-constraintp constraint1)
           (r1cs-constraintp constraint2)
           (equiv-1-comm-2--lc (r1cs-constraint->a constraint1)
                               (r1cs-constraint->a constraint2))
           (equiv-1-comm-2--lc (r1cs-constraint->b constraint1)
                               (r1cs-constraint->b constraint2))
           (equiv-1-comm-2--lc (r1cs-constraint->c constraint1)
                               (r1cs-constraint->c constraint2)))))

(acl2::defequiv equiv-1-comm-2--constraint :hints (("Goal" :in-theory (enable EQUIV-1-COMM-2--constraint))))
; => EQUIV-1-COMM-2--CONSTRAINT-IS-AN-EQUIVALENCE

; Note:
; EQUIV-<equiv_version>-<change>--<component>
; where <change> = "comm-2" means try commuting linear combinations of two addends
; and <component> is "lc" (linear combination) or "constraint" or "cs" (constraint system).}

(acl2::define equiv-1-comm-2--cs (x y)
  :returns (y/n booleanp)
  (if (or (atom x) (atom y))
      (equal x y)
    (b* ((firstx (car x))
         (firsty (car y))
         (restx (cdr x))
         (resty (cdr y)))
      (and (equiv-1-comm-2--constraint firstx firsty)
           (equiv-1-comm-2--cs restx resty)))))

(acl2::defequiv equiv-1-comm-2--cs :hints (("Goal" :in-theory (enable EQUIV-1-COMM-2--cs))))
;  EQUIV-1-COMM-2--CS-IS-AN-EQUIVALENCE

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::define equiv (x y)
  (equiv-1-comm-2--cs x y))

(acl2::defequiv equiv :hints (("Goal" :in-theory (enable EQUIV))))
; EQUIV-IS-AN-EQUIVALENCE

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Define congruence

; We want to be able to rewrite
;   (r1cs-constraints-holdp cs1 v p)
; to
;   (r1cs-constraints-holdp cs2 v p)
; when we know (equiv cs1 cs2).

; Let's build up the holds.
; (Later, move this up to be with the various equiv functions)
; WIP
