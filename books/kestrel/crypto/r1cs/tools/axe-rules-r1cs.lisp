; Rules that use the R1CS axe-syntax functions
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; These rules call axe-syntaxp

(include-book "kestrel/axe/known-booleans" :dir :system)
(include-book "kestrel/typed-lists-light/bit-listp" :dir :system)
(include-book "../fe-listp")
(include-book "kestrel/axe/axe-syntax-functions" :dir :system) ;for syntactic-variablep
(include-book "axe-syntax-functions-r1cs")
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system)) ;for member-equal-of-cons

;move?
(acl2::add-known-boolean acl2::bit-listp)
(acl2::add-known-boolean pfield::fe-listp)

;for Axe only
(defthmd pfield::booleanp-of-fe-listp
  (booleanp (fe-listp elems prime)))

;; Restrict the search for VAR to the branch (namely, X) where we know it is.
(defthm acl2::memberp-of-append-with-key-first-half-axe
  (implies (and (acl2::axe-syntaxp (acl2::var-less-than-unquoted-keyp var key acl2::dag-array))
                (acl2::memberp var x))
           (acl2::memberp var (acl2::append-with-key key x y)))
  :hints (("Goal" :in-theory (enable acl2::append-with-key))))

;; Restrict the search for VAR to the branch (namely, Y) where we know it is.
(defthm acl2::memberp-of-append-with-key-second-half-axe
  (implies (and (acl2::axe-syntaxp (acl2::var-not-less-than-unquoted-keyp var key acl2::dag-array))
                (acl2::memberp var y))
           (acl2::memberp var (acl2::append-with-key key x y)))
  :hints (("Goal" :in-theory (enable acl2::append-with-key))))

;for axe, since member-equal is not a known boolean, todo: why isn't that ok (can't make the axe rule)?
(defthm pfield::fep-when-fe-listp-and-memberp
  (implies (and (acl2::axe-syntaxp (acl2::syntactic-variablep x dag-array)) ;for now, we only generate the fe-listp assumptions for vars
                (fe-listp free p)
                (acl2::memberp x free))
           (fep x p)))

;; Try this after most rules, since it requires searching through assumptions:
(table acl2::axe-rule-priorities-table 'pfield::fep-when-fe-listp-and-memberp 1)

(defun pfield::fe-listp-rules-axe ()
  '(pfield::fep-when-fe-listp-and-memberp
    acl2::memberp-of-append-with-key-first-half-axe
    acl2::memberp-of-append-with-key-second-half-axe
    acl2::memberp-of-cons
    acl2::equal-same))
