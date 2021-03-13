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

(include-book "kestrel/axe/axe-syntax" :dir :system)
(include-book "kestrel/axe/known-booleans" :dir :system)
(include-book "../fe-listp")
(include-book "kestrel/axe/axe-syntax-functions" :dir :system) ;for syntactic-variablep
(include-book "axe-syntax-functions-r1cs")
(include-book "kestrel/lists-light/append-with-key" :dir :system)
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system)) ;for member-equal-of-cons

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

(defun gen-fe-listp-assumption (vars prime)
  (declare (xargs :guard (and (symbol-listp vars)
                              (consp vars))))
  `(fe-listp ,(acl2::make-append-with-key-nest vars) ,prime))

;; test: (gen-fe-listp-assumption '(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))

;for acl2, not Axe
(defthm pfield::fep-when-fe-listp-and-member-equal
  (implies (and (syntaxp (acl2::variablep x)) ;for now, we only generate the fe-listp assumptions for vars
                (fe-listp free p)
                (acl2::member-equal x free))
           (fep x p)))

(acl2::add-known-boolean pfield::fe-listp)

;for Axe
(defthm pfield::booleanp-of-fe-listp
  (booleanp (fe-listp elems prime)))

(defun fe-listp-rules ()
  '(pfield::fep-when-fe-listp-and-memberp
    acl2::memberp-of-append-with-key-first-half-axe
    acl2::memberp-of-append-with-key-second-half-axe
    acl2::memberp-of-cons
    acl2::equal-same))

;move:
;test:
(thm
 (implies (fe-listp
           (acl2::append-with-key
            'x5
            (acl2::append-with-key 'x2
                             (acl2::append-with-key 'x10
                                              (cons x1 nil)
                                              (cons x10 nil))
                             (acl2::append-with-key 'x3
                                              (cons x2 nil)
                                              (acl2::append-with-key 'x4
                                                               (cons x3 nil)
                                                               (cons x4 nil))))
            (acl2::append-with-key 'x7
                             (acl2::append-with-key 'x6
                                              (cons x5 nil)
                                              (cons x6 nil))
                             (acl2::append-with-key 'x8
                                              (cons x7 nil)
                                              (acl2::append-with-key 'x9
                                                               (cons x8 nil)
                                                               (cons x9 nil)))))
           prime)
          (and (fep x1 prime)
               (fep x2 prime)
               (fep x3 prime)
               (fep x4 prime)
               (fep x5 prime)
               (fep x6 prime)
               (fep x7 prime)
               (fep x8 prime)
               (fep x9 prime)
               (fep x10 prime)))
 :hints (("Goal" :in-theory (e/d (member-equal) (ACL2::MEMBER-EQUAL-BECOMES-MEMBERP)))))
