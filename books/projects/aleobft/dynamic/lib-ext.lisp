; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "../static/lib-ext")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::intersect-mono-subset
  (implies (set::subset a b)
           (set::subset (set::intersect a c)
                        (set::intersect b c)))
  :enable set::expensive-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::emptyp-to-subset-of-nil
  (equal (set::emptyp a)
         (set::subset a nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::not-member-when-member-of-disjoint
  (implies (and (not (set::intersect a b))
                (set::in x a))
           (not (set::in x b)))
  :induct t
  :enable set::intersect)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled set::emptyp-of-intersect-of-subset-left
  (implies (and (set::subset a b)
                (set::emptyp (set::intersect b c)))
           (set::emptyp (set::intersect a c)))
  :enable (set::emptyp-to-subset-of-nil
           set::intersect-mono-subset
           set::expensive-rules)
  :disable set::emptyp-subset-2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule omap::lookup-of-update
  (equal (omap::lookup key (omap::update key1 val map))
         (if (equal key key1)
             val
           (omap::lookup key map)))
  :enable omap::lookup)
