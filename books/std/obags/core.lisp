; Ordered Bags (Obags) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "OBAG")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ obags
  :parents (acl2::std)
  :short "A library of obags (ordered bags),
          i.e. finite bags (a.k.a. multisets)
          represented as non-strictly ordered lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is related to the library of "
    (xdoc::seetopic "set::std/osets" "osets (ordered sets)")
    ", i.e. finite sets represented as strictly ordered lists.
     The lists that represent obags are non-strictly ordered,
     i.e. they may have (contiguous) duplicate elements.
     Like osets capture (up to isomorphism)
     the mathematical notion of finite sets (over ACL2 objects),
     obags capture (up to isomorphism)
     the mathematical notion of finite bags (over ACL2 objects).
     In particular, obag equality is @(tsee equal).")
   (xdoc::p
    "Since obags are lists,
     in principle some list operations could be used on obags.
     However, this library provides versions of those list operations
     that have stronger guards (i.e. requiring obags instead of just lists)
     and that treat non-obags as the empty obag.
     That is, the obag operations respect a `non-bag convention'
     analogous to the "
    (xdoc::seetopic "set::primitives" "non-set convention")
    " respected by the oset operations;
     some of the latter are, analogously,
     versions of list operations (e.g. @(tsee head) for @(tsee car)),
     motivated by the fact that the list operations
     do not respect the non-set convention.")
   (xdoc::p
    "The obag operations
     @(tsee bagp),
     @(tsee bfix),
     @(tsee empty),
     @(tsee head),
     @(tsee tail), and
     @(tsee insert)
     are ``primitive'' in the same sense as the "
    (xdoc::seetopic "set::primitives" "oset primitives")
    ": their logical definitions depend on
     the underlying representation as lists,
     and provide replacements of list operations
     that respect the `non-bag convention'.
     The logical definitions of the other obag operations
     are in terms of the primitive operations,
     without reference to the underlying list representation.")
   (xdoc::p
    "There are different logically equivalent ways to define obag operations.
     The current definitions (as well as their names) are preliminary
     and could be improved if needed;
     these definitions favor ease of reasoning over efficiency of execution,
     but, as done in osets, @(tsee mbe) could be used to provide
     equivalent efficient definitions for execution.
     As it is often possible to reason about osets abstractly
     (i.e. without regard to their underlying list representation),
     it should be often possible to reason about obags abstractly
     (i.e. without regard to their underlying list representation),
     using the theorems provided by this library.
     The current theorems are preliminary
     and could be improved and extended if needed.
     The empty obag is @('nil'), like the empty list;
     there is no separate operation for the empty obag,
     as there is none for the empty oset.")
   (xdoc::p
    "Since osets are in the @('\"SET\"') package,
     it would be natural to use a @('\"BAG\') package for obags.
     However, a package with this name is already defined
     in @('[books]/coi/bags/package.lsp') (see below).
     So, we use @('\"OBAG\"') for obags
     to allow interoperability with this @('coi') bag library,
     in the sense that an application can use both @('coi') bags and obags.
     Perhaps the @('\"SET\"') package for osets
     could be renamed to @('\"OSET\"') at some point,
     for consistency.
     (A similar issue applies to "
    (xdoc::seetopic "omap::omaps" "the library of omaps")
    " and the @('[books]/coi/maps') library,
     which defines a @('\"MAP\"') package.)")

   (xdoc::p
    "This obag library is in the same @('SET') package as osets
     because obags are related to osets.
     Furthermore, a @('BAG') package already exists in @('[books]/coi/bags/').")
   (xdoc::p
    "This obag library could become a new @('std/obags') library,
     part of @(csee std), parallel to @(tsee set::std/osets).")
   (xdoc::p
    "Compared to using the built-in @(see acl2::lists) to represent bags,
     obags are closer to the mathematical notion of bags,
     at the cost of maintaining their non-strict order.
     These tradeoffs are analogous to the ones between using osets
     and using the built-in @(see acl2::lists) to represent sets.
     The bag library in @('[books]/coi/bags/')
     operates on possibly unordered lists."))
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bagp (x)
  :returns (yes/no booleanp)
  :short "Recognize obags."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to the definition of @(tsee setp),
     but each element of the list is checked to be
     either equal or smaller than the next.")
   (xdoc::p
    "Since a strictly ordered list is also non-strictly ordered,
     an oset is an obag."))
  (if (atom x)
      (null x)
    (or (null (cdr x))
        (and (consp (cdr x))
             (or (equal (car x) (cadr x))
                 (fast-<< (car x) (cadr x)))
             (bagp (cdr x)))))
  ///

  (defrule bagp-when-setp
    (implies (set::setp x)
             (bagp x))
    :rule-classes (:rewrite :forward-chaining)
    :enable setp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bfix ((x bagp))
  :returns (fixed-x bagp)
  :short "Fixing function for obags."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::sfix) for osets.")
  (mbe :logic (if (bagp x) x nil)
       :exec x)
  ///

  (defrule bfix-when-bagp
    (implies (bagp x)
             (equal (bfix x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define empty ((bag bagp))
  :returns (yes/no booleanp)
  :short "Check if an obag is empty."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::empty) for osets.")
  (null (bfix bag))
  ///

  (defrule bagp-when-not-empty
    (implies (not (empty bag))
             (bagp bag))
    :enable (bfix))

  (defrule bfix-when-empty
    (implies (empty x)
             (equal (bfix x) nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define head ((bag bagp))
  :guard (not (empty bag))
  :short "Smallest element of a non-empty obag."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee head) for osets.")
  (mbe :logic (car (bfix bag))
       :exec (car bag))
  :guard-hints (("Goal" :in-theory (enable bagp empty)))
  ///

  (defrule head-when-empty
    (implies (empty bag)
             (equal (head bag) nil))
    :rule-classes (:rewrite :type-prescription)
    :enable (empty bfix bagp))

  (defrule head-count
    (implies (not (empty bag))
             (< (acl2-count (head bag))
                (acl2-count bag)))
    :rule-classes (:rewrite :linear)
    :enable (empty bfix bagp))

  (defrule head-count-built-in
    (implies (not (empty bag))
             (o< (acl2-count (head bag))
                 (acl2-count bag)))
    :rule-classes :built-in-clause
    :enable (empty bfix bagp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tail ((bag bagp))
  :guard (not (empty bag))
  :returns (bag1 bagp :hints (("Goal" :in-theory (enable bfix bagp))))
  :short "Rest of a non-empty obag after removing
          an occurrence of its smallest element."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::tail) on osets.")
  (mbe :logic (cdr (bfix bag))
       :exec (cdr bag))
  :guard-hints (("Goal" :in-theory (enable bagp empty)))
  ///

  (defrule tail-when-empty
    (implies (empty bag)
             (equal (tail bag) nil))
    :rule-classes (:rewrite :type-prescription)
    :enable (empty bfix bagp))

  (defrule tail-count
    (implies (not (empty bag))
             (< (acl2-count (tail bag))
                (acl2-count bag)))
    :rule-classes (:rewrite :linear)
    :enable (empty bfix bagp))

  (defrule tail-count-built-in
    (implies (not (empty bag))
             (o< (acl2-count (tail bag))
                 (acl2-count bag)))
    :rule-classes :built-in-clause
    :enable (empty bfix bagp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define insert (x (bag bagp))
  :returns (bag1 bagp
                 :hints (("Goal"
                          :in-theory (enable bagp bfix empty head tail))))
  :short "Add (an occurrence of) a value to an obag."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::insert) on osets.")
  (cond ((empty bag) (list x))
        ((equal x (head bag)) (cons x bag))
        ((<< x (head bag)) (cons x bag))
        (t (cons (head bag) (insert x (tail bag))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete (x (bag bagp))
  :returns (bag1 bagp
                 :hints (("Goal"
                          :in-theory (enable bagp bfix empty head tail))))
  :short "Remove (an occurrence of) a value from an obag."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::delete) for osets.")
  (cond ((empty bag) nil)
        ((equal x (head bag)) (tail bag))
        (t (cons (head bag) (delete x (tail bag))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in (x (bag bagp))
  :returns (yes/no booleanp)
  :short "Check if a values occurs in an obag."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::in) on osets.")
  (and (not (empty bag))
       (or (equal x (head bag))
           (in x (tail bag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define occs (x (bag bagp))
  :returns (occs natp)
  :short "Number of occurrences of a value in an obag."
  (cond ((empty bag) 0)
        ((equal x (head bag)) (1+ (occs x (tail bag))))
        (t (occs x (tail bag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cardinality ((bag bagp))
  :returns (card natp)
  :short "Number of (occurrences of) elements in an obag."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::cardinality) on osets.")
  (if (empty bag)
      0
    (1+ (cardinality (tail bag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subbag ((sub bagp) (sup bagp))
  :returns (yes/no booleanp)
  :short "Check if (every occurrence of) every value in the first obag
          is also (an occurrence of) a value in the second obag."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::subset) for osets.")
  (or (empty sub)
      (and (in (head sub) sup)
           (subbag (tail sub)
                   (delete (head sub) sup)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define union ((bag1 bagp) (bag2 bagp))
  :returns (bag bagp)
  :short "Union of all (the occurrences of) all the elements of two obags."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::union) for osets.")
  (if (empty bag1)
      (bfix bag2)
    (insert (head bag1)
            (union (tail bag1) bag2)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define intersect ((bag1 bagp) (bag2 bagp))
  :returns (bag bagp)
  :short "Intersection of
          all (the occurrences of) all the elements of two obags."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee set::intersect) for osets.")
  (cond ((empty bag1) nil)
        ((in (head bag1) bag2)
         (insert (head bag1)
                 (intersect (tail bag1) bag2)))
        (t (intersect (tail bag1) bag2)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define difference ((bag1 bagp) (bag2 bagp))
  :returns (bag bagp)
  :short "Remove from the first obag
          all (the occurrences of) the elements of the second obag."
  (cond ((empty bag1) nil)
        ((in (head bag1) bag2)
         (difference (tail bag1) bag2))
        (t (insert (head bag1)
                   (difference (tail bag1) bag2))))
  :verify-guards :after-returns)
