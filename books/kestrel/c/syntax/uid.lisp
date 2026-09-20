; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "kestrel/fty/deftreemap" :dir :system)
(include-book "kestrel/fty/deftreeset" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/data/treeset/extensionality" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uid
  :parents (validation)
  :short "Fixtype of unique identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are numerical identifiers which are intended
     to be unique to a given variable, function, type name, etc.
     E.g., there may be many variables throughout a program
     with the name @('x'), but all such distinct variables
     will have distinct unique identifiers.")
   (xdoc::p
    "Unique identifiers are assigned during validation
     to aid subsequent analysis.
     By annotating identifiers with their unique alias,
     disambiguation of variables becomes trivial."))
  ((uid nat))
  :pred uidp
  :inline :all
  :layout :fulltree)

(defirrelevant irr-uid
  :parents (uid)
  :short "An irrelevant unique identifier."
  :type uidp
  :body (uid 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption uid-option
  uid
  :parents (uid)
  :short "Fixtype of optional unique identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unique identifiers are defined in @(tsee uid)."))
  :pred uid-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uid-pair
  :parents (uid)
  :short "Fixtype of pairs of unique identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unique identifiers are defined in @(tsee uid)."))
  ((first uid)
   (second uid))
  :pred uid-pairp
  :layout :fulltree
  ///

  (defrule car-of-uid-pair
    (equal (car (uid-pair first second))
           (uid-fix first))
    :enable uid-pair)

  (defrule cdr-of-uid-pair
    (equal (cdr (uid-pair first second))
           (uid-fix second))
    :enable uid-pair))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreeset uid-pair-set
  :parents (uid)
  :elt-type uid-pair
  :pred uid-pair-setp
  :fix uid-pair-sfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uid-pair-swap ((pair uid-pairp))
  :returns (new-pair uid-pairp)
  :parents (uid-pair)
  :short "Swap the components of a pair of unique identifiers."
  (b* (((uid-pair pair) pair))
    (make-uid-pair :first pair.second :second pair.first))

  ///

  (defrule uid-pair->first-of-uid-pair-swap
    (equal (uid-pair->first (uid-pair-swap pair))
           (uid-pair->second pair)))

  (defrule uid-pair->second-of-uid-pair-swap
    (equal (uid-pair->second (uid-pair-swap pair))
           (uid-pair->first pair)))

  (defrule uid-pair-swap-of-uid-pair
    (equal (uid-pair-swap (uid-pair first second))
           (uid-pair second first)))

  (defrule uid-pair-swap-of-uid-pair-swap
    (equal (uid-pair-swap (uid-pair-swap pair))
           (uid-pair-fix pair)))

  (defrule equal-of-uid-pair-swap
    (equal (equal (uid-pair-swap pair1) (uid-pair-fix pair2))
           (equal (uid-pair-fix pair1) (uid-pair-swap pair2)))))

;;;;;;;;;;;;;;;;;;;;

(define uid-pair-set-swap ((set uid-pair-setp))
  :returns (new-set uid-pair-setp)
  :parents (uid-pair-set)
  :short "Swap the components of every pair in a set of pairs
          of unique identifiers."
  (b* ((set (uid-pair-sfix set))
       ((when (treeset::emptyp set)) (treeset::empty))
       (min (treeset::min set)))
    (treeset::insert (uid-pair-swap min)
                     (uid-pair-set-swap (treeset::delete min set))))
  :measure (treeset::cardinality (uid-pair-sfix set))
  :verify-guards :after-returns

  ///

  (defrule in-of-uid-pair-set-swap
    (equal (treeset::in pair (uid-pair-set-swap set))
           (and (uid-pairp pair)
                (treeset::in (uid-pair-swap pair) (uid-pair-sfix set))))
    :induct t)

  (defrule uid-pair-set-swap-of-empty
    (equal (uid-pair-set-swap (treeset::empty))
           (treeset::empty)))

  (defrule insert-of-uid-pair-and-uid-pair-set-swap
    (equal (treeset::insert (uid-pair first second) (uid-pair-set-swap set))
           (uid-pair-set-swap (treeset::insert (uid-pair second first)
                                               (uid-pair-sfix set))))
    :enable treeset::extensionality-no-backchain-limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uid-triple
  :parents (uid)
  :short "Fixtype of triples of unique identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unique identifiers are defined in @(tsee uid)."))
  ((first uid)
   (second uid)
   (third uid))
  :pred uid-triplep
  :layout :fulltree
  ///

  (defrule car-of-uid-triple
    (equal (car (uid-triple first second third))
           (uid-fix first))
    :enable uid-triple)

  (defrule cdr-of-uid-triple
    (equal (cdr (uid-triple first second third))
           (cons (uid-fix second) (uid-fix third)))
    :enable uid-triple))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreeset uid-triple-set
  :parents (uid)
  :elt-type uid-triple
  :pred uid-triple-setp
  :fix uid-triple-sfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uid-triple-swap ((triple uid-triplep))
  :returns (new-triple uid-triplep)
  :parents (uid-triple)
  :short "Swap the first two components of a triple of unique identifiers."
  (b* (((uid-triple triple) triple))
    (make-uid-triple :first triple.second
                     :second triple.first
                     :third triple.third))

  ///

  (defrule uid-triple->first-of-uid-triple-swap
    (equal (uid-triple->first (uid-triple-swap triple))
           (uid-triple->second triple)))

  (defrule uid-triple->second-of-uid-triple-swap
    (equal (uid-triple->second (uid-triple-swap triple))
           (uid-triple->first triple)))

  (defrule uid-triple->third-of-uid-triple-swap
    (equal (uid-triple->third (uid-triple-swap triple))
           (uid-triple->third triple)))

  (defrule uid-triple-swap-of-uid-triple
    (equal (uid-triple-swap (uid-triple first second third))
           (uid-triple second first third)))

  (defrule uid-triple-swap-of-uid-triple-swap
    (equal (uid-triple-swap (uid-triple-swap triple))
           (uid-triple-fix triple)))

  (defrule equal-of-uid-triple-swap
    (equal (equal (uid-triple-swap triple1) (uid-triple-fix triple2))
           (equal (uid-triple-fix triple1) (uid-triple-swap triple2)))))

;;;;;;;;;;;;;;;;;;;;

(define uid-triple-set-swap ((set uid-triple-setp))
  :returns (new-set uid-triple-setp)
  :parents (uid-triple-set)
  :short "Swap the first two components of every triple
          in a set of triples of unique identifiers."
  (b* ((set (uid-triple-sfix set))
       ((when (treeset::emptyp set)) (treeset::empty))
       (min (treeset::min set)))
    (treeset::insert (uid-triple-swap min)
                     (uid-triple-set-swap (treeset::delete min set))))
  :measure (treeset::cardinality (uid-triple-sfix set))
  :verify-guards :after-returns

  ///

  (defrule in-of-uid-triple-set-swap
    (equal (treeset::in triple (uid-triple-set-swap set))
           (and (uid-triplep triple)
                (treeset::in (uid-triple-swap triple)
                             (uid-triple-sfix set))))
    :induct t)

  (defrule uid-triple-set-swap-of-empty
    (equal (uid-triple-set-swap (treeset::empty))
           (treeset::empty)))

  (defrule insert-of-uid-triple-and-uid-triple-set-swap
    (equal (treeset::insert (uid-triple first second third)
                            (uid-triple-set-swap set))
           (uid-triple-set-swap (treeset::insert (uid-triple second first third)
                                                 (uid-triple-sfix set))))
    :enable treeset::extensionality-no-backchain-limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap uid-pair-uid-map
  :parents (uid)
  :key-type uid-pair
  :val-type uid
  :pred uid-pair-uid-mapp
  :fix uid-pair-uid-mfix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uid-equal ((x uidp) (y uidp))
  (mbe :logic (uid-equiv x y)
       :exec (= (the unsigned-byte (uid->uid x))
                (the unsigned-byte (uid->uid y))))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable uidp uid->uid))))

(define uid-increment ((uid uidp))
  :returns (new-uid uidp)
  :parents (uid)
  :short "Create a fresh unique identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "This simply increments the numerical value of the unique identifier."))
  (b* (((uid uid) uid))
    (uid (1+ uid.uid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset uid-set
  :parents (uid)
  :short "Fixtype of sets of UIDs."
  :long
  (xdoc::topstring
   (xdoc::p
    "UIDs are defined in @(tsee uid)."))
  :elt-type uid
  :elementp-of-nil nil
  :pred uid-setp)
