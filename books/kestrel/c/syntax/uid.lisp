; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/utilities/nfix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uid
  :parents (validation-information)
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

(fty::defomap uid-uid-map
  :parents (uid)
  :key-type uid
  :val-type uid
  :pred uid-uid-mapp
  :fix uid-uid-mfix)

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
