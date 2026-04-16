; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/defresult" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-derived-fixtypes
  :parents (abstract-syntax)
  :short "Fixtypes derived from the ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are fixtypes that, in a language with polymorphic types,
     could be constructed on the fly from existing types.
     With ACL2 fixtypes, we need to create explicit instances,
     which we do here.
     Simple derived fixtypes, like lists,
     are defined near the fixtypes they are derived from,
     in @(see abstract-syntax-trees);
     here we define fixtypes that are slightly less straightforward,
     e.g. via @(tsee fty::defresult)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult sort-result
  :short "Fixtype of sorts and errors."
  :ok sort
  :pred sort-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult sort-list-result
  :short "Fixtype of (i) lists of sorts and (ii) errors."
  :ok sort-list
  :pred sort-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult kind-result
  :short "Fixtype of kinds and errors."
  :ok kind
  :pred kind-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult kind-list-result
  :short "Fixtype of (i) lists of kinds and (ii) errors."
  :ok kind-list
  :pred kind-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult index-result
  :short "Fixtype of indices and errors."
  :ok index
  :pred index-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult index-list-result
  :short "Fixtype of (i) lists of kindices and (ii) errors."
  :ok index-list
  :pred index-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-result
  :short "Fixtype of types and errors."
  :ok type
  :pred type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-list-result
  :short "Fixtype of (i) lists of types and (ii) errors."
  :ok type-list
  :pred type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod type+index
  :short "Fixtype of pairs consisting of a type and an index."
  ((type type)
   (index index))
  :pred type+index-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+index-result
  :short "Fixtype of (i) pairs consisting of a type and an index
          and (ii) errors."
  :ok type+index
  :pred type+index-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type+index-list
  :short "Fixtype lists of pairs consisting of a type and an index."
  :elt-type type+index
  :true-listp t
  :elementp-of-nil nil
  :pred type+index-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+index-list-result
  :short "Fixtype of (i) lists of pairs consisting of a type and an index
          and (ii) errors."
  :ok type+index-list
  :pred type+index-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod typelist+type
  :short "Fixtype of pairs consisting of a list of types and a type."
  ((types type-list)
   (type type))
  :pred typelist+type-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult typelist+type-result
  :short "Fixtype of (i) pairs consisting of a list of types and a type
          and (ii) errors."
  :ok typelist+type
  :pred typelist+type-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod kindedvarlist+type
  :short "Fixtype of pairs consisting of a list of kinded variables and a type."
  ((vars kinded-var-list)
   (type type))
  :pred kindedvarlist+type-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult kindedvarlist+type-result
  :short "Fixtype of
          (i) pairs consisting of a list of kinded variables and a type
          and (ii) errors."
  :ok kindedvarlist+type
  :pred kindedvarlist+type-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))
