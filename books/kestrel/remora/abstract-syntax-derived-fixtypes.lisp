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
(include-book "kestrel/fty/string-string-map" :dir :system)

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

(fty::defresult shape-result
  :short "Fixtype of shapes and error."
  :ok shape
  :pred shape-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult shape-list-result
  :short "Fixtype of (i) lists of shapes and (ii) error."
  :ok shape-list
  :pred shape-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult atom-type-result
  :short "Fixtype of atom types and errors."
  :ok atom-type
  :pred atom-type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult atom-type-list-result
  :short "Fixtype of (i) lists of atom types and (ii) errors."
  :ok atom-type-list
  :pred atom-type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult array-type-result
  :short "Fixtype of array types and errors."
  :ok array-type
  :pred array-type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult array-type-list-result
  :short "Fixtype of (i) lists of array types and (ii) errors."
  :ok array-type-list
  :pred array-type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-dim-map
  :short "Fixtype of maps from strings to dimensions."
  :key-type string
  :val-type dim
  :pred string-dim-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-shape-map
  :short "Fixtype of maps from strings to shapes."
  :key-type string
  :val-type shape
  :pred string-shape-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-atomtype-map
  :short "Fixtype of maps from strings to atom types."
  :key-type string
  :val-type atom-type
  :pred string-atomtype-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-arraytype-map
  :short "Fixtype of maps from strings to array types."
  :key-type string
  :val-type array-type
  :pred string-arraytype-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stringstringmap-pair
  :short "Fixtype of pairs consisting of two maps from strings to strings."
  ((1st string-string-map)
   (2nd string-string-map))
  :pred stringstringmap-pairp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult stringstringmap-pair-result
  :short "Fixtype of (i) pairs consisting of two maps from strings to strings
          and (ii) errors."
  :ok stringstringmap-pair
  :pred stringstringmap-pair-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atomtype+shape
  :short "Fixtype of pairs consisting of an atom type and a shape."
  ((type atom-type)
   (shape shape))
  :pred atomtype+shape-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult atomtype+shape-result
  :short "Fixtype of (i) pairs consisting of an atom type and a shape
          and (ii) errors."
  :ok atomtype+shape
  :pred atomtype+shape-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist atomtype+shape-list
  :short "Fixtype lists of pairs consisting of an atom type and a shape."
  :elt-type atomtype+shape
  :true-listp t
  :elementp-of-nil nil
  :pred atomtype+shape-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult atomtype+shape-list-result
  :short "Fixtype of (i) lists of pairs consisting of an atom type and a shape
          and (ii) errors."
  :ok atomtype+shape-list
  :pred atomtype+shape-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod arraytypelist+arraytype
  :short "Fixtype of pairs consisting of
          a list of array types and an array type."
  ((types array-type-list)
   (type array-type))
  :pred arraytypelist+arraytype-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult arraytypelist+arraytype-result
  :short "Fixtype of
          (i) pairs consisting of a list of array types and an array type
          and (ii) errors."
  :ok arraytypelist+arraytype
  :pred arraytypelist+arraytype-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ispacevarlist+arraytype
  :short "Fixtype of pairs consisting of
          a list of type variables and an array type."
  ((vars ispace-var-list)
   (type array-type))
  :pred ispacevarlist+arraytype-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispacevarlist+arraytype-result
  :short "Fixtype of
          (i) pairs consisting of a list of type variables and an array type
          and (ii) errors."
  :ok ispacevarlist+arraytype
  :pred ispacevarlist+arraytype-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod typevarlist+arraytype
  :short "Fixtype of pairs consisting of
          a list of type variables and an array type."
  ((vars type-var-list)
   (type array-type))
  :pred typevarlist+arraytype-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult typevarlist+arraytype-result
  :short "Fixtype of
          (i) pairs consisting of a list of type variables and an array type
          and (ii) errors."
  :ok typevarlist+arraytype
  :pred typevarlist+arraytype-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stringdimmap+stringshapemap
  :short "Fixtype of pairs consisting of
          a map from strings to dimensions
          and a map from strings to shapes."
  ((dim-map string-dim-map)
   (shape-map string-shape-map))
  :pred stringdimmap+stringshapemap-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult stringdimmap+stringshapemap-result
  :short "Fixtype of
          (i) pairs consisting of
          a map from strings to dimensions
          and a map from strings to shapes
          and (ii) errors."
  :ok stringdimmap+stringshapemap
  :pred stringdimmap+stringshapemap-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod stringatomtypemap+stringarraytypemap
  :short "Fixtype of pairs consisting of
          a map from strings to atom types
          and a map from strings to array types."
  ((atom-map string-atomtype-map)
   (array-map string-arraytype-map))
  :pred stringatomtypemap+stringarraytypemap-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult stringatomtypemap+stringarraytypemap-result
  :short "Fixtype of
          (i) pairs consisting of
          a map from strings to atom types
          and a map from strings to array types
          and (ii) errors."
  :ok stringatomtypemap+stringarraytypemap
  :pred stringatomtypemap+stringarraytypemap-resultp
  :prepwork ((local (in-theory (enable strip-cars)))))
