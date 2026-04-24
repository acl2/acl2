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

(fty::defresult index-result
  :short "Fixtype of indices and errors."
  :ok index
  :pred index-resultp
  :prepwork ((local (in-theory (enable index-kind)))))

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

(fty::defomap string-kind-map
  :short "Fixtype of maps from strings to kinds."
  :key-type string
  :val-type kind
  :pred string-kind-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(fty::defomap string-index-map
  :short "Fixtype of maps from strings to indices."
  :key-type string
  :val-type index
  :pred string-index-mapp

  ///

  (defrule string-index-mapp-of-from-lists
    (implies (and (string-listp strings)
                  (index-listp indices)
                  (equal (len indices) (len strings)))
             (string-index-mapp (omap::from-lists strings indices)))
    :induct t
    :enable (omap::from-lists string-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-type-map
  :short "Fixtype of maps from strings to types."
  :key-type string
  :val-type type
  :pred string-type-mapp

  ///

  (defrule string-type-mapp-of-from-lists
    (implies (and (string-listp strings)
                  (type-listp types)
                  (equal (len types) (len strings)))
             (string-type-mapp (omap::from-lists strings types)))
    :induct t
    :enable (omap::from-lists string-listp)))

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

(fty::defprod type+shape
  :short "Fixtype of pairs consisting of a type and a shape."
  ((type type)
   (shape shape))
  :pred type+shape-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+shape-result
  :short "Fixtype of (i) pairs consisting of a type and a shape
          and (ii) errors."
  :ok type+shape
  :pred type+shape-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type+shape-list
  :short "Fixtype lists of pairs consisting of a type and a shape."
  :elt-type type+shape
  :true-listp t
  :elementp-of-nil nil
  :pred type+shape-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+shape-list-result
  :short "Fixtype of (i) lists of pairs consisting of a type and a shape
          and (ii) errors."
  :ok type+shape-list
  :pred type+shape-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(fty::defprod indexparamlist+type
  :short "Fixtype of pairs consisting of a list of index parameters and a type."
  ((params index-param-list)
   (type type))
  :pred indexparamlist+type-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult indexparamlist+type-result
  :short "Fixtype of
          (i) pairs consisting of a list of index parameters and a type
          and (ii) errors."
  :ok indexparamlist+type
  :pred indexparamlist+type-resultp
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
