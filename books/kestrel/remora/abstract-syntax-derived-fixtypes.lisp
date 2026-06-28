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

(fty::defresult dim-result
  :short "Fixtype of dimensions and errors."
  :ok dim
  :pred dim-resultp
  :prepwork ((local (in-theory (enable dim-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult dim-list-result
  :short "Fixtype of (i) lists of dimensions and (ii) errors."
  :ok dim-list
  :pred dim-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult shape-result
  :short "Fixtype of shapes and errors."
  :ok shape
  :pred shape-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult shape-list-result
  :short "Fixtype of (i) lists of shapes and (ii) errors."
  :ok shape-list
  :pred shape-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult shape-list-list-result
  :short "Fixtype of (i) lists of lists of shapes and (ii) errors."
  :ok shape-list-list
  :pred shape-list-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-result
  :short "Fixtype of ispaces and errors."
  :ok ispace
  :pred ispace-resultp
  :prepwork ((local (in-theory (enable ispace-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-list-result
  :short "Fixtype of (i) lists of ispaces and (ii) errors."
  :ok ispace-list
  :pred ispace-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-list-option-result
  :short "Fixtype of optional lists of ispaces and errors."
  :ok ispace-list-option
  :pred ispace-list-option-resultp
  :prepwork ((local (in-theory (enable ispace-list-option-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-var-result
  :short "Fixtype of ispace variables and errors."
  :ok ispace-var
  :pred ispace-var-resultp
  :prepwork ((local (in-theory (enable ispace-var-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-var-list-result
  :short "Fixtype of (i) lists of ispace variables and (ii) errors."
  :ok ispace-var-list
  :pred ispace-var-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispace-var-list-option-result
  :short "Fixtype of optional lists of ispace variables and errors."
  :ok ispace-var-list-option
  :pred ispace-var-list-option-resultp
  :prepwork ((local (in-theory (enable ispace-var-list-option-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult base-type-result
  :short "Fixtype of base types and errors."
  :ok base-type
  :pred base-type-resultp
  :prepwork ((local (in-theory (enable base-type-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-var-result
  :short "Fixtype of type variables and errors."
  :ok type-var
  :pred type-var-resultp
  :prepwork ((local (in-theory (enable type-var-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-var-list-result
  :short "Fixtype of (i) lists of type variables and (ii) errors."
  :ok type-var-list
  :pred type-var-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-var-list-option-result
  :short "Fixtype of optional lists of type variables and errors."
  :ok type-var-list-option
  :pred type-var-list-option-resultp
  :prepwork ((local (in-theory (enable type-var-list-option-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-result
  :short "Fixtype of types and errors."
  :ok type
  :pred type-resultp
  :prepwork ((local (in-theory (enable type-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-list-result
  :short "Fixtype of (i) lists of types and (ii) errors."
  :ok type-list
  :pred type-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-option-result
  :short "Fixtype of optional types and errors."
  :ok type-option
  :pred type-option-resultp
  :prepwork ((local (in-theory (enable typep type-optionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult type-list-option-result
  :short "Fixtype of optional lists of types and errors."
  :ok type-list-option
  :pred type-list-option-resultp
  :prepwork ((local (in-theory (enable type-list-option-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult var+type?-result
  :short "Fixtype of (i) variables with optional types and (ii) errors."
  :ok var+type?
  :pred var+type?-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult var+type?-list-result
  :short "Fixtype of
          (i) lists of variables with optional types and (ii) errors."
  :ok var+type?-list
  :pred var+type?-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult sign-option-result
  :short "Fixtype of optional signs and errors."
  :ok sign-option
  :pred sign-option-resultp
  :prepwork ((local (in-theory (enable signp sign-optionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult char-escape-result
  :short "Fixtype of character escapes and errors."
  :ok char-escape
  :pred char-escape-resultp
  :prepwork ((local (in-theory (enable char-escape-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult ascii-escape-result
  :short "Fixtype of ASCII escapes and errors."
  :ok ascii-escape
  :pred ascii-escape-resultp
  :prepwork ((local (in-theory (enable ascii-escape-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult caret-escape-result
  :short "Fixtype of caret escapes and errors."
  :ok caret-escape
  :pred caret-escape-resultp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult num-escape-result
  :short "Fixtype of numeric escapes and errors."
  :ok num-escape
  :pred num-escape-resultp
  :prepwork ((local (in-theory (enable num-escape-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult escape-result
  :short "Fixtype of escapes and errors."
  :ok escape
  :pred escape-resultp
  :prepwork ((local (in-theory (enable escape-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult char-lit-result
  :short "Fixtype of character literals and errors."
  :ok char-lit
  :pred char-lit-resultp
  :prepwork ((local (in-theory (enable char-lit-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult char-lit-list-result
  :short "Fixtype of lists of character literals and errors."
  :ok char-lit-list
  :pred char-lit-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult base-lit-result
  :short "Fixtype of base literals and errors."
  :ok base-lit
  :pred base-lit-resultp
  :prepwork ((local (in-theory (enable base-lit-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-result
  :short "Fixtype of expressions and errors."
  :ok expr
  :pred expr-resultp
  :prepwork ((local (in-theory (enable expr-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult expr-list-result
  :short "Fixtype of lists of expressions and errors."
  :ok expr-list
  :pred expr-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult atom-result
  :short "Fixtype of atoms and errors."
  :ok atom
  :pred atom-resultp
  :prepwork ((local (in-theory (enable atom-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult atom-list-result
  :short "Fixtype of lists of atoms and errors."
  :ok atom-list
  :pred atom-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult bind-result
  :short "Fixtype of bindings and errors."
  :ok bind
  :pred bind-resultp
  :prepwork ((local (in-theory (enable bind-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult bind-list-result
  :short "Fixtype of lists of bindings and errors."
  :ok bind-list
  :pred bind-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult prog-result
  :short "Fixtype of programs and errors."
  :ok prog
  :pred prog-resultp)

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

(fty::defomap string-type-map
  :short "Fixtype of maps from strings to types."
  :key-type string
  :val-type type
  :pred string-type-mapp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult string-type-map-result
  :short "Fixtype of (i) maps from strings to types and (ii) errors."
  :ok string-type-map
  :pred string-type-map-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-expr-map
  :short "Fixtype of maps from strings to expressions."
  :key-type string
  :val-type expr
  :pred string-expr-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap ispace-var-ispace-option-map
  :short "Fixtype of maps from ispace variables to optional ispaces."
  :key-type ispace-var
  :val-type ispace-option
  :pred ispace-var-ispace-option-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap type-var-type-option-map
  :short "Fixtype of maps from type variables to optional types."
  :key-type type-var
  :val-type type-option
  :pred type-var-type-option-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod string-type-map-pair
  :short "Fixtype of pairs consisting of two maps from strings to types."
  ((1st string-type-map)
   (2nd string-type-map))
  :pred string-type-map-pairp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult string-type-map-pair-result
  :short "Fixtype of (i) pairs consisting of two maps from strings to types
          and (ii) errors."
  :ok string-type-map-pair
  :pred string-type-map-pair-resultp)

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
  :short "Fixtype of lists of pairs consisting of a type and a shape."
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

(fty::defprod type+ispace
  :short "Fixtype of pairs consisting of a type and an ispace."
  ((type type)
   (ispace ispace))
  :pred type+ispace-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+ispace-result
  :short "Fixtype of (i) pairs consisting of a type and an ispace
          and (ii) errors."
  :ok type+ispace
  :pred type+ispace-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist type+ispace-list
  :short "Fixtype of lists of pairs consisting of a type and an ispace."
  :elt-type type+ispace
  :true-listp t
  :elementp-of-nil nil
  :pred type+ispace-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult type+ispace-list-result
  :short "Fixtype of (i) lists of pairs consisting of a type and an ispace
          and (ii) errors."
  :ok type+ispace-list
  :pred type+ispace-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod typelist+type
  :short "Fixtype of pairs consisting of
          a list of types and a type."
  ((types type-list)
   (type type))
  :pred typelist+type-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult typelist+type-result
  :short "Fixtype of
          (i) pairs consisting of a list of types and a type
          and (ii) errors."
  :ok typelist+type
  :pred typelist+type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ispacevarlist+type
  :short "Fixtype of pairs consisting of
          a list of ispace variables and a type."
  ((vars ispace-var-list)
   (type type))
  :pred ispacevarlist+type-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult ispacevarlist+type-result
  :short "Fixtype of
          (i) pairs consisting of a list of ispace variables and a type
          and (ii) errors."
  :ok ispacevarlist+type
  :pred ispacevarlist+type-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod typevarlist+type
  :short "Fixtype of pairs consisting of
          a list of type variables and a type."
  ((vars type-var-list)
   (type type))
  :pred typevarlist+type-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defresult typevarlist+type-result
  :short "Fixtype of
          (i) pairs consisting of a list of type variables and a type
          and (ii) errors."
  :ok typevarlist+type
  :pred typevarlist+type-resultp)

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
  :pred stringdimmap+stringshapemap-resultp)
