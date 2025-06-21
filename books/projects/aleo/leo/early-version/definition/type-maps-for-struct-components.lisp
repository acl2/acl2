; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "files")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-maps-for-struct-components
  :parents (static-semantics dynamic-semantics)
  :short "Maps from identifiers to types
          for struct type components."
  :long
  (xdoc::topstring
   (xdoc::p
    "In both the static and the dynamic semantics,
     environmental information includes
     the types of the components of struct types.
     We model this information via @(tsee type-map):
     a map represents the components of a struct type.
     These maps are also used in results of
     type checking of struct type declarations.
     Here we introduce functions
     to turn struct component delarations into type maps."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-type-map-with-compdecl ((decl compdeclp) (map type-mapp))
  :returns (new-map type-map-resultp)
  :short "Extend a type map with a struct component declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to build a @(tsee struct-sinfo)
     for (the component declarations of) a struct type declaration.")
   (xdoc::p
    "It is an error if the map already has a component with that name,
     because it means that there are duplicate component names."))
  (b* (((compdecl decl) decl)
       (name+type (omap::assoc decl.name (type-map-fix map)))
       ((when (consp name+type))
        (reserrf (list :duplicate-component decl.name))))
    (omap::update decl.name decl.type (type-map-fix map)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-type-map-with-compdecl-list ((decls compdecl-listp)
                                            (map type-mapp))
  :returns (new-map type-map-resultp)
  :short "Extend a type map with a list of struct component declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each component declaration."))
  (b* (((when (endp decls)) (type-map-fix map))
       ((okf map) (extend-type-map-with-compdecl (car decls) map)))
    (extend-type-map-with-compdecl-list (cdr decls) map))
  :hooks (:fix))
