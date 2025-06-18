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

(include-book "type-maps-for-struct-components")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-struct-environments
  :parents (dynamic-environments)
  :short "Dynamic environments for struct types in Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Leo, struct types are referenced by name.
     Thus, the dynamic semantics of Leo constructs
     that reference struct types by name
     must be defined with respect to information for the struct type names.
     We capture that via the notion of dynamic environment for struct types,
     which associates dynamic information for struct types
     to struct type names."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod struct-dinfo
  :short "Fixtype of dynamic information about struct types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this only consists of information about the components,
     organized as a type map from component names to their types.
     The finite map structure is adequate
     because components have unique names.")
   (xdoc::p
    "This dynamic information for struct types may be extended
     with information about associated constants and functions."))
  ((components type-map))
  :tag :struct-dinfo
  :pred struct-dinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption struct-dinfo-option
  struct-dinfo
  :short "Fixtype of optional dynamic information for struct types."
  :pred struct-dinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap struct-denv
  :short "Fixtype of dynamic environments for struct types."
  :long
  (xdoc::topstring
   (xdoc::p
    "A dynamic environment for struct types is a finite map
     from identifiers to dynamic information for struct types.
     Each pair in the map corresponds to a struct type:
     the key is the name and the value is the information."))
  :key-type identifier
  :val-type struct-dinfo
  :pred struct-denvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum struct-denv-option
  :short "Fixtype of optional dynamic environments for struct types."
  (:some ((get struct-denv)))
  (:none ())
  :pred struct-denv-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-struct-dinfo ((name identifierp) (env struct-denvp))
  :returns (info? struct-dinfo-optionp
                  :hints (("Goal" :in-theory (enable struct-dinfo-optionp))))
  :short "Get the information for a struct type in a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no struct type with that name in the environment,
     we return @('nil') to indicate an error."))
  (cdr (omap::assoc (identifier-fix name) (struct-denv-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-struct-dinfo ((name identifierp)
                           (info struct-dinfop)
                           (env struct-denvp))
  :returns (new-env struct-denv-optionp)
  :short "Add information for a struct type to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return `none' if
     there is already a struct type with the same nme in the environment."))
  (b* ((name (identifier-fix name))
       (info (struct-dinfo-fix info))
       (env (struct-denv-fix env))
       ((when (consp (omap::assoc name env))) (struct-denv-option-none))
       (new-env (omap::update name info env)))
    (struct-denv-option-some new-env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-struct-denv ()
  :returns (env struct-denvp)
  :short "Initial dynamic struct environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is empty."))
  nil)
