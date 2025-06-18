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

(include-book "values")
(include-book "dynamic-struct-environments")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ struct-operations
  :parents (dynamic-semantics)
  :short "Leo struct operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are operations to manipulate struct values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-struct-read ((circval valuep) (comp identifierp))
  :returns (result value-resultp)
  :short "Leo struct reading operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value must be a struct value, otherwise it is an error.
     The struct value must have a component with the given name,
     otherwise it is an error."))
  (b* (((unless (value-case circval :struct))
        (reserrf (list :not-struct-value (value-fix circval))))
       (valmap (value-struct->components circval))
       (name+val (omap::assoc (identifier-fix comp) valmap))
       ((unless (consp name+val))
        (reserrf (list :component-not-found (identifier-fix comp)))))
    (cdr name+val))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-struct-write ((circval valuep) (comp identifierp) (val valuep))
  :returns (result value-resultp)
  :short "Leo struct writing operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first value must be a struct value, otherwise it is an error.
     The struct value must have a component with the given name,
     otherwise it is an error.
     Furthermore, the type of the new component value
     must match the one of the value stored in the component,
     which is overwritten."))
  (b* (((unless (value-case circval :struct))
        (reserrf (list :not-struct-value (value-fix circval))))
       (valmap (value-struct->components circval))
       (name+oldval (omap::assoc (identifier-fix comp) valmap))
       ((unless (consp name+oldval))
        (reserrf (list :component-not-found (identifier-fix comp))))
       (oldval (cdr name+oldval))
       ((unless (equal (type-of-value val)
                       (type-of-value oldval)))
        (reserrf (list :component-type-mismatch
                       :name (identifier-fix comp)
                       :required (type-of-value oldval)
                       :supplied (type-of-value val))))
       (new-valmap (omap::update (identifier-fix comp) (value-fix val) valmap))
       (new-circval (change-value-struct circval :components new-valmap)))
    new-circval)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-struct-make ((name identifierp)
                         (valmap value-mapp)
                         (env struct-denvp))
  :returns (result value-resultp)
  :short "Leo struct construction operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the name (identifier) of a struct type
     and a value map (from identifiers to values),
     we return the corresponding value
     provided that the type map corresponding to the value map
     is the one associated to the struct type name
     in the dynamic struct environment.
     It is an error if it differs,
     or if the struct type is not in the environment."))
  (b* ((cinfo (get-struct-dinfo name env))
       ((unless cinfo)
        (reserrf (list :struct-not-found (identifier-fix name))))
       (tymap (type-map-of-value-map valmap))
       ((unless (equal tymap (struct-dinfo->components cinfo)))
        (reserrf (list :struct-mistype
                       :required (struct-dinfo->components cinfo)
                       :supplied tymap))))
    (make-value-struct :type name :components valmap))
  :hooks (:fix))
