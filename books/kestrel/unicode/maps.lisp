; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "code-points")

(include-book "kestrel/fty/deftreemap" :dir :system)
(include-book "kestrel/fty/ubyte8" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ maps
  :parents (tables)
  :short "Maps from code points to values of properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "The properties of the Unicode Character Database that are not binary
     assign a value to each code point.
     Most code points have the default value of the property,
     so we represent such a property as a finite map
     from the code points that have other values to their values.
     The maps are @(see treemap::treemap)s,
     in which a lookup takes logarithmic time;
     the fixtypes are introduced with @(tsee fty::deftreemap).")
   (xdoc::p
    "Here we introduce the fixtypes of the maps
     that the generated tables have.
     The operations on them are the ones of the @(see treemap::treemap)s."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap combining-class-map
  :short "Fixtype of maps from code points to canonical combining classes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The values of the @('Canonical_Combining_Class') property
     are numbers from 0 to 254 [UAX #44, Table 15],
     which we represent as unsigned bytes.
     The default value is 0."))
  :key-type code-point
  :val-type ubyte8
  :pred combining-class-mapp)

;;;;;;;;;;;;;;;;;;;;

(define combining-class-map-lookup ((cp code-point-p)
                                    (map combining-class-mapp))
  :returns (ccc ubyte8p)
  :short "Look up a code point in a map of canonical combining classes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is 0 if the code point is not in the map."))
  (b* (((mv in? ccc) (treemap::lookup? (code-point-fix cp)
                                       (combining-class-map-fix map))))
    (if in? ccc 0))
  :hooks (:fix)

  ///

  (defrule natp-of-combining-class-map-lookup
    (natp (combining-class-map-lookup cp map))
    :rule-classes :type-prescription
    :use ubyte8p-of-combining-class-map-lookup
    :enable (ubyte8p unsigned-byte-p natp)
    :disable (combining-class-map-lookup
              ubyte8p-of-combining-class-map-lookup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap decomposition-map
  :short "Fixtype of maps from code points to sequences of scalar values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the @('Decomposition_Mapping') property,
     and of the decompositions derived from it.
     The default value, for a code point that is not in the map,
     is the code point itself."))
  :key-type code-point
  :val-type scalar-value-list
  :pred decomposition-mapp)

;;;;;;;;;;;;;;;;;;;;

(define decomposition-map-lookup ((cp code-point-p)
                                  (map decomposition-mapp))
  :returns (mapping scalar-value-listp)
  :short "Look up a code point in a map of decompositions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the code point is not in the map.
     The sequences in the maps of the generated tables are not empty,
     so there @('nil') means that the code point is not in the map."))
  (b* (((mv in? mapping) (treemap::lookup? (code-point-fix cp)
                                           (decomposition-map-fix map))))
    (if in? mapping nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bidi-formatting-class
  :short "Fixtype of the bidirectional classes
          of the explicit directional formatting characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are nine of the values of the @('Bidi_Class') property
     [UAX #9, Table 4]:
     the classes of the embeddings (@('LRE') and @('RLE')),
     of the overrides (@('LRO') and @('RLO')),
     of the character that ends them (@('PDF')),
     of the isolates (@('LRI'), @('RLI') and @('FSI')),
     and of the character that ends those (@('PDI'))."))
  (:lre ())
  (:rle ())
  (:lro ())
  (:rlo ())
  (:pdf ())
  (:lri ())
  (:rli ())
  (:fsi ())
  (:pdi ())
  :pred bidi-formatting-class-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption bidi-formatting-class-option
  bidi-formatting-class
  :short "Fixtype of optional bidirectional classes
          of the explicit directional formatting characters."
  :pred bidi-formatting-class-option-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap bidi-formatting-class-map
  :short "Fixtype of maps from code points to bidirectional classes
          of the explicit directional formatting characters."
  :key-type code-point
  :val-type bidi-formatting-class
  :pred bidi-formatting-class-mapp)

;;;;;;;;;;;;;;;;;;;;

(define bidi-formatting-class-map-lookup ((cp code-point-p)
                                          (map bidi-formatting-class-mapp))
  :returns (class? bidi-formatting-class-option-p)
  :short "Look up a code point in a map of bidirectional classes
          of the explicit directional formatting characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the code point is not in the map."))
  (b* (((mv in? class) (treemap::lookup? (code-point-fix cp)
                                         (bidi-formatting-class-map-fix map))))
    (if in? class nil))
  :hooks (:fix))
