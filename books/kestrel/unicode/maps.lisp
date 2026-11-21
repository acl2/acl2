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
    (ubyte8p (combining-class-map-lookup cp map))
    :rule-classes ((:type-prescription
                    :corollary (natp (combining-class-map-lookup cp map))
                    :hints (("Goal" :in-theory (enable ubyte8p
                                                       unsigned-byte-p
                                                       natp)))))
    :disable combining-class-map-lookup))

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

(fty::deftreemap prototype-map
  :short "Fixtype of maps from code points to sequences of scalar values,
          for the prototypes of confusable characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the data of the file @('confusables.txt')
     of Unicode Security Mechanisms [UTS #39, Section 4]:
     the file gives to some characters a prototype,
     which is a sequence of one or more characters
     that stands for what the character looks like.
     The default value, for a code point that is not in the map,
     is the code point itself."))
  :key-type code-point
  :val-type scalar-value-list
  :pred prototype-mapp)

;;;;;;;;;;;;;;;;;;;;

(define prototype-map-lookup ((cp code-point-p)
                              (map prototype-mapp))
  :returns (prototype scalar-value-listp)
  :short "Look up a code point in a map of prototypes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the code point is not in the map.
     The sequences in the maps of the generated tables are not empty,
     so there @('nil') means that the code point is not in the map."))
  (b* (((mv in? prototype) (treemap::lookup? (code-point-fix cp)
                                             (prototype-map-fix map))))
    (if in? prototype nil))
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
     the classes of the embeddings
     (@('LRE'), Left-to-Right Embedding,
     and @('RLE'), Right-to-Left Embedding),
     of the overrides
     (@('LRO'), Left-to-Right Override,
     and @('RLO'), Right-to-Left Override),
     of the character that ends them
     (@('PDF'), Pop Directional Format),
     of the isolates
     (@('LRI'), Left-to-Right Isolate,
     @('RLI'), Right-to-Left Isolate,
     and @('FSI'), First Strong Isolate),
     and of the character that ends those
     (@('PDI'), Pop Directional Isolate)."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define digit-value-p (x)
  :returns (yes/no booleanp)
  :short "Recognize the values of decimal digits:
          the natural numbers from 0 to 9."
  (and (natp x)
       (<= x 9))

  ///

  (defrule natp-when-digit-value-p
    (implies (digit-value-p x)
             (natp x))
    :rule-classes :compound-recognizer)

  (defrule digit-value-p-upper-bound
    (implies (digit-value-p x)
             (<= x 9))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;

(std::deffixer digit-value-fix
  :short "Fixer for @(tsee digit-value-p)."
  :pred digit-value-p
  :body-fix 0)

;;;;;;;;;;;;;;;;;;;;

(defsection digit-value
  :short "Fixtype of the values of decimal digits."
  (fty::deffixtype digit-value
    :pred digit-value-p
    :fix digit-value-fix
    :equiv digit-value-equiv
    :define t))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption digit-value-option
  digit-value
  :short "Fixtype of optional values of decimal digits."
  :pred digit-value-option-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap decimal-digit-map
  :short "Fixtype of maps from code points to values of decimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the table of the code points
     whose @('Numeric_Type') property is @('Decimal'),
     with their values [UAX #44, Table 9].
     A code point that is not in the map is not a decimal digit."))
  :key-type code-point
  :val-type digit-value
  :pred decimal-digit-mapp)

;;;;;;;;;;;;;;;;;;;;

(define decimal-digit-map-lookup ((cp code-point-p)
                                  (map decimal-digit-mapp))
  :returns (value? digit-value-option-p)
  :short "Look up a code point in a map of values of decimal digits."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the code point is not in the map."))
  (b* (((mv in? value) (treemap::lookup? (code-point-fix cp)
                                         (decimal-digit-map-fix map))))
    (if in? value nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bidi-bracket
  :short "Fixtype of what the Unicode Character Database says
          about a paired bracket."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the value of two properties together [UAX #9, Section 3.1.3]:
     @('Bidi_Paired_Bracket_Type'),
     which says whether the bracket is an opening one (@('Open'))
     or a closing one (@('Close')),
     and @('Bidi_Paired_Bracket'),
     which is the other bracket of the pair,
     here called the partner.
     For example, U+0028 LEFT PARENTHESIS is an opening bracket
     whose partner is U+0029 RIGHT PARENTHESIS.")
   (xdoc::p
    "A code point that is not a paired bracket has
     the @('Bidi_Paired_Bracket_Type') @('None')
     and no @('Bidi_Paired_Bracket');
     see @(tsee bidi-bracket-option)."))
  (:open ((partner code-point)))
  (:close ((partner code-point)))
  :pred bidi-bracket-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption bidi-bracket-option
  bidi-bracket
  :short "Fixtype of optional values of the paired bracket properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value @('nil') is for a code point that is not a paired bracket."))
  :pred bidi-bracket-option-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap bidi-bracket-map
  :short "Fixtype of maps from code points
          to values of the paired bracket properties."
  :key-type code-point
  :val-type bidi-bracket
  :pred bidi-bracket-mapp)

;;;;;;;;;;;;;;;;;;;;

(define bidi-bracket-map-lookup ((cp code-point-p)
                                 (map bidi-bracket-mapp))
  :returns (bracket? bidi-bracket-option-p)
  :short "Look up a code point in a map of paired bracket properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the code point is not in the map."))
  (b* (((mv in? bracket) (treemap::lookup? (code-point-fix cp)
                                           (bidi-bracket-map-fix map))))
    (if in? bracket nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption code-point-option
  code-point
  :short "Fixtype of optional code points."
  :pred code-point-option-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap mirroring-map
  :short "Fixtype of maps from code points to code points,
          for the @('Bidi_Mirroring_Glyph') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the table of the code points
     that have a @('Bidi_Mirroring_Glyph') [UAX #9, Section 7]:
     the code point of a character
     whose glyph is the mirror image of the glyph of the first.
     For example, U+003C LESS-THAN SIGN is mapped
     to U+003E GREATER-THAN SIGN."))
  :key-type code-point
  :val-type code-point
  :pred mirroring-mapp)

;;;;;;;;;;;;;;;;;;;;

(define mirroring-map-lookup ((cp code-point-p)
                              (map mirroring-mapp))
  :returns (mirror? code-point-option-p)
  :short "Look up a code point in a map of mirroring glyphs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the code point is not in the map."))
  (b* (((mv in? mirror) (treemap::lookup? (code-point-fix cp)
                                          (mirroring-map-fix map))))
    (if in? mirror nil))
  :hooks (:fix))
