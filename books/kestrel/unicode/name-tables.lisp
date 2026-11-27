; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "ranges")
(include-book "maps")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ name-tables
  :parents (tables)
  :short "Tables for the names of the characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Name') property gives a name to each character,
     such as @('LATIN SMALL LETTER A') to U+0061
     [Unicode, Section 4.8].
     A name is a string of capital letters, digits, spaces and hyphens;
     we represent it as an ACL2 string.
     A code point that has no name,
     such as a control code or an unassigned code point,
     has the empty string as the value of the property.")
   (xdoc::p
    "The file @('DerivedName.txt') of the Unicode Character Database
     gives the names in two ways.
     Most are listed one by one: these go in a map
     from the code point to the name.
     For some ranges of code points the file has a pattern,
     a prefix such as @('CJK UNIFIED IDEOGRAPH-'):
     the name of a code point of the range is the prefix
     followed by the code point in hexadecimal.
     These go in a list of patterns.
     This book has the types of the two tables,
     and of the map that goes back from a name to its code point.
     The functions that use the tables are in @(see names).")
   (xdoc::p
    "The file @('NameAliases.txt') gives some code points
     one or more aliases, which are further names
     (the property @('Name_Alias')).
     This book has the type of an alias,
     and of the map from a code point to its aliases.
     The functions that use that table are in @(see name-aliases)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap name-map
  :short "Fixtype of maps from code points to strings,
          for the names of the characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the table of the names
     that the Unicode Character Database lists one by one,
     and of the table of the short names of the Hangul jamo
     (the property @('Jamo_Short_Name'))."))
  :key-type code-point
  :val-type string
  :pred name-mapp)

;;;;;;;;;;;;;;;;;;;;

(define name-map-lookup ((cp code-point-p) (map name-mapp))
  :returns (name stringp)
  :short "Look up a code point in a map of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the empty string if the code point is not in the map."))
  (b* (((mv in? name) (treemap::lookup? (code-point-fix cp)
                                        (name-map-fix map))))
    (if in?
        (acl2::str-fix name)
      ""))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod name-pattern
  :short "Fixtype of patterns of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "A pattern consists of a range of code points and a prefix.
     It stands for the names of the code points of the range:
     the name of each is the prefix
     followed by the code point in hexadecimal
     [Unicode, Section 4.8, rule NR2].
     For example, the pattern with the range U+4E00 to U+9FFF
     and the prefix @('CJK UNIFIED IDEOGRAPH-')
     gives U+4E00 the name @('CJK UNIFIED IDEOGRAPH-4E00')."))
  ((range range)
   (prefix string))
  :pred name-pattern-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist name-pattern-list
  :short "Fixtype of lists of patterns of names."
  :elt-type name-pattern
  :true-listp t
  :elementp-of-nil nil
  :pred name-pattern-listp)

;;;;;;;;;;;;;;;;;;;;

(define name-patterns-prefix ((cp code-point-p)
                              (patterns name-pattern-listp))
  :returns (prefix stringp)
  :short "The prefix of the first pattern of a list
          whose range has a code point."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the empty string
     if the code point is in the range of no pattern of the list.
     No pattern of the generated tables has an empty prefix."))
  (b* (((when (endp patterns)) "")
       ((name-pattern pattern) (car patterns))
       ((when (code-point-in-range-p cp pattern.range)) pattern.prefix))
    (name-patterns-prefix cp (cdr patterns)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define name-patterns-ordered-p ((patterns name-pattern-listp))
  :returns (yes/no booleanp)
  :short "Check that the ranges of a list of patterns
          are not empty, are in increasing order and do not overlap,
          and that no prefix is empty."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each generated list of patterns is checked with this predicate
     in the book that has it."))
  (b* (((when (endp patterns)) t)
       ((name-pattern pattern) (car patterns))
       ((range range) pattern.range))
    (and (<= range.min range.max)
         (not (equal pattern.prefix ""))
         (or (endp (cdr patterns))
             (< range.max
                (range->min (name-pattern->range (cadr patterns)))))
         (name-patterns-ordered-p (cdr patterns))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap name-key-map
  :short "Fixtype of maps from strings to code points,
          for finding a character by its name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strings are the keys of the names:
     see @(see names)."))
  :key-type string
  :val-type code-point
  :pred name-key-mapp)

;; The macro introduces a rule that concludes that a key of such a map
;; is a string, and that is tried whenever something has to be a string.
;; We leave it disabled.

(in-theory (disable stringp-when-in-name-key-mapp-binds-free-x))

;;;;;;;;;;;;;;;;;;;;

(define name-key-map-lookup ((key stringp) (map name-key-mapp))
  :returns (cp? code-point-option-p)
  :short "Look up a key in a map from keys of names to code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the key is not in the map."))
  (b* (((mv in? cp) (treemap::lookup? (acl2::str-fix key)
                                      (name-key-map-fix map))))
    (if in?
        (code-point-fix cp)
      nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum name-alias-type
  :short "Fixtype of the types of the aliases of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each alias in the file @('NameAliases.txt') has one of five types
     [Unicode, Section 4.8, Table 4-7]:")
   (xdoc::ul
    (xdoc::li
     "@('correction'):
      a correction for a serious problem in the name of the character.
      For example, U+FE18 has the name
      @('PRESENTATION FORM FOR VERTICAL RIGHT WHITE LENTICULAR BRAKCET')
      and an alias that ends in @('BRACKET').")
    (xdoc::li
     "@('control'):
      a name for a control code, such as @('LINE FEED') for U+000A.
      The control codes have no value of the @('Name') property.")
    (xdoc::li
     "@('alternate'):
      a widely used other name for a format character.
      The only one is @('BYTE ORDER MARK') for U+FEFF.")
    (xdoc::li
     "@('figment'):
      a label for a control code that was documented
      and never approved in any standard,
      such as @('PADDING CHARACTER') for U+0080.")
    (xdoc::li
     "@('abbreviation'):
      a common abbreviation for a control code, a format character,
      a space or a variation selector,
      such as @('LF') for U+000A and @('ZWSP') for U+200B.")))
  (:correction ())
  (:control ())
  (:alternate ())
  (:figment ())
  (:abbreviation ())
  :pred name-alias-type-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod name-alias
  :short "Fixtype of aliases of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "An alias consists of a string and a type.
     The string is written like a name:
     with capital letters, digits, spaces and hyphens
     [Unicode, Section 4.8]."))
  ((name string)
   (type name-alias-type))
  :pred name-alias-p)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption name-alias-option
  name-alias
  :short "Fixtype of optional aliases of names."
  :pred name-alias-option-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist name-alias-list
  :short "Fixtype of lists of aliases of names."
  :elt-type name-alias
  :true-listp t
  :elementp-of-nil nil
  :pred name-alias-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap name-alias-map
  :short "Fixtype of maps from code points to lists of aliases of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The aliases of a code point are in the order
     in which the file @('NameAliases.txt') has them."))
  :key-type code-point
  :val-type name-alias-list
  :pred name-alias-mapp)

;;;;;;;;;;;;;;;;;;;;

(define name-alias-map-lookup ((cp code-point-p) (map name-alias-mapp))
  :returns (aliases name-alias-listp)
  :short "Look up a code point in a map of aliases of names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the empty list if the code point is not in the map.
     No list in the maps of the generated tables is empty."))
  (b* (((mv in? aliases) (treemap::lookup? (code-point-fix cp)
                                           (name-alias-map-fix map))))
    (if in?
        (name-alias-list-fix aliases)
      nil))
  :hooks (:fix))
