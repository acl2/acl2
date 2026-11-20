; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "versions")
(include-book "block-tables")

(include-book "data/v16.0.0/blocks")
(include-book "data/v17.0.0/blocks")
(include-book "data/v18.0.0/blocks")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ blocks
  :parents (unicode)
  :short "The @('Block') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code space of Unicode is divided into named blocks,
     such as @('Basic Latin'), from U+0000 to U+007F,
     and @('Letterlike Symbols'), from U+2100 to U+214F.
     A block is a range of code points;
     blocks do not overlap, and some code points are in no block.
     The @('Block') property gives every code point
     the name of its block, or the value @('No_Block').")
   (xdoc::p
    "A block is a way to organize the code charts.
     It says little about its characters:
     the characters of a script can be in several blocks,
     and a block can have characters of several scripts,
     and code points that are not assigned.
     For what a character is,
     the @('Script') and the @('General_Category') are the properties to use
     (see @(see scripts) and @(see general-category-property)).")
   (xdoc::p
    "We take the property from the file @('Blocks.txt')
     of the Unicode Character Database, for each supported version.
     The names are strings, written as in that file, with spaces.")
   (xdoc::p
    "The function @(tsee code-point-block)
     gives the name of the block of a code point,
     and @(tsee block-ranges) gives the code points of a block,
     as a list of ranges, which has one range for a block.
     The theorem @('code-point-in-block-ranges')
     says that the two agree."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define block-runs ((ver versionp))
  :returns (runs block-run-listp)
  :short "The @('Block') of every code point,
          as a list of runs, in a version of Unicode."
  (version-case ver
                :v16.0.0 *block-v16.0.0*
                :v17.0.0 *block-v17.0.0*
                :v18.0.0 *block-v18.0.0*)
  :hooks (:fix)

  ///

  (defrule block-runs-cover-all-code-points
    (block-run-list-covers-p 0 #x10FFFF (block-runs ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-block ((cp code-point-p) (ver versionp))
  :returns (name stringp)
  :short "The name of the block of a code point, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('\"No_Block\"') if the code point is in no block."))
  (block-run-list-lookup cp (block-runs ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define block-ranges ((name stringp) (ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points of a block, given by its name,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is a list of one range if the name is that of a block,
     and the empty list if it is not.
     For the name @('\"No_Block\"'), it is the list of the ranges
     of the code points that are in no block.
     It is computed from the list of runs at each call,
     by going through the whole list."))
  (block-run-list-ranges name (block-runs ver))
  :hooks (:fix)

  ///

  (defruled code-point-in-block-ranges
    (equal (code-point-in-ranges-p cp (block-ranges name ver))
           (equal (code-point-block cp ver)
                  (acl2::str-fix name)))
    :enable (code-point-block
             code-point-in-block-run-list-ranges))

  (defruled equal-of-code-point-block
    (equal (equal (code-point-block cp ver) name)
           (and (stringp name)
                (code-point-in-ranges-p cp (block-ranges name ver))))
    :enable code-point-in-block-ranges
    :disable block-ranges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define block-names ((ver versionp))
  :returns (names string-listp)
  :short "The names of the blocks of a version of Unicode,
          in the order of their code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value @('\"No_Block\"') is not in the list."))
  (block-run-list-names (block-runs ver))
  :hooks (:fix)

  ///

  (defrule no-duplicatesp-equal-of-block-names
    (no-duplicatesp-equal (block-names ver))
    :enable block-runs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection block-theorems
  :short "Theorems about @('Block')
          that hold in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A block is one range of code points:
     the list of the ranges of a name other than @('No_Block')
     has at most one range,
     and none if the name is not that of a block.
     Two blocks do not overlap
     because a code point has one value of the property.")
   (xdoc::p
    "A block of a version of Unicode is a block of every later version,
     with the same range.
     That holds for the supported versions,
     in the order of @(tsee version<=);
     the stability policies of the Unicode Standard [Stability]
     do not cover blocks.
     It is proved by evaluation on the tables, for each pair of versions;
     the rule is disabled by default,
     because the earlier version is in its hypotheses only."))

  (defrule len-of-block-ranges-upper-bound
    (implies (not (equal (acl2::str-fix name) "No_Block"))
             (<= (len (block-ranges name ver)) 1))
    :rule-classes (:rewrite :linear)
    :enable (block-ranges block-names)
    :disable no-duplicatesp-equal-of-block-names
    :use no-duplicatesp-equal-of-block-names)

  (defrule block-ranges-when-not-member-of-block-names
    (implies (and (not (member-equal (acl2::str-fix name) (block-names ver)))
                  (not (equal (acl2::str-fix name) "No_Block")))
             (equal (block-ranges name ver)
                    nil))
    :enable (block-ranges block-names))

  ;; Across versions: we check, for each block of the earlier version,
  ;; that it has the same ranges in the later version.

  (local
   (define block-kept ((name stringp) (ver1 versionp) (ver2 versionp))
     :returns (yes/no booleanp)
     (or (not (version<= ver1 ver2))
         (equal (block-ranges name ver2)
                (block-ranges name ver1)))
     :hooks nil))

  (local (in-theory (enable string-listp)))

  (local
   (std::deflist block-kept-listp (x ver1 ver2)
     :guard (and (string-listp x)
                 (versionp ver1)
                 (versionp ver2))
     (block-kept x ver1 ver2)))

  (defrulel block-kept-listp-of-block-names
    (block-kept-listp (block-names (version-fix ver1))
                      (version-fix ver1)
                      (version-fix ver2))
    :rule-classes nil
    :enable version-fix-in-terms-of-version-case
    :disable block-kept-listp-of-cons)

  (defruled block-ranges-of-later-version
    (implies (and (version<= ver1 ver2)
                  (member-equal (acl2::str-fix name) (block-names ver1)))
             (equal (block-ranges name ver2)
                    (block-ranges name ver1)))
    :enable block-kept
    :disable block-kept-when-member-equal-of-block-kept-listp
    :use (block-kept-listp-of-block-names
          (:instance block-kept-when-member-equal-of-block-kept-listp
                     (acl2::a (acl2::str-fix name))
                     (x (block-names (version-fix ver1)))
                     (ver1 (version-fix ver1))
                     (ver2 (version-fix ver2))))))
