; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "general-category")
(include-book "default-ignorable")
(include-book "variation-selectors")
(include-book "join-controls")
(include-book "noncharacters")
(include-book "prepended-concatenation-marks")
(include-book "pattern-syntax")
(include-book "pattern-white-space")
(include-book "bidi-controls")
(include-book "xid")
(include-book "combining-classes")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ property-relations
  :parents (unicode)
  :short "Theorems that relate properties of code points to each other,
          in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each property of this library is in a book of its own,
     which does not load the tables of the other properties.
     This book loads several of them
     and proves how they relate.")
   (xdoc::p
    "About the @('General_Category') property
     (see @(see general-category-property)),
     whose values are abbreviated by two letters:")
   (xdoc::ul
    (xdoc::li
     "A code point that is not a starter,
      that is, whose @('Canonical_Combining_Class') is not 0,
      is a combining mark:
      its value is @('Nonspacing_Mark') (@('Mn')),
      @('Spacing_Mark') (@('Mc')) or @('Enclosing_Mark') (@('Me')).")
    (xdoc::li
     "Every variation selector is a @('Nonspacing_Mark') (@('Mn')).")
    (xdoc::li
     "Every bidirectional control, every join control
      and every prepended concatenation mark
      is a @('Format') character (@('Cf')).")
    (xdoc::li
     "Every noncharacter is @('Unassigned') (@('Cn')),
      so it is not assigned in the sense of @(tsee assigned-p)."))
   (xdoc::p
    "About the @('Default_Ignorable_Code_Point') property
     (see @(see default-ignorable)):")
   (xdoc::ul
    (xdoc::li
     "Every variation selector, every bidirectional control
      and every join control has it.")
    (xdoc::li
     "No prepended concatenation mark has it:
      these are the format characters that are visible."))
   (xdoc::p
    "About the @('Pattern_Syntax') property
     (see @(see pattern-syntax)):")
   (xdoc::ul
    (xdoc::li
     "No code point has both @('Pattern_Syntax')
      and @('Pattern_White_Space').")
    (xdoc::li
     "No code point has both @('Pattern_Syntax')
      and @('XID_Continue'), or @('XID_Start'):
      a character of syntax is never a character of an identifier."))
   (xdoc::p
    "These are proved by evaluation on the tables, for each version:
     so adding a version checks them for that version,
     and if one fails, that is a change in Unicode to look at."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection general-category-relations
  :short "Theorems that relate @('General_Category') to other properties."

  ;; We prove the first theorem
  ;; by checking it on every code point, for each version.

  (local
   (define mark-ok ((cp code-point-p)
                    (map combining-class-mapp)
                    (runs general-category-run-listp))
     :returns (yes/no booleanp)
     (or (equal (combining-class-map-lookup cp map) 0)
         (general-category-mark-p
          (general-category-run-list-lookup cp runs)))
     :hooks nil))

  (local
   (std::deflist mark-ok-listp (x map runs)
     :guard (and (code-point-listp x)
                 (combining-class-mapp map)
                 (general-category-run-listp runs))
     (mark-ok x map runs)))

  (defrulel mark-ok-listp-of-all-code-points
    (mark-ok-listp (all-code-points)
                   (canonical-combining-class-map ver)
                   (general-category-runs ver))
    :enable (canonical-combining-class-map
             general-category-runs
             (:e all-code-points))
    :disable mark-ok-listp-of-cons)

  (defrule general-category-mark-p-when-not-starter-p
    (implies (not (starter-p cp ver))
             (general-category-mark-p (code-point-general-category cp ver)))
    :enable (mark-ok
             starter-p
             canonical-combining-class
             code-point-general-category)
    :use (:instance mark-ok-when-member-equal-of-mark-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (map (canonical-combining-class-map ver))
                    (runs (general-category-runs ver))))

  ;; The other theorems say that the code points of a property
  ;; all have a certain General_Category.
  ;; Each is proved by evaluating, on the tables,
  ;; that the ranges of the property
  ;; are within the ranges of that General_Category.

  (defrulel variation-selector-ranges-within-nonspacing-mark-ranges
    (ranges-within-ranges-p
     (variation-selector-ranges ver)
     (general-category-ranges (general-category-nonspacing-mark) ver))
    :enable (variation-selector-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-variation-selector-p
    (implies (variation-selector-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-nonspacing-mark)))
    :enable (variation-selector-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-nonspacing-mark)))

  (defrulel bidi-control-ranges-within-format-ranges
    (ranges-within-ranges-p
     (bidi-control-ranges ver)
     (general-category-ranges (general-category-format) ver))
    :enable (bidi-control-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-bidi-control-p
    (implies (bidi-control-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-format)))
    :enable (bidi-control-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-format)))

  (defrulel join-control-ranges-within-format-ranges
    (ranges-within-ranges-p
     (join-control-ranges ver)
     (general-category-ranges (general-category-format) ver))
    :enable (join-control-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-join-control-p
    (implies (join-control-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-format)))
    :enable (join-control-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-format)))

  (defrulel prepended-concatenation-mark-ranges-within-format-ranges
    (ranges-within-ranges-p
     (prepended-concatenation-mark-ranges ver)
     (general-category-ranges (general-category-format) ver))
    :enable (prepended-concatenation-mark-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-prepended-concatenation-mark-p
    (implies (prepended-concatenation-mark-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-format)))
    :enable (prepended-concatenation-mark-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-format)))

  (defrulel noncharacter-ranges-within-unassigned-ranges
    (ranges-within-ranges-p
     (noncharacter-ranges ver)
     (general-category-ranges (general-category-unassigned) ver))
    :enable (noncharacter-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-noncharacter-p
    (implies (noncharacter-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-unassigned)))
    :enable (noncharacter-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-unassigned)))

  (defrule not-assigned-p-when-noncharacter-p
    (implies (noncharacter-p cp ver)
             (not (assigned-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (assigned-p
             code-point-general-category-when-noncharacter-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection default-ignorable-relations
  :short "Theorems that relate @('Default_Ignorable_Code_Point')
          to other properties."

  (defrulel variation-selector-ranges-within-default-ignorable-ranges
    (ranges-within-ranges-p (variation-selector-ranges ver)
                            (default-ignorable-ranges ver))
    :enable (variation-selector-ranges
             default-ignorable-ranges))

  (defrule default-ignorable-p-when-variation-selector-p
    (implies (variation-selector-p cp ver)
             (default-ignorable-p cp ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (variation-selector-p
             default-ignorable-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrulel bidi-control-ranges-within-default-ignorable-ranges
    (ranges-within-ranges-p (bidi-control-ranges ver)
                            (default-ignorable-ranges ver))
    :enable (bidi-control-ranges
             default-ignorable-ranges))

  (defrule default-ignorable-p-when-bidi-control-p
    (implies (bidi-control-p cp ver)
             (default-ignorable-p cp ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (bidi-control-p
             default-ignorable-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrulel join-control-ranges-within-default-ignorable-ranges
    (ranges-within-ranges-p (join-control-ranges ver)
                            (default-ignorable-ranges ver))
    :enable (join-control-ranges
             default-ignorable-ranges))

  (defrule default-ignorable-p-when-join-control-p
    (implies (join-control-p cp ver)
             (default-ignorable-p cp ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (join-control-p
             default-ignorable-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrulel prepended-concatenation-mark-ranges-disjoint-from-default-ignorable
    (ranges-disjoint-from-ranges-p (prepended-concatenation-mark-ranges ver)
                                   (default-ignorable-ranges ver))
    :enable (prepended-concatenation-mark-ranges
             default-ignorable-ranges))

  (defrule not-default-ignorable-p-when-prepended-concatenation-mark-p
    (implies (prepended-concatenation-mark-p cp ver)
             (not (default-ignorable-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (prepended-concatenation-mark-p
             default-ignorable-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pattern-syntax-relations
  :short "Theorems that relate @('Pattern_Syntax') to other properties."

  (defrulel pattern-syntax-ranges-disjoint-from-pattern-white-space-ranges
    (ranges-disjoint-from-ranges-p (pattern-syntax-ranges ver)
                                   (pattern-white-space-ranges ver))
    :enable (pattern-syntax-ranges
             pattern-white-space-ranges))

  (defrule not-pattern-white-space-p-when-pattern-syntax-p
    (implies (pattern-syntax-p cp ver)
             (not (pattern-white-space-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (pattern-syntax-p
             pattern-white-space-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p))

  (defrulel pattern-syntax-ranges-disjoint-from-xid-continue-ranges
    (ranges-disjoint-from-ranges-p (pattern-syntax-ranges ver)
                                   (xid-continue-ranges ver))
    :enable (pattern-syntax-ranges
             xid-continue-ranges))

  (defrule not-xid-continue-p-when-pattern-syntax-p
    (implies (pattern-syntax-p cp ver)
             (not (xid-continue-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (pattern-syntax-p
             xid-continue-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p))

  (defrule not-xid-start-p-when-pattern-syntax-p
    (implies (pattern-syntax-p cp ver)
             (not (xid-start-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)))
