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
(include-book "ranges")
(include-book "maps")

(include-book "data/v16.0.0/prop-list")
(include-book "data/v17.0.0/prop-list")
(include-book "data/v16.0.0/derived-bidi-class")
(include-book "data/v17.0.0/derived-bidi-class")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-controls
  :parents (unicode)
  :short "The bidirectional control characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the format characters that affect
     the Unicode Bidirectional Algorithm [UAX #9],
     i.e. the order in which a text is displayed.
     They do not belong in most program text.
     In particular, the explicit directional formatting characters
     can make a program look,
     to a person reading it in an editor or in a code review tool,
     different from what a compiler sees
     (this is known as the `Trojan Source' attack);
     so several language implementations
     reject, or warn about, these characters in comments and literals.")
   (xdoc::p
    "We provide two sets, which differ by three code points:")
   (xdoc::ul
    (xdoc::li
     "The code points with the @('Bidi_Control') property:
      see @(tsee bidi-control-p).
      We take this property from the file @('PropList.txt')
      of the Unicode Character Database.")
    (xdoc::li
     "The explicit directional formatting characters
      of [UAX #9, Sections 2.1 to 2.5]:
      the embeddings, overrides and isolates, and their terminators.
      These are defined by their @('Bidi_Class'),
      which @(tsee bidi-formatting-class) returns.
      We take the classes from the file
      @('extracted/DerivedBidiClass.txt')
      of the Unicode Character Database.
      They all have the @('Bidi_Control') property;
      the code points with that property that are not among them
      are the three implicit directional marks
      of [UAX #9, Section 2.6]."))
   (xdoc::p
    "The Bidirectional Algorithm itself is not in this library.")
   (xdoc::p
    "Both sets are the same in all the supported versions:
     see the theorems with names ending in @('alt-def').
     The version arguments are there for uniformity,
     and so that this is checked when a version is added."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-control-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Bidi_Control') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *bidi-control-v16.0.0*
                :v17.0.0 *bidi-control-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-control-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Bidi_Control') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (bidi-control-ranges ver))
  :hooks (:fix)

  ///

  (defruled bidi-control-p-alt-def
    (equal (bidi-control-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (equal cp #x061C) ; ARABIC LETTER MARK
                 (equal cp #x200E) ; LEFT-TO-RIGHT MARK
                 (equal cp #x200F) ; RIGHT-TO-LEFT MARK
                 (and (<= #x202A cp) ; LRE, RLE, PDF, LRO, RLO
                      (<= cp #x202E))
                 (and (<= #x2066 cp) ; LRI, RLI, FSI, PDI
                      (<= cp #x2069)))))
    :enable (bidi-control-ranges
             code-point-in-range-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-formatting-class-map ((ver versionp))
  :returns (map bidi-formatting-class-mapp)
  :short "The map from the explicit directional formatting characters
          to their bidirectional classes,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *bidi-formatting-class-v16.0.0*
                :v17.0.0 *bidi-formatting-class-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-formatting-class ((cp code-point-p) (ver versionp))
  :returns (class? bidi-formatting-class-option-p)
  :short "The bidirectional class of a code point,
          if it is an explicit directional formatting character,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the @('Bidi_Class') of the code point
     if that is one of the nine classes
     of the explicit directional formatting characters;
     otherwise it is @('nil').
     So this is the @('Bidi_Class') property
     restricted to the explicit directional formatting characters."))
  (bidi-formatting-class-map-lookup cp (bidi-formatting-class-map ver))
  :hooks (:fix)

  ///

  ;; We prove the alternative definition
  ;; by checking it on every code point, for each version.

  (local
   (define class-ok ((cp code-point-p) (map bidi-formatting-class-mapp))
     :returns (yes/no booleanp)
     (equal (bidi-formatting-class-map-lookup cp map)
            (case (code-point-fix cp)
              (#x202A (bidi-formatting-class-lre))
              (#x202B (bidi-formatting-class-rle))
              (#x202C (bidi-formatting-class-pdf))
              (#x202D (bidi-formatting-class-lro))
              (#x202E (bidi-formatting-class-rlo))
              (#x2066 (bidi-formatting-class-lri))
              (#x2067 (bidi-formatting-class-rli))
              (#x2068 (bidi-formatting-class-fsi))
              (#x2069 (bidi-formatting-class-pdi))
              (t nil)))))

  (local
   (std::deflist class-ok-listp (x map)
     :guard (and (code-point-listp x)
                 (bidi-formatting-class-mapp map))
     (class-ok x map)))

  (defrulel class-ok-listp-of-all-code-points
    (class-ok-listp (all-code-points) (bidi-formatting-class-map ver))
    :enable (bidi-formatting-class-map
             (:e all-code-points))
    :disable class-ok-listp-of-cons)

  (defruled bidi-formatting-class-alt-def
    (equal (bidi-formatting-class cp ver)
           (case (code-point-fix cp)
             (#x202A (bidi-formatting-class-lre)) ; LEFT-TO-RIGHT EMBEDDING
             (#x202B (bidi-formatting-class-rle)) ; RIGHT-TO-LEFT EMBEDDING
             (#x202C (bidi-formatting-class-pdf)) ; POP DIRECTIONAL FORMATTING
             (#x202D (bidi-formatting-class-lro)) ; LEFT-TO-RIGHT OVERRIDE
             (#x202E (bidi-formatting-class-rlo)) ; RIGHT-TO-LEFT OVERRIDE
             (#x2066 (bidi-formatting-class-lri)) ; LEFT-TO-RIGHT ISOLATE
             (#x2067 (bidi-formatting-class-rli)) ; RIGHT-TO-LEFT ISOLATE
             (#x2068 (bidi-formatting-class-fsi)) ; FIRST STRONG ISOLATE
             (#x2069 (bidi-formatting-class-pdi)) ; POP DIRECTIONAL ISOLATE
             (t nil)))
    :enable class-ok
    :use (:instance class-ok-when-member-equal-of-class-ok-listp
          (acl2::a (code-point-fix cp))
          (x (all-code-points))
          (map (bidi-formatting-class-map ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-explicit-formatting-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is
          an explicit directional formatting character,
          in a version of Unicode."
  (and (bidi-formatting-class cp ver) t)
  :hooks (:fix)

  ///

  (defruled bidi-explicit-formatting-p-alt-def
    (equal (bidi-explicit-formatting-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (and (<= #x202A cp) ; LRE, RLE, PDF, LRO, RLO
                      (<= cp #x202E))
                 (and (<= #x2066 cp) ; LRI, RLI, FSI, PDI
                      (<= cp #x2069)))))
    :enable (bidi-formatting-class-alt-def
             code-point-p))

  (defrule bidi-control-p-when-bidi-explicit-formatting-p
    (implies (bidi-explicit-formatting-p cp ver)
             (bidi-control-p cp ver))
    :enable (bidi-explicit-formatting-p-alt-def bidi-control-p-alt-def)
    :disable bidi-explicit-formatting-p)

  (defruled bidi-control-p-when-not-bidi-explicit-formatting-p
    (implies (not (bidi-explicit-formatting-p cp ver))
             (equal (bidi-control-p cp ver)
                    (b* ((cp (code-point-fix cp)))
                      (or (equal cp #x061C) ; ARABIC LETTER MARK
                          (equal cp #x200E) ; LEFT-TO-RIGHT MARK
                          (equal cp #x200F))))) ; RIGHT-TO-LEFT MARK
    :enable (bidi-explicit-formatting-p-alt-def bidi-control-p-alt-def)
    :disable bidi-explicit-formatting-p))
