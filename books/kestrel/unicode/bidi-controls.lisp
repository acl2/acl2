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
(include-book "range-sets")
(include-book "range-maps")

(include-book "data/v16.0.0/prop-list")
(include-book "data/v17.0.0/prop-list")
(include-book "data/v16.0.0/derived-bidi-class")
(include-book "data/v17.0.0/derived-bidi-class")

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

(define bidi-control-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          that have the @('Bidi_Control') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *bidi-control-v16.0.0*
                :v17.0.0 *bidi-control-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-control-p ((cp natp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Bidi_Control') property,
          in a version of Unicode."
  (in-range-set-p cp (bidi-control-set ver))

  ///

  (defruled bidi-control-p-alt-def
    (equal (bidi-control-p cp ver)
           (b* ((cp (nfix cp)))
             (or (equal cp #x061C) ; ARABIC LETTER MARK
                 (equal cp #x200E) ; LEFT-TO-RIGHT MARK
                 (equal cp #x200F) ; RIGHT-TO-LEFT MARK
                 (and (<= #x202A cp) ; LRE, RLE, PDF, LRO, RLO
                      (<= cp #x202E))
                 (and (<= #x2066 cp) ; LRI, RLI, FSI, PDI
                      (<= cp #x2069)))))
    :enable (bidi-control-set in-range-set-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-formatting-map ((ver versionp))
  :returns (map bidi-formatting-range-map-p)
  :short "The map from the explicit directional formatting characters
          to their bidirectional classes,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *bidi-explicit-formatting-v16.0.0*
                :v17.0.0 *bidi-explicit-formatting-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-formatting-class ((cp natp) (ver versionp))
  :returns (class? (or (bidi-formatting-class-p class?)
                       (not class?))
                   :rule-classes nil)
  :short "The bidirectional class of a code point,
          if it is an explicit directional formatting character,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is one of the keywords
     @(':lre'), @(':rle'), @(':lro'), @(':rlo'), @(':pdf'),
     @(':lri'), @(':rli'), @(':fsi') and @(':pdi')
     if the @('Bidi_Class') of the code point is the one of that name;
     otherwise it is @('nil').
     So this is the @('Bidi_Class') property
     restricted to the explicit directional formatting characters."))
  (range-map-lookup cp (bidi-formatting-map ver))

  ///

  (defruled bidi-formatting-class-alt-def
    (equal (bidi-formatting-class cp ver)
           (case (nfix cp)
             (#x202A :lre)   ; LEFT-TO-RIGHT EMBEDDING
             (#x202B :rle)   ; RIGHT-TO-LEFT EMBEDDING
             (#x202C :pdf)   ; POP DIRECTIONAL FORMATTING
             (#x202D :lro)   ; LEFT-TO-RIGHT OVERRIDE
             (#x202E :rlo)   ; RIGHT-TO-LEFT OVERRIDE
             (#x2066 :lri)   ; LEFT-TO-RIGHT ISOLATE
             (#x2067 :rli)   ; RIGHT-TO-LEFT ISOLATE
             (#x2068 :fsi)   ; FIRST STRONG ISOLATE
             (#x2069 :pdi)   ; POP DIRECTIONAL ISOLATE
             (t nil)))
    :enable (bidi-formatting-map range-map-lookup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-explicit-formatting-p ((cp natp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is
          an explicit directional formatting character,
          in a version of Unicode."
  (and (bidi-formatting-class cp ver) t)

  ///

  (defruled bidi-explicit-formatting-p-alt-def
    (equal (bidi-explicit-formatting-p cp ver)
           (b* ((cp (nfix cp)))
             (or (and (<= #x202A cp) ; LRE, RLE, PDF, LRO, RLO
                      (<= cp #x202E))
                 (and (<= #x2066 cp) ; LRI, RLI, FSI, PDI
                      (<= cp #x2069)))))
    :enable (bidi-formatting-class-alt-def nfix))

  (defrule bidi-control-p-when-bidi-explicit-formatting-p
    (implies (bidi-explicit-formatting-p cp ver)
             (bidi-control-p cp ver))
    :enable (bidi-explicit-formatting-p-alt-def bidi-control-p-alt-def)
    :disable bidi-explicit-formatting-p)

  (defruled bidi-control-p-when-not-bidi-explicit-formatting-p
    (implies (not (bidi-explicit-formatting-p cp ver))
             (equal (bidi-control-p cp ver)
                    (b* ((cp (nfix cp)))
                      (or (equal cp #x061C) ; ARABIC LETTER MARK
                          (equal cp #x200E) ; LEFT-TO-RIGHT MARK
                          (equal cp #x200F))))) ; RIGHT-TO-LEFT MARK
    :enable (bidi-explicit-formatting-p-alt-def bidi-control-p-alt-def)
    :disable bidi-explicit-formatting-p))
