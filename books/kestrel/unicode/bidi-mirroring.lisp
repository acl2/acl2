; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-brackets")
(include-book "data/v16.0.0/bidi-mirroring")
(include-book "data/v17.0.0/bidi-mirroring")
(include-book "data/v18.0.0/bidi-mirroring")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-mirroring
  :parents (unicode)
  :short "The mirroring glyphs:
          the property @('Bidi_Mirroring_Glyph')."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a character such as a parenthesis
     is displayed in text that runs from right to left,
     it is drawn as its mirror image:
     an opening parenthesis opens toward the left
     [UAX #9, rule L4 and Section 7].
     The property @('Bidi_Mirroring_Glyph') helps to do that:
     for a character, it is another character
     whose usual glyph is the mirror image of the usual glyph of the first.
     The @('Bidi_Mirroring_Glyph') of U+0028 LEFT PARENTHESIS
     is U+0029 RIGHT PARENTHESIS.
     Most code points have none.")
   (xdoc::p
    "The property is informative.
     The characters whose glyph is to be mirrored
     are those with the property @('Bidi_Mirrored'),
     which this library does not have.
     Every character with a @('Bidi_Mirroring_Glyph')
     has @('Bidi_Mirrored'),
     which the tool that generates the tables checks for each version;
     some characters with @('Bidi_Mirrored'),
     such as U+222B INTEGRAL,
     have no character with the mirrored glyph
     and so no @('Bidi_Mirroring_Glyph').")
   (xdoc::p
    "We take the property from the file @('BidiMirroring.txt')
     of the Unicode Character Database, for each supported version.
     There are 428 code points with a mirroring glyph
     in Unicode 16.0.0 and 17.0.0, and 438 in 18.0.0."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-mirroring-glyphs ((ver versionp))
  :returns (map mirroring-mapp)
  :short "The map from the code points that have a mirroring glyph
          to that glyph, in a version of Unicode."
  (version-case ver
                :v16.0.0 *bidi-mirroring-v16.0.0*
                :v17.0.0 *bidi-mirroring-v17.0.0*
                :v18.0.0 *bidi-mirroring-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-bidi-mirroring-glyph ((cp code-point-p) (ver versionp))
  :returns (mirror? code-point-option-p)
  :short "The @('Bidi_Mirroring_Glyph') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') for a code point that has none."))
  (mirroring-map-lookup cp (bidi-mirroring-glyphs ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-mirroring-theorems
  :short "The mirroring glyph of a mirroring glyph is the first code point,
          the partner of a paired bracket is its mirroring glyph,
          and a mirroring glyph is a scalar value."
  :long
  (xdoc::topstring
   (xdoc::p
    "So the code points with a mirroring glyph come in pairs,
     and each paired bracket (see @(see bidi-paired-brackets))
     is the mirror image of its partner.
     No mirroring glyph is a surrogate code point,
     so replacing characters by their mirroring glyphs
     keeps a list of scalar values a list of scalar values.
     We prove the three by checking them on every code point,
     for each version;
     so adding a version checks them for that version."))

  (local
   (define mirror-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((mirror? (code-point-bidi-mirroring-glyph cp ver))
          (bracket? (code-point-bidi-bracket cp ver)))
       (and (or (not mirror?)
                (equal (code-point-bidi-mirroring-glyph mirror? ver)
                       (code-point-fix cp)))
            (or (not mirror?)
                (scalar-value-p mirror?))
            (or (not bracket?)
                (equal mirror?
                       (bidi-bracket-case bracket?
                                          :open bracket?.partner
                                          :close bracket?.partner)))))
     :hooks nil))

  (local
   (std::deflist mirror-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (mirror-ok x ver)))

  (defrulel mirror-ok-listp-of-all-code-points
    (mirror-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable mirror-ok-listp-of-cons)

  (defrulel mirror-ok-holds
    (mirror-ok cp ver)
    :rule-classes nil
    :use (:instance mirror-ok-when-member-equal-of-mirror-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable mirror-ok)

  (defrule code-point-bidi-mirroring-glyph-of-code-point-bidi-mirroring-glyph
    (b* ((mirror? (code-point-bidi-mirroring-glyph cp ver)))
      (implies mirror?
               (equal (code-point-bidi-mirroring-glyph mirror? ver)
                      (code-point-fix cp))))
    :enable mirror-ok
    :use mirror-ok-holds)

  (defrule scalar-value-p-of-code-point-bidi-mirroring-glyph
    (b* ((mirror? (code-point-bidi-mirroring-glyph cp ver)))
      (implies mirror?
               (scalar-value-p mirror?)))
    :enable mirror-ok
    :use mirror-ok-holds)

  (defrule code-point-bidi-mirroring-glyph-when-bracket
    (b* ((bracket? (code-point-bidi-bracket cp ver)))
      (implies bracket?
               (equal (code-point-bidi-mirroring-glyph cp ver)
                      (bidi-bracket-case bracket?
                                         :open bracket?.partner
                                         :close bracket?.partner))))
    :enable mirror-ok
    :use mirror-ok-holds))
