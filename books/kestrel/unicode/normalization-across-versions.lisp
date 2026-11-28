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
(include-book "normalization")
(include-book "stream-safe")
(include-book "quick-check")

(local (include-book "range-operations"))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ normalization-across-versions
  :parents (normalization)
  :short "The normalization forms of text whose characters are assigned
          in a version of Unicode are the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode Standard promises that normalization is stable
     [Stability, Normalization Stability]:
     if all the characters of a string are assigned in a version,
     then each of the four normalization forms of the string
     (see @(see normalization))
     is the same in that version and in every later version.
     So text that is in a normalization form stays in that form,
     and two identifiers that are the same after normalization stay the same,
     when an implementation moves to a later version of Unicode.")
   (xdoc::p
    "Here this is a theorem about the supported versions,
     in the order of @(tsee version<=),
     for the lists of code points
     that are all assigned in the earlier version
     (see @(tsee assigned-listp)):
     see @(see normalization-forms-across-versions).
     The hypothesis is needed.
     A code point that is not assigned in the earlier version
     has no decomposition and combining class 0 there,
     and may have others once it is assigned.")
   (xdoc::p
    "The theorem follows from facts about the tables,
     which we check on every code point, for each pair of versions,
     so that adding a version checks them for that version.
     For a code point that is assigned in the earlier version,
     the combining class, the two decompositions,
     the canonical decomposition mapping
     and the @('Full_Composition_Exclusion') property
     are the same in the later version.
     The decompositions of an assigned code point
     consist of assigned code points.
     And a primary composite of the later version
     that is not assigned in the earlier one
     has a decomposition mapping with a code point
     that is not assigned in the earlier one either:
     so two code points of the earlier version
     compose in the later version exactly as they did.")
   (xdoc::p
    "Two consequences are also here.
     Text of assigned characters that is in Stream-Safe Text Format
     is in that format in every later version,
     and the Stream-Safe Text Process gives the same result:
     see @(see stream-safe-across-versions).
     And the quick check properties of an assigned code point
     are the same in every later version,
     which the standard promises only in part:
     see @(see quick-check-across-versions).")
   (xdoc::p
    "The rules here are disabled by default:
     they have a version in their hypotheses
     that is not in their left sides.
     They rewrite a term about the later version
     to the same term about the earlier version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection properties-across-versions
  :short "The combining class, the decompositions,
          the canonical decomposition mapping
          and the @('Full_Composition_Exclusion') property
          of a code point that is assigned in a version of Unicode
          are the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see normalization-across-versions).
     We check this on every code point, for each pair of versions.
     The check looks first at whether the values are the same,
     and only if they are not at whether the code point is assigned,
     which takes longer."))

  (local
   (define stable-ok ((cp code-point-p) (ver1 versionp) (ver2 versionp))
     :returns (yes/no booleanp)
     (or (not (version<= ver1 ver2))
         (and (equal (canonical-combining-class cp ver2)
                     (canonical-combining-class cp ver1))
              (equal (decomposition cp nil ver2)
                     (decomposition cp nil ver1))
              (equal (decomposition cp t ver2)
                     (decomposition cp t ver1))
              (equal (decomposition-map-lookup cp (canonical-mappings ver2))
                     (decomposition-map-lookup cp (canonical-mappings ver1)))
              (equal (full-composition-exclusion-p cp ver2)
                     (full-composition-exclusion-p cp ver1)))
         (not (assigned-p cp ver1)))
     :hooks nil))

  (local
   (std::deflist stable-ok-listp (x ver1 ver2)
     :guard (and (code-point-listp x)
                 (versionp ver1)
                 (versionp ver2))
     (stable-ok x ver1 ver2)))

  (defrulel stable-ok-listp-of-all-code-points
    (stable-ok-listp (all-code-points) (version-fix ver1) (version-fix ver2))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable stable-ok-listp-of-cons)

  (defrulel stable-ok-holds
    (stable-ok cp ver1 ver2)
    :enable stable-ok
    :use (:instance stable-ok-when-member-equal-of-stable-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver1 (version-fix ver1))
                    (ver2 (version-fix ver2))))

  (defruled canonical-combining-class-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (canonical-combining-class cp ver2)
                    (canonical-combining-class cp ver1)))
    :enable stable-ok
    :disable stable-ok-holds
    :use stable-ok-holds)

  (defruled decomposition-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (decomposition cp compat ver2)
                    (decomposition cp compat ver1)))
    :enable stable-ok
    :disable stable-ok-holds
    :cases (compat)
    :use stable-ok-holds)

  (defruled canonical-mapping-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (decomposition-map-lookup cp (canonical-mappings ver2))
                    (decomposition-map-lookup cp (canonical-mappings ver1))))
    :enable stable-ok
    :disable stable-ok-holds
    :use stable-ok-holds)

  (defruled full-composition-exclusion-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (full-composition-exclusion-p cp ver2)
                    (full-composition-exclusion-p cp ver1)))
    :enable stable-ok
    :disable stable-ok-holds
    :use stable-ok-holds)

  (defruled starter-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (starter-p cp ver2)
                    (starter-p cp ver1)))
    :enable (starter-p
             canonical-combining-class-of-later-version)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection decompositions-of-assigned-code-points
  :short "The decompositions of an assigned code point
          consist of assigned code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "This holds within one version of Unicode,
     for the canonical and for the compatibility decomposition.
     Also, the code points that have a canonical decomposition mapping,
     the precomposed Hangul syllables,
     and so the code points that two code points compose to,
     are assigned.
     We check these facts on every code point, for each version."))

  (local
   (define closed-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (and (or (undecomposable-p cp t ver)
              (not (assigned-p cp ver))
              (and (assigned-listp (decomposition cp nil ver) ver)
                   (assigned-listp (decomposition cp t ver) ver)))
          (or (not (decomposition-map-lookup cp (canonical-mappings ver)))
              (assigned-p cp ver))
          (or (not (hangul-syllable-p cp))
              (assigned-p cp ver)))
     :hooks nil))

  (local
   (std::deflist closed-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (closed-ok x ver)))

  (defrulel closed-ok-listp-of-all-code-points
    (closed-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable closed-ok-listp-of-cons)

  (defrulel closed-ok-holds
    (closed-ok cp ver)
    :enable closed-ok
    :use (:instance closed-ok-when-member-equal-of-closed-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver))))

  (defrule assigned-listp-of-decomposition
    (implies (assigned-p cp ver)
             (assigned-listp (decomposition cp compat ver) ver))
    :enable (closed-ok
             decomposition-when-undecomposable-p)
    :disable closed-ok-holds
    :cases (compat)
    :use closed-ok-holds)

  (defrule assigned-listp-of-decompose
    (implies (assigned-listp cps ver)
             (assigned-listp (decompose cps compat ver) ver))
    :induct t
    :enable decompose)

  (defruled assigned-p-when-canonical-mapping
    (implies (decomposition-map-lookup cp (canonical-mappings ver))
             (assigned-p cp ver))
    :enable closed-ok
    :disable closed-ok-holds
    :use closed-ok-holds)

  (defrule assigned-p-when-hangul-syllable-p
    (implies (hangul-syllable-p cp)
             (assigned-p cp ver))
    :enable closed-ok
    :disable closed-ok-holds
    :use closed-ok-holds)

  (defrule assigned-p-of-composition
    (implies (composition first second ver)
             (assigned-p (composition first second ver) ver))
    :enable (composition
             assigned-p-when-canonical-mapping
             canonical-mapping-of-composition-map-lookup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection composition-across-versions
  :short "Two code points that are assigned in a version of Unicode
          compose in the same way in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see normalization-across-versions).
     If the two code points compose in the earlier version,
     their composite is assigned there,
     so it has the same decomposition mapping
     and is not excluded in the later version either:
     they compose to it there too.
     If they compose in the later version,
     we need a fact about the tables of the two versions,
     which we check on every code point, for each pair of versions:
     a code point of the later version
     whose canonical decomposition mapping consists of two code points
     that are both assigned in the earlier version,
     and that does not have the @('Full_Composition_Exclusion') property,
     is assigned in the earlier version.
     So it is their composite there too.")
   (xdoc::p
    "That fact is what keeps normalization stable
     when characters are added:
     a new character may have a canonical decomposition
     into characters that already exist
     only if it is excluded from composition
     [Stability, Normalization Stability]."))

  (local
   (define composite-ok ((cp code-point-p) (ver1 versionp) (ver2 versionp))
     :returns (yes/no booleanp)
     (b* ((mapping (decomposition-map-lookup cp (canonical-mappings ver2))))
       (or (not (version<= ver1 ver2))
           (not (equal (len mapping) 2))
           (full-composition-exclusion-p cp ver2)
           (assigned-p cp ver1)
           (not (assigned-p (first mapping) ver1))
           (not (assigned-p (second mapping) ver1))))
     :hooks nil
     :guard-hints (("Goal" :in-theory (enable len)))))

  (local
   (std::deflist composite-ok-listp (x ver1 ver2)
     :guard (and (code-point-listp x)
                 (versionp ver1)
                 (versionp ver2))
     (composite-ok x ver1 ver2)))

  (defrulel composite-ok-listp-of-all-code-points
    (composite-ok-listp (all-code-points)
                        (version-fix ver1)
                        (version-fix ver2))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable composite-ok-listp-of-cons)

  (defrulel composite-ok-holds
    (composite-ok cp ver1 ver2)
    :enable composite-ok
    :use (:instance composite-ok-when-member-equal-of-composite-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver1 (version-fix ver1))
                    (ver2 (version-fix ver2))))

  ;; So a code point that two code points of the earlier version
  ;; are mapped to, in the table of the compositions of the later version,
  ;; is assigned in the earlier version:

  (defrulel assigned-p-of-earlier-version-when-composite
    (b* ((mapping (decomposition-map-lookup cp (canonical-mappings ver2))))
      (implies (and (version<= ver1 ver2)
                    (equal (len mapping) 2)
                    (not (full-composition-exclusion-p cp ver2))
                    (assigned-p (first mapping) ver1)
                    (assigned-p (second mapping) ver1))
               (assigned-p cp ver1)))
    :rule-classes nil
    :enable composite-ok
    :disable composite-ok-holds
    :use composite-ok-holds)

  (defruledl assigned-p-of-earlier-version-of-composition-map-lookup
    (b* ((cp (composition-map-lookup first
                                     second
                                     (canonical-compositions ver2))))
      (implies (and (version<= ver1 ver2)
                    (assigned-p first ver1)
                    (assigned-p second ver1)
                    cp)
               (assigned-p cp ver1)))
    :enable canonical-mapping-of-composition-map-lookup
    :use (:instance assigned-p-of-earlier-version-when-composite
                    (cp (composition-map-lookup
                         first
                         second
                         (canonical-compositions ver2)))))

  ;; The same facts as in PROPERTIES-ACROSS-VERSIONS,
  ;; but as rules that rewrite a term about the earlier version
  ;; to the same term about the later version.
  ;; They are not to be enabled together with those.

  (defruledl canonical-mapping-of-earlier-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (decomposition-map-lookup cp (canonical-mappings ver1))
                    (decomposition-map-lookup cp (canonical-mappings ver2))))
    :enable canonical-mapping-of-later-version)

  (defruledl full-composition-exclusion-p-of-earlier-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (full-composition-exclusion-p cp ver1)
                    (full-composition-exclusion-p cp ver2)))
    :enable full-composition-exclusion-p-of-later-version)

  ;; A code point that is not a precomposed Hangul syllable
  ;; is what the two code points of its canonical mapping are mapped to
  ;; in the table of the compositions, if it is not excluded:

  (defrulel composition-map-lookup-when-canonical-mapping
    (implies (and (equal (decomposition-map-lookup cp (canonical-mappings ver))
                         (list (code-point-fix first)
                               (code-point-fix second)))
                  (not (full-composition-exclusion-p cp ver))
                  (not (hangul-syllable-p (code-point-fix cp))))
             (equal (composition-map-lookup first
                                            second
                                            (canonical-compositions ver))
                    (code-point-fix cp)))
    :rule-classes nil
    :enable (composition
             len)
    :disable hangul-syllable-p-of-hangul-composition
    :use (composition-of-canonical-mapping
          hangul-syllable-p-of-hangul-composition))

  (defruledl composition-map-lookup-of-later-version-when-composite
    (implies (and (version<= ver1 ver2)
                  (composition-map-lookup first
                                          second
                                          (canonical-compositions ver1)))
             (equal (composition-map-lookup first
                                            second
                                            (canonical-compositions ver2))
                    (composition-map-lookup first
                                            second
                                            (canonical-compositions ver1))))
    :enable (canonical-mapping-of-composition-map-lookup
             canonical-mapping-of-later-version
             full-composition-exclusion-p-of-later-version
             assigned-p-when-canonical-mapping)
    :use (:instance composition-map-lookup-when-canonical-mapping
                    (cp (composition-map-lookup first
                                                second
                                                (canonical-compositions ver1)))
                    (ver ver2)))

  (defruledl composition-map-lookup-of-later-version-when-not-composite
    (implies (and (version<= ver1 ver2)
                  (assigned-p first ver1)
                  (assigned-p second ver1)
                  (not (composition-map-lookup first
                                               second
                                               (canonical-compositions ver1))))
             (equal (composition-map-lookup first
                                            second
                                            (canonical-compositions ver2))
                    nil))
    :enable (canonical-mapping-of-composition-map-lookup
             canonical-mapping-of-earlier-version
             full-composition-exclusion-p-of-earlier-version
             assigned-p-of-earlier-version-of-composition-map-lookup)
    :use (:instance composition-map-lookup-when-canonical-mapping
                    (cp (composition-map-lookup first
                                                second
                                                (canonical-compositions ver2)))
                    (ver ver1)))

  (defruled composition-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p first ver1)
                  (assigned-p second ver1))
             (equal (composition first second ver2)
                    (composition first second ver1)))
    :enable (composition
             composition-map-lookup-of-later-version-when-composite
             composition-map-lookup-of-later-version-when-not-composite)
    :cases ((composition-map-lookup first
                                    second
                                    (canonical-compositions ver1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalization-steps-across-versions
  :short "Decomposition, canonical ordering and canonical composition
          of code points that are assigned in a version of Unicode
          are the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see normalization-across-versions).
     Each of the three steps also keeps the code points assigned:
     for decomposition this is in
     @(see decompositions-of-assigned-code-points);
     canonical ordering only moves code points;
     and the code points that two code points compose to are assigned."))

  (defruled decompose-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (decompose cps compat ver2)
                    (decompose cps compat ver1)))
    :induct (len cps)
    :enable (decompose
             decomposition-of-later-version
             len))

  ;; Canonical ordering:

  (defrule assigned-listp-of-canonical-order-insert
    (equal (assigned-listp (canonical-order-insert cp cps ver1) ver)
           (and (assigned-p cp ver)
                (assigned-listp cps ver)))
    :induct (canonical-order-insert cp cps ver1)
    :enable canonical-order-insert)

  (defrule assigned-listp-of-canonical-order
    (equal (assigned-listp (canonical-order cps ver1) ver)
           (assigned-listp cps ver))
    :induct (canonical-order cps ver1)
    :enable canonical-order)

  (defruledl canonical-order-insert-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1)
                  (assigned-listp cps ver1))
             (equal (canonical-order-insert cp cps ver2)
                    (canonical-order-insert cp cps ver1)))
    :induct (canonical-order-insert cp cps ver1)
    :enable (canonical-order-insert
             canonical-combining-class-of-later-version))

  (defruled canonical-order-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (canonical-order cps ver2)
                    (canonical-order cps ver1)))
    :induct (canonical-order cps ver1)
    :enable (canonical-order
             canonical-combining-class-of-later-version
             canonical-order-insert-of-later-version))

  ;; Canonical composition:

  (defrule assigned-listp-of-canonical-compose-from-starter
    (implies (and (assigned-p starter ver)
                  (assigned-listp pending ver)
                  (assigned-listp cps ver))
             (assigned-listp
              (canonical-compose-from-starter starter pending last-ccc cps ver)
              ver))
    :induct (canonical-compose-from-starter starter pending last-ccc cps ver)
    :enable canonical-compose-from-starter)

  (defrule assigned-listp-of-canonical-compose
    (implies (assigned-listp cps ver)
             (assigned-listp (canonical-compose cps ver) ver))
    :induct (canonical-compose cps ver)
    :enable canonical-compose)

  (defruledl canonical-compose-from-starter-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p starter ver1)
                  (assigned-listp cps ver1))
             (equal (canonical-compose-from-starter starter
                                                    pending
                                                    last-ccc
                                                    cps
                                                    ver2)
                    (canonical-compose-from-starter starter
                                                    pending
                                                    last-ccc
                                                    cps
                                                    ver1)))
    :induct (canonical-compose-from-starter starter pending last-ccc cps ver1)
    :expand (canonical-compose-from-starter starter pending last-ccc cps ver2)
    :enable (canonical-compose-from-starter
             canonical-combining-class-of-later-version
             composition-of-later-version))

  (defruled canonical-compose-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (canonical-compose cps ver2)
                    (canonical-compose cps ver1)))
    :induct (canonical-compose cps ver1)
    :enable (canonical-compose
             canonical-combining-class-of-later-version
             canonical-compose-from-starter-of-later-version)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalization-forms-of-assigned-code-points
  :short "The normalization forms of a list of assigned code points
          consist of assigned code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "This holds within one version of Unicode,
     for each of the four forms:
     Normalization Form D (NFD), which is canonical decomposition;
     Normalization Form C (NFC), which is
     canonical decomposition followed by canonical composition;
     Normalization Form KD (NFKD), which is compatibility decomposition;
     and Normalization Form KC (NFKC), which is
     compatibility decomposition followed by canonical composition."))

  (defrule assigned-listp-of-nfd
    (implies (assigned-listp cps ver)
             (assigned-listp (nfd cps ver) ver))
    :enable nfd)

  (defrule assigned-listp-of-nfc
    (implies (assigned-listp cps ver)
             (assigned-listp (nfc cps ver) ver))
    :enable nfc)

  (defrule assigned-listp-of-nfkd
    (implies (assigned-listp cps ver)
             (assigned-listp (nfkd cps ver) ver))
    :enable nfkd)

  (defrule assigned-listp-of-nfkc
    (implies (assigned-listp cps ver)
             (assigned-listp (nfkc cps ver) ver))
    :enable nfkc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalization-forms-across-versions
  :short "The four normalization forms
          of a list of code points that are assigned in a version of Unicode
          are the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the stability of normalization
     [Stability, Normalization Stability]:
     see @(see normalization-across-versions).
     The four forms are
     Normalization Form D (NFD), Normalization Form C (NFC),
     Normalization Form KD (NFKD) and Normalization Form KC (NFKC).")
   (xdoc::p
    "So a list of assigned code points that is in one of the forms
     is in that form in every later version,
     and two lists of assigned code points
     that are canonical equivalents, or compatibility equivalents,
     are so in every later version.
     In fact each of these holds in the later version
     exactly when it holds in the earlier one.")
   (xdoc::p
    "For example, an identifier
     that consists of characters of Unicode 16.0.0
     and that is in NFC in that version
     is in NFC in Unicode 18.0.0,
     and two such identifiers that have the same NFC form in one version
     have the same NFC form in the other."))

  (defruled nfd-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfd cps ver2)
                    (nfd cps ver1)))
    :enable (nfd
             decompose-of-later-version
             canonical-order-of-later-version))

  (defruled nfc-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfc cps ver2)
                    (nfc cps ver1)))
    :enable (nfc
             nfd-of-later-version
             canonical-compose-of-later-version))

  (defruled nfkd-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfkd cps ver2)
                    (nfkd cps ver1)))
    :enable (nfkd
             decompose-of-later-version
             canonical-order-of-later-version))

  (defruled nfkc-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfkc cps ver2)
                    (nfkc cps ver1)))
    :enable (nfkc
             nfkd-of-later-version
             canonical-compose-of-later-version))

  (defruled nfd-memberp-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfd-memberp cps ver2)
                    (nfd-memberp cps ver1)))
    :enable (nfd-memberp
             nfd-of-later-version))

  (defruled nfc-memberp-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfc-memberp cps ver2)
                    (nfc-memberp cps ver1)))
    :enable (nfc-memberp
             nfc-of-later-version))

  (defruled nfkd-memberp-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfkd-memberp cps ver2)
                    (nfkd-memberp cps ver1)))
    :enable (nfkd-memberp
             nfkd-of-later-version))

  (defruled nfkc-memberp-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (nfkc-memberp cps ver2)
                    (nfkc-memberp cps ver1)))
    :enable (nfkc-memberp
             nfkc-of-later-version))

  (defruled canonical-equivalent-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps1 ver1)
                  (assigned-listp cps2 ver1))
             (equal (canonical-equivalent-p cps1 cps2 ver2)
                    (canonical-equivalent-p cps1 cps2 ver1)))
    :enable (canonical-equivalent-p
             nfd-of-later-version))

  (defruled compatibility-equivalent-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps1 ver1)
                  (assigned-listp cps2 ver1))
             (equal (compatibility-equivalent-p cps1 cps2 ver2)
                    (compatibility-equivalent-p cps1 cps2 ver1)))
    :enable (compatibility-equivalent-p
             nfkd-of-later-version)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stream-safe-across-versions
  :short "For a list of code points
          that are assigned in a version of Unicode,
          being in Stream-Safe Text Format,
          and the result of the Stream-Safe Text Process,
          are the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see stream-safe) for the format and the process.
     Both are defined by Normalization Form KD (NFKD),
     which is compatibility decomposition,
     and by which code points are starters;
     for assigned code points
     neither changes in a later version
     (see @(see normalization-across-versions)).
     So this follows from the stability of normalization,
     and it cannot fail when a version is added
     unless that theorem does."))

  (defruledl leading-non-starter-count-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (leading-non-starter-count cps ver2)
                    (leading-non-starter-count cps ver1)))
    :induct (len cps)
    :enable (leading-non-starter-count
             starter-p-of-later-version
             len))

  (defruledl non-starter-count-after-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (non-starter-count-after count cps ver2)
                    (non-starter-count-after count cps ver1)))
    :induct (non-starter-count-after count cps ver1)
    :expand (non-starter-count-after count cps ver2)
    :enable (non-starter-count-after
             starter-p-of-later-version))

  (defruledl non-starter-runs-within-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (non-starter-runs-within-p count cps ver2)
                    (non-starter-runs-within-p count cps ver1)))
    :induct (non-starter-runs-within-p count cps ver1)
    :expand (non-starter-runs-within-p count cps ver2)
    :enable (non-starter-runs-within-p
             starter-p-of-later-version))

  (defruled stream-safe-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (stream-safe-p cps ver2)
                    (stream-safe-p cps ver1)))
    :enable (stream-safe-p
             nfkd-of-later-version
             non-starter-runs-within-p-of-later-version))

  (defruledl stream-safe-process-from-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (stream-safe-process-from count cps ver2)
                    (stream-safe-process-from count cps ver1)))
    :induct (stream-safe-process-from count cps ver1)
    :expand (stream-safe-process-from count cps ver2)
    :enable (stream-safe-process-from
             nfkd-of-later-version
             leading-non-starter-count-of-later-version
             non-starter-count-after-of-later-version))

  (defruled stream-safe-process-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (equal (stream-safe-process cps ver2)
                    (stream-safe-process cps ver1)))
    :enable (stream-safe-process
             stream-safe-process-from-of-later-version)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection quick-check-across-versions
  :short "The quick check properties of a code point
          that is assigned in a version of Unicode
          are the same in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see quick-check) for the four properties,
     one for each normalization form:
     @('NFD_Quick_Check'), @('NFC_Quick_Check'),
     @('NFKD_Quick_Check') and @('NFKC_Quick_Check').")
   (xdoc::p
    "This holds for the supported versions,
     in the order of @(tsee version<=).
     The stability of normalization
     [Stability, Normalization Stability] implies part of it:
     the values for the two decomposed forms,
     which say whether the code point has a decomposition,
     and the value `no' for the two composed forms,
     which says that the form changes the code point
     (see @(see quick-check-theorems)).
     It does not imply that a `yes' stays a `yes':
     a later version could add a character
     that decomposes into a new character
     followed by an existing mark,
     and the mark would then get the value `maybe'.
     No supported version does that.
     So when a version is added, the theorems for the two composed forms
     can fail without a table being wrong;
     then their conclusions have to be weakened
     to what the standard promises.")
   (xdoc::p
    "The theorems are proved by evaluation on lists of ranges,
     for each pair of versions:
     the code points that are in a table of one version
     and not in the table of the other
     are all unassigned in the earlier version."))

  ;; For each of the six tables: a code point that is assigned
  ;; in the earlier version is in the table of the later version
  ;; exactly when it is in the table of the earlier one.

  (local
   (defmacro def-table-across-versions (table)
     (b* ((changes (acl2::packn-pos (list table '-changes-are-unassigned)
                                    'quick-check))
          (thm (acl2::packn-pos (list 'in- table '-of-later-version)
                                'quick-check)))
       `(progn
          (defrulel ,changes
            (implies (version<= ver1 ver2)
                     (and (equal (ranges-difference
                                  (ranges-difference (,table ver1)
                                                     (,table ver2))
                                  (general-category-ranges
                                   (general-category-unassigned) ver1))
                                 nil)
                          (equal (ranges-difference
                                  (ranges-difference (,table ver2)
                                                     (,table ver1))
                                  (general-category-ranges
                                   (general-category-unassigned) ver1))
                                 nil)))
            :rule-classes nil
            :enable (version<=
                     version-rank
                     ,table
                     general-category-ranges
                     general-category-runs))
          (defruledl ,thm
            (implies (and (version<= ver1 ver2)
                          (assigned-p cp ver1))
                     (equal (code-point-in-ranges-p cp (,table ver2))
                            (code-point-in-ranges-p cp (,table ver1))))
            :enable assigned-p-in-terms-of-ranges
            :disable ((:e general-category-unassigned))
            :use (,changes
                  (:instance
                   code-point-in-ranges-p-when-ranges-difference-is-empty
                   (ranges1 (ranges-difference (,table ver1) (,table ver2)))
                   (ranges2 (general-category-ranges
                             (general-category-unassigned) ver1)))
                  (:instance
                   code-point-in-ranges-p-when-ranges-difference-is-empty
                   (ranges1 (ranges-difference (,table ver2) (,table ver1)))
                   (ranges2 (general-category-ranges
                             (general-category-unassigned) ver1)))))))))

  (local (def-table-across-versions nfd-quick-check-no-ranges))
  (local (def-table-across-versions nfc-quick-check-no-ranges))
  (local (def-table-across-versions nfc-quick-check-maybe-ranges))
  (local (def-table-across-versions nfkd-quick-check-no-ranges))
  (local (def-table-across-versions nfkc-quick-check-no-ranges))
  (local (def-table-across-versions nfkc-quick-check-maybe-ranges))

  (defruled nfd-quick-check-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (nfd-quick-check cp ver2)
                    (nfd-quick-check cp ver1)))
    :enable (nfd-quick-check
             in-nfd-quick-check-no-ranges-of-later-version))

  (defruled nfc-quick-check-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (nfc-quick-check cp ver2)
                    (nfc-quick-check cp ver1)))
    :enable (nfc-quick-check
             in-nfc-quick-check-no-ranges-of-later-version
             in-nfc-quick-check-maybe-ranges-of-later-version))

  (defruled nfkd-quick-check-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (nfkd-quick-check cp ver2)
                    (nfkd-quick-check cp ver1)))
    :enable (nfkd-quick-check
             in-nfkd-quick-check-no-ranges-of-later-version))

  (defruled nfkc-quick-check-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (equal (nfkc-quick-check cp ver2)
                    (nfkc-quick-check cp ver1)))
    :enable (nfkc-quick-check
             in-nfkc-quick-check-no-ranges-of-later-version
             in-nfkc-quick-check-maybe-ranges-of-later-version)))
