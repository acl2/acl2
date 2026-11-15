; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "decompositions")
(include-book "ranges")

(include-book "data/v16.0.0/derived-normalization-props")
(include-book "data/v17.0.0/derived-normalization-props")

(include-book "std/util/defconsts" :dir :system)

(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ compositions
  :parents (normalization)
  :short "Primary composites, and the pairs that compose to them."
  :long
  (xdoc::topstring
   (xdoc::p
    "The normalization forms C and KC replace
     certain pairs of code points by single code points.
     A pair is replaced by a code point
     if that code point is a primary composite [Unicode, D114]
     whose canonical decomposition mapping is the pair;
     also, the pairs of jamo that make up a Hangul syllable
     are replaced as described in @(see hangul).")
   (xdoc::p
    "A primary composite is a code point
     that has a canonical decomposition mapping
     and that does not have
     the @('Full_Composition_Exclusion') property [Unicode, D113].
     That property is derived:
     it holds for the code points listed in
     the file @('CompositionExclusions.txt'),
     for those whose canonical mapping is a single code point,
     and for those whose canonical mapping starts with a non-starter.
     We take it from the file @('DerivedNormalizationProps.txt')
     of the Unicode Character Database, for each supported version;
     we do not recompute it.
     (The generator of the tables does recompute it,
     to check the three files involved against each other.)")
   (xdoc::p
    "The Unicode Character Database
     does not have the map from pairs to primary composites.
     We compute it from the canonical decomposition mappings
     and from the exclusions,
     once for each supported version, when this book is certified:
     see @(tsee primary-composites).
     The map is a tree map whose keys are pairs of code points:
     see @(tsee composition-map)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-composition-exclusion-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Full_Composition_Exclusion') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *full-composition-exclusion-v16.0.0*
                :v17.0.0 *full-composition-exclusion-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-composition-exclusion-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has
          the @('Full_Composition_Exclusion') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (full-composition-exclusion-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod code-point-pair
  :short "Fixtype of pairs of code points."
  ((first code-point)
   (second code-point))
  :pred code-point-pair-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deftreemap composition-map
  :short "Fixtype of maps from pairs of code points to scalar values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the map
     from the pairs of code points that compose
     to the primary composites that they compose to."))
  :key-type code-point-pair
  :val-type scalar-value
  :pred composition-mapp)

;;;;;;;;;;;;;;;;;;;;

(define composition-map-lookup ((first code-point-p)
                                (second code-point-p)
                                (map composition-mapp))
  :returns (composite? scalar-value-option-p)
  :short "Look up a pair of code points in a map of compositions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the pair is not in the map."))
  (b* (((mv in? composite)
        (treemap::lookup? (code-point-pair first second)
                          (composition-map-fix map))))
    (if in? composite nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primary-composites ((cps code-point-listp)
                            (mappings decomposition-mapp)
                            (exclusions range-listp)
                            (map composition-mapp))
  :returns (new-map composition-mapp :hints (("Goal" :induct t)))
  :short "Add to a map of compositions
          the primary composites among the code points of a list,
          given a map of canonical decomposition mappings
          and the ranges of the excluded code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each code point of the list
     that is not excluded
     and whose mapping consists of two code points
     is associated, in the resulting map,
     with the pair of those two code points.")
   (xdoc::p
    "If two code points had the same mapping,
     only one of them would end up in the result.
     That never happens;
     we check it by comparing the size of the result
     with the number of code points that qualify:
     see @(tsee primary-composite-count).")
   (xdoc::p
    "Surrogates have no mappings,
     so the test that the code point is a scalar value
     never fails on the tables;
     it is there so that the type of the result
     does not depend on that."))
  (b* ((map (composition-map-fix map))
       ((when (endp cps)) map)
       (cp (code-point-fix (car cps)))
       (mapping (decomposition-map-lookup cp mappings))
       (map (if (and (equal (len mapping) 2)
                     (scalar-value-p cp)
                     (not (code-point-in-ranges-p cp exclusions)))
                (treemap::update (code-point-pair (first mapping)
                                                  (second mapping))
                                 cp
                                 map)
              map)))
    (primary-composites (cdr cps) mappings exclusions map))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable len))))

;;;;;;;;;;;;;;;;;;;;

(define primary-composite-count ((cps code-point-listp)
                                 (mappings decomposition-mapp)
                                 (exclusions range-listp)
                                 (count natp))
  :returns (new-count natp
                      :rule-classes (:rewrite :type-prescription)
                      :hints (("Goal" :induct t :in-theory (enable nfix))))
  :short "Add to a number the number of primary composites,
          among the code points of a list,
          whose mappings consist of two code points."
  (b* ((count (lnfix count))
       ((when (endp cps)) count)
       (cp (code-point-fix (car cps)))
       (mapping (decomposition-map-lookup cp mappings))
       (count (if (and (equal (len mapping) 2)
                       (scalar-value-p cp)
                       (not (code-point-in-ranges-p cp exclusions)))
                  (+ 1 count)
                count)))
    (primary-composite-count (cdr cps) mappings exclusions count))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection composition-tables
  :short "The tables of the pairs that compose, for each version."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each table we check that it has the type of the composition maps,
     and that no two primary composites have the same mapping.")
   (xdoc::p
    "The tables are defined with @(tsee defconsts), not @(tsee defconst):
     they are computed when this book is certified
     and kept in its certificate,
     so they are not computed again each time the book is included."))

  ;; Unicode 16.0.0:

  (defconsts *composition-v16.0.0*
    (primary-composites (all-code-points)
                        *canonical-decomposition-mapping-v16.0.0*
                        *full-composition-exclusion-v16.0.0*
                        (treemap::empty)))

  (assert-event
   (and (composition-mapp *composition-v16.0.0*)
        (equal (treemap::size *composition-v16.0.0*)
               (primary-composite-count
                (all-code-points)
                *canonical-decomposition-mapping-v16.0.0*
                *full-composition-exclusion-v16.0.0*
                0))))

  ;; Unicode 17.0.0:

  (defconsts *composition-v17.0.0*
    (primary-composites (all-code-points)
                        *canonical-decomposition-mapping-v17.0.0*
                        *full-composition-exclusion-v17.0.0*
                        (treemap::empty)))

  (assert-event
   (and (composition-mapp *composition-v17.0.0*)
        (equal (treemap::size *composition-v17.0.0*)
               (primary-composite-count
                (all-code-points)
                *canonical-decomposition-mapping-v17.0.0*
                *full-composition-exclusion-v17.0.0*
                0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compositions ((ver versionp))
  :returns (map composition-mapp)
  :short "The map from pairs of code points
          to the primary composites they compose to,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The map does not have the pairs
     that compose to precomposed Hangul syllables."))
  (version-case ver
                :v16.0.0 *composition-v16.0.0*
                :v17.0.0 *composition-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define composition ((first code-point-p)
                     (second code-point-p)
                     (ver versionp))
  :returns (composite? scalar-value-option-p)
  :short "The code point, if any, that two code points compose to,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the precomposed Hangul syllable
     or the primary composite
     that is canonically equivalent to the two code points in this order;
     it is @('nil') if there is none."))
  (or (hangul-composition first second)
      (composition-map-lookup first second (compositions ver)))
  :hooks (:fix)

  ///

  (defrule scalar-value-p-of-composition
    (implies (composition first second ver)
             (scalar-value-p (composition first second ver)))
    :use scalar-value-option-p-of-composition
    :enable scalar-value-option-p
    :disable (composition scalar-value-option-p-of-composition))

  (defrule code-point-p-of-composition
    (implies (composition first second ver)
             (code-point-p (composition first second ver)))
    :disable composition)

  ;; We prove the next theorem by checking, for each version,
  ;; that the second code point of every pair in the map
  ;; is not below #x300.
  ;; The check is that the map has a type like the one above,
  ;; but whose keys are restricted to such pairs.

  (local
   (define later-pair-p (x)
     :returns (yes/no booleanp)
     (and (code-point-pair-p x)
          (<= #x300 (code-point-pair->second x)))))

  (local
   (std::deffixer later-pair-fix
     :pred later-pair-p
     :body-fix (code-point-pair 0 #x300)))

  (local
   (fty::deffixtype later-pair
     :pred later-pair-p
     :fix later-pair-fix
     :equiv later-pair-equiv
     :define t))

  (local
   (fty::deftreemap later-composition-map
     :key-type later-pair
     :val-type scalar-value
     :pred later-composition-mapp))

  (defrulel later-composition-mapp-of-compositions
    (later-composition-mapp (compositions ver))
    :enable compositions)

  (defruled composition-when-second-below-300
    (implies (< (code-point-fix second) #x300)
             (equal (composition first second ver)
                    nil))
    :enable (hangul-composition-when-not-hangul-v-p-and-not-hangul-t-p
             hangul-v-p
             hangul-t-p
             composition-map-lookup
             later-pair-p)
    :use (:instance not-in-later-composition-mapp-when-not-later-pair-p
                    (acl2::a (code-point-pair first second))
                    (x (compositions ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection composition-of-decomposition-mapping
  :short "Composing the canonical decomposition mapping
          of a primary composite, or of a precomposed Hangul syllable,
          gives that code point back."
  :long
  (xdoc::topstring
   (xdoc::p
    "This holds for the code points
     whose canonical decomposition mappings consist of two code points
     and that do not have the @('Full_Composition_Exclusion') property.
     For the precomposed Hangul syllables it is a theorem about arithmetic:
     see @(see hangul-theorems).
     For the other code points
     we prove it by checking it on every code point, for each version."))

  (local
   (define pair-ok ((cp code-point-p)
                    (mappings decomposition-mapp)
                    (exclusions range-listp)
                    (map composition-mapp))
     :returns (yes/no booleanp)
     (b* ((mapping (decomposition-map-lookup cp mappings)))
       (or (not (equal (len mapping) 2))
           (code-point-in-ranges-p cp exclusions)
           (and (not (hangul-composition (first mapping) (second mapping)))
                (equal (composition-map-lookup (first mapping)
                                               (second mapping)
                                               map)
                       (code-point-fix cp)))))
     :guard-hints (("Goal" :in-theory (enable len)))))

  (local
   (std::deflist pair-ok-listp (x mappings exclusions map)
     :guard (and (code-point-listp x)
                 (decomposition-mapp mappings)
                 (range-listp exclusions)
                 (composition-mapp map))
     (pair-ok x mappings exclusions map)))

  (defrulel pair-ok-listp-of-all-code-points
    (pair-ok-listp (all-code-points)
                   (canonical-mappings ver)
                   (full-composition-exclusion-ranges ver)
                   (compositions ver))
    :enable (canonical-mappings
             full-composition-exclusion-ranges
             compositions
             (:e all-code-points))
    :disable pair-ok-listp-of-cons)

  (defruled composition-of-canonical-mapping
    (b* ((mapping (decomposition-map-lookup cp (canonical-mappings ver))))
      (implies (and (code-point-p cp)
                    (equal (len mapping) 2)
                    (not (full-composition-exclusion-p cp ver)))
               (equal (composition (first mapping) (second mapping) ver)
                      cp)))
    :enable (composition
             full-composition-exclusion-p
             pair-ok)
    :use (:instance pair-ok-when-member-equal-of-pair-ok-listp
                    (acl2::a cp)
                    (x (all-code-points))
                    (mappings (canonical-mappings ver))
                    (exclusions (full-composition-exclusion-ranges ver))
                    (map (compositions ver))))

  (defrule composition-of-decomposition-mapping
    (b* (((mv canonical mapping) (decomposition-mapping cp ver)))
      (implies (and (code-point-p cp)
                    canonical
                    (equal (len mapping) 2)
                    (not (full-composition-exclusion-p cp ver)))
               (equal (composition (first mapping) (second mapping) ver)
                      cp)))
    :enable (decomposition-mapping
             composition
             hangul-composition-of-hangul-syllable-decomposition-mapping)
    :use composition-of-canonical-mapping))
