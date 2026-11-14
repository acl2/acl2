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
(include-book "range-sets")

(include-book "data/v16.0.0/derived-normalization-props")
(include-book "data/v17.0.0/derived-normalization-props")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix)))

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
     The map is a nat map (see @(see nat-maps))
     whose keys encode pairs of code points: see @(tsee pair-key).
     The encoding puts the second code point of the pair
     in the more significant position.
     Since the second code points of the pairs in the map
     are combining marks and the like, none below @('#x300'),
     looking up a pair whose second code point is small,
     e.g. an ASCII one,
     stops at the first entry of the map."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-composition-exclusion-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          that have the @('Full_Composition_Exclusion') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *full-composition-exclusion-v16.0.0*
                :v17.0.0 *full-composition-exclusion-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-composition-exclusion-p ((cp natp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has
          the @('Full_Composition_Exclusion') property,
          in a version of Unicode."
  (in-range-set-p cp (full-composition-exclusion-set ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pair-key ((first code-point-p) (second code-point-p))
  :returns (key natp :rule-classes :type-prescription)
  :short "Encode a pair of code points as a natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "The encoding is injective,
     and it orders the pairs by their second components first."))
  (+ (* #x110000 (code-point-fix second))
     (code-point-fix first))

  ///

  (defruled pair-key-upper-bound-when-second-below
    (implies (and (< (code-point-fix second) bound)
                  (natp bound))
             (< (pair-key first second)
                (* #x110000 bound)))
    :rule-classes :linear
    :enable (code-point-fix code-point-p)
    :prep-books ((include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define composition-map-p (x)
  :returns (yes/no booleanp)
  :short "Recognize nat maps to scalar values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the maps
     from (encoded) pairs of code points to primary composites."))
  (and (nat-map-p x)
       (composition-map-values-p x))

  :prepwork
  ((define composition-map-values-p ((map nat-map-p))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp map)
         (and (scalar-value-p (cdr (car map)))
              (composition-map-values-p (cdr map))))
     :hooks nil

     ///

     (defruled scalar-value-p-of-nat-map-lookup
       (implies (and (composition-map-values-p map)
                     (nat-map-lookup key map))
                (scalar-value-p (nat-map-lookup key map)))
       :induct t
       :enable nat-map-lookup)))

  ///

  (defrule nat-map-p-when-composition-map-p
    (implies (composition-map-p x)
             (nat-map-p x)))

  (defrule scalar-value-p-of-nat-map-lookup-when-composition-map-p
    (implies (and (composition-map-p map)
                  (nat-map-lookup key map))
             (scalar-value-p (nat-map-lookup key map)))
    :enable scalar-value-p-of-nat-map-lookup))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primary-composites ((decompositions decomposition-map-p)
                            (exclusions range-set-p))
  :returns (map nat-map-p
                :hyp (decomposition-map-p decompositions)
                :hints (("Goal"
                         :induct t
                         :in-theory (enable decomposition-map-p
                                            decomposition-map-entries-p
                                            nat-map-p))))
  :short "The map from pairs of code points to primary composites,
          computed from a map of canonical decomposition mappings
          and from a set of excluded code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each code point of the first map
     that is not in the set
     and whose mapping consists of two code points
     is associated with the key that encodes those two code points.")
   (xdoc::p
    "If two code points had the same mapping,
     only one of them would end up in the result.
     That never happens;
     we check it by comparing the size of the result
     with the number of code points that qualify:
     see @(tsee primary-composite-count)."))
  (b* (((when (endp decompositions)) nil)
       (map (primary-composites (cdr decompositions) exclusions))
       (composite (car (car decompositions)))
       (mapping (cdr (car decompositions)))
       ((unless (and (consp (cdr mapping))
                     (endp (cddr mapping))
                     (not (in-range-set-p composite exclusions))))
        map))
    (nat-map-put (pair-key (first mapping) (second mapping))
                 composite
                 map))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable decomposition-map-p
                                           decomposition-map-entries-p
                                           nat-map-p))))

;;;;;;;;;;;;;;;;;;;;

(define primary-composite-count ((decompositions decomposition-map-p)
                                 (exclusions range-set-p))
  :returns (count natp :rule-classes :type-prescription)
  :short "The number of primary composites
          whose mappings consist of two code points."
  (b* (((when (endp decompositions)) 0)
       (count (primary-composite-count (cdr decompositions) exclusions))
       (composite (car (car decompositions)))
       (mapping (cdr (car decompositions)))
       ((unless (and (consp (cdr mapping))
                     (endp (cddr mapping))
                     (not (in-range-set-p composite exclusions))))
        count))
    (+ 1 count))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable decomposition-map-p
                                           decomposition-map-entries-p
                                           nat-map-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection composition-tables
  :short "The tables of the pairs that compose, for each version."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each table we check that it has the type of the composition maps,
     in particular that it is sorted,
     and that no two primary composites have the same mapping."))

  ;; Unicode 16.0.0:

  (defconst *composition-v16.0.0*
    (primary-composites *canonical-decomposition-v16.0.0*
                        *full-composition-exclusion-v16.0.0*))

  (assert-event
   (and (composition-map-p *composition-v16.0.0*)
        (equal (len *composition-v16.0.0*)
               (primary-composite-count
                *canonical-decomposition-v16.0.0*
                *full-composition-exclusion-v16.0.0*))))

  ;; Unicode 17.0.0:

  (defconst *composition-v17.0.0*
    (primary-composites *canonical-decomposition-v17.0.0*
                        *full-composition-exclusion-v17.0.0*))

  (assert-event
   (and (composition-map-p *composition-v17.0.0*)
        (equal (len *composition-v17.0.0*)
               (primary-composite-count
                *canonical-decomposition-v17.0.0*
                *full-composition-exclusion-v17.0.0*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define composition-map ((ver versionp))
  :returns (map composition-map-p)
  :short "The map from (encoded) pairs of code points
          to the primary composites they compose to,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The map does not have the pairs
     that compose to precomposed Hangul syllables."))
  (version-case ver
                :v16.0.0 *composition-v16.0.0*
                :v17.0.0 *composition-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define composition ((first code-point-p)
                     (second code-point-p)
                     (ver versionp))
  :returns
  (composite?
   acl2::maybe-natp
   :rule-classes :type-prescription
   :hints
   (("Goal"
     :in-theory
     (e/d (acl2::maybe-natp)
          (scalar-value-p-of-nat-map-lookup-when-composition-map-p))
     :use (:instance scalar-value-p-of-nat-map-lookup-when-composition-map-p
                     (key (pair-key first second))
                     (map (composition-map ver))))))
  :short "The code point, if any, that two code points compose to,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the precomposed Hangul syllable
     or the primary composite
     that is canonically equivalent to the two code points in this order;
     it is @('nil') if there is none."))
  (b* ((first (code-point-fix first))
       (second (code-point-fix second)))
    (or (hangul-composition first second)
        (nat-map-lookup (pair-key first second)
                        (composition-map ver))))
  :guard-hints (("Goal" :in-theory (enable code-point-p)))

  ///

  (defrule scalar-value-p-of-composition
    (implies (composition first second ver)
             (scalar-value-p (composition first second ver))))

  (defrule code-point-p-of-composition
    (implies (composition first second ver)
             (code-point-p (composition first second ver))))

  (defruled composition-when-second-below-300
    (implies (< (code-point-fix second) #x300)
             (equal (composition first second ver)
                    nil))
    :enable (hangul-composition-when-not-hangul-v-p-and-not-hangul-t-p
             hangul-v-p
             hangul-t-p
             composition-map
             nat-map-lookup-when-below-first)
    :use (:instance pair-key-upper-bound-when-second-below
                    (first (code-point-fix first))
                    (second (code-point-fix second))
                    (bound #x300))))
