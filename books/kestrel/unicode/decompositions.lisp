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
(include-book "nat-maps")
(include-book "hangul")

(include-book "data/v16.0.0/unicode-data")
(include-book "data/v17.0.0/unicode-data")

(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defconsts" :dir :system)

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ decompositions
  :parents (normalization)
  :short "Decomposition mappings and full decompositions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Decomposition_Mapping') property
     maps some code points to short sequences of code points
     that they are equivalent to.
     A mapping is either canonical or a compatibility one:
     a compatibility mapping has, in the Unicode Character Database,
     a tag that says what kind of formatting it loses
     (which we do not record).
     We take the mappings from the file @('UnicodeData.txt')
     of the Unicode Character Database, for each supported version.
     That file does not list the canonical mappings
     of the precomposed Hangul syllables,
     which are given by an algorithm: see @(see hangul).")
   (xdoc::p
    "A mapping may contain code points that have mappings themselves.
     The full decomposition of a code point
     is the result of applying the mappings repeatedly,
     until no code point has one:
     the canonical decomposition [Unicode, D68] uses
     only the canonical mappings (and the Hangul algorithm),
     while the compatibility decomposition [Unicode, D65] uses
     all the mappings.
     (The names are slightly misleading:
     the compatibility decomposition of a code point
     that has only canonical mappings
     is its canonical decomposition.)")
   (xdoc::p
    "We compute the full decompositions of
     all the code points that have mappings,
     once for each supported version, when this book is certified,
     and we keep them in tables;
     the function @(tsee decomposition) looks a code point up there.
     The computation is by the function @(tsee expand-decomposition),
     which is recursive and so needs a bound on the depth of the recursion
     in order to be admitted.
     We check, by evaluation, that the bound was large enough,
     i.e. that no code point in the tables can be decomposed further:
     see @(tsee full-decomposition-map-closed-p)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-decomposition-map ((ver versionp))
  :returns (map decomposition-map-p)
  :short "The map from code points
          to their canonical decomposition mappings,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The map does not have the precomposed Hangul syllables."))
  (version-case ver
                :v16.0.0 *canonical-decomposition-v16.0.0*
                :v17.0.0 *canonical-decomposition-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define compatibility-decomposition-map ((ver versionp))
  :returns (map decomposition-map-p)
  :short "The map from code points
          to their compatibility decomposition mappings,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *compatibility-decomposition-v16.0.0*
                :v17.0.0 *compatibility-decomposition-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expand-decomposition ((cps scalar-value-listp)
                              (canonical decomposition-map-p)
                              (compat decomposition-map-p)
                              (depth natp))
  :returns (expansion scalar-value-listp
                      :hyp (and (scalar-value-listp cps)
                                (decomposition-map-p canonical)
                                (decomposition-map-p compat))
                      :hints (("Goal" :induct t)))
  :short "Replace the code points of a list by their decompositions,
          repeatedly."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each code point that is a precomposed Hangul syllable
     is replaced by its decomposition into jamo.
     Each code point that has a mapping in one of the two given maps
     is replaced by the expansion of that mapping.
     The other code points are left alone.")
   (xdoc::p
    "The first map is for the canonical mappings
     and the second one is for the compatibility mappings;
     no code point has both.
     Passing an empty second map gives canonical decompositions.")
   (xdoc::p
    "The depth bounds the recursion on the mappings:
     at depth 0, a code point is left alone even if it has a mapping.
     So the result is fully decomposed only if the depth is large enough;
     @(tsee fully-decomposed-p) is used to check that it is."))
  (b* (((when (endp cps)) nil)
       (cp (car cps))
       (rest (expand-decomposition (cdr cps) canonical compat depth))
       ((when (zp depth)) (cons cp rest))
       ((when (hangul-syllable-p cp))
        (append (hangul-syllable-decomposition cp) rest))
       (mapping (or (nat-map-lookup cp canonical)
                    (nat-map-lookup cp compat)))
       ((unless mapping) (cons cp rest)))
    (append (expand-decomposition mapping canonical compat (1- depth))
            rest))
  :measure (acl2::two-nats-measure depth (len cps))
  :hooks nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection decomposition-expansion-depth
  :short "The depth to which mappings are expanded
          to compute the full decompositions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the supported versions of Unicode, a depth of 3 is enough.
     If a future version needs more than the depth we use,
     the check that the tables are fully decomposed will fail
     when this book is certified,
     and this constant will have to be increased."))

  (defconst *decomposition-expansion-depth* 8))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-decomposition-map ((entries decomposition-map-p)
                                (canonical decomposition-map-p)
                                (compat decomposition-map-p))
  :returns (full true-listp :rule-classes :type-prescription)
  :short "Expand all the mappings of a map."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result associates each code point of the map
     with the expansion of its mapping.
     See @(tsee expand-decomposition) for the other two arguments."))
  (cond ((endp entries) nil)
        (t (cons (cons (car (car entries))
                       (expand-decomposition (cdr (car entries))
                                             canonical
                                             compat
                                             *decomposition-expansion-depth*))
                 (full-decomposition-map (cdr entries) canonical compat))))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable decomposition-map-p
                                           decomposition-map-entries-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-map-put-all ((entries nat-map-p) (map nat-map-p))
  :returns (new-map nat-map-p
                    :hyp (and (nat-map-p entries)
                              (nat-map-p map))
                    :hints (("Goal"
                             :induct t
                             :in-theory (enable cdar-when-nat-map-p))))
  :short "Add all the entries of a nat map to another nat map."
  (cond ((endp entries) map)
        (t (nat-map-put-all (cdr entries)
                            (nat-map-put (car (car entries))
                                         (cdr (car entries))
                                         map))))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable cdar-when-nat-map-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fully-decomposed-p ((cps scalar-value-listp)
                            (canonical decomposition-map-p)
                            (compat decomposition-map-p))
  :returns (yes/no booleanp)
  :short "Check that no code point of a list
          is a precomposed Hangul syllable or has a mapping."
  (or (endp cps)
      (and (not (hangul-syllable-p (car cps)))
           (not (nat-map-lookup (car cps) canonical))
           (not (nat-map-lookup (car cps) compat))
           (fully-decomposed-p (cdr cps) canonical compat)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

(define full-decomposition-map-closed-p ((full decomposition-map-p)
                                         (canonical decomposition-map-p)
                                         (compat decomposition-map-p))
  :returns (yes/no booleanp)
  :short "Check that all the values of a map of full decompositions
          are fully decomposed."
  (or (endp full)
      (and (fully-decomposed-p (cdr (car full)) canonical compat)
           (full-decomposition-map-closed-p (cdr full) canonical compat)))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable decomposition-map-p
                                           decomposition-map-entries-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection full-decomposition-tables
  :short "The tables of the full decompositions, for each version."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each version there are two tables.
     The first one has the canonical decompositions
     of the code points that have canonical mappings.
     The second one has the compatibility decompositions
     of the code points that have mappings of either kind.
     Neither has the precomposed Hangul syllables.")
   (xdoc::p
    "For each table we check that it has the type of the decomposition maps,
     in particular that it is sorted,
     and that it is fully decomposed.")
   (xdoc::p
    "The tables are defined with @(tsee defconsts), not @(tsee defconst):
     they are computed when this book is certified
     and kept in its certificate,
     so they are not computed again each time the book is included."))

  ;; Unicode 16.0.0:

  (defconsts *canonical-full-decomposition-v16.0.0*
    (full-decomposition-map *canonical-decomposition-v16.0.0*
                            *canonical-decomposition-v16.0.0*
                            nil))

  (defconsts *compatibility-full-decomposition-v16.0.0*
    (full-decomposition-map
     (nat-map-put-all *compatibility-decomposition-v16.0.0*
                      *canonical-decomposition-v16.0.0*)
     *canonical-decomposition-v16.0.0*
     *compatibility-decomposition-v16.0.0*))

  (assert-event
   (and (decomposition-map-p *canonical-full-decomposition-v16.0.0*)
        (full-decomposition-map-closed-p
         *canonical-full-decomposition-v16.0.0*
         *canonical-decomposition-v16.0.0*
         nil)
        (equal (len *canonical-full-decomposition-v16.0.0*)
               (len *canonical-decomposition-v16.0.0*))))

  (assert-event
   (and (decomposition-map-p *compatibility-full-decomposition-v16.0.0*)
        (full-decomposition-map-closed-p
         *compatibility-full-decomposition-v16.0.0*
         *canonical-decomposition-v16.0.0*
         *compatibility-decomposition-v16.0.0*)
        (equal (len *compatibility-full-decomposition-v16.0.0*)
               (+ (len *canonical-decomposition-v16.0.0*)
                  (len *compatibility-decomposition-v16.0.0*)))))

  ;; Unicode 17.0.0:

  (defconsts *canonical-full-decomposition-v17.0.0*
    (full-decomposition-map *canonical-decomposition-v17.0.0*
                            *canonical-decomposition-v17.0.0*
                            nil))

  (defconsts *compatibility-full-decomposition-v17.0.0*
    (full-decomposition-map
     (nat-map-put-all *compatibility-decomposition-v17.0.0*
                      *canonical-decomposition-v17.0.0*)
     *canonical-decomposition-v17.0.0*
     *compatibility-decomposition-v17.0.0*))

  (assert-event
   (and (decomposition-map-p *canonical-full-decomposition-v17.0.0*)
        (full-decomposition-map-closed-p
         *canonical-full-decomposition-v17.0.0*
         *canonical-decomposition-v17.0.0*
         nil)
        (equal (len *canonical-full-decomposition-v17.0.0*)
               (len *canonical-decomposition-v17.0.0*))))

  (assert-event
   (and (decomposition-map-p *compatibility-full-decomposition-v17.0.0*)
        (full-decomposition-map-closed-p
         *compatibility-full-decomposition-v17.0.0*
         *canonical-decomposition-v17.0.0*
         *compatibility-decomposition-v17.0.0*)
        (equal (len *compatibility-full-decomposition-v17.0.0*)
               (+ (len *canonical-decomposition-v17.0.0*)
                  (len *compatibility-decomposition-v17.0.0*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-full-decomposition-map ((ver versionp))
  :returns (map decomposition-map-p)
  :short "The map from the code points that have canonical mappings
          to their canonical decompositions,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *canonical-full-decomposition-v16.0.0*
                :v17.0.0 *canonical-full-decomposition-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define compatibility-full-decomposition-map ((ver versionp))
  :returns (map decomposition-map-p)
  :short "The map from the code points that have mappings
          to their compatibility decompositions,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *compatibility-full-decomposition-v16.0.0*
                :v17.0.0 *compatibility-full-decomposition-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decomposition-mapping ((cp natp) (ver versionp))
  :returns (mv (canonical booleanp)
               (mapping scalar-value-listp))
  :short "The @('Decomposition_Mapping') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the property itself: the mapping is not expanded.
     For a precomposed Hangul syllable
     it is the one of @(tsee hangul-syllable-decomposition-mapping);
     for the other code points
     it is the one in the file @('UnicodeData.txt').
     The first result says whether the mapping is canonical;
     it is @('nil') if the mapping is a compatibility one
     or if there is no mapping.
     The second result is the mapping,
     or @('nil') if the code point has none
     (the standard says that such a code point maps to itself).")
   (xdoc::p
    "This function is not used by normalization,
     which uses @(tsee decomposition) instead."))
  (b* ((cp (lnfix cp))
       ((when (hangul-syllable-p cp))
        (mv t (hangul-syllable-decomposition-mapping cp)))
       (canonical (nat-map-lookup cp (canonical-decomposition-map ver)))
       ((when canonical) (mv t canonical)))
    (mv nil (nat-map-lookup cp (compatibility-decomposition-map ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decomposition ((cp code-point-p) (compat booleanp) (ver versionp))
  :returns (cps code-point-listp
                :hints (("Goal" :in-theory (enable code-point-fix
                                                   code-point-p))))
  :short "The canonical or compatibility decomposition of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the full decomposition:
     canonical if the flag is @('nil'), compatibility otherwise.
     A code point that has no decomposition
     is returned as a list of one element."))
  (b* ((cp (code-point-fix cp))
       ((when (hangul-syllable-p cp)) (hangul-syllable-decomposition cp))
       (full (nat-map-lookup cp
                             (if compat
                                 (compatibility-full-decomposition-map ver)
                               (canonical-full-decomposition-map ver)))))
    (or full
        (list cp)))
  :guard-hints (("Goal" :in-theory (enable code-point-p)))

  ///

  (defrule true-listp-of-decomposition
    (true-listp (decomposition cp compat ver))
    :rule-classes :type-prescription
    :use code-point-listp-of-decomposition
    :disable (decomposition code-point-listp-of-decomposition))

  (defrule consp-of-decomposition
    (consp (decomposition cp compat ver))
    :rule-classes :type-prescription)

  (defrule scalar-value-listp-of-decomposition
    (implies (scalar-value-p cp)
             (scalar-value-listp (decomposition cp compat ver))))

  (defruled decomposition-when-below-a0
    (implies (and (code-point-p cp)
                  (< cp #xA0))
             (equal (decomposition cp compat ver)
                    (list cp)))
    :enable (hangul-syllable-p
             canonical-full-decomposition-map
             compatibility-full-decomposition-map
             nat-map-lookup-when-below-first
             nfix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decompose ((cps code-point-listp) (compat booleanp) (ver versionp))
  :returns (new-cps code-point-listp)
  :short "Replace the code points of a list by their
          canonical or compatibility decompositions,
          in a version of Unicode."
  (cond ((endp cps) nil)
        (t (append (decomposition (car cps) compat ver)
                   (decompose (cdr cps) compat ver))))

  ///

  (defrule scalar-value-listp-of-decompose
    (implies (scalar-value-listp cps)
             (scalar-value-listp (decompose cps compat ver)))
    :induct t)

  (defruled decompose-when-all-below-a0
    (implies (and (code-point-listp cps)
                  (code-points-below-p cps #xA0))
             (equal (decompose cps compat ver)
                    cps))
    :induct t
    :enable (code-points-below-p decomposition-when-below-a0)))
