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
(include-book "maps")
(include-book "hangul")

(include-book "data/v16.0.0/unicode-data")
(include-book "data/v17.0.0/unicode-data")

(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defconsts" :dir :system)

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

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
     see @(tsee full-decompositions-closed-p)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-mappings ((ver versionp))
  :returns (map decomposition-mapp)
  :short "The map from code points
          to their canonical decomposition mappings,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The map does not have the precomposed Hangul syllables."))
  (version-case ver
                :v16.0.0 *canonical-decomposition-mapping-v16.0.0*
                :v17.0.0 *canonical-decomposition-mapping-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define compatibility-mappings ((ver versionp))
  :returns (map decomposition-mapp)
  :short "The map from code points
          to their compatibility decomposition mappings,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *compatibility-decomposition-mapping-v16.0.0*
                :v17.0.0 *compatibility-decomposition-mapping-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decomposition-mapping ((cp code-point-p) (ver versionp))
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
  (b* ((cp (code-point-fix cp))
       ((when (hangul-syllable-p cp))
        (mv t (hangul-syllable-decomposition-mapping cp)))
       (canonical (decomposition-map-lookup cp (canonical-mappings ver)))
       ((when canonical) (mv t canonical)))
    (mv nil (decomposition-map-lookup cp (compatibility-mappings ver))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(define expand-decomposition ((cps scalar-value-listp)
                              (canonical decomposition-mapp)
                              (compat decomposition-mapp)
                              (depth natp))
  :returns (expansion scalar-value-listp :hints (("Goal" :induct t)))
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
       (cp (scalar-value-fix (car cps)))
       (rest (expand-decomposition (cdr cps) canonical compat depth))
       ((when (zp depth)) (cons cp rest))
       ((when (hangul-syllable-p cp))
        (append (hangul-syllable-decomposition cp) rest))
       (mapping (or (decomposition-map-lookup cp canonical)
                    (decomposition-map-lookup cp compat)))
       ((unless mapping) (cons cp rest)))
    (append (expand-decomposition mapping canonical compat (1- depth))
            rest))
  :measure (acl2::two-nats-measure depth (len cps))
  :hooks nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fully-decomposed-p ((cps scalar-value-listp)
                            (canonical decomposition-mapp)
                            (compat decomposition-mapp))
  :returns (yes/no booleanp)
  :short "Check that no code point of a list
          is a precomposed Hangul syllable or has a mapping."
  (b* (((when (endp cps)) t)
       (cp (scalar-value-fix (car cps))))
    (and (not (hangul-syllable-p cp))
         (not (decomposition-map-lookup cp canonical))
         (not (decomposition-map-lookup cp compat))
         (fully-decomposed-p (cdr cps) canonical compat)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-decompositions ((cps code-point-listp)
                             (canonical decomposition-mapp)
                             (compat decomposition-mapp)
                             (full decomposition-mapp))
  :returns (new-full decomposition-mapp :hints (("Goal" :induct t)))
  :short "Add to a map the full decompositions
          of the code points of a list that have mappings."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each code point of the list that has a mapping
     is associated, in the resulting map,
     with the expansion of its mapping.
     See @(tsee expand-decomposition)
     for the two maps of mappings."))
  (b* ((full (decomposition-map-fix full))
       ((when (endp cps)) full)
       (cp (code-point-fix (car cps)))
       (mapping (or (decomposition-map-lookup cp canonical)
                    (decomposition-map-lookup cp compat)))
       (full (if mapping
                 (treemap::update cp
                                  (expand-decomposition
                                   mapping
                                   canonical
                                   compat
                                   *decomposition-expansion-depth*)
                                  full)
               full)))
    (full-decompositions (cdr cps) canonical compat full))
  :hooks nil
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define full-decompositions-closed-p ((cps code-point-listp)
                                      (full decomposition-mapp)
                                      (canonical decomposition-mapp)
                                      (compat decomposition-mapp))
  :returns (yes/no booleanp)
  :short "Check that the full decompositions, in a map,
          of the code points of a list
          are fully decomposed."
  (b* (((when (endp cps)) t))
    (and (fully-decomposed-p (decomposition-map-lookup (car cps) full)
                             canonical
                             compat)
         (full-decompositions-closed-p (cdr cps) full canonical compat)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection decomposition-tables
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
     that it has as many code points as the mappings it is computed from,
     and that it is fully decomposed.")
   (xdoc::p
    "The tables are defined with @(tsee defconsts), not @(tsee defconst):
     they are computed when this book is certified
     and kept in its certificate,
     so they are not computed again each time the book is included."))

  ;; Unicode 16.0.0:

  (defconsts *canonical-decomposition-v16.0.0*
    (full-decompositions (all-code-points)
                         *canonical-decomposition-mapping-v16.0.0*
                         (treemap::empty)
                         (treemap::empty)))

  (defconsts *compatibility-decomposition-v16.0.0*
    (full-decompositions (all-code-points)
                         *canonical-decomposition-mapping-v16.0.0*
                         *compatibility-decomposition-mapping-v16.0.0*
                         (treemap::empty)))

  (assert-event
   (and (decomposition-mapp *canonical-decomposition-v16.0.0*)
        (full-decompositions-closed-p
         (all-code-points)
         *canonical-decomposition-v16.0.0*
         *canonical-decomposition-mapping-v16.0.0*
         (treemap::empty))
        (equal (treemap::size *canonical-decomposition-v16.0.0*)
               (treemap::size *canonical-decomposition-mapping-v16.0.0*))))

  (assert-event
   (and (decomposition-mapp *compatibility-decomposition-v16.0.0*)
        (full-decompositions-closed-p
         (all-code-points)
         *compatibility-decomposition-v16.0.0*
         *canonical-decomposition-mapping-v16.0.0*
         *compatibility-decomposition-mapping-v16.0.0*)
        (equal (treemap::size *compatibility-decomposition-v16.0.0*)
               (+ (treemap::size
                   *canonical-decomposition-mapping-v16.0.0*)
                  (treemap::size
                   *compatibility-decomposition-mapping-v16.0.0*)))))

  ;; Unicode 17.0.0:

  (defconsts *canonical-decomposition-v17.0.0*
    (full-decompositions (all-code-points)
                         *canonical-decomposition-mapping-v17.0.0*
                         (treemap::empty)
                         (treemap::empty)))

  (defconsts *compatibility-decomposition-v17.0.0*
    (full-decompositions (all-code-points)
                         *canonical-decomposition-mapping-v17.0.0*
                         *compatibility-decomposition-mapping-v17.0.0*
                         (treemap::empty)))

  (assert-event
   (and (decomposition-mapp *canonical-decomposition-v17.0.0*)
        (full-decompositions-closed-p
         (all-code-points)
         *canonical-decomposition-v17.0.0*
         *canonical-decomposition-mapping-v17.0.0*
         (treemap::empty))
        (equal (treemap::size *canonical-decomposition-v17.0.0*)
               (treemap::size *canonical-decomposition-mapping-v17.0.0*))))

  (assert-event
   (and (decomposition-mapp *compatibility-decomposition-v17.0.0*)
        (full-decompositions-closed-p
         (all-code-points)
         *compatibility-decomposition-v17.0.0*
         *canonical-decomposition-mapping-v17.0.0*
         *compatibility-decomposition-mapping-v17.0.0*)
        (equal (treemap::size *compatibility-decomposition-v17.0.0*)
               (+ (treemap::size
                   *canonical-decomposition-mapping-v17.0.0*)
                  (treemap::size
                   *compatibility-decomposition-mapping-v17.0.0*))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-decompositions ((ver versionp))
  :returns (map decomposition-mapp)
  :short "The map from the code points that have canonical mappings
          to their canonical decompositions,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *canonical-decomposition-v16.0.0*
                :v17.0.0 *canonical-decomposition-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define compatibility-decompositions ((ver versionp))
  :returns (map decomposition-mapp)
  :short "The map from the code points that have mappings
          to their compatibility decompositions,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *compatibility-decomposition-v16.0.0*
                :v17.0.0 *compatibility-decomposition-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decomposition ((cp code-point-p) (compat booleanp) (ver versionp))
  :returns (cps code-point-listp)
  :short "The canonical or compatibility decomposition of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the full decomposition:
     canonical [Unicode, D68] if the flag is @('nil'),
     compatibility [Unicode, D65] otherwise.
     A code point that has no decomposition
     is returned as a list of one element."))
  (b* ((cp (code-point-fix cp))
       ((when (hangul-syllable-p cp)) (hangul-syllable-decomposition cp))
       (full (decomposition-map-lookup
              cp
              (if compat
                  (compatibility-decompositions ver)
                (canonical-decompositions ver)))))
    (or full
        (list cp)))
  :hooks (:fix)

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

  ;; We prove the next theorem
  ;; by checking it on every code point, for each version.

  (local
   (define maps-ok ((cp code-point-p)
                    (canonical decomposition-mapp)
                    (compat decomposition-mapp))
     :returns (yes/no booleanp)
     (or (>= (code-point-fix cp) #xA0)
         (and (not (decomposition-map-lookup cp canonical))
              (not (decomposition-map-lookup cp compat))))))

  (local
   (std::deflist maps-ok-listp (x canonical compat)
     :guard (and (code-point-listp x)
                 (decomposition-mapp canonical)
                 (decomposition-mapp compat))
     (maps-ok x canonical compat)))

  (defrulel maps-ok-listp-of-all-code-points
    (maps-ok-listp (all-code-points)
                   (canonical-decompositions ver)
                   (compatibility-decompositions ver))
    :enable (canonical-decompositions
             compatibility-decompositions
             (:e all-code-points))
    :disable maps-ok-listp-of-cons)

  (defruled decomposition-when-below-a0
    (implies (and (code-point-p cp)
                  (< cp #xA0))
             (equal (decomposition cp compat ver)
                    (list cp)))
    :enable (hangul-syllable-p
             maps-ok)
    :use (:instance maps-ok-when-member-equal-of-maps-ok-listp
                    (acl2::a cp)
                    (x (all-code-points))
                    (canonical (canonical-decompositions ver))
                    (compat (compatibility-decompositions ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decompose ((cps code-point-listp) (compat booleanp) (ver versionp))
  :returns (new-cps code-point-listp :hints (("Goal" :induct t)))
  :short "Replace the code points of a list by their
          canonical or compatibility decompositions,
          in a version of Unicode."
  (cond ((endp cps) nil)
        (t (append (decomposition (car cps) compat ver)
                   (decompose (cdr cps) compat ver))))
  :hooks (:fix)

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
