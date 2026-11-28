; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "compositions")

(include-book "kestrel/fty/deftset" :dir :system)

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ composing-pairs
  :parents (normalization)
  :short "The code points that compose with a code point after them,
          and those that compose with a code point before them."
  :long
  (xdoc::topstring
   (xdoc::p
    "Normalization Forms C and KC
     (NFC and NFKC: see @(see normalization))
     replace certain pairs of code points by single code points:
     see @(see compositions) and @(tsee composition).
     Here we say which code points are
     the first code point of such a pair,
     and which are the second code point of such a pair.
     A code point that is neither
     is never put together with another code point
     by these two normalization forms.")
   (xdoc::p
    "[UAX #15, Section 9.1] uses these two notions
     to say which code points are stable under NFC and NFKC:
     among other conditions, a stable code point
     never composes with a previous character
     and never composes with a following character.
     See @(see normalization-inert-code-points).")
   (xdoc::p
    "The pairs that compose are
     the canonical decomposition mappings of the primary composites
     [Unicode, D114],
     and the pairs of the Hangul syllable composition algorithm
     [Unicode, Section 3.12].
     For the former we compute, for each supported version of Unicode,
     the set of the first code points and the set of the second code points,
     from the same tables
     from which the pairs themselves are computed
     (see @(tsee primary-composites)).
     The sets are computed when this book is certified.
     They are tree sets of code points:
     see @(tsee code-point-set)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftset code-point-set
  :short "Fixtype of sets of code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sets are @(see tset::tset)s,
     in which a membership test takes logarithmic time;
     the fixtype is introduced with @(tsee fty::deftset).
     The operations on these sets are the ones of the tree sets:
     for example, @(tsee tset::in) for membership."))
  :elt-type code-point
  :pred code-point-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define composition-firsts ((cps code-point-listp)
                            (mappings decomposition-mapp)
                            (exclusions range-listp)
                            (set code-point-setp))
  :returns (new-set code-point-setp :hints (("Goal" :induct t)))
  :short "Add to a set of code points
          the first code points of the pairs
          that compose to the primary composites
          among the code points of a list,
          given a map of canonical decomposition mappings
          and the ranges of the excluded code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "This goes through the code points of the list
     as @(tsee primary-composites) does.
     Where that function adds to its map
     the pair of the two code points of a mapping,
     this one adds to its set the first code point of the mapping."))
  (b* ((set (code-point-set-fix set))
       ((when (endp cps)) set)
       (cp (code-point-fix (car cps)))
       (mapping (decomposition-map-lookup cp mappings))
       (set (if (and (equal (len mapping) 2)
                     (scalar-value-p cp)
                     (not (code-point-in-ranges-p cp exclusions)))
                (tset::insert (code-point-fix (first mapping)) set)
              set)))
    (composition-firsts (cdr cps) mappings exclusions set))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable len))))

;;;;;;;;;;;;;;;;;;;;

(define composition-seconds ((cps code-point-listp)
                             (mappings decomposition-mapp)
                             (exclusions range-listp)
                             (set code-point-setp))
  :returns (new-set code-point-setp :hints (("Goal" :induct t)))
  :short "Add to a set of code points
          the second code points of the pairs
          that compose to the primary composites
          among the code points of a list,
          given a map of canonical decomposition mappings
          and the ranges of the excluded code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee composition-firsts),
     for the second code point of each mapping."))
  (b* ((set (code-point-set-fix set))
       ((when (endp cps)) set)
       (cp (code-point-fix (car cps)))
       (mapping (decomposition-map-lookup cp mappings))
       (set (if (and (equal (len mapping) 2)
                     (scalar-value-p cp)
                     (not (code-point-in-ranges-p cp exclusions)))
                (tset::insert (code-point-fix (second mapping)) set)
              set)))
    (composition-seconds (cdr cps) mappings exclusions set))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection composing-pair-tables
  :short "The sets of the first code points and of the second code points
          of the pairs that compose to primary composites,
          for each version."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each set we check that it has the type
     of the sets of code points.")
   (xdoc::p
    "The sets are defined with @(tsee defconsts), not @(tsee defconst):
     they are computed when this book is certified
     and kept in its certificate,
     so they are not computed again each time the book is included."))

  ;; Unicode 16.0.0:

  (defconsts *composition-firsts-v16.0.0*
    (composition-firsts (all-code-points)
                        *canonical-decomposition-mapping-v16.0.0*
                        *full-composition-exclusion-v16.0.0*
                        (tset::empty)))

  (defconsts *composition-seconds-v16.0.0*
    (composition-seconds (all-code-points)
                         *canonical-decomposition-mapping-v16.0.0*
                         *full-composition-exclusion-v16.0.0*
                         (tset::empty)))

  (assert-event
   (and (code-point-setp *composition-firsts-v16.0.0*)
        (code-point-setp *composition-seconds-v16.0.0*)))

  ;; Unicode 17.0.0:

  (defconsts *composition-firsts-v17.0.0*
    (composition-firsts (all-code-points)
                        *canonical-decomposition-mapping-v17.0.0*
                        *full-composition-exclusion-v17.0.0*
                        (tset::empty)))

  (defconsts *composition-seconds-v17.0.0*
    (composition-seconds (all-code-points)
                         *canonical-decomposition-mapping-v17.0.0*
                         *full-composition-exclusion-v17.0.0*
                         (tset::empty)))

  (assert-event
   (and (code-point-setp *composition-firsts-v17.0.0*)
        (code-point-setp *composition-seconds-v17.0.0*)))

  ;; Unicode 18.0.0:

  (defconsts *composition-firsts-v18.0.0*
    (composition-firsts (all-code-points)
                        *canonical-decomposition-mapping-v18.0.0*
                        *full-composition-exclusion-v18.0.0*
                        (tset::empty)))

  (defconsts *composition-seconds-v18.0.0*
    (composition-seconds (all-code-points)
                         *canonical-decomposition-mapping-v18.0.0*
                         *full-composition-exclusion-v18.0.0*
                         (tset::empty)))

  (assert-event
   (and (code-point-setp *composition-firsts-v18.0.0*)
        (code-point-setp *composition-seconds-v18.0.0*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-composition-firsts ((ver versionp))
  :returns (set code-point-setp)
  :short "The set of the first code points
          of the pairs that compose to primary composites,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set does not have the first code points of the pairs
     that compose to precomposed Hangul syllables."))
  (version-case ver
                :v16.0.0 *composition-firsts-v16.0.0*
                :v17.0.0 *composition-firsts-v17.0.0*
                :v18.0.0 *composition-firsts-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define canonical-composition-seconds ((ver versionp))
  :returns (set code-point-setp)
  :short "The set of the second code points
          of the pairs that compose to primary composites,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set does not have the second code points of the pairs
     that compose to precomposed Hangul syllables."))
  (version-case ver
                :v16.0.0 *composition-seconds-v16.0.0*
                :v17.0.0 *composition-seconds-v17.0.0*
                :v18.0.0 *composition-seconds-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define composes-with-following-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point composes with some code point after it,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if it is the first code point of a pair that composes.
     Such a code point is
     the first code point of the canonical decomposition mapping
     of a primary composite;
     or a Hangul leading consonant, which composes with a vowel;
     or a Hangul syllable made of a leading consonant and a vowel
     (an LV syllable),
     which composes with a trailing consonant."))
  (b* ((cp (code-point-fix cp)))
    (or (hangul-l-p cp)
        (hangul-lv-syllable-p cp)
        (tset::in cp (canonical-composition-firsts ver))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define composes-with-previous-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point composes with some code point before it,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if it is the second code point of a pair that composes.
     Such a code point is
     the second code point of the canonical decomposition mapping
     of a primary composite;
     or a Hangul vowel, which composes with a leading consonant;
     or a Hangul trailing consonant, which composes with an LV syllable."))
  (b* ((cp (code-point-fix cp)))
    (or (hangul-v-p cp)
        (hangul-t-p cp)
        (tset::in cp (canonical-composition-seconds ver))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection composing-pairs-theorems
  :short "Theorems about the code points that compose with others."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sets of each version are
     what @(tsee composition-firsts) and @(tsee composition-seconds)
     give on all the code points, with the tables of that version.")
   (xdoc::p
    "If two code points compose (see @(tsee composition)),
     the first one composes with a code point after it
     and the second one composes with a code point before it.
     We state this the other way round, as two rewrite rules:
     a code point that does not compose with any code point after it
     does not compose with a given one, and likewise for the second.
     The rules are disabled by default.")
   (xdoc::p
    "No code point below @('#x300') composes with a code point before it.
     The ASCII code points that compose with a code point after them
     are the three characters @('<'), @('='), @('>'),
     which compose with U+0338 COMBINING LONG SOLIDUS OVERLAY,
     and the letters other than @('Q') and @('q'):
     the theorem lists them as five ranges.")
   (xdoc::p
    "These are proved by evaluation,
     or by checking them on every code point, for each version."))

  (defruled canonical-composition-firsts-is-composition-firsts
    (equal (canonical-composition-firsts ver)
           (composition-firsts (all-code-points)
                               (canonical-mappings ver)
                               (full-composition-exclusion-ranges ver)
                               (tset::empty)))
    :enable (canonical-composition-firsts
             canonical-mappings
             full-composition-exclusion-ranges
             (:e all-code-points)
             (:e tset::empty)))

  (defruled canonical-composition-seconds-is-composition-seconds
    (equal (canonical-composition-seconds ver)
           (composition-seconds (all-code-points)
                                (canonical-mappings ver)
                                (full-composition-exclusion-ranges ver)
                                (tset::empty)))
    :enable (canonical-composition-seconds
             canonical-mappings
             full-composition-exclusion-ranges
             (:e all-code-points)
             (:e tset::empty)))

  ;; We check, on every code point, for each version,
  ;; that if the code point is not excluded
  ;; and its canonical mapping consists of two code points,
  ;; these are in the two sets.

  (local
   (define members-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((mapping (decomposition-map-lookup cp (canonical-mappings ver))))
       (or (not (equal (len mapping) 2))
           (full-composition-exclusion-p cp ver)
           (and (tset::in (code-point-fix (first mapping))
                             (canonical-composition-firsts ver))
                (tset::in (code-point-fix (second mapping))
                             (canonical-composition-seconds ver)))))
     :hooks nil
     :guard-hints (("Goal" :in-theory (enable len)))))

  (local
   (std::deflist members-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (members-ok x ver)))

  (defrulel members-ok-listp-of-all-code-points
    (members-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable members-ok-listp-of-cons)

  ;; In particular, this holds for a code point that two code points compose to.
  ;; Its canonical mapping consists of those two code points,
  ;; and it is not excluded.

  (defrulel members-ok-of-composition-map-lookup
    (members-ok (composition-map-lookup first
                                        second
                                        (canonical-compositions ver))
                ver)
    :use (:instance members-ok-when-member-equal-of-members-ok-listp
                    (acl2::a (code-point-fix
                              (composition-map-lookup
                               first
                               second
                               (canonical-compositions ver))))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable members-ok)

  (defruled composition-when-not-composes-with-following-p
    (implies (not (composes-with-following-p first ver))
             (equal (composition first second ver)
                    nil))
    :enable (composition
             hangul-composition
             composes-with-following-p
             members-ok
             canonical-mapping-of-composition-map-lookup)
    :disable members-ok-of-composition-map-lookup
    :use members-ok-of-composition-map-lookup)

  (defruled composition-when-not-composes-with-previous-p
    (implies (not (composes-with-previous-p second ver))
             (equal (composition first second ver)
                    nil))
    :enable (composition
             hangul-composition
             composes-with-previous-p
             members-ok
             canonical-mapping-of-composition-map-lookup)
    :disable members-ok-of-composition-map-lookup
    :use members-ok-of-composition-map-lookup)

  ;; The code points below #x300, and the ASCII code points.

  (local
   (define low-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((n (code-point-fix cp)))
       (and (or (>= n #x300)
                (not (composes-with-previous-p cp ver)))
            (or (>= n #x80)
                (equal (composes-with-following-p cp ver)
                       (or (and (<= #x3C n) (<= n #x3E))
                           (and (<= #x41 n) (<= n #x50))
                           (and (<= #x52 n) (<= n #x5A))
                           (and (<= #x61 n) (<= n #x70))
                           (and (<= #x72 n) (<= n #x7A)))))))
     :hooks nil))

  (local
   (std::deflist low-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (low-ok x ver)))

  (defrulel low-ok-listp-of-all-code-points
    (low-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable low-ok-listp-of-cons)

  (defruled not-composes-with-previous-p-when-below-300
    (implies (< (code-point-fix cp) #x300)
             (not (composes-with-previous-p cp ver)))
    :enable low-ok
    :use (:instance low-ok-when-member-equal-of-low-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver))))

  (defruled composes-with-following-p-when-ascii
    (implies (< (code-point-fix cp) #x80)
             (equal (composes-with-following-p cp ver)
                    (b* ((n (code-point-fix cp)))
                      (or (and (<= #x3C n) (<= n #x3E))
                          (and (<= #x41 n) (<= n #x50))
                          (and (<= #x52 n) (<= n #x5A))
                          (and (<= #x61 n) (<= n #x70))
                          (and (<= #x72 n) (<= n #x7A))))))
    :enable low-ok
    :use (:instance low-ok-when-member-equal-of-low-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))))
