; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "code-points")

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hangul
  :parents (normalization)
  :short "Decomposition and composition of Hangul syllables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The 11,172 precomposed Hangul syllables,
     at the code points from @('#xAC00') to @('#xD7A3'),
     are canonically equivalent to sequences of two or three
     conjoining jamo:
     a leading consonant (L), a vowel (V),
     and possibly a trailing consonant (T).
     The Unicode Character Database does not list these decompositions:
     they are given by the arithmetic of [Unicode, Section 3.12],
     because the syllables are encoded in the order of their jamo.")
   (xdoc::p
    "A syllable without trailing consonant is called an LV syllable,
     and one with trailing consonant is called an LVT syllable.
     With the names of the constants of [Unicode, Section 3.12],
     the syllable for the L, V and T
     with indices @('LIndex'), @('VIndex') and @('TIndex')
     (where @('TIndex') is 0 if there is no T)
     is at")
   (xdoc::codeblock
    "SBase + (LIndex * VCount + VIndex) * TCount + TIndex")
   (xdoc::p
    "This algorithm is the same in all versions of Unicode,
     by the normalization stability policy;
     so the functions here do not take a version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hangul-constants
  :short "The constants of the Hangul syllable algorithms
          [Unicode, Section 3.12]."

  (defconst *hangul-s-base* #xAC00)
  (defconst *hangul-l-base* #x1100)
  (defconst *hangul-v-base* #x1161)
  (defconst *hangul-t-base* #x11A7)
  (defconst *hangul-l-count* 19)
  (defconst *hangul-v-count* 21)
  (defconst *hangul-t-count* 28)
  (defconst *hangul-n-count* 588)
  (defconst *hangul-s-count* 11172)

  (assert-event (equal *hangul-n-count*
                       (* *hangul-v-count* *hangul-t-count*)))
  (assert-event (equal *hangul-s-count*
                       (* *hangul-l-count* *hangul-n-count*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hangul-syllable-p ((cp code-point-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is a precomposed Hangul syllable."
  (b* ((cp (code-point-fix cp)))
    (and (<= *hangul-s-base* cp)
         (< cp (+ *hangul-s-base* *hangul-s-count*))))

  ///

  (defrule scalar-value-p-when-hangul-syllable-p
    (implies (and (hangul-syllable-p cp)
                  (code-point-p cp))
             (scalar-value-p cp))
    :enable scalar-value-p-alt-def
    :disable scalar-value-p))

;;;;;;;;;;;;;;;;;;;;

(define hangul-l-p ((cp code-point-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is a leading consonant
          that the Hangul syllable algorithms use."
  (b* ((cp (code-point-fix cp)))
    (and (<= *hangul-l-base* cp)
         (< cp (+ *hangul-l-base* *hangul-l-count*)))))

;;;;;;;;;;;;;;;;;;;;

(define hangul-v-p ((cp code-point-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is a vowel
          that the Hangul syllable algorithms use."
  (b* ((cp (code-point-fix cp)))
    (and (<= *hangul-v-base* cp)
         (< cp (+ *hangul-v-base* *hangul-v-count*)))))

;;;;;;;;;;;;;;;;;;;;

(define hangul-t-p ((cp code-point-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is a trailing consonant
          that the Hangul syllable algorithms use."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code point @('TBase') itself is not a trailing consonant:
     the index 0 stands for the absence of a trailing consonant."))
  (b* ((cp (code-point-fix cp)))
    (and (< *hangul-t-base* cp)
         (< cp (+ *hangul-t-base* *hangul-t-count*)))))

;;;;;;;;;;;;;;;;;;;;

(define hangul-lv-syllable-p ((cp code-point-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is a precomposed Hangul syllable
          without trailing consonant."
  (b* ((cp (code-point-fix cp)))
    (and (hangul-syllable-p cp)
         (equal (mod (- cp *hangul-s-base*) *hangul-t-count*) 0)))

  ///

  (defrule hangul-syllable-p-when-hangul-lv-syllable-p
    (implies (hangul-lv-syllable-p cp)
             (hangul-syllable-p cp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hangul-syllable-decomposition ((s code-point-p))
  :guard (hangul-syllable-p s)
  :returns (jamos true-listp :rule-classes :type-prescription)
  :short "The full canonical decomposition of a precomposed Hangul syllable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list of the leading consonant, of the vowel,
     and of the trailing consonant if there is one."))
  (b* ((s-index (- (code-point-fix s) *hangul-s-base*))
       (l (+ *hangul-l-base* (floor s-index *hangul-n-count*)))
       (v (+ *hangul-v-base* (floor (mod s-index *hangul-n-count*)
                                    *hangul-t-count*)))
       (t-index (mod s-index *hangul-t-count*)))
    (if (equal t-index 0)
        (list l v)
      (list l v (+ *hangul-t-base* t-index))))
  :guard-hints (("Goal" :in-theory (enable mod)))

  ///

  (defrule consp-of-hangul-syllable-decomposition
    (consp (hangul-syllable-decomposition s))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hangul-syllable-decomposition-mapping ((s code-point-p))
  :guard (hangul-syllable-p s)
  :returns (mapping true-listp :rule-classes :type-prescription)
  :short "The canonical decomposition mapping
          of a precomposed Hangul syllable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the value of the @('Decomposition_Mapping') property
     for the syllable, which always consists of two code points:
     the leading consonant and the vowel, for an LV syllable;
     the LV syllable with the same leading consonant and vowel,
     and the trailing consonant, for an LVT syllable.
     Expanding the mapping of an LVT syllable
     gives its full decomposition;
     see @(tsee hangul-syllable-decomposition).
     Normalization uses the full decomposition directly."))
  (b* ((s (code-point-fix s))
       (s-index (- s *hangul-s-base*))
       (t-index (mod s-index *hangul-t-count*)))
    (if (equal t-index 0)
        (list (+ *hangul-l-base* (floor s-index *hangul-n-count*))
              (+ *hangul-v-base* (floor (mod s-index *hangul-n-count*)
                                        *hangul-t-count*)))
      (list (- s t-index)
            (+ *hangul-t-base* t-index))))
  :guard-hints (("Goal" :in-theory (enable mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hangul-composition ((first code-point-p) (second code-point-p))
  :returns (composite? acl2::maybe-natp
                       :rule-classes :type-prescription
                       :hints (("Goal" :in-theory (enable acl2::maybe-natp
                                                          natp
                                                          hangul-l-p
                                                          hangul-v-p
                                                          hangul-t-p
                                                          hangul-lv-syllable-p
                                                          hangul-syllable-p))))
  :short "The precomposed Hangul syllable, if any,
          that two code points compose to."
  :long
  (xdoc::topstring
   (xdoc::p
    "A leading consonant and a vowel compose to an LV syllable.
     An LV syllable and a trailing consonant compose to an LVT syllable.
     For any other pair of code points, the result is @('nil')."))
  (b* ((first (code-point-fix first))
       (second (code-point-fix second)))
    (cond ((and (hangul-l-p first)
                (hangul-v-p second))
           (+ *hangul-s-base*
              (* *hangul-t-count*
                 (+ (* *hangul-v-count* (- first *hangul-l-base*))
                    (- second *hangul-v-base*)))))
          ((and (hangul-lv-syllable-p first)
                (hangul-t-p second))
           (+ first (- second *hangul-t-base*)))
          (t nil)))
  :guard-hints (("Goal" :in-theory (enable hangul-l-p hangul-v-p)))

  ///

  (defruled hangul-composition-when-not-hangul-v-p-and-not-hangul-t-p
    (implies (and (not (hangul-v-p second))
                  (not (hangul-t-p second)))
             (equal (hangul-composition first second)
                    nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hangul-theorems
  :short "Theorems about the Hangul syllable algorithms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The decomposition of a precomposed syllable consists of
     a leading consonant, a vowel,
     and possibly a trailing consonant,
     which are all scalar values.
     Composing the first two gives an LV syllable,
     which is the original syllable if there is no third;
     if there is a third,
     composing that LV syllable with it gives the original syllable.
     The composition of two code points, when there is one,
     is a precomposed syllable, and so a scalar value.
     The decomposition mapping of a syllable
     consists of two scalar values that compose to the syllable:
     for an LV syllable it is the decomposition;
     for an LVT syllable it is
     the LV syllable that the first two jamo of the decomposition compose to,
     followed by the third jamo.")
   (xdoc::p
    "There are only 11,172 precomposed syllables,
     so we prove the facts about each of them by checking them all,
     by evaluation,
     which does not depend on any library of arithmetic:
     @('hangul-syllable-facts-p') says what is checked
     for one syllable."))

  (define hangul-syllable-facts-p ((s code-point-p))
    :guard (hangul-syllable-p s)
    :returns (yes/no booleanp)
    :parents nil
    (b* ((jamos (hangul-syllable-decomposition s))
         ((unless (and (scalar-value-listp jamos)
                       (or (equal (len jamos) 2)
                           (equal (len jamos) 3))))
          nil)
         (l (first jamos))
         (v (second jamos))
         ((unless (and (hangul-l-p l)
                       (hangul-v-p v)))
          nil)
         (lv (hangul-composition l v))
         ((unless (and lv
                       (code-point-p lv)
                       (hangul-lv-syllable-p lv)))
          nil)
         ((unless (implies (hangul-lv-syllable-p s)
                           (<= (+ s *hangul-t-count*)
                               (+ *hangul-s-base* *hangul-s-count*))))
          nil)
         (mapping (hangul-syllable-decomposition-mapping s))
         ((unless (and (scalar-value-listp mapping)
                       (equal (len mapping) 2)
                       (equal (hangul-composition (first mapping)
                                                  (second mapping))
                              (code-point-fix s))))
          nil))
      (if (equal (len jamos) 3)
          (b* ((tt (third jamos)))
            (and (hangul-t-p tt)
                 (equal (hangul-composition lv tt) (code-point-fix s))
                 (equal mapping (list lv tt))))
        (and (equal lv (code-point-fix s))
             (equal mapping jamos))))
    :guard-hints (("Goal" :in-theory (enable len)))
    :hooks nil)

  (define hangul-syllable-facts-below-p ((n natp))
    :guard (<= n *hangul-s-count*)
    :returns (yes/no booleanp)
    :parents nil
    (or (zp n)
        (and (hangul-syllable-facts-p (+ *hangul-s-base* (1- n)))
             (hangul-syllable-facts-below-p (1- n))))
    :guard-hints (("Goal" :in-theory (enable hangul-syllable-p
                                             code-point-p)))
    :hooks nil

    ///

    (defruled hangul-syllable-facts-p-when-below
      (implies (and (hangul-syllable-facts-below-p n)
                    (natp i)
                    (< i (nfix n)))
               (hangul-syllable-facts-p (+ *hangul-s-base* i)))
      :induct t))

  (defruled hangul-syllable-facts-p-when-hangul-syllable-p
    (implies (hangul-syllable-p s)
             (hangul-syllable-facts-p (code-point-fix s)))
    :enable hangul-syllable-p
    :use (:instance hangul-syllable-facts-p-when-below
                    (n *hangul-s-count*)
                    (i (- (code-point-fix s) *hangul-s-base*))))

  (defrule scalar-value-listp-of-hangul-syllable-decomposition
    (implies (hangul-syllable-p s)
             (scalar-value-listp (hangul-syllable-decomposition s)))
    :use hangul-syllable-facts-p-when-hangul-syllable-p
    :enable hangul-syllable-facts-p)

  (defruled hangul-syllable-decomposition-jamos
    (implies (hangul-syllable-p s)
             (b* ((jamos (hangul-syllable-decomposition s)))
               (and (hangul-l-p (first jamos))
                    (hangul-v-p (second jamos))
                    (or (equal (len jamos) 2)
                        (and (equal (len jamos) 3)
                             (hangul-t-p (third jamos)))))))
    :use hangul-syllable-facts-p-when-hangul-syllable-p
    :enable hangul-syllable-facts-p)

  (defruled hangul-composition-of-hangul-syllable-decomposition
    (implies (and (hangul-syllable-p s)
                  (code-point-p s))
             (b* ((jamos (hangul-syllable-decomposition s))
                  (lv (hangul-composition (first jamos) (second jamos))))
               (equal (if (equal (len jamos) 3)
                          (hangul-composition lv (third jamos))
                        lv)
                      s)))
    :use hangul-syllable-facts-p-when-hangul-syllable-p
    :enable hangul-syllable-facts-p)

  (defrule scalar-value-listp-of-hangul-syllable-decomposition-mapping
    (implies (hangul-syllable-p s)
             (scalar-value-listp (hangul-syllable-decomposition-mapping s)))
    :use hangul-syllable-facts-p-when-hangul-syllable-p
    :enable hangul-syllable-facts-p)

  (defruled hangul-syllable-decomposition-mapping-alt-def
    (implies (hangul-syllable-p s)
             (equal (hangul-syllable-decomposition-mapping s)
                    (b* ((jamos (hangul-syllable-decomposition s)))
                      (if (equal (len jamos) 3)
                          (list (hangul-composition (first jamos)
                                                    (second jamos))
                                (third jamos))
                        jamos))))
    :use (hangul-syllable-facts-p-when-hangul-syllable-p
          scalar-value-listp-of-hangul-syllable-decomposition)
    :enable hangul-syllable-facts-p
    :disable scalar-value-listp-of-hangul-syllable-decomposition)

  (defruled hangul-composition-of-hangul-syllable-decomposition-mapping
    (implies (and (hangul-syllable-p s)
                  (code-point-p s))
             (b* ((mapping (hangul-syllable-decomposition-mapping s)))
               (equal (hangul-composition (first mapping) (second mapping))
                      s)))
    :use (hangul-syllable-facts-p-when-hangul-syllable-p
          scalar-value-listp-of-hangul-syllable-decomposition-mapping)
    :enable hangul-syllable-facts-p
    :disable scalar-value-listp-of-hangul-syllable-decomposition-mapping)

  (defrule hangul-syllable-p-of-hangul-composition
    (implies (hangul-composition first second)
             (hangul-syllable-p (hangul-composition first second)))
    :use (:instance hangul-syllable-facts-p-when-hangul-syllable-p
                    (s (code-point-fix first)))
    :enable (hangul-composition
             hangul-syllable-facts-p
             hangul-syllable-p
             hangul-lv-syllable-p
             hangul-l-p
             hangul-v-p
             hangul-t-p
             code-point-p))

  (defrule code-point-p-of-hangul-composition
    (implies (hangul-composition first second)
             (code-point-p (hangul-composition first second)))
    :enable (hangul-composition
             hangul-syllable-p
             hangul-lv-syllable-p
             hangul-l-p
             hangul-v-p
             hangul-t-p
             code-point-p))

  (defrule scalar-value-p-of-hangul-composition
    (implies (hangul-composition first second)
             (scalar-value-p (hangul-composition first second)))
    :use hangul-syllable-p-of-hangul-composition
    :disable hangul-syllable-p-of-hangul-composition)

  (defrule scalar-value-option-p-of-hangul-composition
    (scalar-value-option-p (hangul-composition first second))
    :enable scalar-value-option-p))
