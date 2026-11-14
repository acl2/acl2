; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "combining-classes")
(include-book "compositions")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/rev" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ normalization
  :parents (unicode)
  :short "The Unicode normalization forms: NFD, NFC, NFKD and NFKC."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode has more than one way to encode some texts:
     for example, a letter with an accent may be a single code point,
     or a letter followed by a combining mark.
     Sequences of code points that stand for the same text
     are called canonically equivalent.
     A normalization form [UAX #15] [Unicode, Section 3.11]
     maps every sequence of code points
     to one that is equivalent to it,
     and maps equivalent sequences to the same sequence.
     There are four forms:")
   (xdoc::ul
    (xdoc::li
     "NFD replaces each code point by its canonical decomposition
      (see @(see decompositions))
      and puts the combining marks in a canonical order
      (see @(see canonical-ordering)).")
    (xdoc::li
     "NFC does what NFD does and then recombines
      the code points that compose
      (see @(see canonical-composition)).")
    (xdoc::li
     "NFKD and NFKC are like NFD and NFC,
      but they use the compatibility decompositions,
      which lose some distinctions (of font, width, and so on)
      between sequences that are not canonically equivalent."))
   (xdoc::p
    "Programming languages that allow Unicode identifiers
     usually say that two identifiers are the same
     if they have the same NFC form (or, in some languages, NFKC form);
     this is what [UAX #31] recommends.")
   (xdoc::p
    "The functions take and return lists of code points.
     They are defined on all code points,
     including the surrogates, which they leave alone;
     if all the code points of the argument are scalar values,
     so are all the code points of the result.
     Like all the functions of this library
     that depend on the Unicode Character Database,
     they take the version of Unicode as an argument.")
   (xdoc::p
    "The definitions follow the specification directly.
     They are executable, and efficient enough for identifiers and the like,
     but they are not meant for large texts:
     they are not tail recursive,
     and the canonical ordering of a run of @('n') combining marks
     takes time proportional to the square of @('n').")
   (xdoc::p
    "The functions are validated in two ways,
     neither of which is a proof:
     by running the whole of the conformance test
     of the Unicode Character Database, for each version,
     which is done when the books in the @('tests') directory are certified;
     and by comparing them, on every code point,
     with independent implementations of the same version of Unicode,
     as described in the file @('README.md')."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ canonical-ordering
  :parents (normalization)
  :short "The Canonical Ordering Algorithm [Unicode, D109]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two adjacent combining marks whose classes differ
     (see @(see combining-classes))
     do not interact, typographically,
     so that either order stands for the same text.
     The algorithm picks one order:
     in each maximal run of non-starters,
     it sorts the code points by their classes,
     keeping the code points of the same class in their original order.
     Starters are never moved,
     and non-starters never move across a starter.")
   (xdoc::p
    "The specification says to exchange adjacent non-starters
     that are out of order until none are left.
     We sort each run by insertion instead, from its end,
     which gives the same result."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-order-insert ((cp code-point-p)
                                (cps code-point-listp)
                                (ver versionp))
  :returns (new-cps code-point-listp)
  :short "Put a non-starter in front of a canonically ordered list
          and move it to its place."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code point moves past the non-starters that follow it
     and whose classes are strictly smaller than its own.
     It does not move past a code point of the same class,
     nor past a starter."))
  (b* ((cp (code-point-fix cp))
       ((when (endp cps)) (list cp))
       (next (code-point-fix (car cps)))
       (next-ccc (canonical-combining-class next ver)))
    (if (and (not (equal next-ccc 0))
             (< next-ccc (canonical-combining-class cp ver)))
        (cons next (canonical-order-insert cp (cdr cps) ver))
      (cons cp (code-point-list-fix cps))))
  :measure (len cps)

  ///

  (defrule scalar-value-listp-of-canonical-order-insert
    (implies (and (scalar-value-p cp)
                  (scalar-value-listp cps))
             (scalar-value-listp (canonical-order-insert cp cps ver)))
    :induct t)

  (defrule len-of-canonical-order-insert
    (equal (len (canonical-order-insert cp cps ver))
           (+ 1 (len cps)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-order ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :short "Put a list of code points in canonical order."
  (b* (((when (endp cps)) nil)
       (cp (code-point-fix (car cps)))
       (rest (canonical-order (cdr cps) ver)))
    (if (equal (canonical-combining-class cp ver) 0)
        (cons cp rest)
      (canonical-order-insert cp rest ver)))
  :measure (len cps)
  :verify-guards :after-returns

  ///

  (defrule scalar-value-listp-of-canonical-order
    (implies (scalar-value-listp cps)
             (scalar-value-listp (canonical-order cps ver)))
    :induct t)

  (defrule len-of-canonical-order
    (equal (len (canonical-order cps ver))
           (len cps))
    :induct t)

  (defruled canonical-order-when-all-below-300
    (implies (and (code-point-listp cps)
                  (code-points-below-p cps #x300))
             (equal (canonical-order cps ver)
                    cps))
    :induct t
    :enable (code-points-below-p
             canonical-combining-class-when-below-300)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ canonical-composition
  :parents (normalization)
  :short "The Canonical Composition Algorithm [Unicode, D117]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The algorithm applies to a list of code points
     that is fully decomposed and canonically ordered.
     It goes through the list from the second code point on.
     For each code point C,
     it finds the last starter L that precedes C;
     if C is not blocked from L,
     and if L and C compose to a code point P (see @(see compositions)),
     it replaces L with P and removes C.
     C is blocked from L [Unicode, D115]
     if there is a code point between them
     that is a starter or whose class is not lower than the class of C;
     in a canonically ordered list, the code point just before C
     is such a code point if any is.")
   (xdoc::p
    "So a starter collects the combining marks that follow it
     and that it composes with, possibly out of several marks;
     a mark that does not compose stays where it is
     and blocks the marks of its class that follow.
     A starter can also compose with the starter right after it,
     which is how the Hangul syllables are put together,
     and how a few other pairs compose.")
   (xdoc::p
    "We go through the list once, keeping, as we go,
     the last starter (possibly already composed),
     the code points after it that did not compose, in reverse order,
     and the class of the last one of those."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-compose-from-starter ((starter code-point-p)
                                        (pending code-point-listp)
                                        (last-ccc natp)
                                        (cps code-point-listp)
                                        (ver versionp))
  :returns (new-cps code-point-listp)
  :short "Canonical composition, from a starter on."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are:
     the last starter seen;
     the code points seen after it that did not compose with it,
     most recent first;
     the class of the most recent one of those,
     which is only used if there is one;
     and the code points still to be processed.")
   (xdoc::p
    "The next code point is blocked from the starter
     if there are pending code points
     and the class of the most recent one
     is not lower than the class of the next code point.
     (The pending code points are all non-starters,
     because a starter that does not compose becomes the new starter.)
     If the next code point is not blocked
     and composes with the starter,
     the composite becomes the starter.
     Otherwise, if the next code point is a starter,
     the old starter and the pending code points are done,
     and we go on from the new starter.
     Otherwise the next code point becomes pending."))
  (b* ((starter (code-point-fix starter))
       (pending (code-point-list-fix pending))
       (last-ccc (lnfix last-ccc))
       ((when (endp cps)) (cons starter (rev pending)))
       (cp (code-point-fix (car cps)))
       (ccc (canonical-combining-class cp ver))
       (blocked (and (consp pending)
                     (>= last-ccc ccc)))
       (composite (and (not blocked)
                       (composition starter cp ver)))
       ((when composite)
        (canonical-compose-from-starter composite
                                        pending
                                        last-ccc
                                        (cdr cps)
                                        ver))
       ((when (equal ccc 0))
        (append (cons starter (rev pending))
                (canonical-compose-from-starter cp nil 0 (cdr cps) ver))))
    (canonical-compose-from-starter starter
                                    (cons cp pending)
                                    ccc
                                    (cdr cps)
                                    ver))
  :measure (len cps)
  :hooks nil ; done below
  :verify-guards :after-returns

  ///

  ;; The fixing theorems need a hint, and are proved in an order that works.

  (defmacro canonical-compose-from-starter-fix (arg)
    `(fty::deffixequiv canonical-compose-from-starter
       :args (,arg)
       :hints (("Goal"
                :induct (canonical-compose-from-starter starter
                                                        pending
                                                        last-ccc
                                                        cps
                                                        ver)
                :in-theory (enable canonical-compose-from-starter)))))

  (canonical-compose-from-starter-fix (cps code-point-listp))
  (canonical-compose-from-starter-fix (ver versionp))
  (canonical-compose-from-starter-fix (starter code-point-p))
  (canonical-compose-from-starter-fix (pending code-point-listp))
  (canonical-compose-from-starter-fix (last-ccc natp))

  (defrule scalar-value-listp-of-canonical-compose-from-starter
    (implies (and (scalar-value-p starter)
                  (scalar-value-listp pending)
                  (scalar-value-listp cps))
             (scalar-value-listp
              (canonical-compose-from-starter starter
                                              pending
                                              last-ccc
                                              cps
                                              ver)))
    :induct t
    :disable nfix)

  (defruled canonical-compose-from-starter-when-all-below-300
    (implies (and (code-point-p starter)
                  (code-point-listp cps)
                  (code-points-below-p cps #x300))
             (equal (canonical-compose-from-starter starter nil 0 cps ver)
                    (cons starter cps)))
    :induct t
    :enable (code-points-below-p
             canonical-combining-class-when-below-300
             composition-when-second-below-300)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-compose ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :short "Canonical composition of a list of code points
          that is fully decomposed and canonically ordered."
  :long
  (xdoc::topstring
   (xdoc::p
    "The non-starters at the start of the list have no starter before them,
     so they stay as they are."))
  (b* (((when (endp cps)) nil)
       (cp (code-point-fix (car cps))))
    (if (equal (canonical-combining-class cp ver) 0)
        (canonical-compose-from-starter cp nil 0 (cdr cps) ver)
      (cons cp (canonical-compose (cdr cps) ver))))
  :measure (len cps)

  ///

  (defrule scalar-value-listp-of-canonical-compose
    (implies (scalar-value-listp cps)
             (scalar-value-listp (canonical-compose cps ver)))
    :induct t)

  (defruled canonical-compose-when-all-below-300
    (implies (and (code-point-listp cps)
                  (code-points-below-p cps #x300))
             (equal (canonical-compose cps ver)
                    cps))
    :enable (code-points-below-p
             canonical-combining-class-when-below-300
             canonical-compose-from-starter-when-all-below-300)
    :expand (canonical-compose cps ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfd ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form D (canonical decomposition)
          of a list of code points, in a version of Unicode."
  (canonical-order (decompose cps nil ver) ver)

  ///

  (defrule scalar-value-listp-of-nfd
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfd cps ver)))))

;;;;;;;;;;;;;;;;;;;;

(define nfc ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form C
          (canonical decomposition, then canonical composition)
          of a list of code points, in a version of Unicode."
  (canonical-compose (nfd cps ver) ver)

  ///

  (defrule scalar-value-listp-of-nfc
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfc cps ver)))))

;;;;;;;;;;;;;;;;;;;;

(define nfkd ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form KD (compatibility decomposition)
          of a list of code points, in a version of Unicode."
  (canonical-order (decompose cps t ver) ver)

  ///

  (defrule scalar-value-listp-of-nfkd
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfkd cps ver)))))

;;;;;;;;;;;;;;;;;;;;

(define nfkc ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form KC
          (compatibility decomposition, then canonical composition)
          of a list of code points, in a version of Unicode."
  (canonical-compose (nfkd cps ver) ver)

  ///

  (defrule scalar-value-listp-of-nfkc
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfkc cps ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalization-of-ascii
  :parents (normalization)
  :short "The normalization forms leave ASCII alone."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, in every supported version of Unicode,
     each of the four normalization forms
     maps a list of code points that are all below @('#xA0') to itself.
     (For the canonical forms this is so up to @('#xC0'),
     but we do not need that.)
     The ASCII code points are those below @('#x80').")
   (xdoc::p
    "So a tool that handles only ASCII identifiers,
     and does not normalize them,
     agrees on those identifiers
     with one that follows the Unicode rules.")
   (xdoc::p
    "This follows from three facts about the tables,
     which are proved by evaluation for each version:
     no code point below @('#xA0') has a decomposition mapping;
     every code point below @('#x300') is a starter;
     and no pair of code points composes
     if the second one is below @('#x300')."))

  (defrule nfd-when-all-below-a0
    (implies (and (code-point-listp cps)
                  (code-points-below-p cps #xA0))
             (equal (nfd cps ver)
                    cps))
    :enable (nfd
             decompose-when-all-below-a0
             canonical-order-when-all-below-300)
    :use (:instance code-points-below-p-when-below-smaller
                    (bound1 #xA0)
                    (bound2 #x300)))

  (defrule nfc-when-all-below-a0
    (implies (and (code-point-listp cps)
                  (code-points-below-p cps #xA0))
             (equal (nfc cps ver)
                    cps))
    :enable (nfc canonical-compose-when-all-below-300)
    :use (:instance code-points-below-p-when-below-smaller
                    (bound1 #xA0)
                    (bound2 #x300)))

  (defrule nfkd-when-all-below-a0
    (implies (and (code-point-listp cps)
                  (code-points-below-p cps #xA0))
             (equal (nfkd cps ver)
                    cps))
    :enable (nfkd
             decompose-when-all-below-a0
             canonical-order-when-all-below-300)
    :use (:instance code-points-below-p-when-below-smaller
                    (bound1 #xA0)
                    (bound2 #x300)))

  (defrule nfkc-when-all-below-a0
    (implies (and (code-point-listp cps)
                  (code-points-below-p cps #xA0))
             (equal (nfkc cps ver)
                    cps))
    :enable (nfkc canonical-compose-when-all-below-300)
    :use (:instance code-points-below-p-when-below-smaller
                    (bound1 #xA0)
                    (bound2 #x300))))
