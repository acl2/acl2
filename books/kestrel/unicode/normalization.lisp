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
(local (include-book "std/lists/sets" :dir :system)) ; for DEFLIST theorems

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
     are called canonical equivalents.
     A normalization form [UAX #15] [Unicode, Section 3.11]
     maps every sequence of code points
     to one that is equivalent to it,
     and maps equivalent sequences to the same sequence.
     There are four forms:")
   (xdoc::ul
    (xdoc::li
     "Normalization Form D (NFD), which is canonical decomposition,
      replaces each code point by its canonical decomposition
      (see @(see decompositions))
      and puts the combining marks in a canonical order
      (see @(see canonical-ordering)).")
    (xdoc::li
     "Normalization Form C (NFC), which is
      canonical decomposition followed by canonical composition,
      does what NFD does and then recombines
      the code points that compose
      (see @(see canonical-composition)).")
    (xdoc::li
     "Normalization Form KD (NFKD), which is compatibility decomposition,
      and Normalization Form KC (NFKC), which is
      compatibility decomposition followed by canonical composition,
      are like NFD and NFC,
      but they use the compatibility decompositions,
      which lose some distinctions (of font, width, and so on)
      between sequences that are not canonical equivalents."))
   (xdoc::p
    "These are the names and the abbreviations of [UAX #15, Table 1].
     The letter D is for the two decomposed forms,
     and the letter C for the two composed forms.
     The letter K stands for compatibility:
     it is a K because C already stands for composition
     [UAX #15, Section 1.2].")
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
    "Applying one of the four forms to the result of another one
     gives one of the four forms of the original list.
     The form that is applied last says whether the result is composed,
     and the result is a compatibility form if either of the two is.
     For example, the NFC form of the NFKD form of a list
     is the NFKC form of the list.
     These are sixteen theorems, with names like @('nfc-of-nfkd'):
     see @(tsee nfd), @(tsee nfc), @(tsee nfkd) and @(tsee nfkc).")
   (xdoc::p
    "A list of code points is in one of the four forms
     if that form of the list is the list itself:
     see @(tsee nfd-memberp), @(tsee nfc-memberp),
     @(tsee nfkd-memberp) and @(tsee nfkc-memberp).
     These predicates are with the forms,
     so they need no book that the forms do not need.
     A list is in NFD, or in NFKD, exactly when
     it is fully decomposed and in canonical order.")
   (xdoc::p
    "Two lists of code points are canonical equivalents
     if they have the same NFD form,
     and compatibility equivalents
     if they have the same NFKD form:
     see @(tsee canonical-equivalent-p)
     and @(tsee compatibility-equivalent-p).
     Each of the two is an equivalence relation.
     A list is a canonical equivalent of its NFD and NFC forms,
     and a compatibility equivalent of all four.
     Two lists are canonical equivalents
     exactly when they have the same NFC form,
     and compatibility equivalents
     exactly when they have the same NFKC form.")
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
    (implies (code-points-below-p cps #x300)
             (equal (canonical-order cps ver)
                    (code-point-list-fix cps)))
    :induct t
    :enable (code-points-below-p
             canonical-combining-class-when-below-300)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonically-ordered-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points is in canonical order."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if it has no reorderable pair [Unicode, D108]:
     no two adjacent code points such that
     the canonical combining class of the first one
     is greater than the one of the second one,
     and the latter is not 0."))
  (or (endp cps)
      (endp (cdr cps))
      (b* ((ccc1 (canonical-combining-class (car cps) ver))
           (ccc2 (canonical-combining-class (cadr cps) ver)))
        (and (or (<= ccc1 ccc2)
                 (equal ccc2 0))
             (canonically-ordered-p (cdr cps) ver))))
  :hooks nil ; done below

  ///

  (fty::deffixequiv canonically-ordered-p
    :hints (("Goal"
             :induct (canonically-ordered-p cps ver)
             :expand ((canonically-ordered-p (code-point-list-fix cps) ver))
             :in-theory (enable canonically-ordered-p)))))

;;;;;;;;;;;;;;;;;;;;

(defsection canonical-order-theorems
  :short "Theorems about canonical ordering."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result of @(tsee canonical-order) is in canonical order.
     A list that is in canonical order is left unchanged.
     So putting a list in canonical order a second time changes nothing.")
   (xdoc::p
    "Canonical ordering only moves code points,
     so a fully decomposed list stays fully decomposed.")
   (xdoc::p
    "Two non-starters of different classes
     can be put in front of a list in either order."))

  (defruled canonical-order-insert-of-canonical-order-insert
    (implies (and (not (equal (canonical-combining-class cp1 ver) 0))
                  (< (canonical-combining-class cp1 ver)
                     (canonical-combining-class cp2 ver)))
             (equal (canonical-order-insert
                     cp1
                     (canonical-order-insert cp2 cps ver)
                     ver)
                    (canonical-order-insert
                     cp2
                     (canonical-order-insert cp1 cps ver)
                     ver)))
    :rule-classes ((:rewrite :loop-stopper nil))
    :induct (canonical-order-insert cp1 cps ver)
    :enable canonical-order-insert)

  (defrulel canonically-ordered-p-of-canonical-order-insert
    (implies (and (canonically-ordered-p cps ver)
                  (not (equal (canonical-combining-class cp ver) 0)))
             (canonically-ordered-p (canonical-order-insert cp cps ver) ver))
    :induct (canonical-order-insert cp cps ver)
    :enable (canonical-order-insert
             canonically-ordered-p)
    :expand ((canonical-order-insert cp (cdr cps) ver)))

  (defrule canonically-ordered-p-of-canonical-order
    (canonically-ordered-p (canonical-order cps ver) ver)
    :induct t
    :enable (canonical-order
             canonically-ordered-p))

  (defrule canonical-order-when-canonically-ordered-p
    (implies (canonically-ordered-p cps ver)
             (equal (canonical-order cps ver)
                    (code-point-list-fix cps)))
    :induct t
    :enable (canonical-order
             canonical-order-insert
             canonically-ordered-p))

  (defrule canonical-order-of-canonical-order
    (equal (canonical-order (canonical-order cps ver) ver)
           (canonical-order cps ver)))

  (defrulel undecomposable-listp-of-canonical-order-insert
    (implies (and (undecomposable-p cp compat ver1)
                  (undecomposable-listp cps compat ver1))
             (undecomposable-listp (canonical-order-insert cp cps ver)
                                   compat
                                   ver1))
    :induct t
    :enable (canonical-order-insert
             undecomposable-listp))

  (defrule undecomposable-listp-of-canonical-order
    (implies (undecomposable-listp cps compat ver1)
             (undecomposable-listp (canonical-order cps ver) compat ver1))
    :induct t
    :enable (canonical-order
             undecomposable-listp)))

;;;;;;;;;;;;;;;;;;;;

(defsection canonical-ordering-before-decomposition
  :short "Putting a list of code points in canonical order
          before decomposing it
          does not change the canonical order of its decomposition."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, decomposing the canonical order of a list
     and decomposing the list
     give two lists that have the same canonical order.
     This holds for the canonical decompositions
     and for the compatibility decompositions.")
   (xdoc::p
    "The reason is this.
     Canonical ordering moves a non-starter
     past non-starters of lower classes.
     Every code point in the decomposition of a non-starter
     has the class of that non-starter;
     we prove this by checking it on every code point,
     for each table of decompositions of each version.
     So, when a non-starter has moved past another one,
     the decompositions of the two are in the other order,
     but they consist of non-starters of two different classes,
     and canonical ordering does not depend on
     the order of non-starters of different classes.")
   (xdoc::p
    "In the proof we use
     the canonical order of a list followed by another list
     as a function of the first list
     and of the canonical order of the second one."))

  ;; Put a list of code points in canonical order
  ;; in front of a list that is in canonical order.
  ;; The canonical order of two lists, one after the other,
  ;; is this function of the first list
  ;; and of the canonical order of the second list.

  (local
   (define canonical-order-onto ((cps code-point-listp)
                                 (ordered code-point-listp)
                                 (ver versionp))
     :returns (new-cps code-point-listp)
     (b* (((when (endp cps)) (code-point-list-fix ordered))
          (cp (code-point-fix (car cps)))
          (rest (canonical-order-onto (cdr cps) ordered ver)))
       (if (equal (canonical-combining-class cp ver) 0)
           (cons cp rest)
         (canonical-order-insert cp rest ver)))
     :measure (len cps)
     :verify-guards :after-returns))

  (defruledl canonical-order-of-append
    (equal (canonical-order (append cps1 cps2) ver)
           (canonical-order-onto cps1 (canonical-order cps2 ver) ver))
    :induct (canonical-order cps1 ver)
    :enable (canonical-order
             canonical-order-onto))

  ;; Check that a code point has a given class,
  ;; and that all the code points of a list do,
  ;; with a table of classes.

  (local
   (define class-is-p ((cp code-point-p)
                       (class natp)
                       (map combining-class-mapp))
     :returns (yes/no booleanp)
     (equal (combining-class-map-lookup cp map)
            (lnfix class))
     :hooks nil))

  (local
   (std::deflist classes-are-p (x class map)
     :guard (and (code-point-listp x)
                 (natp class)
                 (combining-class-mapp map))
     (class-is-p x class map)))

  (defrulel class-is-p-of-canonical-combining-class-map
    (implies (natp class)
             (equal (class-is-p cp class (canonical-combining-class-map ver))
                    (equal (canonical-combining-class cp ver) class)))
    :enable (class-is-p
             canonical-combining-class))

  ;; Every code point in the decomposition of a non-starter
  ;; has the class of the non-starter.

  (local
   (define class-kept-ok ((cp code-point-p)
                          (full decomposition-mapp)
                          (map combining-class-mapp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp))
          (class (combining-class-map-lookup cp map)))
       (or (equal class 0)
           (classes-are-p (if (hangul-syllable-p cp)
                              (hangul-syllable-decomposition cp)
                            (decomposition-map-lookup cp full))
                          class
                          map)))
     :hooks nil))

  (local
   (std::deflist class-kept-ok-listp (x full map)
     :guard (and (code-point-listp x)
                 (decomposition-mapp full)
                 (combining-class-mapp map))
     (class-kept-ok x full map)))

  (defrulel class-kept-ok-listp-of-all-code-points
    (class-kept-ok-listp (all-code-points)
                         (if compat
                             (compatibility-decompositions ver)
                           (canonical-decompositions ver))
                         (canonical-combining-class-map ver))
    :enable (canonical-decompositions
             compatibility-decompositions
             canonical-combining-class-map
             (:e all-code-points))
    :disable class-kept-ok-listp-of-cons)

  (defrulel classes-are-p-of-decomposition
    (implies (< 0 (canonical-combining-class cp ver))
             (classes-are-p (decomposition cp compat ver)
                            (canonical-combining-class cp ver)
                            (canonical-combining-class-map ver)))
    :enable (decomposition
             canonical-combining-class
             class-kept-ok
             class-is-p)
    :use (:instance class-kept-ok-when-member-equal-of-class-kept-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (full (if compat
                              (compatibility-decompositions ver)
                            (canonical-decompositions ver)))
                    (map (canonical-combining-class-map ver))))

  ;; A non-starter can be put in front of an ordered list
  ;; before or after non-starters of one lower class.

  (defrulel canonical-order-onto-of-canonical-order-insert
    (implies (and (classes-are-p cps
                                 class
                                 (canonical-combining-class-map ver))
                  (natp class)
                  (not (equal class 0))
                  (< class (canonical-combining-class cp ver)))
             (equal (canonical-order-onto
                     cps
                     (canonical-order-insert cp ordered ver)
                     ver)
                    (canonical-order-insert
                     cp
                     (canonical-order-onto cps ordered ver)
                     ver)))
    :induct (canonical-order-onto cps ordered ver)
    :enable (canonical-order-onto
             canonical-order-insert-of-canonical-order-insert))

  ;; Non-starters of one class and non-starters of another class
  ;; can be put in front of an ordered list in either order.

  (defruledl canonical-order-onto-of-canonical-order-onto
    (implies (and (classes-are-p cps1
                                 class1
                                 (canonical-combining-class-map ver))
                  (classes-are-p cps2
                                 class2
                                 (canonical-combining-class-map ver))
                  (natp class1)
                  (natp class2)
                  (not (equal class1 0))
                  (< class1 class2))
             (equal (canonical-order-onto
                     cps1
                     (canonical-order-onto cps2 ordered ver)
                     ver)
                    (canonical-order-onto
                     cps2
                     (canonical-order-onto cps1 ordered ver)
                     ver)))
    :induct (canonical-order-onto cps2 ordered ver)
    :enable canonical-order-onto)

  ;; So can the decompositions of two non-starters of different classes.

  (defrulel canonical-order-onto-of-decomposition-of-decomposition
    (implies (and (not (equal (canonical-combining-class cp1 ver) 0))
                  (< (canonical-combining-class cp1 ver)
                     (canonical-combining-class cp2 ver)))
             (equal (canonical-order-onto
                     (decomposition cp1 compat ver)
                     (canonical-order-onto (decomposition cp2 compat ver)
                                           ordered
                                           ver)
                     ver)
                    (canonical-order-onto
                     (decomposition cp2 compat ver)
                     (canonical-order-onto (decomposition cp1 compat ver)
                                           ordered
                                           ver)
                     ver)))
    :use (:instance canonical-order-onto-of-canonical-order-onto
                    (cps1 (decomposition cp1 compat ver))
                    (cps2 (decomposition cp2 compat ver))
                    (class1 (canonical-combining-class cp1 ver))
                    (class2 (canonical-combining-class cp2 ver))))

  ;; Decomposing a list in which a code point has moved to its place
  ;; gives the same canonical order as
  ;; decomposing the code point and the list.

  (defrulel canonical-order-of-decompose-of-canonical-order-insert
    (equal (canonical-order
            (decompose (canonical-order-insert cp cps ver) compat ver)
            ver)
           (canonical-order
            (append (decomposition cp compat ver)
                    (decompose cps compat ver))
            ver))
    :induct (canonical-order-insert cp cps ver)
    :enable (canonical-order-insert
             decompose
             canonical-order-of-append))

  (defrule canonical-order-of-decompose-of-canonical-order
    (equal (canonical-order
            (decompose (canonical-order cps ver) compat ver)
            ver)
           (canonical-order (decompose cps compat ver) ver))
    :induct (canonical-order cps ver)
    :enable (canonical-order
             decompose
             canonical-order-of-append)))

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
    (implies (code-points-below-p cps #x300)
             (equal (canonical-compose-from-starter starter nil 0 cps ver)
                    (cons (code-point-fix starter)
                          (code-point-list-fix cps))))
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
    (implies (code-points-below-p cps #x300)
             (equal (canonical-compose cps ver)
                    (code-point-list-fix cps)))
    :enable (code-points-below-p
             canonical-combining-class-when-below-300
             canonical-compose-from-starter-when-all-below-300)
    :expand (canonical-compose cps ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection canonical-composition-theorems
  :short "Theorems about canonical composition."
  :long
  (xdoc::topstring
   (xdoc::p
    "Canonical composition can be undone:
     if a list of code points is fully decomposed and canonically ordered,
     then decomposing its canonical composition
     and putting the result in canonical order
     gives the list back.
     This holds for the canonical decompositions
     and for the compatibility decompositions.")
   (xdoc::p
    "The reason is this.
     When the last starter composes with a code point,
     the decomposition of the composite
     is the decomposition of the starter followed by that code point
     (see @(see decomposition-of-composition)).
     The code point was after the code points that had not composed;
     these are non-starters whose classes are lower than its own,
     since it was not blocked,
     so canonical ordering puts it back after them.")
   (xdoc::p
    "We prove, for @(tsee canonical-compose-from-starter),
     that the decomposition of its result,
     after any list of code points,
     has the same canonical order as
     the decomposition of the starter,
     the code points that have not composed
     and the code points still to be processed,
     after the same list.
     This holds if the code points that have not composed
     and the ones still to be processed are fully decomposed,
     the latter are canonically ordered,
     the former are non-starters
     whose classes do not exceed the @('last-ccc') argument,
     and that argument does not exceed the class of the next code point,
     unless the next code point is a starter.
     These conditions hold when the function is called on
     a list that is fully decomposed and canonically ordered,
     and each recursive call preserves them."))

  ;; Check that a code point is a non-starter whose class is below a bound,
  ;; and that all the code points of a list are.

  (local
   (define non-starter-below-p ((cp code-point-p) (bound natp) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((ccc (canonical-combining-class cp ver)))
       (and (not (equal ccc 0))
            (< ccc bound)))
     :hooks nil))

  (local
   (std::deflist non-starters-below-p (x bound ver)
     :guard (and (code-point-listp x)
                 (natp bound)
                 (versionp ver))
     (non-starter-below-p x bound ver)))

  (defrulel non-starters-below-p-when-below-smaller
    (implies (and (non-starters-below-p x bound1 ver)
                  (<= bound1 bound2))
             (non-starters-below-p x bound2 ver))
    :induct (non-starters-below-p x bound1 ver)
    :enable (non-starters-below-p
             non-starter-below-p))

  ;; A code point that is followed by non-starters of lower classes
  ;; can be moved after them without changing the canonical order:
  ;; at the start of the list, after one list, and after two lists.

  (defrulel canonical-order-of-cons-of-append-when-non-starters-below-p
    (implies (non-starters-below-p cps1
                                   (canonical-combining-class cp ver)
                                   ver)
             (equal (canonical-order (cons cp (append cps1 cps2)) ver)
                    (canonical-order (append cps1 (cons cp cps2)) ver)))
    :induct (non-starters-below-p cps1
                                  (canonical-combining-class cp ver)
                                  ver)
    :enable (non-starters-below-p
             non-starter-below-p
             canonical-order
             canonical-order-insert-of-canonical-order-insert))

  (defrulel canonical-order-of-append-of-cons-of-append
    (implies (non-starters-below-p cps1
                                   (canonical-combining-class cp ver)
                                   ver)
             (equal (canonical-order
                     (append cps (cons cp (append cps1 cps2)))
                     ver)
                    (canonical-order
                     (append cps (append cps1 (cons cp cps2)))
                     ver)))
    :induct (canonical-order cps ver)
    :enable canonical-order)

  (defrulel canonical-order-of-append-of-append-of-cons-of-append
    (implies (non-starters-below-p cps1
                                   (canonical-combining-class cp ver)
                                   ver)
             (equal (canonical-order
                     (append cps
                             (append cps0 (cons cp (append cps1 cps2))))
                     ver)
                    (canonical-order
                     (append cps
                             (append cps0 (append cps1 (cons cp cps2))))
                     ver)))
    :induct (canonical-order cps ver)
    :enable canonical-order)

  ;; What holds of the arguments of CANONICAL-COMPOSE-FROM-STARTER
  ;; other than the starter, when it is called by CANONICAL-COMPOSE
  ;; on a list that is fully decomposed and canonically ordered.

  (local
   (define compose-state-p ((pending code-point-listp)
                            (last-ccc natp)
                            (cps code-point-listp)
                            (compat booleanp)
                            (ver versionp))
     :returns (yes/no booleanp)
     (and (undecomposable-listp pending compat ver)
          (undecomposable-listp cps compat ver)
          (canonically-ordered-p cps ver)
          (non-starters-below-p pending (+ 1 last-ccc) ver)
          (or (endp pending)
              (endp cps)
              (equal (canonical-combining-class (car cps) ver) 0)
              (<= last-ccc (canonical-combining-class (car cps) ver))))
     :hooks nil))

  ;; What it says about the code points.

  (defrulel compose-state-p-forward
    (implies (compose-state-p pending last-ccc cps compat ver)
             (and (undecomposable-listp pending compat ver)
                  (undecomposable-listp cps compat ver)
                  (non-starters-below-p pending (+ 1 last-ccc) ver)))
    :rule-classes :forward-chaining
    :enable compose-state-p)

  ;; It holds again at each of the three recursive calls:
  ;; when the next code point composes with the starter,
  ;; when it is a new starter,
  ;; and when it is added to the code points that have not composed.

  (defrulel compose-state-p-after-composing
    (implies (and (compose-state-p pending last-ccc cps compat ver)
                  (consp cps)
                  (or (not (consp pending))
                      (< last-ccc
                         (canonical-combining-class (car cps) ver))))
             (compose-state-p pending last-ccc (cdr cps) compat ver))
    :enable (compose-state-p
             canonically-ordered-p))

  (defrulel compose-state-p-after-new-starter
    (implies (and (compose-state-p pending last-ccc cps compat ver)
                  (consp cps))
             (compose-state-p nil 0 (cdr cps) compat ver))
    :enable compose-state-p)

  (defrulel compose-state-p-after-not-composing
    (implies (and (compose-state-p pending last-ccc cps compat ver)
                  (consp cps)
                  (not (equal (canonical-combining-class (car cps) ver) 0)))
             (compose-state-p (cons (car cps) pending)
                              (canonical-combining-class (car cps) ver)
                              (cdr cps)
                              compat
                              ver))
    :enable (compose-state-p
             canonically-ordered-p
             non-starter-below-p))

  ;; The induction: as in CANONICAL-COMPOSE-FROM-STARTER,
  ;; with a list of code points that come before the result.
  ;; When a new starter is found,
  ;; the old starter and the code points that did not compose
  ;; are added to that list.

  (local
   (defun compose-induction (prefix starter pending last-ccc cps compat ver)
     (declare (xargs :measure (acl2-count cps)))
     (b* (((when (atom cps)) (list prefix starter pending last-ccc compat))
          (cp (car cps))
          (ccc (canonical-combining-class cp ver))
          (blocked (and (consp pending)
                        (>= last-ccc ccc)))
          (composite (and (not blocked)
                          (composition starter cp ver)))
          ((when composite)
           (compose-induction prefix
                              composite
                              pending
                              last-ccc
                              (cdr cps)
                              compat
                              ver))
          ((when (equal ccc 0))
           (compose-induction (append prefix
                                      (decomposition starter compat ver)
                                      (rev pending))
                              cp
                              nil
                              0
                              (cdr cps)
                              compat
                              ver)))
       (compose-induction prefix
                          starter
                          (cons cp pending)
                          ccc
                          (cdr cps)
                          compat
                          ver))))

  (defrulel canonical-order-of-append-of-decompose-of-compose-from-starter
    (implies (and (code-point-p starter)
                  (code-point-listp pending)
                  (natp last-ccc)
                  (code-point-listp cps)
                  (compose-state-p pending last-ccc cps compat ver))
             (equal (canonical-order
                     (append prefix
                             (decompose
                              (canonical-compose-from-starter starter
                                                              pending
                                                              last-ccc
                                                              cps
                                                              ver)
                              compat
                              ver))
                     ver)
                    (canonical-order
                     (append prefix
                             (decomposition starter compat ver)
                             (rev pending)
                             cps)
                     ver)))
    :induct (compose-induction prefix starter pending last-ccc cps compat ver)
    :expand ((:free (pending)
              (canonical-compose-from-starter starter pending last-ccc cps ver))
             (canonical-compose-from-starter starter pending last-ccc nil ver))
    :enable (decompose
             decomposition-when-undecomposable-p))

  (defrulel canonical-order-of-decompose-of-canonical-compose-from-starter
    (implies (and (undecomposable-p starter compat ver)
                  (undecomposable-listp cps compat ver)
                  (canonically-ordered-p cps ver))
             (equal (canonical-order
                     (decompose
                      (canonical-compose-from-starter starter nil 0 cps ver)
                      compat
                      ver)
                     ver)
                    (canonical-order (cons starter cps) ver)))
    :use (:instance
          canonical-order-of-append-of-decompose-of-compose-from-starter
          (prefix nil)
          (starter (code-point-fix starter))
          (pending nil)
          (last-ccc 0)
          (cps (code-point-list-fix cps)))
    :enable (compose-state-p
             decomposition-when-undecomposable-p)
    :disable canonical-order-of-append-of-decompose-of-compose-from-starter)

  (defrulel canonical-order-of-decompose-of-canonical-compose-lemma
    (implies (and (undecomposable-listp cps compat ver)
                  (canonically-ordered-p cps ver))
             (equal (canonical-order
                     (decompose (canonical-compose cps ver) compat ver)
                     ver)
                    (canonical-order cps ver)))
    :induct (canonical-compose cps ver)
    :enable (canonical-compose
             canonical-order
             canonically-ordered-p
             decompose
             decomposition-when-undecomposable-p)
    :disable canonical-order-when-canonically-ordered-p)

  (defrule canonical-order-of-decompose-of-canonical-compose
    (implies (and (undecomposable-listp cps compat ver)
                  (canonically-ordered-p cps ver))
             (equal (canonical-order
                     (decompose (canonical-compose cps ver) compat ver)
                     ver)
                    (code-point-list-fix cps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nfd ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form D (NFD), which is canonical decomposition,
          of a list of code points, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see normalization) for the names of the four forms."))
  (canonical-order (decompose cps nil ver) ver)

  ///

  (defrule scalar-value-listp-of-nfd
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfd cps ver))))

  (defrule undecomposable-listp-of-nfd
    (undecomposable-listp (nfd cps ver) nil ver))

  (defrule canonically-ordered-p-of-nfd
    (canonically-ordered-p (nfd cps ver) ver))

  (defrule nfd-when-undecomposable-listp-and-canonically-ordered-p
    (implies (and (undecomposable-listp cps nil ver)
                  (canonically-ordered-p cps ver))
             (equal (nfd cps ver)
                    (code-point-list-fix cps))))

  (defrule nfd-of-nfd
    (equal (nfd (nfd cps ver) ver)
           (nfd cps ver)))

  (defrule nfd-of-canonical-compose
    (implies (and (undecomposable-listp cps nil ver)
                  (canonically-ordered-p cps ver))
             (equal (nfd (canonical-compose cps ver) ver)
                    (code-point-list-fix cps)))))

;;;;;;;;;;;;;;;;;;;;

(define nfd-memberp ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :parents (normalization)
  :short "Check if a list of code points
          is in Normalization Form D (NFD),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of code points is in Normalization Form D
     if putting it in that form leaves it unchanged.
     This is @('isNFD') in [UAX #15, Section 2, Table 3].
     The lists that are in that form are the members of NFD,
     which is where the name of this predicate comes from."))
  (equal (nfd cps ver)
         (code-point-list-fix cps))
  :hooks (:fix)

  ///

  (defrule nfd-when-nfd-memberp
    (implies (nfd-memberp cps ver)
             (equal (nfd cps ver)
                    (code-point-list-fix cps))))

  (defrule nfd-memberp-of-nfd
    (nfd-memberp (nfd cps ver) ver))

  (defrule nfd-memberp-when-undecomposable-listp-and-canonically-ordered-p
    (implies (and (undecomposable-listp cps nil ver)
                  (canonically-ordered-p cps ver))
             (nfd-memberp cps ver)))

  ;; The NFD form of a list is fully decomposed and in canonical order.
  ;; So a list that is in NFD, which is its own NFD form, is too.
  ;; (The two theorems about the NFD form are disabled in these proofs,
  ;; because as rules they would rewrite their own instances to true.)

  (defrule undecomposable-listp-when-nfd-memberp
    (implies (nfd-memberp cps ver)
             (undecomposable-listp cps nil ver))
    :rule-classes (:rewrite :forward-chaining)
    :use undecomposable-listp-of-nfd
    :disable undecomposable-listp-of-nfd)

  (defrule canonically-ordered-p-when-nfd-memberp
    (implies (nfd-memberp cps ver)
             (canonically-ordered-p cps ver))
    :rule-classes (:rewrite :forward-chaining)
    :use canonically-ordered-p-of-nfd
    :disable canonically-ordered-p-of-nfd)

  (defruled nfd-memberp-alt-def
    (equal (nfd-memberp cps ver)
           (and (undecomposable-listp cps nil ver)
                (canonically-ordered-p cps ver)))
    :cases ((nfd-memberp cps ver))
    :disable nfd-memberp))

;;;;;;;;;;;;;;;;;;;;

(define nfc ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form C (NFC), which is
          canonical decomposition followed by canonical composition,
          of a list of code points, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see normalization) for the names of the four forms."))
  (canonical-compose (nfd cps ver) ver)

  ///

  (defrule scalar-value-listp-of-nfc
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfc cps ver))))

  (defrule nfc-of-nfd
    (equal (nfc (nfd cps ver) ver)
           (nfc cps ver)))

  (defrule nfd-of-nfc
    (equal (nfd (nfc cps ver) ver)
           (nfd cps ver)))

  (defrule nfc-of-nfc
    (equal (nfc (nfc cps ver) ver)
           (nfc cps ver))))

;;;;;;;;;;;;;;;;;;;;

(define nfc-memberp ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :parents (normalization)
  :short "Check if a list of code points
          is in Normalization Form C (NFC),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of code points is in Normalization Form C
     if putting it in that form leaves it unchanged.
     This is @('isNFC') in [UAX #15, Section 2, Table 3].
     The lists that are in that form are the members of NFC,
     which is where the name of this predicate comes from."))
  (equal (nfc cps ver)
         (code-point-list-fix cps))
  :hooks (:fix)

  ///

  (defrule nfc-when-nfc-memberp
    (implies (nfc-memberp cps ver)
             (equal (nfc cps ver)
                    (code-point-list-fix cps))))

  (defrule nfc-memberp-of-nfc
    (nfc-memberp (nfc cps ver) ver)))

;;;;;;;;;;;;;;;;;;;;

(define nfkd ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form KD (NFKD), which is compatibility decomposition,
          of a list of code points, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The letter K stands for compatibility.
     See @(see normalization) for the names of the four forms."))
  (canonical-order (decompose cps t ver) ver)

  ///

  (defrule scalar-value-listp-of-nfkd
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfkd cps ver))))

  (defrule undecomposable-listp-of-nfkd
    (undecomposable-listp (nfkd cps ver) t ver))

  (defrule canonically-ordered-p-of-nfkd
    (canonically-ordered-p (nfkd cps ver) ver))

  (defrule nfkd-when-undecomposable-listp-and-canonically-ordered-p
    (implies (and (undecomposable-listp cps t ver)
                  (canonically-ordered-p cps ver))
             (equal (nfkd cps ver)
                    (code-point-list-fix cps))))

  (defrule nfkd-of-nfkd
    (equal (nfkd (nfkd cps ver) ver)
           (nfkd cps ver)))

  (defrule nfd-of-nfkd
    (equal (nfd (nfkd cps ver) ver)
           (nfkd cps ver))
    :disable nfkd)

  (defrule nfkd-of-canonical-compose
    (implies (and (undecomposable-listp cps t ver)
                  (canonically-ordered-p cps ver))
             (equal (nfkd (canonical-compose cps ver) ver)
                    (code-point-list-fix cps))))

  (defrule nfkd-of-nfd
    (equal (nfkd (nfd cps ver) ver)
           (nfkd cps ver))
    :enable nfd)

  ;; NFC has the same NFD form as the list,
  ;; and the theorem just proved says that
  ;; the NFKD form of a list is that of its NFD form.

  (defrule nfkd-of-nfc
    (equal (nfkd (nfc cps ver) ver)
           (nfkd cps ver))
    :use (:instance nfkd-of-nfd (cps (nfc cps ver)))
    :disable nfkd))

;;;;;;;;;;;;;;;;;;;;

(define nfkd-memberp ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :parents (normalization)
  :short "Check if a list of code points
          is in Normalization Form KD (NFKD),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of code points is in Normalization Form KD
     if putting it in that form leaves it unchanged.
     This is @('isNFKD') in [UAX #15, Section 2, Table 3].
     The lists that are in that form are the members of NFKD,
     which is where the name of this predicate comes from.")
   (xdoc::p
    "The letter K stands for compatibility.
     See @(see normalization) for the names of the four forms."))
  (equal (nfkd cps ver)
         (code-point-list-fix cps))
  :hooks (:fix)

  ///

  (defrule nfkd-when-nfkd-memberp
    (implies (nfkd-memberp cps ver)
             (equal (nfkd cps ver)
                    (code-point-list-fix cps))))

  (defrule nfkd-memberp-of-nfkd
    (nfkd-memberp (nfkd cps ver) ver))

  (defrule nfkd-memberp-when-undecomposable-listp-and-canonically-ordered-p
    (implies (and (undecomposable-listp cps t ver)
                  (canonically-ordered-p cps ver))
             (nfkd-memberp cps ver)))

  ;; The NFKD form of a list is fully decomposed.
  ;; So a list that is in NFKD, which is its own NFKD form, is too.
  ;; (The theorem about the NFKD form is disabled in this proof,
  ;; because as a rule it would rewrite its own instance to true.)

  (defrule undecomposable-listp-when-nfkd-memberp
    (implies (nfkd-memberp cps ver)
             (undecomposable-listp cps t ver))
    :rule-classes (:rewrite :forward-chaining)
    :use undecomposable-listp-of-nfkd
    :disable undecomposable-listp-of-nfkd)

  ;; The NFKD form of a list is in NFD.
  ;; So a list that is in NFKD is in NFD.
  ;; (The first theorem is disabled in the proof of the second one,
  ;; because as a rule it would rewrite its own instance to true.)

  (defrule nfd-memberp-of-nfkd
    (nfd-memberp (nfkd cps ver) ver)
    :enable nfd-memberp)

  (defrule nfd-memberp-when-nfkd-memberp
    (implies (nfkd-memberp cps ver)
             (nfd-memberp cps ver))
    :rule-classes (:rewrite :forward-chaining)
    :use nfd-memberp-of-nfkd
    :disable nfd-memberp-of-nfkd)

  ;; A list that is in NFKD is in NFD, and so it is in canonical order.

  (defruled nfkd-memberp-alt-def
    (equal (nfkd-memberp cps ver)
           (and (undecomposable-listp cps t ver)
                (canonically-ordered-p cps ver)))
    :cases ((nfkd-memberp cps ver))
    :disable nfkd-memberp))

;;;;;;;;;;;;;;;;;;;;

(define nfkc ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form KC (NFKC), which is
          compatibility decomposition followed by canonical composition,
          of a list of code points, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The letter K stands for compatibility.
     See @(see normalization) for the names of the four forms."))
  (canonical-compose (nfkd cps ver) ver)

  ///

  (defrule scalar-value-listp-of-nfkc
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfkc cps ver))))

  (defrule nfkc-of-nfkd
    (equal (nfkc (nfkd cps ver) ver)
           (nfkc cps ver)))

  (defrule nfc-of-nfkd
    (equal (nfc (nfkd cps ver) ver)
           (nfkc cps ver))
    :enable nfc)

  (defrule nfkd-of-nfkc
    (equal (nfkd (nfkc cps ver) ver)
           (nfkd cps ver)))

  (defrule nfkc-of-nfkc
    (equal (nfkc (nfkc cps ver) ver)
           (nfkc cps ver)))

  (defrule nfd-of-nfkc
    (equal (nfd (nfkc cps ver) ver)
           (nfkd cps ver)))

  (defrule nfc-of-nfkc
    (equal (nfc (nfkc cps ver) ver)
           (nfkc cps ver))
    :enable nfc)

  (defrule nfkc-of-nfd
    (equal (nfkc (nfd cps ver) ver)
           (nfkc cps ver)))

  (defrule nfkc-of-nfc
    (equal (nfkc (nfc cps ver) ver)
           (nfkc cps ver))))

;;;;;;;;;;;;;;;;;;;;

(define nfkc-memberp ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :parents (normalization)
  :short "Check if a list of code points
          is in Normalization Form KC (NFKC),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of code points is in Normalization Form KC
     if putting it in that form leaves it unchanged.
     This is @('isNFKC') in [UAX #15, Section 2, Table 3].
     The lists that are in that form are the members of NFKC,
     which is where the name of this predicate comes from.")
   (xdoc::p
    "The letter K stands for compatibility.
     See @(see normalization) for the names of the four forms."))
  (equal (nfkc cps ver)
         (code-point-list-fix cps))
  :hooks (:fix)

  ///

  (defrule nfkc-when-nfkc-memberp
    (implies (nfkc-memberp cps ver)
             (equal (nfkc cps ver)
                    (code-point-list-fix cps))))

  (defrule nfkc-memberp-of-nfkc
    (nfkc-memberp (nfkc cps ver) ver))

  ;; The NFKC form of a list is in NFC.
  ;; So a list that is in NFKC is in NFC.
  ;; (The first theorem is disabled in the proof of the second one,
  ;; because as a rule it would rewrite its own instance to true.)

  (defrule nfc-memberp-of-nfkc
    (nfc-memberp (nfkc cps ver) ver)
    :enable nfc-memberp)

  (defrule nfc-memberp-when-nfkc-memberp
    (implies (nfkc-memberp cps ver)
             (nfc-memberp cps ver))
    :rule-classes (:rewrite :forward-chaining)
    :use nfc-memberp-of-nfkc
    :disable nfc-memberp-of-nfkc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The decomposed forms of a list, in terms of other forms of the list.
;; These rules are for the theorems about equivalence below,
;; where two lists are known to have the same form of one kind
;; and their forms of another kind are to be shown equal.
;; The right sides are the definitions of NFD and NFKD, unfolded,
;; so that the rules do not apply to their own results.

(defruledl nfd-in-terms-of-nfc
  (equal (nfd cps ver)
         (canonical-order (decompose (nfc cps ver) nil ver) ver))
  :enable nfc)

(defruledl nfkd-in-terms-of-nfd
  (equal (nfkd cps ver)
         (canonical-order (decompose (nfd cps ver) t ver) ver))
  :enable (nfkd nfd))

(defruledl nfkd-in-terms-of-nfkc
  (equal (nfkd cps ver)
         (canonical-order (decompose (nfkc cps ver) t ver) ver))
  :enable nfkc)

;;;;;;;;;;;;;;;;;;;;

(define canonical-equivalent-p ((cps1 code-point-listp)
                                (cps2 code-point-listp)
                                (ver versionp))
  :returns (yes/no booleanp)
  :parents (normalization)
  :short "Check if two lists of code points are canonical equivalents
          [Unicode, D70], in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two sequences of code points are canonical equivalents
     if their full canonical decompositions are identical [Unicode, D70],
     that is, if they have the same form
     in Normalization Form D (NFD), which is canonical decomposition.
     Canonical equivalents stand for the same text:
     a process is not to assume that they are to be interpreted differently
     [Unicode, C6].")
   (xdoc::p
    "This is an equivalence relation:
     it is reflexive, symmetric and transitive.
     A list is a canonical equivalent of its NFD form,
     and of its form in Normalization Form C (NFC), which is
     canonical decomposition followed by canonical composition;
     so either form of a list can take the place of the list
     as an argument of this predicate.
     Two lists are canonical equivalents
     exactly when they have the same NFC form,
     which is how programming languages usually compare identifiers
     (see @(see normalization)).")
   (xdoc::p
    "Canonical equivalents are also compatibility equivalents:
     see @(tsee compatibility-equivalent-p)."))
  (equal (nfd cps1 ver)
         (nfd cps2 ver))
  :hooks (:fix)

  ///

  (defrule canonical-equivalent-p-reflexive
    (canonical-equivalent-p cps cps ver))

  (defrule canonical-equivalent-p-symmetric
    (equal (canonical-equivalent-p cps1 cps2 ver)
           (canonical-equivalent-p cps2 cps1 ver)))

  (defruled canonical-equivalent-p-transitive
    (implies (and (canonical-equivalent-p cps1 cps2 ver)
                  (canonical-equivalent-p cps2 cps3 ver))
             (canonical-equivalent-p cps1 cps3 ver)))

  (defrule canonical-equivalent-p-of-nfd-arg1
    (equal (canonical-equivalent-p (nfd cps1 ver) cps2 ver)
           (canonical-equivalent-p cps1 cps2 ver)))

  (defrule canonical-equivalent-p-of-nfd-arg2
    (equal (canonical-equivalent-p cps1 (nfd cps2 ver) ver)
           (canonical-equivalent-p cps1 cps2 ver)))

  (defrule canonical-equivalent-p-of-nfc-arg1
    (equal (canonical-equivalent-p (nfc cps1 ver) cps2 ver)
           (canonical-equivalent-p cps1 cps2 ver)))

  (defrule canonical-equivalent-p-of-nfc-arg2
    (equal (canonical-equivalent-p cps1 (nfc cps2 ver) ver)
           (canonical-equivalent-p cps1 cps2 ver)))

  ;; Two lists with the same NFD form have the same NFC form,
  ;; which is the canonical composition of that NFD form.
  ;; Two lists with the same NFC form have the same NFD form,
  ;; which is the NFD form of that NFC form.

  (defrulel equal-of-nfc-and-nfc-when-equal-of-nfd-and-nfd
    (implies (equal (nfd cps1 ver) (nfd cps2 ver))
             (equal (equal (nfc cps1 ver) (nfc cps2 ver))
                    t))
    :enable nfc)

  (defrulel equal-of-nfd-and-nfd-when-equal-of-nfc-and-nfc
    (implies (equal (nfc cps1 ver) (nfc cps2 ver))
             (equal (equal (nfd cps1 ver) (nfd cps2 ver))
                    t))
    :enable nfd-in-terms-of-nfc)

  (defruled canonical-equivalent-p-in-terms-of-nfc
    (equal (canonical-equivalent-p cps1 cps2 ver)
           (equal (nfc cps1 ver)
                  (nfc cps2 ver)))))

;;;;;;;;;;;;;;;;;;;;

(define compatibility-equivalent-p ((cps1 code-point-listp)
                                    (cps2 code-point-listp)
                                    (ver versionp))
  :returns (yes/no booleanp)
  :parents (normalization)
  :short "Check if two lists of code points are compatibility equivalents
          [Unicode, D67], in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two sequences of code points are compatibility equivalents
     if their full compatibility decompositions are identical [Unicode, D67],
     that is, if they have the same form
     in Normalization Form KD (NFKD), which is compatibility decomposition.
     (The letter K stands for compatibility:
     see @(see normalization) for the names of the four forms.)
     Compatibility equivalents may differ in appearance or in behavior,
     for example in font or in width.")
   (xdoc::p
    "This is an equivalence relation:
     it is reflexive, symmetric and transitive.
     A list is a compatibility equivalent of each of its four forms,
     so any form of a list can take the place of the list
     as an argument of this predicate.
     Two lists are compatibility equivalents
     exactly when they have the same form
     in Normalization Form KC (NFKC), which is
     compatibility decomposition followed by canonical composition.")
   (xdoc::p
    "Canonical equivalents (see @(tsee canonical-equivalent-p))
     are also compatibility equivalents [Unicode, Section 3.7]."))
  (equal (nfkd cps1 ver)
         (nfkd cps2 ver))
  :hooks (:fix)

  ///

  (defrule compatibility-equivalent-p-reflexive
    (compatibility-equivalent-p cps cps ver))

  (defrule compatibility-equivalent-p-symmetric
    (equal (compatibility-equivalent-p cps1 cps2 ver)
           (compatibility-equivalent-p cps2 cps1 ver)))

  (defruled compatibility-equivalent-p-transitive
    (implies (and (compatibility-equivalent-p cps1 cps2 ver)
                  (compatibility-equivalent-p cps2 cps3 ver))
             (compatibility-equivalent-p cps1 cps3 ver)))

  (defrule compatibility-equivalent-p-of-nfd-arg1
    (equal (compatibility-equivalent-p (nfd cps1 ver) cps2 ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  (defrule compatibility-equivalent-p-of-nfd-arg2
    (equal (compatibility-equivalent-p cps1 (nfd cps2 ver) ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  (defrule compatibility-equivalent-p-of-nfc-arg1
    (equal (compatibility-equivalent-p (nfc cps1 ver) cps2 ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  (defrule compatibility-equivalent-p-of-nfc-arg2
    (equal (compatibility-equivalent-p cps1 (nfc cps2 ver) ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  (defrule compatibility-equivalent-p-of-nfkd-arg1
    (equal (compatibility-equivalent-p (nfkd cps1 ver) cps2 ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  (defrule compatibility-equivalent-p-of-nfkd-arg2
    (equal (compatibility-equivalent-p cps1 (nfkd cps2 ver) ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  (defrule compatibility-equivalent-p-of-nfkc-arg1
    (equal (compatibility-equivalent-p (nfkc cps1 ver) cps2 ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  (defrule compatibility-equivalent-p-of-nfkc-arg2
    (equal (compatibility-equivalent-p cps1 (nfkc cps2 ver) ver)
           (compatibility-equivalent-p cps1 cps2 ver)))

  ;; Two lists with the same NFKD form have the same NFKC form,
  ;; which is the canonical composition of that NFKD form.
  ;; Two lists with the same NFKC form have the same NFKD form,
  ;; which is the NFKD form of that NFKC form.

  (defrulel equal-of-nfkc-and-nfkc-when-equal-of-nfkd-and-nfkd
    (implies (equal (nfkd cps1 ver) (nfkd cps2 ver))
             (equal (equal (nfkc cps1 ver) (nfkc cps2 ver))
                    t))
    :enable nfkc)

  (defrulel equal-of-nfkd-and-nfkd-when-equal-of-nfkc-and-nfkc
    (implies (equal (nfkc cps1 ver) (nfkc cps2 ver))
             (equal (equal (nfkd cps1 ver) (nfkd cps2 ver))
                    t))
    :enable nfkd-in-terms-of-nfkc)

  (defruled compatibility-equivalent-p-in-terms-of-nfkc
    (equal (compatibility-equivalent-p cps1 cps2 ver)
           (equal (nfkc cps1 ver)
                  (nfkc cps2 ver))))

  ;; Two lists with the same NFD form have the same NFKD form,
  ;; which is the NFKD form of that NFD form.

  (defrule compatibility-equivalent-p-when-canonical-equivalent-p
    (implies (canonical-equivalent-p cps1 cps2 ver)
             (compatibility-equivalent-p cps1 cps2 ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (canonical-equivalent-p
             nfkd-in-terms-of-nfd)))

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
     So such a list is in each of the four forms
     (see @(tsee nfc-memberp) and the other three predicates).
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
    (implies (code-points-below-p cps #xA0)
             (equal (nfd cps ver)
                    (code-point-list-fix cps)))
    :enable (nfd
             decompose-when-all-below-a0
             canonical-order-when-all-below-300
             code-points-below-p-when-below-smaller))

  (defrule nfc-when-all-below-a0
    (implies (code-points-below-p cps #xA0)
             (equal (nfc cps ver)
                    (code-point-list-fix cps)))
    :enable (nfc
             canonical-compose-when-all-below-300
             code-points-below-p-when-below-smaller))

  (defrule nfkd-when-all-below-a0
    (implies (code-points-below-p cps #xA0)
             (equal (nfkd cps ver)
                    (code-point-list-fix cps)))
    :enable (nfkd
             decompose-when-all-below-a0
             canonical-order-when-all-below-300
             code-points-below-p-when-below-smaller))

  (defrule nfkc-when-all-below-a0
    (implies (code-points-below-p cps #xA0)
             (equal (nfkc cps ver)
                    (code-point-list-fix cps)))
    :enable (nfkc
             canonical-compose-when-all-below-300
             code-points-below-p-when-below-smaller))

  (defrule nfd-memberp-when-all-below-a0
    (implies (code-points-below-p cps #xA0)
             (nfd-memberp cps ver))
    :enable nfd-memberp)

  (defrule nfc-memberp-when-all-below-a0
    (implies (code-points-below-p cps #xA0)
             (nfc-memberp cps ver))
    :enable nfc-memberp)

  (defrule nfkd-memberp-when-all-below-a0
    (implies (code-points-below-p cps #xA0)
             (nfkd-memberp cps ver))
    :enable nfkd-memberp)

  (defrule nfkc-memberp-when-all-below-a0
    (implies (code-points-below-p cps #xA0)
             (nfkc-memberp cps ver))
    :enable nfkc-memberp))
