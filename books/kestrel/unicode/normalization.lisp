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
     so a fully decomposed list stays fully decomposed."))

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

  ;; Two non-starters of different classes
  ;; can be put in front of a list in either order.

  (defruledl canonical-order-insert-of-canonical-order-insert
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
  :short "Normalization Form D (canonical decomposition)
          of a list of code points, in a version of Unicode."
  (canonical-order (decompose cps nil ver) ver)

  ///

  (defrule scalar-value-listp-of-nfd
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfd cps ver))))

  (defrule undecomposable-listp-of-nfd
    (undecomposable-listp (nfd cps ver) nil ver))

  (defrule canonically-ordered-p-of-nfd
    (canonically-ordered-p (nfd cps ver) ver))

  (defrule nfd-of-nfd
    (equal (nfd (nfd cps ver) ver)
           (nfd cps ver)))

  (defrule nfd-of-canonical-compose
    (implies (and (undecomposable-listp cps nil ver)
                  (canonically-ordered-p cps ver))
             (equal (nfd (canonical-compose cps ver) ver)
                    (code-point-list-fix cps)))))

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

(define nfkd ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :parents (normalization)
  :short "Normalization Form KD (compatibility decomposition)
          of a list of code points, in a version of Unicode."
  (canonical-order (decompose cps t ver) ver)

  ///

  (defrule scalar-value-listp-of-nfkd
    (implies (scalar-value-listp cps)
             (scalar-value-listp (nfkd cps ver))))

  (defrule undecomposable-listp-of-nfkd
    (undecomposable-listp (nfkd cps ver) t ver))

  (defrule canonically-ordered-p-of-nfkd
    (canonically-ordered-p (nfkd cps ver) ver))

  (defrule nfkd-of-nfkd
    (equal (nfkd (nfkd cps ver) ver)
           (nfkd cps ver)))

  (defrule nfd-of-nfkd
    (equal (nfd (nfkd cps ver) ver)
           (nfkd cps ver))
    :enable nfd
    :disable nfkd
    :use (undecomposable-listp-of-nfkd
          canonically-ordered-p-of-nfkd))

  (defrule nfkd-of-canonical-compose
    (implies (and (undecomposable-listp cps t ver)
                  (canonically-ordered-p cps ver))
             (equal (nfkd (canonical-compose cps ver) ver)
                    (code-point-list-fix cps)))))

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
    :enable nfc))

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
