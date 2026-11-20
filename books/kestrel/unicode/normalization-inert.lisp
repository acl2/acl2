; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "composing-pairs")
(include-book "normalization")
(include-book "pattern-white-space")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ normalization-inert-code-points
  :parents (normalization)
  :short "Code points that the normalization forms leave alone,
          and across which the normalization forms do not reach."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call a code point inert under normalization
     if it is a starter,
     it has no decomposition, canonical or compatibility,
     and it composes neither with a code point after it
     nor with a code point before it
     (see @(tsee normalization-inert-p)).
     The word `inert' is ours, not the standard's.")
   (xdoc::p
    "The main theorems say that such a code point
     splits the text in two parts that are normalized separately.
     For each of the four normalization forms,
     which are Normalization Forms D, C, KD and KC
     (NFD, NFC, NFKD and NFKC: see @(see normalization)),
     and in every supported version of Unicode:
     the form of a list, followed by an inert code point,
     followed by another list,
     is the form of the first list,
     followed by the same code point,
     followed by the form of the second list.")
   (xdoc::p
    "So an inert code point is stable under each of the four forms
     in the sense of [UAX #15, Section 9.1]:
     it is a starter;
     a form does not change it;
     it does not compose with a previous or with a following character;
     and it does not change when characters are added around it.
     The definition here is a sufficient condition for all four forms at once;
     we do not prove that it is a necessary one.")
   (xdoc::p
    "This is what a language needs to know about its delimiters
     if it normalizes its identifiers, or its whole source text:
     if the delimiters are inert,
     normalizing the text is the same as normalizing each piece
     between delimiters,
     and normalization neither joins a delimiter to its neighbors
     nor changes it.
     The predicate is executable,
     so that a given code point is inert in a given version
     is proved by evaluation.
     The ASCII code points other than the letters
     and @('<'), @('='), @('>') are inert, in every supported version,
     and so are @('Q') and @('q').
     The other letters, and those three characters,
     compose with a combining mark after them.
     The code points with the @('Pattern_White_Space') property
     are inert too.")
   (xdoc::p
    "These theorems generalize
     the ones about a dollar sign or an underscore at the start of a list,
     in @(see identifier-closure-with-optional-start)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalization-inert-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is inert under normalization,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if it is a starter,
     it is its own compatibility decomposition
     (and thus also its own canonical decomposition),
     it does not compose with any code point after it,
     and it does not compose with any code point before it."))
  (and (starter-p cp ver)
       (undecomposable-p cp t ver)
       (not (composes-with-following-p cp ver))
       (not (composes-with-previous-p cp ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection canonical-ordering-around-starter
  :short "Canonical ordering does not move code points past a starter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The canonical order of a list, followed by a starter,
     followed by another list,
     is the canonical order of the first list,
     followed by the starter,
     followed by the canonical order of the second list.
     This is because canonical ordering
     only exchanges adjacent non-starters [Unicode, D108, D109]."))

  (defrulel canonical-order-insert-of-append-of-cons-when-starter-p
    (implies (starter-p starter ver)
             (equal (canonical-order-insert cp
                                            (append cps1 (cons starter cps2))
                                            ver)
                    (append (canonical-order-insert cp cps1 ver)
                            (cons (code-point-fix starter)
                                  (code-point-list-fix cps2)))))
    :induct (canonical-order-insert cp cps1 ver)
    :enable (canonical-order-insert
             starter-p))

  (defruled canonical-order-of-append-of-cons-when-starter-p
    (implies (starter-p cp ver)
             (equal (canonical-order (append cps1 (cons cp cps2)) ver)
                    (append (canonical-order cps1 ver)
                            (cons (code-point-fix cp)
                                  (canonical-order cps2 ver)))))
    :induct (canonical-order cps1 ver)
    :enable (canonical-order
             starter-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection canonical-composition-around-starter
  :short "Canonical composition stops at a starter
          that does not compose with a code point before it,
          and starts again after a starter
          that does not compose with a code point after it."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem is about a starter that does not compose
     with any code point before it
     (see @(tsee composes-with-previous-p)):
     the canonical composition of a list, followed by such a starter,
     followed by another list,
     is the canonical composition of the first list,
     followed by the canonical composition
     of the starter and the second list.")
   (xdoc::p
    "The second theorem is about a starter that does not compose
     with any code point after it
     (see @(tsee composes-with-following-p)):
     the canonical composition of such a starter followed by a list
     is the starter followed by the canonical composition of the list.
     The theorem before it says the same of
     @(tsee canonical-compose-from-starter),
     with the code points that have not composed after the starter."))

  ;; From a starter on: the starter that does not compose with what is before
  ;; ends the work on the starter before it.

  (defrulel canonical-compose-from-starter-of-append-of-cons
    (implies (and (starter-p cp ver)
                  (not (composes-with-previous-p cp ver)))
             (equal (canonical-compose-from-starter starter
                                                    pending
                                                    last-ccc
                                                    (append cps1
                                                            (cons cp cps2))
                                                    ver)
                    (append (canonical-compose-from-starter starter
                                                            pending
                                                            last-ccc
                                                            cps1
                                                            ver)
                            (canonical-compose (cons cp cps2) ver))))
    :induct (canonical-compose-from-starter starter pending last-ccc cps1 ver)
    :enable (canonical-compose-from-starter
             canonical-compose
             starter-p
             composition-when-not-composes-with-previous-p))

  (defruled canonical-compose-of-append-when-not-composes-with-previous-p
    (implies (and (starter-p cp ver)
                  (not (composes-with-previous-p cp ver)))
             (equal (canonical-compose (append cps1 (cons cp cps2)) ver)
                    (append (canonical-compose cps1 ver)
                            (canonical-compose (cons cp cps2) ver))))
    :induct (canonical-compose cps1 ver)
    :enable canonical-compose)

  ;; From a starter that does not compose with what is after it,
  ;; the code points after it are composed among themselves.

  (defruled canonical-compose-from-starter-when-not-composes-with-following-p
    (implies (not (composes-with-following-p starter ver))
             (equal (canonical-compose-from-starter starter
                                                    pending
                                                    last-ccc
                                                    cps
                                                    ver)
                    (cons (code-point-fix starter)
                          (append (rev (code-point-list-fix pending))
                                  (canonical-compose cps ver)))))
    :induct (canonical-compose-from-starter starter pending last-ccc cps ver)
    :enable (canonical-compose-from-starter
             canonical-compose
             composition-when-not-composes-with-following-p))

  (defruled canonical-compose-of-cons-when-not-composes-with-following-p
    (implies (and (starter-p cp ver)
                  (not (composes-with-following-p cp ver)))
             (equal (canonical-compose (cons cp cps) ver)
                    (cons (code-point-fix cp)
                          (canonical-compose cps ver))))
    :enable
    (canonical-compose
     starter-p
     canonical-compose-from-starter-when-not-composes-with-following-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection normalization-around-inert-code-point
  :short "Each normalization form normalizes separately
          what is before and what is after an inert code point,
          and leaves the code point as it is."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see normalization-inert-code-points).
     There is a theorem for each of the four forms,
     for an inert code point between two lists.
     From it we get the case of an inert code point at the start of a list,
     the fact that an inert code point alone is in each of the four forms,
     and the fact that two lists that are in a form
     are still in that form when they are put together
     with an inert code point between them."))

  (defrule nfd-of-append-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfd (append cps1 (cons cp cps2)) ver)
                    (append (nfd cps1 ver)
                            (cons (code-point-fix cp)
                                  (nfd cps2 ver)))))
    :enable (normalization-inert-p
             nfd
             decompose
             decomposition-when-undecomposable-p
             canonical-order-of-append-of-cons-when-starter-p))

  (defrule nfkd-of-append-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfkd (append cps1 (cons cp cps2)) ver)
                    (append (nfkd cps1 ver)
                            (cons (code-point-fix cp)
                                  (nfkd cps2 ver)))))
    :enable (normalization-inert-p
             nfkd
             decompose
             decomposition-when-undecomposable-p
             canonical-order-of-append-of-cons-when-starter-p))

  (defrule nfc-of-append-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfc (append cps1 (cons cp cps2)) ver)
                    (append (nfc cps1 ver)
                            (cons (code-point-fix cp)
                                  (nfc cps2 ver)))))
    :enable
    (normalization-inert-p
     nfc
     canonical-compose-of-append-when-not-composes-with-previous-p
     canonical-compose-of-cons-when-not-composes-with-following-p))

  (defrule nfkc-of-append-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfkc (append cps1 (cons cp cps2)) ver)
                    (append (nfkc cps1 ver)
                            (cons (code-point-fix cp)
                                  (nfkc cps2 ver)))))
    :enable
    (normalization-inert-p
     nfkc
     canonical-compose-of-append-when-not-composes-with-previous-p
     canonical-compose-of-cons-when-not-composes-with-following-p))

  ;; An inert code point at the start of a list.

  (defrule nfd-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfd (cons cp cps) ver)
                    (cons (code-point-fix cp)
                          (nfd cps ver))))
    :enable (normalization-inert-p
             nfd
             decompose
             decomposition-when-undecomposable-p
             canonical-order
             starter-p))

  (defrule nfc-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfc (cons cp cps) ver)
                    (cons (code-point-fix cp)
                          (nfc cps ver))))
    :enable (normalization-inert-p
             nfc
             canonical-compose-of-cons-when-not-composes-with-following-p))

  (defrule nfkd-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfkd (cons cp cps) ver)
                    (cons (code-point-fix cp)
                          (nfkd cps ver))))
    :enable (normalization-inert-p
             nfkd
             decompose
             decomposition-when-undecomposable-p
             canonical-order
             starter-p))

  (defrule nfkc-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfkc (cons cp cps) ver)
                    (cons (code-point-fix cp)
                          (nfkc cps ver))))
    :enable (normalization-inert-p
             nfkc
             canonical-compose-of-cons-when-not-composes-with-following-p))

  ;; Membership in the forms.

  (defrule nfd-memberp-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfd-memberp (cons cp cps) ver)
                    (nfd-memberp cps ver)))
    :enable nfd-memberp)

  (defrule nfc-memberp-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfc-memberp (cons cp cps) ver)
                    (nfc-memberp cps ver)))
    :enable nfc-memberp)

  (defrule nfkd-memberp-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfkd-memberp (cons cp cps) ver)
                    (nfkd-memberp cps ver)))
    :enable nfkd-memberp)

  (defrule nfkc-memberp-of-cons-when-normalization-inert-p
    (implies (normalization-inert-p cp ver)
             (equal (nfkc-memberp (cons cp cps) ver)
                    (nfkc-memberp cps ver)))
    :enable nfkc-memberp)

  (defrule nfd-memberp-of-append-of-cons-when-normalization-inert-p
    (implies (and (normalization-inert-p cp ver)
                  (nfd-memberp cps1 ver)
                  (nfd-memberp cps2 ver))
             (nfd-memberp (append cps1 (cons cp cps2)) ver))
    :enable nfd-memberp)

  (defrule nfc-memberp-of-append-of-cons-when-normalization-inert-p
    (implies (and (normalization-inert-p cp ver)
                  (nfc-memberp cps1 ver)
                  (nfc-memberp cps2 ver))
             (nfc-memberp (append cps1 (cons cp cps2)) ver))
    :enable nfc-memberp)

  (defrule nfkd-memberp-of-append-of-cons-when-normalization-inert-p
    (implies (and (normalization-inert-p cp ver)
                  (nfkd-memberp cps1 ver)
                  (nfkd-memberp cps2 ver))
             (nfkd-memberp (append cps1 (cons cp cps2)) ver))
    :enable nfkd-memberp)

  (defrule nfkc-memberp-of-append-of-cons-when-normalization-inert-p
    (implies (and (normalization-inert-p cp ver)
                  (nfkc-memberp cps1 ver)
                  (nfkc-memberp cps2 ver))
             (nfkc-memberp (append cps1 (cons cp cps2)) ver))
    :enable nfkc-memberp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection inert-ascii-code-points
  :short "The ASCII code points that are inert under normalization."
  :long
  (xdoc::topstring
   (xdoc::p
    "In every supported version of Unicode,
     an ASCII code point is inert under normalization
     (see @(tsee normalization-inert-p))
     exactly when it does not compose with a code point after it.
     So the ASCII code points that are not inert are
     the three characters @('<'), @('='), @('>'),
     and the letters other than @('Q') and @('q').
     The theorem lists them as five ranges.")
   (xdoc::p
    "In particular the ASCII digits, the space, the control characters,
     and the ASCII punctuation and symbols other than those three
     are inert.")
   (xdoc::p
    "This follows from facts about the code points below @('#xA0')
     and below @('#x300') that are proved elsewhere:
     see @(see normalization-of-ascii)
     and @(see composing-pairs-theorems)."))

  (defruled normalization-inert-p-when-ascii
    (implies (< (code-point-fix cp) #x80)
             (equal (normalization-inert-p cp ver)
                    (b* ((n (code-point-fix cp)))
                      (not (or (and (<= #x3C n) (<= n #x3E))
                               (and (<= #x41 n) (<= n #x50))
                               (and (<= #x52 n) (<= n #x5A))
                               (and (<= #x61 n) (<= n #x70))
                               (and (<= #x72 n) (<= n #x7A)))))))
    :enable (normalization-inert-p
             starter-p-when-below-300
             undecomposable-p
             decomposition-when-below-a0
             not-composes-with-previous-p-when-below-300
             composes-with-following-p-when-ascii)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection inert-pattern-white-space
  :short "The code points with the @('Pattern_White_Space') property
          are inert under normalization."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee pattern-white-space-p) and @(tsee normalization-inert-p).
     So in a language whose white space is defined by that property,
     as [UAX #31] recommends,
     normalization does not reach across white space:
     normalizing the text is the same as
     normalizing each piece between two white space characters.")
   (xdoc::p
    "We prove it by checking it on every code point, for each version."))

  (local
   (define space-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (not (pattern-white-space-p cp ver))
         (normalization-inert-p cp ver))))

  (local
   (std::deflist space-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (space-ok x ver)))

  (defrulel space-ok-listp-of-all-code-points
    (space-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable space-ok-listp-of-cons)

  (defrule normalization-inert-p-when-pattern-white-space-p
    (implies (pattern-white-space-p cp ver)
             (normalization-inert-p cp ver))
    :enable space-ok
    :use (:instance space-ok-when-member-equal-of-space-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))))
