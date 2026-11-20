; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "normalization-inert")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ normalization-members
  :parents (normalization)
  :short "Which code points can occur in the normalization forms of a list,
          given the code points of the list."
  :long
  (xdoc::topstring
   (xdoc::p
    "A language that normalizes its source text,
     or parts of it,
     needs to know that normalization
     does not bring in characters of its syntax
     that were not in the text.
     The theorems here say where certain code points
     of a normalization form of a list come from
     (see @(see normalization) for the four forms,
     which are NFD, NFC, NFKD and NFKC).")
   (xdoc::ul
    (xdoc::li
     "Canonical ordering only moves code points:
      see @(see members-of-canonical-order).")
    (xdoc::li
     "Canonical composition does not make
      a code point that has no canonical decomposition,
      and it does not remove a code point that is inert under normalization
      (see @(tsee normalization-inert-p)).
      So an inert code point occurs in NFC exactly when it occurs in NFD,
      and in NFKC exactly when it occurs in NFKD:
      see @(see members-of-canonical-composition).")
    (xdoc::li
     "For the two canonical forms, NFD and NFC,
      and for an ASCII code point that is inert,
      we say exactly when it occurs in the form of a list:
      when it occurs in the list,
      with two exceptions, which are the semicolon and the grave accent:
      see @(see ascii-in-canonical-forms).")
    (xdoc::li
     "NFC does not bring in any ASCII code point,
      inert or not, with three exceptions:
      an ASCII code point that occurs in NFC of a list
      occurs in the list,
      unless it is the semicolon, the grave accent or the letter K
      and the list has a certain other code point:
      see @(see ascii-in-nfc)."))
   (xdoc::p
    "So a language that puts its source text in NFC
     can say which ASCII characters of the normalized text
     were not in the text as written:
     only those three, and only where the text had
     U+037E GREEK QUESTION MARK, U+1FEF GREEK VARIA or U+212A KELVIN SIGN.")
   (xdoc::p
    "We do not have such statements
     for the two compatibility forms, NFKD and NFKC,
     into which many compatibility characters bring ASCII characters."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection members-of-canonical-order
  :short "The canonical order of a list
          has the same code points as the list."

  (defrulel member-equal-of-canonical-order-insert
    (iff (member-equal a (canonical-order-insert cp cps ver))
         (or (equal a (code-point-fix cp))
             (member-equal a (code-point-list-fix cps))))
    :induct (canonical-order-insert cp cps ver)
    :enable (canonical-order-insert
             code-point-list-fix))

  (defrule member-equal-of-canonical-order
    (iff (member-equal a (canonical-order cps ver))
         (member-equal a (code-point-list-fix cps)))
    :induct (canonical-order cps ver)
    :enable (canonical-order
             code-point-list-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection members-of-canonical-composition
  :short "Canonical composition does not make
          a code point that has no canonical decomposition,
          and does not remove a code point that is inert under normalization."
  :long
  (xdoc::topstring
   (xdoc::p
    "A code point that two code points compose to
     has a canonical decomposition, which is made of theirs.
     So if a code point that is its own canonical decomposition
     occurs in the canonical composition of a list,
     it occurs in the list;
     and if it occurs in NFC, it occurs in NFD;
     and if it occurs in NFKC, it occurs in NFKD.")
   (xdoc::p
    "A code point that is inert under normalization
     (see @(tsee normalization-inert-p))
     has no decomposition,
     and it does not compose with the code points around it.
     So it occurs in NFC exactly when it occurs in NFD,
     and in NFKC exactly when it occurs in NFKD."))

  ;; A code point that two code points compose to is not undecomposable.

  (defrulel not-equal-of-append-and-list-when-both-consp
    (implies (and (consp x)
                  (consp y))
             (not (equal (append x y) (list a))))
    :enable append)

  (defrule not-undecomposable-p-of-composition
    (implies (composition first second ver)
             (not (undecomposable-p (composition first second ver)
                                    compat
                                    ver)))
    :enable (undecomposable-p
             decompose
             decomposition-when-decomposition-mapping)
    :disable (decomposition-mapping-of-composition
              composition)
    :use decomposition-mapping-of-composition)

  ;; So an undecomposable code point that is not in what is being composed
  ;; is not in the result.

  (defrulel not-member-equal-of-canonical-compose-from-starter
    (implies (and (undecomposable-p a nil ver)
                  (not (equal a (code-point-fix starter)))
                  (not (member-equal a (code-point-list-fix pending)))
                  (not (member-equal a (code-point-list-fix cps))))
             (not (member-equal a
                                (canonical-compose-from-starter starter
                                                                pending
                                                                last-ccc
                                                                cps
                                                                ver))))
    :induct (canonical-compose-from-starter starter pending last-ccc cps ver)
    :enable canonical-compose-from-starter
    :expand (code-point-list-fix cps))

  ;; The next three theorems are stored as rewrite rules
  ;; that say that the code point is not in the result
  ;; if it is not in the argument.

  (defruled member-equal-of-canonical-compose-when-undecomposable-p
    (implies (and (undecomposable-p a nil ver)
                  (member-equal a (canonical-compose cps ver)))
             (member-equal a (code-point-list-fix cps)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (and (undecomposable-p a nil ver)
                    (not (member-equal a (code-point-list-fix cps))))
               (not (member-equal a (canonical-compose cps ver))))))
    :induct (canonical-compose cps ver)
    :enable canonical-compose
    :expand (code-point-list-fix cps))

  (defruled member-equal-of-nfd-when-member-equal-of-nfc
    (implies (and (undecomposable-p a nil ver)
                  (member-equal a (nfc cps ver)))
             (member-equal a (nfd cps ver)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (and (undecomposable-p a nil ver)
                    (not (member-equal a (nfd cps ver))))
               (not (member-equal a (nfc cps ver))))))
    :enable (nfc
             member-equal-of-canonical-compose-when-undecomposable-p))

  (defruled member-equal-of-nfkd-when-member-equal-of-nfkc
    (implies (and (undecomposable-p a nil ver)
                  (member-equal a (nfkc cps ver)))
             (member-equal a (nfkd cps ver)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (and (undecomposable-p a nil ver)
                    (not (member-equal a (nfkd cps ver))))
               (not (member-equal a (nfkc cps ver))))))
    :enable (nfkc
             member-equal-of-canonical-compose-when-undecomposable-p))

  ;; The code points that have not composed stay in the result.

  (defrulel member-equal-of-canonical-compose-from-starter-when-pending
    (implies (member-equal a (code-point-list-fix pending))
             (member-equal a
                           (canonical-compose-from-starter starter
                                                           pending
                                                           last-ccc
                                                           cps
                                                           ver)))
    :induct (canonical-compose-from-starter starter pending last-ccc cps ver)
    :enable canonical-compose-from-starter
    :expand (code-point-list-fix cps))

  ;; A starter that composes neither with a code point before it
  ;; nor with a code point after it stays in the result.

  (defrulel member-equal-of-canonical-compose-from-starter-when-not-composes
    (implies (and (starter-p a ver)
                  (not (composes-with-previous-p a ver))
                  (not (composes-with-following-p a ver))
                  (member-equal a (code-point-list-fix cps)))
             (member-equal a
                           (canonical-compose-from-starter starter
                                                           pending
                                                           last-ccc
                                                           cps
                                                           ver)))
    :induct (canonical-compose-from-starter starter pending last-ccc cps ver)
    :enable (canonical-compose-from-starter
             starter-p
             composition-when-not-composes-with-previous-p
             canonical-compose-from-starter-when-not-composes-with-following-p)
    :expand (code-point-list-fix cps))

  (defruled member-equal-of-canonical-compose-when-normalization-inert-p
    (implies (and (normalization-inert-p a ver)
                  (member-equal a (code-point-list-fix cps)))
             (member-equal a (canonical-compose cps ver)))
    :induct (canonical-compose cps ver)
    :enable (canonical-compose
             normalization-inert-p
             starter-p
             canonical-compose-from-starter-when-not-composes-with-following-p)
    :expand (code-point-list-fix cps))

  (defruled member-equal-of-nfc-when-normalization-inert-p
    (implies (and (code-point-p a)
                  (normalization-inert-p a ver))
             (iff (member-equal a (nfc cps ver))
                  (member-equal a (nfd cps ver))))
    :enable (nfc
             normalization-inert-p
             member-equal-of-canonical-compose-when-undecomposable-p
             member-equal-of-canonical-compose-when-normalization-inert-p))

  (defruled member-equal-of-nfkc-when-normalization-inert-p
    (implies (and (code-point-p a)
                  (normalization-inert-p a ver))
             (iff (member-equal a (nfkc cps ver))
                  (member-equal a (nfkd cps ver))))
    :enable (nfkc
             normalization-inert-p
             member-equal-of-canonical-compose-when-undecomposable-p
             member-equal-of-canonical-compose-when-normalization-inert-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ascii-in-canonical-forms
  :short "When an inert ASCII code point occurs
          in a canonical normalization form of a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "Let @('a') be an ASCII code point that is inert under normalization
     (see @(tsee normalization-inert-p)
     and @(see inert-ascii-code-points)):
     a digit, a space, a control character,
     @('Q'), @('q'),
     or a punctuation mark or symbol other than @('<'), @('='), @('>').
     In every supported version of Unicode,
     @('a') occurs in NFD of a list of code points,
     and in NFC of that list,
     exactly when one of these holds:")
   (xdoc::ul
    (xdoc::li
     "@('a') occurs in the list.")
    (xdoc::li
     "@('a') is U+003B SEMICOLON
      and U+037E GREEK QUESTION MARK occurs in the list.")
    (xdoc::li
     "@('a') is U+0060 GRAVE ACCENT
      and U+1FEF GREEK VARIA occurs in the list."))
   (xdoc::p
    "So, apart from these two characters,
     the canonical forms neither bring in nor take away
     an inert ASCII character.
     For the ASCII code points that are not inert,
     which are the other letters and @('<'), @('='), @('>'),
     there is a theorem in one direction, for NFC:
     see @(see ascii-in-nfc).
     The semicolon and the grave accent
     are the canonical decompositions of the two Greek characters;
     a language in which one of them is a delimiter,
     and which normalizes its source text before it reads delimiters,
     reads those Greek characters as that delimiter.")
   (xdoc::p
    "The theorem about NFD relies on a fact about the tables,
     which we check on every code point, for each version:
     an inert ASCII code point
     that occurs in the canonical decomposition of a code point
     is that code point,
     or the decomposition is one of the two above.
     The theorem about NFC follows from the one about NFD:
     see @(see members-of-canonical-composition)."))

  ;; What is checked for a code point CP:
  ;; every code point A of its canonical decomposition
  ;; is not ASCII, or is not inert, or is CP,
  ;; or is one of the two exceptions.

  (local
   (define ascii-source-ok ((a code-point-p)
                            (cp code-point-p)
                            (ver versionp))
     :returns (yes/no booleanp)
     (b* ((a (code-point-fix a))
          (cp (code-point-fix cp)))
       (or (>= a #x80)
           (not (normalization-inert-p a ver))
           (equal a cp)
           (and (equal a #x3B) (equal cp #x37E))
           (and (equal a #x60) (equal cp #x1FEF))))
     :hooks nil))

  (local
   (std::deflist ascii-source-ok-listp (x cp ver)
     :guard (and (code-point-listp x)
                 (code-point-p cp)
                 (versionp ver))
     (ascii-source-ok x cp ver)))

  (local
   (define ascii-sources-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (ascii-source-ok-listp (decomposition cp nil ver) cp ver)
     :hooks nil))

  (local
   (std::deflist ascii-sources-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (ascii-sources-ok x ver)))

  (defrulel ascii-sources-ok-listp-of-all-code-points
    (ascii-sources-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable ascii-sources-ok-listp-of-cons)

  (defrulel ascii-source-ok-listp-of-canonical-decomposition
    (ascii-source-ok-listp (decomposition cp nil ver)
                           (code-point-fix cp)
                           (version-fix ver))
    :enable ascii-sources-ok
    :use (:instance ascii-sources-ok-when-member-equal-of-ascii-sources-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver))))

  ;; The two exceptions.

  (defrulel decomposition-of-greek-question-mark
    (implies (equal (code-point-fix cp) #x37E)
             (equal (decomposition cp nil ver)
                    (list #x3B)))
    :enable (decomposition
             canonical-decompositions))

  (defrulel decomposition-of-greek-varia
    (implies (equal (code-point-fix cp) #x1FEF)
             (equal (decomposition cp nil ver)
                    (list #x60)))
    :enable (decomposition
             canonical-decompositions))

  ;; When an inert ASCII code point occurs
  ;; in the canonical decomposition of a code point,
  ;; and of a list of code points.

  (defrulel member-equal-of-canonical-decomposition-when-inert-ascii
    (implies (and (code-point-p a)
                  (< a #x80)
                  (normalization-inert-p a ver))
             (iff (member-equal a (decomposition cp nil ver))
                  (b* ((cp (code-point-fix cp)))
                    (or (equal a cp)
                        (and (equal a #x3B) (equal cp #x37E))
                        (and (equal a #x60) (equal cp #x1FEF))))))
    :enable (ascii-source-ok
             decomposition-when-below-a0)
    :use (:instance ascii-source-ok-when-member-equal-of-ascii-source-ok-listp
                    (acl2::a a)
                    (x (decomposition cp nil ver))
                    (cp (code-point-fix cp))
                    (ver (version-fix ver))))

  (defrulel member-equal-of-canonical-decompose-when-inert-ascii
    (implies (and (code-point-p a)
                  (< a #x80)
                  (normalization-inert-p a ver))
             (iff (member-equal a (decompose cps nil ver))
                  (b* ((cps (code-point-list-fix cps)))
                    (or (member-equal a cps)
                        (and (equal a #x3B) (member-equal #x37E cps))
                        (and (equal a #x60) (member-equal #x1FEF cps))))))
    :induct (len cps)
    :enable (decompose
             len)
    :expand (code-point-list-fix cps))

  ;; The two theorems.

  (defruled member-equal-of-nfd-when-inert-ascii
    (implies (and (code-point-p a)
                  (< a #x80)
                  (normalization-inert-p a ver))
             (iff (member-equal a (nfd cps ver))
                  (b* ((cps (code-point-list-fix cps)))
                    (or (member-equal a cps)
                        (and (equal a #x3B) (member-equal #x37E cps))
                        (and (equal a #x60) (member-equal #x1FEF cps))))))
    :enable nfd)

  (defruled member-equal-of-nfc-when-inert-ascii
    (implies (and (code-point-p a)
                  (< a #x80)
                  (normalization-inert-p a ver))
             (iff (member-equal a (nfc cps ver))
                  (b* ((cps (code-point-list-fix cps)))
                    (or (member-equal a cps)
                        (and (equal a #x3B) (member-equal #x37E cps))
                        (and (equal a #x60) (member-equal #x1FEF cps))))))
    :enable (member-equal-of-nfc-when-normalization-inert-p
             member-equal-of-nfd-when-inert-ascii)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ascii-in-nfc
  :short "NFC does not bring in ASCII code points,
          with three exceptions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In every supported version of Unicode,
     if an ASCII code point occurs in NFC of a list of code points,
     then one of these holds:")
   (xdoc::ul
    (xdoc::li
     "It occurs in the list.")
    (xdoc::li
     "It is U+003B SEMICOLON
      and U+037E GREEK QUESTION MARK occurs in the list.")
    (xdoc::li
     "It is U+0060 GRAVE ACCENT
      and U+1FEF GREEK VARIA occurs in the list.")
    (xdoc::li
     "It is U+004B LATIN CAPITAL LETTER K
      and U+212A KELVIN SIGN occurs in the list."))
   (xdoc::p
    "This holds for every ASCII code point,
     including the letters and @('<'), @('='), @('>'),
     which are not inert under normalization.
     For those, the converse does not hold:
     a letter that occurs in a list
     does not occur in NFC of the list
     if it composes with the mark that follows it.
     For the inert ASCII code points both directions hold:
     see @(see ascii-in-canonical-forms).")
   (xdoc::p
    "The same is not true of NFD:
     the canonical decompositions of many code points
     start with an ASCII letter, or with @('<'), @('=') or @('>').
     The theorem says that when such a code point is decomposed,
     the ASCII code point always composes again.
     It may compose with another mark than the one it came with:
     NFC of U+00C5 LATIN CAPITAL LETTER A WITH RING ABOVE
     followed by U+0323 COMBINING DOT BELOW
     is U+1EA0 LATIN CAPITAL LETTER A WITH DOT BELOW
     followed by U+030A COMBINING RING ABOVE.
     But some mark composes with it.")
   (xdoc::p
    "The proof uses these facts about the tables,
     which we check on every code point, for each version.
     If the canonical decomposition of a code point has an ASCII code point,
     then either it is that ASCII code point alone,
     and the code point is that one or one of the three above;
     or the ASCII code point is the first one of the decomposition,
     the second one is a non-starter that composes with it,
     and no other code point of the decomposition is ASCII.
     After canonical ordering,
     that second code point is still the first of its combining class
     after the ASCII code point,
     so no code point blocks it:
     either an earlier mark composes with the ASCII code point,
     or that one does."))

  ;; In this section, A is a starter that has no canonical decomposition
  ;; and that does not compose with a code point before it.
  ;; Every ASCII code point is such.

  ;; Whether A occurs in what canonical composition gives from a starter on
  ;; does not depend on the starter and on the code points that have not
  ;; composed, if A is not one of them.
  ;; The induction is the one of the function,
  ;; with one more recursive call where the next code point composes:
  ;; the call for that code point as the starter.

  (local
   (define compose-members-induct ((starter code-point-p)
                                   (pending code-point-listp)
                                   (last-ccc natp)
                                   (cps code-point-listp)
                                   (ver versionp))
     (b* ((starter (code-point-fix starter))
          (pending (code-point-list-fix pending))
          (last-ccc (lnfix last-ccc))
          ((when (endp cps)) nil)
          (cp (code-point-fix (car cps)))
          (ccc (canonical-combining-class cp ver))
          (blocked (and (consp pending)
                        (>= last-ccc ccc)))
          (composite (and (not blocked)
                          (composition starter cp ver))))
       (if composite
           (list (compose-members-induct composite
                                         pending
                                         last-ccc
                                         (cdr cps)
                                         ver)
                 (compose-members-induct cp nil 0 (cdr cps) ver))
         (list (compose-members-induct cp nil 0 (cdr cps) ver)
               (compose-members-induct starter
                                       (cons cp pending)
                                       ccc
                                       (cdr cps)
                                       ver))))
     :measure (len cps)
     :hooks nil))

  (defrulel member-equal-of-canonical-compose-from-starter-when-other
    (implies (and (starter-p a ver)
                  (not (composes-with-previous-p a ver))
                  (undecomposable-p a nil ver)
                  (not (equal a (code-point-fix starter)))
                  (not (member-equal a (code-point-list-fix pending))))
             (iff (member-equal a
                                (canonical-compose-from-starter starter
                                                                pending
                                                                last-ccc
                                                                cps
                                                                ver))
                  (member-equal a (canonical-compose cps ver))))
    :induct (compose-members-induct starter pending last-ccc cps ver)
    :enable (compose-members-induct
             canonical-compose
             starter-p
             composition-when-not-composes-with-previous-p)
    :expand (canonical-compose-from-starter starter pending last-ccc cps ver))

  ;; Putting a non-starter in its place in a list
  ;; does not change whether A occurs in the canonical composition.

  (defrulel member-equal-of-canonical-compose-of-canonical-order-insert
    (implies (and (starter-p a ver)
                  (not (starter-p cp ver)))
             (iff (member-equal a
                                (canonical-compose
                                 (canonical-order-insert cp cps ver)
                                 ver))
                  (member-equal a (canonical-compose cps ver))))
    :induct (canonical-order-insert cp cps ver)
    :enable (canonical-order-insert
             canonical-compose
             starter-p))

  ;; Code points other than A in front of a list do not change
  ;; whether A occurs in the canonical composition of its canonical order.

  (defrulel member-equal-of-canonical-compose-of-canonical-order-of-append
    (implies (and (starter-p a ver)
                  (not (composes-with-previous-p a ver))
                  (undecomposable-p a nil ver)
                  (not (member-equal a (code-point-list-fix cps1))))
             (iff (member-equal a
                                (canonical-compose
                                 (canonical-order (append cps1 cps2) ver)
                                 ver))
                  (member-equal a
                                (canonical-compose (canonical-order cps2 ver)
                                                   ver))))
    :induct (len cps1)
    :enable (canonical-order
             canonical-compose
             starter-p
             len)
    :expand (code-point-list-fix cps1))

  ;; A is not a code point that two code points compose to.

  (defrulel not-equal-of-composition-when-undecomposable-p
    (implies (and (undecomposable-p a compat ver)
                  (composition first second ver))
             (not (equal a (composition first second ver)))))

  ;; When A is the starter and a non-starter that composes with it
  ;; is put in its place in the list that follows,
  ;; A composes, with that non-starter or with one before it.
  ;; So whether A occurs in the result is whether it occurs
  ;; in the canonical composition of the list.
  ;; The induction follows the non-starter as it moves into the list,
  ;; with the code points that it passes added to the ones that have not
  ;; composed.

  (local
   (define consume-induct ((cp code-point-p)
                           (cps code-point-listp)
                           (pending code-point-listp)
                           (last-ccc natp)
                           (ver versionp))
     (b* (((when (endp cps)) nil)
          (next (code-point-fix (car cps)))
          (next-ccc (canonical-combining-class next ver)))
       (if (and (not (equal next-ccc 0))
                (< next-ccc (canonical-combining-class cp ver)))
           (consume-induct cp (cdr cps) (cons next pending) next-ccc ver)
         nil))
     :measure (len cps)
     :hooks nil
     :ignore-ok t
     :irrelevant-formals-ok t))

  (defrulel member-equal-of-canonical-compose-from-starter-of-insert
    (implies (and (code-point-p a)
                  (starter-p a ver)
                  (not (composes-with-previous-p a ver))
                  (undecomposable-p a nil ver)
                  (composition a cp ver)
                  (not (starter-p cp ver))
                  (not (member-equal a (code-point-list-fix pending)))
                  (or (not (consp pending))
                      (< (nfix last-ccc)
                         (canonical-combining-class cp ver))))
             (iff (member-equal a
                                (canonical-compose-from-starter
                                 a
                                 pending
                                 last-ccc
                                 (canonical-order-insert cp cps ver)
                                 ver))
                  (member-equal a (canonical-compose cps ver))))
    :induct (consume-induct cp cps pending last-ccc ver)
    :enable (consume-induct
             canonical-order-insert
             canonical-compose-from-starter
             canonical-compose
             starter-p
             nfix))

  ;; So A, a non-starter that composes with it, and code points other than A,
  ;; in front of a list, do not change whether A occurs
  ;; in the canonical composition of its canonical order.

  (defrulel member-equal-of-canonical-compose-of-canonical-order-of-list*
    (implies (and (code-point-p a)
                  (starter-p a ver)
                  (not (composes-with-previous-p a ver))
                  (undecomposable-p a nil ver)
                  (composition a cp ver)
                  (not (starter-p cp ver))
                  (not (member-equal a (code-point-list-fix cps1))))
             (iff (member-equal a
                                (canonical-compose
                                 (canonical-order
                                  (list* a cp (append cps1 cps2))
                                  ver)
                                 ver))
                  (member-equal a
                                (canonical-compose (canonical-order cps2 ver)
                                                   ver))))
    :enable (canonical-order
             canonical-compose
             starter-p))

  ;; What is checked for a code point: see the documentation above.

  (defrulel rationalp-when-code-point-p
    (implies (code-point-p x)
             (rationalp x))
    :enable code-point-p)

  (local
   (define non-ascii-p ((cp code-point-p))
     :returns (yes/no booleanp)
     (>= (code-point-fix cp) #x80)
     :hooks nil))

  (local
   (std::deflist non-ascii-listp (x)
     :guard (code-point-listp x)
     (non-ascii-p x)))

  (local
   (define ascii-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp))
          (decomposition (decomposition cp nil ver))
          (first (code-point-fix (car decomposition)))
          (rest (cdr decomposition)))
       (or (non-ascii-listp decomposition)
           (and (not (consp rest))
                (or (equal first cp)
                    (and (equal cp #x37E) (equal first #x3B))
                    (and (equal cp #x1FEF) (equal first #x60))
                    (and (equal cp #x212A) (equal first #x4B))))
           (and (consp rest)
                (< first #x80)
                (not (starter-p (car rest) ver))
                (composition first (car rest) ver)
                (non-ascii-listp rest)
                t)))
     :hooks nil))

  (local
   (std::deflist ascii-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (ascii-ok x ver)))

  (defrulel ascii-ok-listp-of-all-code-points
    (ascii-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable ascii-ok-listp-of-cons)

  ;; Membership of an ASCII code point in the canonical decomposition
  ;; of a code point, in the cases of the check.

  (defrulel not-member-equal-when-non-ascii-listp
    (implies (and (non-ascii-listp x)
                  (code-point-p a)
                  (< a #x80))
             (not (member-equal a x)))
    :induct (non-ascii-listp x)
    :enable (non-ascii-listp
             non-ascii-p
             member-equal))

  (defrulel not-member-equal-when-not-car-and-not-in-cdr
    (implies (and (consp x)
                  (not (equal a (car x)))
                  (not (member-equal a (cdr x))))
             (not (member-equal a x)))
    :enable member-equal)

  ;; The decomposition of a code point, in front of a list,
  ;; does not change whether an ASCII code point A occurs
  ;; in the canonical composition of the canonical order,
  ;; unless A is the code point or it is one of the three exceptions.
  ;; First the case in which A is the first code point of the decomposition
  ;; and the second one composes with it; then all the cases.

  (defrulel member-equal-of-canonical-compose-of-canonical-order-when-car
    (implies (and (code-point-p a)
                  (starter-p a ver)
                  (not (composes-with-previous-p a ver))
                  (undecomposable-p a nil ver)
                  (consp cps1)
                  (consp (cdr cps1))
                  (equal a (car cps1))
                  (composition a (cadr cps1) ver)
                  (not (starter-p (cadr cps1) ver))
                  (not (member-equal a (code-point-list-fix (cddr cps1)))))
             (iff (member-equal a
                                (canonical-compose
                                 (canonical-order (append cps1 cps2) ver)
                                 ver))
                  (member-equal a
                                (canonical-compose (canonical-order cps2 ver)
                                                   ver))))
    :expand ((append cps1 cps2)
             (append (cdr cps1) cps2)))

  (defrulel member-equal-of-canonical-compose-when-ascii-and-decomposition
    (implies (and (code-point-p a)
                  (< a #x80)
                  (not (equal a (code-point-fix cp)))
                  (not (and (equal a #x3B)
                            (equal (code-point-fix cp) #x37E)))
                  (not (and (equal a #x60)
                            (equal (code-point-fix cp) #x1FEF)))
                  (not (and (equal a #x4B)
                            (equal (code-point-fix cp) #x212A))))
             (iff (member-equal a
                                (canonical-compose
                                 (canonical-order
                                  (append (decomposition cp nil ver) cps)
                                  ver)
                                 ver))
                  (member-equal a
                                (canonical-compose (canonical-order cps ver)
                                                   ver))))
    :enable (ascii-ok
             starter-p-when-below-300
             not-composes-with-previous-p-when-below-300
             undecomposable-p
             decomposition-when-below-a0)
    :cases ((equal a (car (decomposition cp nil ver))))
    :use (:instance ascii-ok-when-member-equal-of-ascii-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver))))

  ;; So an ASCII code point that is not in a list,
  ;; and is not one of the three exceptions for that list,
  ;; is not in NFC of the list.

  (defrulel not-member-equal-of-canonical-compose-of-decompose-when-ascii
    (implies (and (code-point-p a)
                  (< a #x80)
                  (not (member-equal a (code-point-list-fix cps)))
                  (not (and (equal a #x3B)
                            (member-equal #x37E (code-point-list-fix cps))))
                  (not (and (equal a #x60)
                            (member-equal #x1FEF (code-point-list-fix cps))))
                  (not (and (equal a #x4B)
                            (member-equal #x212A (code-point-list-fix cps)))))
             (not (member-equal a
                                (canonical-compose
                                 (canonical-order (decompose cps nil ver) ver)
                                 ver))))
    :induct (len cps)
    :enable (decompose
             len)
    ;; This rule would rewrite the hypothesis that A is a code point to true,
    ;; from the conclusion, which says that A is not in a list of code points;
    ;; then the hypothesis would not be there for the conclusion.
    :disable code-point-p-when-member-equal-of-code-point-listp
    :expand ((code-point-list-fix cps)
             (canonical-order cps ver)
             (canonical-compose nil ver)))

  (defruled member-equal-of-nfc-when-ascii
    (implies (and (code-point-p a)
                  (< a #x80)
                  (member-equal a (nfc cps ver)))
             (b* ((cps (code-point-list-fix cps)))
               (or (member-equal a cps)
                   (and (equal a #x3B) (member-equal #x37E cps))
                   (and (equal a #x60) (member-equal #x1FEF cps))
                   (and (equal a #x4B) (member-equal #x212A cps)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (and (code-point-p a)
                    (< a #x80)
                    (not (member-equal a (code-point-list-fix cps)))
                    (not (and (equal a #x3B)
                              (member-equal #x37E (code-point-list-fix cps))))
                    (not (and (equal a #x60)
                              (member-equal #x1FEF
                                            (code-point-list-fix cps))))
                    (not (and (equal a #x4B)
                              (member-equal #x212A
                                            (code-point-list-fix cps)))))
               (not (member-equal a (nfc cps ver))))))
    :enable (nfc
             nfd)
    ;; See the comment in the previous theorem.
    :disable code-point-p-when-member-equal-of-code-point-listp))
