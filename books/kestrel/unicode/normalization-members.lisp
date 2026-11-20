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
      see @(see ascii-in-canonical-forms)."))
   (xdoc::p
    "We do not have such a statement for the ASCII letters,
     nor for @('<'), @('='), @('>').
     These occur in the canonical decompositions of many code points,
     and they compose again with the marks that follow them;
     saying when they are left over needs more about canonical composition
     than is proved here.
     We do not have one either for the two compatibility forms,
     NFKD and NFKC, into which
     many compatibility characters bring ASCII characters."))
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
