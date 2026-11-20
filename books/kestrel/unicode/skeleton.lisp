; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "normalization")
(include-book "default-ignorable")
(include-book "confusables")
(include-book "bidi-class")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ confusable-detection
  :parents (unicode)
  :short "The skeleton of a string,
          by which strings that look alike are found."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode Security Mechanisms [UTS #39, Section 4]
     defines when two strings are confusable,
     that is, when they look alike although they are different:
     when they have the same skeleton.
     The skeleton of a string is another string,
     which is not meant to be displayed:
     it is to the string what a hash code is to a value.")
   (xdoc::p
    "The specification defines two functions.
     The internal skeleton of a string,
     written @('internalSkeleton') there,
     is the result of four steps:")
   (xdoc::ol
    (xdoc::li
     "Put the string in Normalization Form D (NFD),
      which is canonical decomposition.")
    (xdoc::li
     "Remove the characters that have the
      @('Default_Ignorable_Code_Point') property.")
    (xdoc::li
     "Replace each character by its prototype (see @(see confusables)).")
    (xdoc::li
     "Put the result in NFD again."))
   (xdoc::p
    "The bidirectional skeleton, written @('bidiSkeleton') there,
     is the internal skeleton of the string
     after its characters have been put in the order
     in which they are displayed,
     which is the work of the Unicode Bidirectional Algorithm [UAX #9];
     it takes the direction of the paragraph as a parameter.
     The skeleton, without qualification,
     is the bidirectional skeleton for a paragraph from left to right.")
   (xdoc::p
    "This library does not have the bidirectional algorithm yet.
     So we define the internal skeleton, for every list of code points:
     see @(tsee internal-skeleton).
     And we define the skeleton
     for the lists that are displayed in the order in which they are stored,
     where the two skeletons are the same:
     see @(tsee skeleton) and @(tsee right-to-left-free-p).
     Two such lists are confusable when their skeletons are equal:
     see @(tsee confusable-p).")
   (xdoc::p
    "The three revisions of the specification
     that go with the supported versions of Unicode
     define the internal skeleton in the same words;
     only the data differs.
     Skeletons are not stable:
     the skeleton of a string in one version of Unicode
     can differ from its skeleton in another."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-default-ignorable ((cps code-point-listp) (ver versionp))
  :returns (new-cps code-point-listp)
  :short "Remove from a list the code points that have the
          @('Default_Ignorable_Code_Point') property,
          in a version of Unicode."
  (cond ((endp cps) nil)
        ((default-ignorable-p (car cps) ver)
         (remove-default-ignorable (cdr cps) ver))
        (t (cons (code-point-fix (car cps))
                 (remove-default-ignorable (cdr cps) ver))))
  :hooks (:fix)

  ///

  (defrule scalar-value-listp-of-remove-default-ignorable
    (implies (scalar-value-listp cps)
             (scalar-value-listp (remove-default-ignorable cps ver)))
    :induct t)

  (defrule remove-default-ignorable-of-append
    (equal (remove-default-ignorable (append cps1 cps2) ver)
           (append (remove-default-ignorable cps1 ver)
                   (remove-default-ignorable cps2 ver)))
    :induct (remove-default-ignorable cps1 ver))

  (defrule remove-default-ignorable-of-remove-default-ignorable
    (equal (remove-default-ignorable (remove-default-ignorable cps ver) ver)
           (remove-default-ignorable cps ver))
    :induct t)

  (defrule undecomposable-listp-of-remove-default-ignorable
    (implies (undecomposable-listp cps compat ver1)
             (undecomposable-listp (remove-default-ignorable cps ver)
                                   compat
                                   ver1))
    :induct t
    :enable undecomposable-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define internal-skeleton ((cps code-point-listp) (ver versionp))
  :returns (skeleton code-point-listp)
  :short "The internal skeleton of a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @('internalSkeleton') of [UTS #39, Section 4]:
     Normalization Form D (NFD), which is canonical decomposition;
     then the removal of the default ignorable code points;
     then the replacement of each code point by its prototype;
     then NFD again.")
   (xdoc::p
    "The result is in NFD.
     A list, its NFD form and its form
     in Normalization Form C (NFC), which is
     canonical decomposition followed by canonical composition,
     have the same internal skeleton,
     and so do any two lists that are canonical equivalents:
     the first step makes them the same list."))
  (nfd (replace-by-prototypes
        (remove-default-ignorable (nfd cps ver) ver)
        ver)
       ver)
  :hooks (:fix)

  ///

  (defrule scalar-value-listp-of-internal-skeleton
    (implies (scalar-value-listp cps)
             (scalar-value-listp (internal-skeleton cps ver))))

  (defrule nfd-memberp-of-internal-skeleton
    (nfd-memberp (internal-skeleton cps ver) ver))

  (defrule nfd-of-internal-skeleton
    (equal (nfd (internal-skeleton cps ver) ver)
           (internal-skeleton cps ver)))

  (defrule internal-skeleton-of-nfd
    (equal (internal-skeleton (nfd cps ver) ver)
           (internal-skeleton cps ver)))

  (defrule internal-skeleton-of-nfc
    (equal (internal-skeleton (nfc cps ver) ver)
           (internal-skeleton cps ver)))

  (defrule internal-skeleton-when-canonical-equivalent-p
    (implies (canonical-equivalent-p cps1 cps2 ver)
             (equal (internal-skeleton cps1 ver)
                    (internal-skeleton cps2 ver)))
    :rule-classes nil
    :enable canonical-equivalent-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define internal-skeleton-unstable-code-points ((ver versionp))
  :returns (cps code-point-listp)
  :short "The code points whose internal skeleton
          is not its own internal skeleton,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see skeleton-idempotence).
     There are thirteen such code points
     in Unicode 16.0.0 and in Unicode 17.0.0, the same ones,
     and none in Unicode 18.0.0.
     Eight of them are presentation forms of Arabic letters;
     the others are
     U+01C4 LATIN CAPITAL LETTER DZ WITH CARON
     and its titlecase and lowercase forms,
     U+048B CYRILLIC SMALL LETTER SHORT I WITH TAIL,
     and U+321D PARENTHESIZED KOREAN CHARACTER OJEON."))
  (version-case ver
                :v16.0.0 '(#x01C4 #x01C5 #x01C6 #x048B #x321D
                           #xFBA4 #xFBA5 #xFBB0 #xFBB1
                           #xFE81 #xFE82 #xFEF5 #xFEF6)
                :v17.0.0 '(#x01C4 #x01C5 #x01C6 #x048B #x321D
                           #xFBA4 #xFBA5 #xFBB0 #xFBB1
                           #xFE81 #xFE82 #xFEF5 #xFEF6)
                :v18.0.0 nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define internal-skeleton-stable-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check that a code point is not one of those
          whose internal skeleton is not its own internal skeleton,
          in a version of Unicode."
  (not (member-equal (code-point-fix cp)
                     (internal-skeleton-unstable-code-points ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist internal-skeleton-stable-listp (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that a list has none of the code points
          whose internal skeleton is not its own internal skeleton,
          in a version of Unicode."
  (internal-skeleton-stable-p x ver)

  ///

  (fty::deffixequiv internal-skeleton-stable-listp
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (internal-skeleton-stable-listp x ver)
             :in-theory (enable internal-skeleton-stable-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection skeleton-idempotence
  :short "When taking the internal skeleton a second time changes nothing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specification says that the internal skeleton is idempotent:
     the internal skeleton of the internal skeleton of a string
     is the internal skeleton of the string [UTS #39, Section 4].
     That holds for every string in Unicode 18.0.0.
     In Unicode 16.0.0 and in Unicode 17.0.0
     it holds for every string that has none of thirteen characters,
     and it fails for each of those thirteen:
     see @(tsee internal-skeleton-unstable-code-points).
     The three facts are theorems here.")
   (xdoc::p
    "An example of the failure, in Unicode 17.0.0:
     the prototype of U+01C6 LATIN SMALL LETTER DZ WITH CARON
     is U+0064, U+017E, that is, d followed by z with caron.
     The last step of the internal skeleton
     decomposes the z with caron into z and U+030C COMBINING CARON.
     But U+030C has a prototype of its own, U+0306 COMBINING BREVE.
     So the internal skeleton of U+01C6 is U+0064, U+007A, U+030C,
     and the internal skeleton of that is U+0064, U+007A, U+0306.
     In Unicode 18.0.0 the prototype of U+01C6
     is U+0064, U+007A, U+0306.")
   (xdoc::p
    "The proof has two parts.
     The first part is general:
     a list in Normalization Form D (NFD), which is canonical decomposition,
     with no default ignorable code point
     and whose code points are their own prototypes
     is its own internal skeleton;
     and the internal skeleton of a list is such a list
     when, for each code point that the third step replaces,
     the NFD form of its prototype is such a list.
     The second part is a check of the tables, for each version:
     every code point that can be there at the third step,
     other than the thirteen, has such a prototype.
     So adding a version checks it for that version."))

  ;; A code point that the internal skeleton leaves alone.

  (local
   (define fixed-p ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (and (not (default-ignorable-p cp ver))
          (own-prototype-p cp ver))
     :hooks (:fix)))

  (local
   (std::deflist fixed-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (fixed-p x ver)

     ///

     (fty::deffixequiv fixed-listp
       :args ((x code-point-listp) (ver versionp))
       :hints (("Goal"
                :induct (fixed-listp x ver)
                :in-theory (enable fixed-listp))))))

  (defrulel remove-default-ignorable-when-fixed-listp
    (implies (fixed-listp cps ver)
             (equal (remove-default-ignorable cps ver)
                    (code-point-list-fix cps)))
    :induct t
    :enable (remove-default-ignorable
             fixed-listp
             fixed-p))

  (defrulel own-prototype-listp-when-fixed-listp
    (implies (fixed-listp cps ver)
             (own-prototype-listp cps ver))
    :induct t
    :enable (fixed-listp
             fixed-p))

  (defrulel internal-skeleton-when-fixed-listp
    (implies (and (nfd-memberp cps ver)
                  (fixed-listp cps ver))
             (equal (internal-skeleton cps ver)
                    (code-point-list-fix cps)))
    :enable internal-skeleton)

  (defrulel fixed-listp-of-canonical-order-insert
    (equal (fixed-listp (canonical-order-insert cp cps ver1) ver)
           (and (fixed-p cp ver)
                (fixed-listp cps ver)))
    :induct t
    :enable (canonical-order-insert
             fixed-listp))

  (defrulel fixed-listp-of-canonical-order
    (equal (fixed-listp (canonical-order cps ver1) ver)
           (fixed-listp cps ver))
    :induct t
    :enable (canonical-order
             fixed-listp))

  ;; A code point whose prototype, in NFD,
  ;; consists of code points that the internal skeleton leaves alone.

  (local
   (define stable-p ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (fixed-listp (nfd (prototype cp ver) ver) ver)
     :hooks (:fix)))

  (local
   (std::deflist stable-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (stable-p x ver)))

  (defrulel fixed-listp-of-decompose-of-prototype-when-stable-p
    (implies (stable-p cp ver)
             (fixed-listp (decompose (prototype cp ver) nil ver) ver))
    :enable (stable-p
             nfd))

  (defrulel fixed-listp-of-decompose-of-replace-by-prototypes
    (implies (stable-listp cps ver)
             (fixed-listp (decompose (replace-by-prototypes cps ver) nil ver)
                          ver))
    :induct t
    :enable (replace-by-prototypes
             stable-listp))

  (defrulel fixed-listp-of-nfd-of-replace-by-prototypes
    (implies (stable-listp cps ver)
             (fixed-listp (nfd (replace-by-prototypes cps ver) ver) ver))
    :enable nfd)

  (defrulel internal-skeleton-of-internal-skeleton-when-stable-listp
    (implies (stable-listp (remove-default-ignorable (nfd cps ver) ver) ver)
             (equal (internal-skeleton (internal-skeleton cps ver) ver)
                    (internal-skeleton cps ver)))
    :enable internal-skeleton
    :disable internal-skeleton-when-fixed-listp
    :use (:instance internal-skeleton-when-fixed-listp
                    (cps (internal-skeleton cps ver))))

  ;; The check of the tables: a code point that can be in a list in NFD,
  ;; that is not default ignorable and that is not one of the thirteen
  ;; has a prototype of that kind.

  (local
   (define stable-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (not (undecomposable-p cp nil ver))
         (default-ignorable-p cp ver)
         (not (internal-skeleton-stable-p cp ver))
         (stable-p cp ver))
     :hooks nil))

  (local
   (std::deflist stable-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (stable-ok x ver)))

  (defrulel stable-ok-listp-of-all-code-points
    (stable-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable stable-ok-listp-of-cons)

  (defrulel stable-p-when-undecomposable-p
    (implies (and (undecomposable-p cp nil ver)
                  (not (default-ignorable-p cp ver))
                  (internal-skeleton-stable-p cp ver))
             (stable-p cp ver))
    :use (:instance stable-ok-when-member-equal-of-stable-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable stable-ok)

  (defrulel stable-listp-of-remove-default-ignorable
    (implies (and (undecomposable-listp cps nil ver)
                  (internal-skeleton-stable-listp cps ver))
             (stable-listp (remove-default-ignorable cps ver) ver))
    :induct t
    :enable (remove-default-ignorable
             undecomposable-listp
             internal-skeleton-stable-listp
             stable-listp))

  ;; The canonical decomposition of a code point
  ;; that is not one of the thirteen has none of the thirteen;
  ;; so the NFD form of a list that has none of them has none of them.

  (local
   (define decomposition-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (not (internal-skeleton-stable-p cp ver))
         (internal-skeleton-stable-listp (decomposition cp nil ver) ver))
     :hooks nil))

  (local
   (std::deflist decomposition-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (decomposition-ok x ver)))

  (defrulel decomposition-ok-listp-of-all-code-points
    (decomposition-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable decomposition-ok-listp-of-cons)

  (defrulel internal-skeleton-stable-listp-of-decomposition
    (implies (internal-skeleton-stable-p cp ver)
             (internal-skeleton-stable-listp (decomposition cp nil ver) ver))
    :use (:instance decomposition-ok-when-member-equal-of-decomposition-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable decomposition-ok)

  (defrulel internal-skeleton-stable-listp-of-decompose
    (implies (internal-skeleton-stable-listp cps ver)
             (internal-skeleton-stable-listp (decompose cps nil ver) ver))
    :induct t
    :enable (decompose
             internal-skeleton-stable-listp))

  (defrulel internal-skeleton-stable-listp-of-canonical-order-insert
    (equal (internal-skeleton-stable-listp
            (canonical-order-insert cp cps ver1) ver)
           (and (internal-skeleton-stable-p cp ver)
                (internal-skeleton-stable-listp cps ver)))
    :induct t
    :enable (canonical-order-insert
             internal-skeleton-stable-listp))

  (defrulel internal-skeleton-stable-listp-of-canonical-order
    (equal (internal-skeleton-stable-listp (canonical-order cps ver1) ver)
           (internal-skeleton-stable-listp cps ver))
    :induct t
    :enable (canonical-order
             internal-skeleton-stable-listp))

  (defrule internal-skeleton-stable-listp-of-nfd
    (implies (internal-skeleton-stable-listp cps ver)
             (internal-skeleton-stable-listp (nfd cps ver) ver))
    :enable nfd)

  ;; The theorems.

  (defrule internal-skeleton-of-internal-skeleton
    (implies (internal-skeleton-stable-listp cps ver)
             (equal (internal-skeleton (internal-skeleton cps ver) ver)
                    (internal-skeleton cps ver))))

  (defrule internal-skeleton-stable-p-from-v18.0.0
    (implies (version<= (version-v18.0.0) ver)
             (internal-skeleton-stable-p cp ver))
    :enable (internal-skeleton-stable-p
             internal-skeleton-unstable-code-points
             version<=
             version-rank))

  (defrule internal-skeleton-stable-listp-from-v18.0.0
    (implies (version<= (version-v18.0.0) ver)
             (internal-skeleton-stable-listp cps ver))
    :induct t
    :enable internal-skeleton-stable-listp)

  (defrule internal-skeleton-of-internal-skeleton-from-v18.0.0
    (implies (version<= (version-v18.0.0) ver)
             (equal (internal-skeleton (internal-skeleton cps ver) ver)
                    (internal-skeleton cps ver))))

  (defruled internal-skeleton-of-internal-skeleton-when-unstable
    (implies (member-equal cp (internal-skeleton-unstable-code-points ver))
             (not (equal (internal-skeleton (internal-skeleton (list cp) ver)
                                            ver)
                         (internal-skeleton (list cp) ver))))
    :use lemma
    :prep-lemmas
    ((defrule lemma
       (implies (member-equal cp
                              (internal-skeleton-unstable-code-points
                               (version-fix ver)))
                (not (equal (internal-skeleton
                             (internal-skeleton (list cp) (version-fix ver))
                             (version-fix ver))
                            (internal-skeleton (list cp) (version-fix ver)))))
       :rule-classes nil
       :enable (version-fix-in-terms-of-version-case
                internal-skeleton-unstable-code-points)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define right-to-left-code-point-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point can make text
          be displayed from right to left,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if its bidirectional class
     is one of the following six [UAX #9, Table 4]:")
   (xdoc::ul
    (xdoc::li
     "The two strong right-to-left classes,
      @('R') (@('Right_To_Left')) and @('AL') (@('Arabic_Letter')).")
    (xdoc::li
     "@('AN') (@('Arabic_Number')),
      the class of the Arabic-Indic digits
      and of a few other characters used in numbers.
      A number is displayed from left to right,
      but in a paragraph from left to right
      two numbers of this class with a space between them
      are displayed in the opposite order:
      for the characters between them,
      numbers act as right-to-left characters [UAX #9, rule N1].
      The European digits, of class @('EN'), do not do this
      in a text that has no character of the two strong classes above.")
    (xdoc::li
     "The three classes
      of the explicit directional formatting characters
      that start an embedding, an override or an isolate
      from right to left:
      @('RLE') (@('Right_To_Left_Embedding')),
      @('RLO') (@('Right_To_Left_Override'))
      and @('RLI') (@('Right_To_Left_Isolate')).")))
  (b* ((class (code-point-bidi-class cp ver)))
    (bidi-class-case class
                     :right-to-left t
                     :arabic-letter t
                     :arabic-number t
                     :right-to-left-embedding t
                     :right-to-left-override t
                     :right-to-left-isolate t
                     :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist right-to-left-free-p (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that no code point of a list
          can make text be displayed from right to left,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee right-to-left-code-point-p).
     A text that satisfies this predicate,
     in a paragraph from left to right,
     is displayed in the order in which it is stored,
     by the Unicode Bidirectional Algorithm [UAX #9].
     This library does not have that algorithm,
     so this is not a theorem here.
     It was tested with an implementation of the algorithm,
     on every string of up to six characters
     over twenty characters of sixteen of the other seventeen classes
     (all but the paragraph separators,
     which only cut a text into paragraphs);
     and for each of the six classes that the predicate excludes,
     the same test finds strings that are displayed in another order.
     The file @('README.md') says how to repeat the test.")
   (xdoc::p
    "The specification of the skeleton states a weaker condition:
     that the bidirectional skeleton
     of a string with no character of class @('R') or @('AL'),
     for a paragraph from left to right,
     is its internal skeleton [UTS #39, Section 4].
     We exclude four more classes, because of that test:
     the Arabic-Indic digits U+0661 and U+0662 with a space between them
     are displayed with U+0662 first;
     and after U+202E RIGHT-TO-LEFT OVERRIDE,
     the letters a, b are displayed as b, a."))
  (right-to-left-code-point-p x ver)
  :negatedp t

  ///

  (fty::deffixequiv right-to-left-free-p
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (right-to-left-free-p x ver)
             :in-theory (enable right-to-left-free-p)))))

;;;;;;;;;;;;;;;;;;;;

(defsection right-to-left-free-p-below-590
  :short "No code point below U+0590
          can make text be displayed from right to left."
  :long
  (xdoc::topstring
   (xdoc::p
    "U+0590 is the first code point of the Hebrew block.
     So a list of code points below it,
     such as a list of ASCII code points
     or of Latin, Greek and Cyrillic letters,
     satisfies the guard of @(tsee skeleton).
     We prove this by checking the code points below U+0590,
     for each version."))

  (local
   (define below-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (>= (code-point-fix cp) #x590)
         (not (right-to-left-code-point-p cp ver)))
     :hooks nil))

  (local
   (std::deflist below-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (below-ok x ver)))

  (defrulel below-ok-listp-of-all-code-points
    (below-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable below-ok-listp-of-cons)

  (defrule not-right-to-left-code-point-p-when-below-590
    (implies (< (code-point-fix cp) #x590)
             (not (right-to-left-code-point-p cp ver)))
    :use (:instance below-ok-when-member-equal-of-below-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable below-ok)

  (defrule right-to-left-free-p-when-all-below-590
    (implies (code-points-below-p cps #x590)
             (right-to-left-free-p cps ver))
    :induct t
    :enable (code-points-below-p
             right-to-left-free-p)))

;;;;;;;;;;;;;;;;;;;;

(define skeleton ((cps code-point-listp) (ver versionp))
  :guard (right-to-left-free-p cps ver)
  :returns (skeleton code-point-listp)
  :short "The skeleton of a list of code points
          that has no code point that can make text
          be displayed from right to left,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The skeleton of [UTS #39, Section 4], written @('skeleton') there,
     is the bidirectional skeleton for a paragraph from left to right.
     For a list that satisfies the guard of this function,
     that is the internal skeleton:
     see @(tsee right-to-left-free-p) and @(see confusable-detection).
     So this function is the skeleton of the specification
     for the lists that satisfy its guard, and only for those.
     For any other list, use @(tsee internal-skeleton),
     which says nothing about the order of display."))
  (internal-skeleton cps ver)
  :hooks (:fix)

  ///

  (defrule scalar-value-listp-of-skeleton
    (implies (scalar-value-listp cps)
             (scalar-value-listp (skeleton cps ver))))

  (defrule nfd-memberp-of-skeleton
    (nfd-memberp (skeleton cps ver) ver))

  (defrule skeleton-of-nfd
    (equal (skeleton (nfd cps ver) ver)
           (skeleton cps ver)))

  (defrule skeleton-of-nfc
    (equal (skeleton (nfc cps ver) ver)
           (skeleton cps ver)))

  (defruled skeleton-in-terms-of-internal-skeleton
    (equal (skeleton cps ver)
           (internal-skeleton cps ver))))

;;;;;;;;;;;;;;;;;;;;

(define confusable-p ((cps1 code-point-listp)
                      (cps2 code-point-listp)
                      (ver versionp))
  :guard (and (right-to-left-free-p cps1 ver)
              (right-to-left-free-p cps2 ver))
  :returns (yes/no booleanp)
  :short "Check if two lists of code points are confusable,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two strings are confusable if and only if
     they have the same skeleton [UTS #39, Section 4].
     Like @(tsee skeleton),
     this function is the one of the specification
     for the lists that satisfy its guard.")
   (xdoc::p
    "This is an equivalence relation:
     it is reflexive, symmetric and transitive.
     Lists that are canonical equivalents are confusable;
     in particular, each list is confusable with itself,
     so the lists of interest
     are the confusable ones that are not the same."))
  (equal (skeleton cps1 ver)
         (skeleton cps2 ver))
  :hooks (:fix)

  ///

  (defrule confusable-p-reflexive
    (confusable-p cps cps ver))

  (defrule confusable-p-symmetric
    (equal (confusable-p cps1 cps2 ver)
           (confusable-p cps2 cps1 ver)))

  (defruled confusable-p-transitive
    (implies (and (confusable-p cps1 cps2 ver)
                  (confusable-p cps2 cps3 ver))
             (confusable-p cps1 cps3 ver)))

  (defrule confusable-p-of-nfd-arg1
    (equal (confusable-p (nfd cps1 ver) cps2 ver)
           (confusable-p cps1 cps2 ver)))

  (defrule confusable-p-of-nfd-arg2
    (equal (confusable-p cps1 (nfd cps2 ver) ver)
           (confusable-p cps1 cps2 ver)))

  (defrule confusable-p-of-nfc-arg1
    (equal (confusable-p (nfc cps1 ver) cps2 ver)
           (confusable-p cps1 cps2 ver)))

  (defrule confusable-p-of-nfc-arg2
    (equal (confusable-p cps1 (nfc cps2 ver) ver)
           (confusable-p cps1 cps2 ver)))

  (defrule confusable-p-when-canonical-equivalent-p
    (implies (canonical-equivalent-p cps1 cps2 ver)
             (confusable-p cps1 cps2 ver))
    :enable (skeleton
             canonical-equivalent-p)
    :use internal-skeleton-when-canonical-equivalent-p)

  (defrule confusable-p-of-skeleton-arg1
    (implies (internal-skeleton-stable-listp cps1 ver)
             (equal (confusable-p (skeleton cps1 ver) cps2 ver)
                    (confusable-p cps1 cps2 ver)))
    :enable skeleton)

  (defrule confusable-p-of-skeleton-arg2
    (implies (internal-skeleton-stable-listp cps2 ver)
             (equal (confusable-p cps1 (skeleton cps2 ver) ver)
                    (confusable-p cps1 cps2 ver)))
    :enable skeleton))
