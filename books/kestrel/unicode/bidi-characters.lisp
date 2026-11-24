; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-class")
(include-book "bidi-brackets")
(include-book "decompositions")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-characters
  :parents (bidirectional-algorithm)
  :short "What the Unicode Bidirectional Algorithm looks at in a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "The algorithm [UAX #9] does not look at which character it is given.
     It looks at three properties of the character:
     its @('Bidi_Class') (see @(see bidi-class-property)),
     and, for rule N0 alone,
     its @('Bidi_Paired_Bracket_Type') and @('Bidi_Paired_Bracket')
     (see @(see bidi-paired-brackets)).
     So we define the algorithm on lists of values of the type
     @(tsee bidi-char), which has just that,
     and not on lists of code points.
     The rules of the algorithm are the same in the three versions of
     [UAX #9] that go with the supported versions of Unicode
     (revisions 50, 51 and 52);
     a version of Unicode comes in only where code points
     are turned into values of that type,
     in @(tsee code-point-bidi-char).")
   (xdoc::p
    "This book also has the predicates on bidirectional classes
     that the rules use,
     the type of the direction of a paragraph,
     and rules P2 and P3, which find that direction in the text."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-class-list
  :short "Fixtype of lists of bidirectional classes."
  :elt-type bidi-class
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-class-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defoption bidi-class-option
  bidi-class
  :short "Fixtype of optional bidirectional classes."
  :pred bidi-class-option-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-class-isolate-initiator-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class is that of an isolate initiator."
  :long
  (xdoc::topstring
   (xdoc::p
    "An isolate initiator is a character of class
     @('LRI') (Left-to-Right Isolate),
     @('RLI') (Right-to-Left Isolate)
     or @('FSI') (First Strong Isolate) [UAX #9, BD8]."))
  (bidi-class-case class
                   :left-to-right-isolate t
                   :right-to-left-isolate t
                   :first-strong-isolate t
                   :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-isolate-formatting-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class
          is that of an isolate formatting character."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, of an isolate initiator
     (see @(tsee bidi-class-isolate-initiator-p))
     or of the character that ends an isolate,
     whose class is @('PDI') (Pop Directional Isolate)."))
  (or (bidi-class-isolate-initiator-p class)
      (equal (bidi-class-kind class) :pop-directional-isolate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-removed-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class is one
          whose characters rule X9 removes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the classes of the embeddings and overrides
     and of the character that ends them
     (@('RLE'), @('LRE'), @('RLO'), @('LRO') and @('PDF')),
     and the class @('BN') (Boundary Neutral) [UAX #9, rule X9].
     The characters of these classes take no further part
     in the algorithm, and they get no level and no place in the display.
     The isolate formatting characters are not among them."))
  (bidi-class-case class
                   :right-to-left-embedding t
                   :left-to-right-embedding t
                   :right-to-left-override t
                   :left-to-right-override t
                   :pop-directional-format t
                   :boundary-neutral t
                   :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-neutral-or-isolate-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class is neutral
          or that of an isolate formatting character."
  :long
  (xdoc::topstring
   (xdoc::p
    "The specification writes @('NI') for these classes
     [UAX #9, Section 3.1.4]:
     @('B'), @('S'), @('WS') and @('ON'),
     and @('LRI'), @('RLI'), @('FSI') and @('PDI').
     Rules N1 and N2 give them a direction."))
  (or (bidi-class-neutral-p class)
      (bidi-class-isolate-formatting-p class))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-direction ((class bidi-class-p))
  :returns (direction? bidi-class-option-p)
  :short "The direction that a bidirectional class has
          for the rules about neutral characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the class @('L') for the class @('L');
     the class @('R') for the classes @('R'),
     @('EN') (European Number) and @('AN') (Arabic Number),
     because rules N0 and N1 treat numbers as @('R')
     [UAX #9, rules N0 and N1];
     and @('nil') for every other class."))
  (bidi-class-case class
                   :left-to-right (bidi-class-left-to-right)
                   :right-to-left (bidi-class-right-to-left)
                   :european-number (bidi-class-right-to-left)
                   :arabic-number (bidi-class-right-to-left)
                   :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-level-direction ((level natp))
  :returns (direction bidi-class-p)
  :short "The direction of an embedding level, as a bidirectional class."
  :long
  (xdoc::topstring
   (xdoc::p
    "An even level is a left-to-right level,
     and an odd level is a right-to-left level [UAX #9, BD2 and BD3].
     The result is the class @('L') for an even level
     and the class @('R') for an odd one."))
  (if (evenp (lnfix level))
      (bidi-class-left-to-right)
    (bidi-class-right-to-left))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bidi-bracket-role
  :short "Fixtype of the roles that a character can have
          in a bracket pair."
  :long
  (xdoc::topstring
   (xdoc::p
    "A character is not a paired bracket (@(':none')),
     or is an opening one (@(':open')) or a closing one (@(':close')).
     A bracket has an identifier, which says of which pair it is:
     an opening and a closing bracket can form a bracket pair
     exactly when they have the same identifier.")
   (xdoc::p
    "By [UAX #9, BD16], an opening bracket goes with a closing bracket
     when the @('Bidi_Paired_Bracket') of the former,
     or its canonical equivalent,
     is the latter or its canonical equivalent.
     So we take as identifier, for a closing bracket,
     the code point of its canonical equivalent
     if it has one and its own code point otherwise;
     and for an opening bracket, the identifier of its partner.
     See @(tsee code-point-bidi-bracket-role)."))
  (:none ())
  (:open ((id code-point)))
  (:close ((id code-point)))
  :pred bidi-bracket-role-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-bracket-role-list
  :short "Fixtype of lists of roles in bracket pairs."
  :elt-type bidi-bracket-role
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-bracket-role-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bidi-char
  :short "Fixtype of what the Unicode Bidirectional Algorithm
          looks at in a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the bidirectional class of the character
     and its role in a bracket pair."))
  ((class bidi-class)
   (bracket bidi-bracket-role))
  :pred bidi-char-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-char-list
  :short "Fixtype of lists of characters
          as the Unicode Bidirectional Algorithm sees them."
  :elt-type bidi-char
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-char-listp)

;;;;;;;;;;;;;;;;;;;;

(define bidi-char-list-classes ((chars bidi-char-listp))
  :returns (classes bidi-class-listp)
  :short "The bidirectional classes of a list of characters."
  (if (endp chars)
      nil
    (cons (bidi-char->class (car chars))
          (bidi-char-list-classes (cdr chars))))
  :hooks (:fix)

  ///

  (defrule len-of-bidi-char-list-classes
    (equal (len (bidi-char-list-classes chars))
           (len chars))
    :induct t
    :enable len))

;;;;;;;;;;;;;;;;;;;;

(define bidi-char-list-brackets ((chars bidi-char-listp))
  :returns (roles bidi-bracket-role-listp)
  :short "The roles in bracket pairs of a list of characters."
  (if (endp chars)
      nil
    (cons (bidi-char->bracket (car chars))
          (bidi-char-list-brackets (cdr chars))))
  :hooks (:fix)

  ///

  (defrule len-of-bidi-char-list-brackets
    (equal (len (bidi-char-list-brackets chars))
           (len chars))
    :induct t
    :enable len))

;;;;;;;;;;;;;;;;;;;;

(define bidi-classes-to-chars ((classes bidi-class-listp))
  :returns (chars bidi-char-listp)
  :short "Turn a list of bidirectional classes into a list of characters
          of which none is a paired bracket."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for statements about the algorithm
     in which brackets play no part,
     such as the lines of the conformance file @('BidiTest.txt'),
     which are lists of classes."))
  (if (endp classes)
      nil
    (cons (make-bidi-char :class (car classes)
                          :bracket (bidi-bracket-role-none))
          (bidi-classes-to-chars (cdr classes))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define canonical-singleton ((cp code-point-p) (ver versionp))
  :returns (equivalent code-point-p)
  :short "The single code point that a code point
          is canonically equivalent to, if there is one,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the canonical decomposition of the code point
     is one code point, the result is that code point;
     otherwise it is the code point itself.
     For example, U+232A RIGHT-POINTING ANGLE BRACKET
     gives U+3009 RIGHT ANGLE BRACKET."))
  (b* ((full (decomposition cp nil ver)))
    (if (and (consp full)
             (endp (cdr full)))
        (code-point-fix (car full))
      (code-point-fix cp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-point-bidi-bracket-role ((cp code-point-p) (ver versionp))
  :returns (role bidi-bracket-role-p)
  :short "The role of a code point in a bracket pair,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-bracket-role) for the identifier.
     The specification says that the only brackets
     with canonical equivalents are
     U+2329 and U+232A, which are equivalent to U+3008 and U+3009,
     and that no other will be added [UAX #9, BD16];
     we do not rely on that, and ask the decomposition tables."))
  (b* ((bracket? (code-point-bidi-bracket cp ver))
       ((unless bracket?) (bidi-bracket-role-none)))
    (bidi-bracket-case
     bracket?
     :open (bidi-bracket-role-open (canonical-singleton bracket?.partner ver))
     :close (bidi-bracket-role-close (canonical-singleton cp ver))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defsection bidi-brackets-are-neutral
  :short "Every paired bracket has the bidirectional class @('ON')
          (Other Neutral)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('BidiBrackets.txt') of the Unicode Character Database
     says that the stability policy guarantees this.
     The Unicode Bidirectional Algorithm asks, of a bracket of a pair,
     both that it is a paired bracket and that its class is @('ON')
     when the pairs are looked for [UAX #9, BD14 and BD15];
     by this theorem the second condition can only fail
     for a bracket whose class a rule of the algorithm has changed.
     We prove the theorem by checking it on every code point,
     for each version;
     so adding a version checks it for that version."))

  (local
   (define bracket-class-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (not (code-point-bidi-bracket cp ver))
         (equal (bidi-class-kind (code-point-bidi-class cp ver))
                :other-neutral))
     :hooks nil))

  (local
   (std::deflist bracket-class-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (bracket-class-ok x ver)))

  (defrulel bracket-class-ok-listp-of-all-code-points
    (bracket-class-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable bracket-class-ok-listp-of-cons)

  (defrulel bracket-class-ok-holds
    (bracket-class-ok cp ver)
    :rule-classes nil
    :use (:instance bracket-class-ok-when-member-equal-of-bracket-class-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable bracket-class-ok)

  (defrule code-point-bidi-class-when-code-point-bidi-bracket
    (implies (code-point-bidi-bracket cp ver)
             (equal (bidi-class-kind (code-point-bidi-class cp ver))
                    :other-neutral))
    :enable bracket-class-ok
    :use bracket-class-ok-holds)

  (defrule code-point-bidi-class-when-bracket-role
    (implies (not (equal (bidi-bracket-role-kind
                          (code-point-bidi-bracket-role cp ver))
                         :none))
             (equal (bidi-class-kind (code-point-bidi-class cp ver))
                    :other-neutral))
    :enable code-point-bidi-bracket-role))

;;;;;;;;;;;;;;;;;;;;

(define code-point-bidi-char ((cp code-point-p) (ver versionp))
  :returns (char bidi-char-p)
  :short "A code point as the Unicode Bidirectional Algorithm sees it,
          in a version of Unicode."
  (make-bidi-char :class (code-point-bidi-class cp ver)
                  :bracket (code-point-bidi-bracket-role cp ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define code-points-to-bidi-chars ((cps code-point-listp) (ver versionp))
  :returns (chars bidi-char-listp)
  :short "A list of code points as the Unicode Bidirectional Algorithm
          sees it, in a version of Unicode."
  (if (endp cps)
      nil
    (cons (code-point-bidi-char (car cps) ver)
          (code-points-to-bidi-chars (cdr cps) ver)))
  :hooks (:fix)

  ///

  (defrule len-of-code-points-to-bidi-chars
    (equal (len (code-points-to-bidi-chars cps ver))
           (len cps))
    :induct t
    :enable len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum paragraph-direction
  :short "Fixtype of the ways to give the direction of a paragraph."
  :long
  (xdoc::topstring
   (xdoc::p
    "The direction of a paragraph is from left to right
     or from right to left;
     it is the direction of the paragraph embedding level,
     which is 0 or 1 [UAX #9, BD4 and BD5].
     Either a higher-level protocol gives it
     (@(':left-to-right') or @(':right-to-left'))
     [UAX #9, HL1],
     or it is found in the text, by rules P2 and P3,
     from the first character with a strong direction
     (@(':first-strong'))."))
  (:left-to-right ())
  (:right-to-left ())
  (:first-strong ())
  :pred paragraph-direction-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-first-strong ((classes bidi-class-listp)
                           (depth natp)
                           (in-isolate booleanp))
  :returns (class? bidi-class-option-p)
  :short "The first strong class in a list of bidirectional classes,
          not looking inside isolates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the search of rule P2 [UAX #9, rule P2]:
     for the first character of class @('L'), @('AL') or @('R'),
     skipping the characters between an isolate initiator
     and its matching @('PDI'),
     or the end of the list if it has none.
     The result is the class found, or @('nil') if there is none.")
   (xdoc::p
    "The matching @('PDI') of an isolate initiator is found
     by counting [UAX #9, BD9]:
     up at each isolate initiator, down at each @('PDI'),
     until the count is back to where it was.
     The argument @('depth') is that count:
     the number of isolates that we are inside of and are skipping.
     A @('PDI') met when the count is zero matches no isolate initiator
     of the list.
     If the flag @('in-isolate') is @('nil'), such a @('PDI') is ignored,
     as rule P2 does in a paragraph.
     If the flag is true, the search ends there:
     this is for rule X5c, which applies rule P2
     to the characters between an @('FSI') and its matching @('PDI')."))
  (b* (((when (endp classes)) nil)
       (class (bidi-class-fix (car classes)))
       (depth (lnfix depth))
       ((when (bidi-class-isolate-initiator-p class))
        (bidi-first-strong (cdr classes) (+ 1 depth) in-isolate))
       ((when (equal (bidi-class-kind class) :pop-directional-isolate))
        (cond ((> depth 0)
               (bidi-first-strong (cdr classes) (- depth 1) in-isolate))
              (in-isolate nil)
              (t (bidi-first-strong (cdr classes) 0 in-isolate))))
       ((when (and (equal depth 0)
                   (bidi-class-strong-p class)))
        class))
    (bidi-first-strong (cdr classes) depth in-isolate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-first-strong-level ((classes bidi-class-listp)
                                 (in-isolate booleanp))
  :returns (level natp :rule-classes (:rewrite :type-prescription))
  :short "The embedding level that rules P2 and P3 give
          to a list of bidirectional classes."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is 1 if the first strong class found by rule P2
     (see @(tsee bidi-first-strong)) is @('AL') or @('R'),
     and 0 if it is @('L') or if there is none [UAX #9, rule P3]."))
  (b* ((class? (bidi-first-strong classes 0 in-isolate)))
    (if (and class?
             (bidi-class-right-to-left-p class?))
        1
      0))
  :hooks (:fix)

  ///

  (defrule bidi-first-strong-level-upper-bound
    (<= (bidi-first-strong-level classes in-isolate) 1)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;

(define bidi-paragraph-embedding-level ((chars bidi-char-listp)
                                        (direction paragraph-direction-p))
  :returns (level natp :rule-classes (:rewrite :type-prescription))
  :short "The paragraph embedding level of a paragraph."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is 0 for a paragraph from left to right
     and 1 for a paragraph from right to left.
     If the direction is to be found in the text,
     rules P2 and P3 find it [UAX #9, rules P2 and P3]."))
  (paragraph-direction-case
   direction
   :left-to-right 0
   :right-to-left 1
   :first-strong (bidi-first-strong-level (bidi-char-list-classes chars)
                                          nil))
  :hooks (:fix)

  ///

  (defrule bidi-paragraph-embedding-level-upper-bound
    (<= (bidi-paragraph-embedding-level chars direction) 1)
    :rule-classes :linear))
