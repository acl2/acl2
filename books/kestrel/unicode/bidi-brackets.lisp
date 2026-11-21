; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "versions")
(include-book "maps")
(include-book "data/v16.0.0/bidi-brackets")
(include-book "data/v17.0.0/bidi-brackets")
(include-book "data/v18.0.0/bidi-brackets")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-paired-brackets
  :parents (unicode)
  :short "The paired brackets:
          the properties @('Bidi_Paired_Bracket_Type')
          and @('Bidi_Paired_Bracket')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode Bidirectional Algorithm treats some brackets in pairs,
     so that an opening bracket and the bracket that closes it
     are displayed in the same direction
     [UAX #9, Section 3.1.3 and rule N0].
     It finds them with two properties.
     @('Bidi_Paired_Bracket_Type') is @('Open') for an opening bracket,
     @('Close') for a closing bracket,
     and @('None') for every other code point.
     @('Bidi_Paired_Bracket') is, for a bracket,
     the other bracket of its pair, which we call its partner:
     the partner of U+0028 LEFT PARENTHESIS is U+0029 RIGHT PARENTHESIS,
     and the partner of U+0029 is U+0028.")
   (xdoc::p
    "Not every bracket of Unicode is a paired bracket in this sense,
     and the quotation marks are not:
     the two properties list the pairs
     that are used as brackets in mathematics and in ordinary text
     and whose two members are mirror images of each other.")
   (xdoc::p
    "We take the two properties from the file @('BidiBrackets.txt')
     of the Unicode Character Database, for each supported version.
     There are 64 pairs in Unicode 16.0.0 and 17.0.0, and 65 in 18.0.0."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-brackets ((ver versionp))
  :returns (map bidi-bracket-mapp)
  :short "The map from the paired brackets to their type and partner,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *bidi-bracket-v16.0.0*
                :v17.0.0 *bidi-bracket-v17.0.0*
                :v18.0.0 *bidi-bracket-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-bidi-bracket ((cp code-point-p) (ver versionp))
  :returns (bracket? bidi-bracket-option-p)
  :short "The @('Bidi_Paired_Bracket_Type') and @('Bidi_Paired_Bracket')
          of a code point, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') for a code point that is not a paired bracket,
     that is, whose @('Bidi_Paired_Bracket_Type') is @('None').
     For an opening bracket it is a value of the kind @(':open'),
     and for a closing bracket a value of the kind @(':close'),
     each with the partner of the bracket:
     see @(tsee bidi-bracket)."))
  (bidi-bracket-map-lookup cp (bidi-brackets ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-bracket-partners
  :short "Each paired bracket is the partner of its partner,
          and the two are of different types."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is: the partner of an opening bracket is a closing bracket
     whose partner is that opening bracket,
     and the partner of a closing bracket is an opening bracket
     whose partner is that closing bracket.
     So the paired brackets come in pairs of one opening
     and one closing bracket, and no bracket is in two pairs.
     We prove this by checking it on every code point, for each version;
     so adding a version checks it for that version."))

  (local
   (define bracket-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (b* ((bracket? (code-point-bidi-bracket cp ver))
          ((unless bracket?) t))
       (bidi-bracket-case
        bracket?
        :open (equal (code-point-bidi-bracket bracket?.partner ver)
                     (bidi-bracket-close (code-point-fix cp)))
        :close (equal (code-point-bidi-bracket bracket?.partner ver)
                      (bidi-bracket-open (code-point-fix cp)))))
     :hooks nil))

  (local
   (std::deflist bracket-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (bracket-ok x ver)))

  (defrulel bracket-ok-listp-of-all-code-points
    (bracket-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable bracket-ok-listp-of-cons)

  (defrulel bracket-ok-holds
    (bracket-ok cp ver)
    :rule-classes nil
    :use (:instance bracket-ok-when-member-equal-of-bracket-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable bracket-ok)

  (defrule code-point-bidi-bracket-of-partner-when-open
    (b* ((bracket? (code-point-bidi-bracket cp ver)))
      (implies (and bracket?
                    (equal (bidi-bracket-kind bracket?) :open))
               (equal (code-point-bidi-bracket
                       (bidi-bracket-open->partner bracket?) ver)
                      (bidi-bracket-close (code-point-fix cp)))))
    :enable bracket-ok
    :use bracket-ok-holds)

  (defrule code-point-bidi-bracket-of-partner-when-close
    (b* ((bracket? (code-point-bidi-bracket cp ver)))
      (implies (and bracket?
                    (equal (bidi-bracket-kind bracket?) :close))
               (equal (code-point-bidi-bracket
                       (bidi-bracket-close->partner bracket?) ver)
                      (bidi-bracket-open (code-point-fix cp)))))
    :enable bracket-ok
    :use bracket-ok-holds))
