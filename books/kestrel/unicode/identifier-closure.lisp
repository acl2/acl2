; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "xid")
(include-book "normalization")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifier-closure
  :parents (unicode)
  :short "Identifiers are closed under normalization."
  :long
  (xdoc::topstring
   (xdoc::p
    "[UAX #31, Section 5.1.3] says that
     the identifiers that are defined with
     the @('XID_Start') and @('XID_Continue') properties
     are closed under the four normalization forms:
     if a string is an identifier,
     so is each of its four normalized forms.
     This is what these two properties are for:
     they are derived from @('ID_Start') and @('ID_Continue'),
     where @('ID') is short for `identifier',
     so as to make it hold (see @(see xid)).
     It also says that, for the two canonical forms, the reverse holds:
     if the form of a string
     in Normalization Form D (NFD) or in Normalization Form C (NFC)
     is an identifier, so is the string.")
   (xdoc::p
    "Here we prove both statements,
     for the @('XID') identifiers of @(tsee xid-identifier-p)
     and for the four normalization forms of @(see normalization),
     which are NFD, NFC,
     and the two compatibility forms NFKD and NFKC,
     in every supported version of Unicode.
     So a tool that normalizes the identifiers that it reads
     does not turn an identifier into something else;
     and if it normalizes to NFC before it checks for identifiers,
     it accepts the same strings as if it checked first.")
   (xdoc::p
    "We also prove the same for the lists of code points
     that all have @('XID_Continue') (see @(tsee xid-continue-listp)),
     which are what can follow the first code point of an identifier.")
   (xdoc::p
    "The proof has two layers.
     The first layer consists of facts about single code points,
     which we prove by checking them on every code point, for each version;
     so adding a version checks them for that version.
     The second layer follows the definitions of the normalization forms:
     see @(see identifier-closure-under-decomposition)
     and @(see identifier-closure-under-composition)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The checks below take tables of ranges.
;; These rules turn what they say about the tables of the two properties
;; into statements about the properties.

(defrulel code-point-in-ranges-p-of-xid-start-ranges
  (equal (code-point-in-ranges-p cp (xid-start-ranges ver))
         (xid-start-p cp ver))
  :enable xid-start-p)

(defrulel code-point-in-ranges-p-of-xid-continue-ranges
  (equal (code-point-in-ranges-p cp (xid-continue-ranges ver))
         (xid-continue-p cp ver))
  :enable xid-continue-p)

(local
 (std::deflist code-points-in-ranges-p (x ranges)
   :guard (and (code-point-listp x)
               (range-listp ranges))
   (code-point-in-ranges-p x ranges)))

(defrulel code-points-in-ranges-p-of-xid-continue-ranges
  (equal (code-points-in-ranges-p cps (xid-continue-ranges ver))
         (xid-continue-listp cps ver))
  :induct t
  :enable (code-points-in-ranges-p
           xid-continue-listp))

(defrulel true-listp-of-decomposition-map-lookup
  (scalar-value-listp (decomposition-map-lookup cp map))
  :rule-classes ((:type-prescription
                  :corollary (true-listp (decomposition-map-lookup cp map)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xid-start-starters
  :short "A code point that can start an identifier is a starter."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if a code point has the @('XID_Start') property
     (see @(tsee xid-start-p)),
     its canonical combining class is 0.
     So canonical ordering does not move
     the first code point of an identifier.
     We prove it by checking it on every code point, for each version."))

  (local
   (define starter-ok ((cp code-point-p)
                       (map combining-class-mapp)
                       (start range-listp))
     :returns (yes/no booleanp)
     (or (equal (combining-class-map-lookup cp map) 0)
         (not (code-point-in-ranges-p cp start)))
     :hooks nil))

  (local
   (std::deflist starter-ok-listp (x map start)
     :guard (and (code-point-listp x)
                 (combining-class-mapp map)
                 (range-listp start))
     (starter-ok x map start)))

  (defrulel starter-ok-listp-of-all-code-points
    (starter-ok-listp (all-code-points)
                      (canonical-combining-class-map ver)
                      (xid-start-ranges ver))
    :enable (canonical-combining-class-map
             xid-start-ranges
             (:e all-code-points))
    :disable starter-ok-listp-of-cons)

  (defrule canonical-combining-class-when-xid-start-p
    (implies (xid-start-p cp ver)
             (equal (canonical-combining-class cp ver)
                    0))
    :enable (canonical-combining-class
             starter-ok)
    :use (:instance starter-ok-when-member-equal-of-starter-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (map (canonical-combining-class-map ver))
                    (start (xid-start-ranges ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xid-of-canonical-decomposition
  :short "A code point can continue an identifier
          exactly when its canonical decomposition
          consists of code points that can;
          it can start an identifier
          exactly when its canonical decomposition is an identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here a code point can continue an identifier
     if it has the @('XID_Continue') property,
     it can start one if it has the @('XID_Start') property,
     and an identifier is an @('XID') identifier:
     see @(see xid) for these names.")
   (xdoc::p
    "We prove it by checking it on every code point, for each version.
     The check looks at the ranges of the two properties
     only for the code points that have decompositions other than themselves,
     which keeps it fast."))

  (local
   (define canonical-ok ((cp code-point-p)
                         (full decomposition-mapp)
                         (start range-listp)
                         (continue range-listp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp))
          (cps (if (hangul-syllable-p cp)
                   (hangul-syllable-decomposition cp)
                 (decomposition-map-lookup cp full))))
       (or (not (consp cps))
           (and (equal (code-point-in-ranges-p cp continue)
                       (code-points-in-ranges-p cps continue))
                (equal (code-point-in-ranges-p cp start)
                       (and (code-point-in-ranges-p (car cps) start)
                            (code-points-in-ranges-p (cdr cps) continue))))))
     :hooks nil))

  (local
   (std::deflist canonical-ok-listp (x full start continue)
     :guard (and (code-point-listp x)
                 (decomposition-mapp full)
                 (range-listp start)
                 (range-listp continue))
     (canonical-ok x full start continue)))

  (defrulel canonical-ok-listp-of-all-code-points
    (canonical-ok-listp (all-code-points)
                        (canonical-decompositions ver)
                        (xid-start-ranges ver)
                        (xid-continue-ranges ver))
    :enable (canonical-decompositions
             xid-start-ranges
             xid-continue-ranges
             (:e all-code-points))
    :disable canonical-ok-listp-of-cons)

  (defrule xid-continue-listp-of-canonical-decomposition
    (equal (xid-continue-listp (decomposition cp nil ver) ver)
           (xid-continue-p cp ver))
    :enable (decomposition
             canonical-ok)
    :use (:instance canonical-ok-when-member-equal-of-canonical-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (full (canonical-decompositions ver))
                    (start (xid-start-ranges ver))
                    (continue (xid-continue-ranges ver))))

  (defrule xid-identifier-p-of-canonical-decomposition
    (equal (xid-identifier-p (decomposition cp nil ver) ver)
           (xid-start-p cp ver))
    :enable (decomposition
             canonical-ok
             xid-identifier-p)
    :use (:instance canonical-ok-when-member-equal-of-canonical-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (full (canonical-decompositions ver))
                    (start (xid-start-ranges ver))
                    (continue (xid-continue-ranges ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xid-of-compatibility-decomposition
  :short "The compatibility decomposition
          of a code point that can continue an identifier
          consists of code points that can;
          the compatibility decomposition
          of a code point that can start an identifier
          is an identifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "The terms are those of @(see xid-of-canonical-decomposition).
     Unlike for the canonical decompositions,
     the converses do not hold.
     For example, U+2122 TRADE MARK SIGN cannot be in an identifier,
     but its compatibility decomposition, which is @('TM'), is an identifier.")
   (xdoc::p
    "We prove it by checking it on every code point, for each version."))

  (local
   (define compatibility-ok ((cp code-point-p)
                             (full decomposition-mapp)
                             (start range-listp)
                             (continue range-listp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp))
          (cps (if (hangul-syllable-p cp)
                   (hangul-syllable-decomposition cp)
                 (decomposition-map-lookup cp full))))
       (or (not (consp cps))
           (and (or (not (code-point-in-ranges-p cp continue))
                    (code-points-in-ranges-p cps continue))
                (or (not (code-point-in-ranges-p cp start))
                    (code-point-in-ranges-p (car cps) start)))))
     :hooks nil))

  (local
   (std::deflist compatibility-ok-listp (x full start continue)
     :guard (and (code-point-listp x)
                 (decomposition-mapp full)
                 (range-listp start)
                 (range-listp continue))
     (compatibility-ok x full start continue)))

  (defrulel compatibility-ok-listp-of-all-code-points
    (compatibility-ok-listp (all-code-points)
                            (compatibility-decompositions ver)
                            (xid-start-ranges ver)
                            (xid-continue-ranges ver))
    :enable (compatibility-decompositions
             xid-start-ranges
             xid-continue-ranges
             (:e all-code-points))
    :disable compatibility-ok-listp-of-cons)

  (defrule xid-continue-listp-of-compatibility-decomposition
    (implies (xid-continue-p cp ver)
             (xid-continue-listp (decomposition cp t ver) ver))
    :enable (decomposition
             compatibility-ok)
    :use (:instance compatibility-ok-when-member-equal-of-compatibility-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (full (compatibility-decompositions ver))
                    (start (xid-start-ranges ver))
                    (continue (xid-continue-ranges ver))))

  (defrule xid-identifier-p-of-compatibility-decomposition
    (implies (xid-start-p cp ver)
             (xid-identifier-p (decomposition cp t ver) ver))
    :enable (decomposition
             compatibility-ok
             xid-identifier-p)
    :use (:instance compatibility-ok-when-member-equal-of-compatibility-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (full (compatibility-decompositions ver))
                    (start (xid-start-ranges ver))
                    (continue (xid-continue-ranges ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection identifier-closure-under-decomposition
  :short "The two decomposed normalization forms, NFD and NFKD,
          take identifiers to identifiers;
          NFD takes only identifiers to identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here NFD and NFKD are Normalization Forms D and KD
     (see @(tsee nfd) and @(tsee nfkd)),
     and an identifier is an @('XID') identifier
     (see @(tsee xid-identifier-p)).")
   (xdoc::p
    "The first statement is the closure
     of [UAX #31, Section 5.1.3, Figure 5], for these two forms.
     The second one is the reverse closure of Figure 7 there, for NFD;
     it does not hold for NFKD
     (see @(see xid-of-compatibility-decomposition)).
     The same holds for the lists of code points
     that can continue an identifier
     (see @(tsee xid-continue-listp)).")
   (xdoc::p
    "The decomposed forms are obtained in two steps.
     Decomposition replaces each code point with its decomposition,
     so what it does follows from
     what the decomposition of a code point is like
     (see @(see xid-of-canonical-decomposition)
     and @(see xid-of-compatibility-decomposition)).
     Canonical ordering only rearranges the code points,
     and it leaves the first one where it is if that is a starter,
     which the first code point of an identifier is
     (see @(see xid-start-starters));
     so a list is an identifier exactly when its canonical ordering is."))

  ;; Decomposition.

  (defrule xid-continue-listp-of-canonical-decompose
    (equal (xid-continue-listp (decompose cps nil ver) ver)
           (xid-continue-listp cps ver))
    :induct t
    :enable decompose)

  (defrule xid-identifier-p-of-canonical-decompose
    (equal (xid-identifier-p (decompose cps nil ver) ver)
           (xid-identifier-p cps ver))
    :enable xid-identifier-p
    :expand (decompose cps nil ver))

  (defrule xid-continue-listp-of-compatibility-decompose
    (implies (xid-continue-listp cps ver)
             (xid-continue-listp (decompose cps t ver) ver))
    :induct t
    :enable decompose)

  (defrule xid-identifier-p-of-compatibility-decompose
    (implies (xid-identifier-p cps ver)
             (xid-identifier-p (decompose cps t ver) ver))
    :enable xid-identifier-p
    :expand (decompose cps t ver))

  ;; Canonical ordering.

  (defrule xid-continue-listp-of-canonical-order-insert
    (equal (xid-continue-listp (canonical-order-insert cp cps ver) ver)
           (and (xid-continue-p cp ver)
                (xid-continue-listp cps ver)))
    :induct t
    :enable canonical-order-insert)

  (defrule xid-continue-listp-of-canonical-order
    (equal (xid-continue-listp (canonical-order cps ver) ver)
           (xid-continue-listp cps ver))
    :induct t
    :enable canonical-order)

  (defrulel not-xid-identifier-p-of-canonical-order-insert
    (implies (not (equal (canonical-combining-class cp ver) 0))
             (not (xid-identifier-p (canonical-order-insert cp cps ver)
                                    ver)))
    :expand (canonical-order-insert cp cps ver))

  (defrule xid-identifier-p-of-canonical-order
    (equal (xid-identifier-p (canonical-order cps ver) ver)
           (xid-identifier-p cps ver))
    :enable xid-identifier-p
    :expand (canonical-order cps ver))

  ;; The two forms.

  (defrule xid-continue-listp-of-nfd
    (equal (xid-continue-listp (nfd cps ver) ver)
           (xid-continue-listp cps ver))
    :enable nfd)

  (defrule xid-identifier-p-of-nfd
    (equal (xid-identifier-p (nfd cps ver) ver)
           (xid-identifier-p cps ver))
    :enable nfd)

  (defrule xid-continue-listp-of-nfkd
    (implies (xid-continue-listp cps ver)
             (xid-continue-listp (nfkd cps ver) ver))
    :enable nfkd)

  (defrule xid-identifier-p-of-nfkd
    (implies (xid-identifier-p cps ver)
             (xid-identifier-p (nfkd cps ver) ver))
    :enable nfkd))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection identifier-closure-under-composition
  :short "The two composed normalization forms, NFC and NFKC,
          take identifiers to identifiers;
          NFC takes only identifiers to identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here NFC and NFKC are Normalization Forms C and KC
     (see @(tsee nfc) and @(tsee nfkc)),
     and an identifier is an @('XID') identifier
     (see @(tsee xid-identifier-p)).")
   (xdoc::p
    "The first statement is the closure
     of [UAX #31, Section 5.1.3, Figure 5], for these two forms.
     The second one is the reverse closure of Figure 7 there, for NFC;
     it does not hold for NFKC.
     The same holds for the lists of code points
     that can continue an identifier
     (see @(tsee xid-continue-listp)).")
   (xdoc::p
    "The composed forms are obtained from the decomposed ones
     by canonical composition.
     We do not need to look at how canonical composition works:
     it can be undone by NFD, which is Normalization Form D
     (see @(see canonical-composition-theorems)),
     and NFD neither makes nor unmakes identifiers
     (see @(see identifier-closure-under-decomposition)).
     So a list that is fully decomposed and canonically ordered
     is an identifier exactly when its canonical composition is."))

  ;; Canonical composition.
  ;; We use the theorem about NFD on the canonical composition of the list.
  ;; (That theorem is disabled in these two proofs,
  ;; because as a rule it would rewrite its own instance to true.)

  (defrule xid-continue-listp-of-canonical-compose
    (implies (and (undecomposable-listp cps nil ver)
                  (canonically-ordered-p cps ver))
             (equal (xid-continue-listp (canonical-compose cps ver) ver)
                    (xid-continue-listp cps ver)))
    :use (:instance xid-continue-listp-of-nfd
                    (cps (canonical-compose cps ver)))
    :disable xid-continue-listp-of-nfd)

  (defrule xid-identifier-p-of-canonical-compose
    (implies (and (undecomposable-listp cps nil ver)
                  (canonically-ordered-p cps ver))
             (equal (xid-identifier-p (canonical-compose cps ver) ver)
                    (xid-identifier-p cps ver)))
    :use (:instance xid-identifier-p-of-nfd
                    (cps (canonical-compose cps ver)))
    :disable xid-identifier-p-of-nfd)

  ;; The two forms.

  (defrule xid-continue-listp-of-nfc
    (equal (xid-continue-listp (nfc cps ver) ver)
           (xid-continue-listp cps ver))
    :enable nfc)

  (defrule xid-identifier-p-of-nfc
    (equal (xid-identifier-p (nfc cps ver) ver)
           (xid-identifier-p cps ver))
    :enable nfc)

  (defrule xid-continue-listp-of-nfkc
    (implies (xid-continue-listp cps ver)
             (xid-continue-listp (nfkc cps ver) ver))
    :enable nfkc)

  (defrule xid-identifier-p-of-nfkc
    (implies (xid-identifier-p cps ver)
             (xid-identifier-p (nfkc cps ver) ver))
    :enable nfkc))
