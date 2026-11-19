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
(include-book "ranges")

(include-book "data/v16.0.0/derived-core-properties")
(include-book "data/v17.0.0/derived-core-properties")
(include-book "data/v18.0.0/derived-core-properties")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ xid
  :parents (unicode)
  :short "The @('XID_Start') and @('XID_Continue') properties,
          and the identifiers that they define."
  :long
  (xdoc::topstring
   (xdoc::p
    "In these names, @('ID') is short for `identifier'.
     [UAX #31] has the properties @('ID_Start') and @('ID_Continue'),
     of the code points that can start an identifier
     and of the code points that can continue one.
     It derives @('XID_Start') and @('XID_Continue') from those two
     with the modifications of [UAX #31, Section 5.1],
     which are there so that normalizing an identifier gives an identifier
     (this is proved in @(see identifier-closure)).
     So the letter @('X') marks the two properties
     that have those modifications;
     the Unicode documents do not say what it stands for.
     Like [UAX #31], we write @('XID')
     for @('XID_Start') and @('XID_Continue') together.")
   (xdoc::p
    "[UAX #31] recommends the @('XID') properties
     for the identifiers of programming languages.
     In its default identifier syntax,
     an identifier consists of a code point with @('XID_Start')
     followed by any number of code points with @('XID_Continue')
     (see @(tsee xid-identifier-p)).
     Languages adjust this;
     many also let an identifier start with an underscore,
     which has @('XID_Continue') but not @('XID_Start')
     (see @(tsee optional-start-p)).")
   (xdoc::p
    "Both are derived properties.
     We take them from the file @('DerivedCoreProperties.txt')
     of the Unicode Character Database, for each supported version;
     we do not recompute them from the properties they derive from.")
   (xdoc::p
    "No surrogate has either property,
     so a code point that has one of them is a scalar value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xid-start-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('XID_Start') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *xid-start-v16.0.0*
                :v17.0.0 *xid-start-v17.0.0*
                :v18.0.0 *xid-start-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define xid-continue-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('XID_Continue') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *xid-continue-v16.0.0*
                :v17.0.0 *xid-continue-v17.0.0*
                :v18.0.0 *xid-continue-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xid-start-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('XID_Start') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the code point can start an identifier.
     See @(see xid) for the name of the property."))
  (code-point-in-ranges-p cp (xid-start-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define xid-continue-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('XID_Continue') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the code point can continue an identifier;
     the code points that can start one can also continue one.
     See @(see xid) for the name of the property."))
  (code-point-in-ranges-p cp (xid-continue-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xid-theorems
  :short "Theorems about @('XID_Start') and @('XID_Continue')
          that hold in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every code point that can start an identifier can continue one.
     Every code point that can continue an identifier is a scalar value.
     Among the ASCII code points, which are those below @('#x80'),
     the ones that can start an identifier are the letters,
     and the ones that can continue an identifier are
     the letters, the digits and the underscore.")
   (xdoc::p
    "These are proved by evaluation on the tables, for each version:
     so adding a version checks them for that version."))

  (defrule xid-start-ranges-within-xid-continue-ranges
    (ranges-within-ranges-p (xid-start-ranges ver)
                            (xid-continue-ranges ver))
    :enable (xid-start-ranges xid-continue-ranges))

  (defrule xid-continue-ranges-within-scalar-value-ranges
    (ranges-within-ranges-p (xid-continue-ranges ver)
                            (scalar-value-ranges))
    :enable (xid-continue-ranges (:e scalar-value-ranges)))

  (defrule xid-continue-p-when-xid-start-p
    (implies (xid-start-p cp ver)
             (xid-continue-p cp ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (xid-start-p
             xid-continue-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule scalar-value-p-when-xid-continue-p
    (implies (and (xid-continue-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :enable (xid-continue-p
             scalar-value-p-when-code-point-in-scalar-value-ranges
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule scalar-value-p-when-xid-start-p
    (implies (and (xid-start-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining))

  ;; The ASCII code points that have, and that do not have, XID_Start.
  ;; We check each of the 128 ASCII code points, for each version.

  (local
   (define ascii-start-ok ((cp code-point-p) (ranges range-listp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp)))
       (equal (code-point-in-ranges-p cp ranges)
              (or (and (<= (char-code #\A) cp)
                       (<= cp (char-code #\Z)))
                  (and (<= (char-code #\a) cp)
                       (<= cp (char-code #\z))))))
     :hooks nil))

  (local
   (std::deflist ascii-start-ok-listp (x ranges)
     :guard (and (code-point-listp x)
                 (range-listp ranges))
     (ascii-start-ok x ranges)))

  (defrulel ascii-start-ok-listp-of-ascii
    (ascii-start-ok-listp (integers-from-to 0 #x7F)
                          (xid-start-ranges ver))
    :enable xid-start-ranges
    :disable ascii-start-ok-listp-of-cons)

  (defruled xid-start-p-when-ascii
    (implies (and (code-point-p cp)
                  (< cp #x80))
             (equal (xid-start-p cp ver)
                    (or (and (<= (char-code #\A) cp)
                             (<= cp (char-code #\Z)))
                        (and (<= (char-code #\a) cp)
                             (<= cp (char-code #\z))))))
    :enable (xid-start-p
             ascii-start-ok
             code-point-p)
    :disable ((:e integers-from-to))
    :use (:instance ascii-start-ok-when-member-equal-of-ascii-start-ok-listp
                    (acl2::a cp)
                    (x (integers-from-to 0 #x7F))
                    (ranges (xid-start-ranges ver))))

  ;; The ASCII code points that have, and that do not have, XID_Continue.
  ;; We check each of the 128 ASCII code points, for each version.

  (local
   (define ascii-continue-ok ((cp code-point-p) (ranges range-listp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp)))
       (equal (code-point-in-ranges-p cp ranges)
              (or (and (<= (char-code #\0) cp)
                       (<= cp (char-code #\9)))
                  (and (<= (char-code #\A) cp)
                       (<= cp (char-code #\Z)))
                  (equal cp (char-code #\_))
                  (and (<= (char-code #\a) cp)
                       (<= cp (char-code #\z))))))
     :hooks nil))

  (local
   (std::deflist ascii-continue-ok-listp (x ranges)
     :guard (and (code-point-listp x)
                 (range-listp ranges))
     (ascii-continue-ok x ranges)))

  (defrulel ascii-continue-ok-listp-of-ascii
    (ascii-continue-ok-listp (integers-from-to 0 #x7F)
                             (xid-continue-ranges ver))
    :enable xid-continue-ranges
    :disable ascii-continue-ok-listp-of-cons)

  (defruled xid-continue-p-when-ascii
    (implies (and (code-point-p cp)
                  (< cp #x80))
             (equal (xid-continue-p cp ver)
                    (or (and (<= (char-code #\0) cp)
                             (<= cp (char-code #\9)))
                        (and (<= (char-code #\A) cp)
                             (<= cp (char-code #\Z)))
                        (equal cp (char-code #\_))
                        (and (<= (char-code #\a) cp)
                             (<= cp (char-code #\z))))))
    :enable (xid-continue-p
             ascii-continue-ok
             code-point-p)
    :disable ((:e integers-from-to))
    :use (:instance
          ascii-continue-ok-when-member-equal-of-ascii-continue-ok-listp
          (acl2::a cp)
          (x (integers-from-to 0 #x7F))
          (ranges (xid-continue-ranges ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist xid-continue-listp (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check if all the code points of a list
          have the @('XID_Continue') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if each of them can continue an identifier.
     See @(see xid) for the name of the property."))
  (xid-continue-p x ver)

  ///

  (fty::deffixequiv xid-continue-listp
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (xid-continue-listp x ver)
             :in-theory (enable xid-continue-listp))))

  (defruled scalar-value-listp-when-xid-continue-listp
    (implies (and (xid-continue-listp cps ver)
                  (code-point-listp cps))
             (scalar-value-listp cps))
    :induct t
    :enable xid-continue-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xid-identifier-p ((cps code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points is an @('XID') identifier,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "By @('XID') identifier we mean an identifier
     that is made of code points with the @('XID') properties:
     a code point that has @('XID_Start'),
     followed by any number of code points that have @('XID_Continue').
     This is the default identifier syntax of [UAX #31, UAX31-D1]
     with the lexical classes of [UAX #31, UAX31-R1-1];
     there are no medial code points.")
   (xdoc::p
    "In @('XID'), @('ID') is short for `identifier',
     and the letter @('X') distinguishes these two properties
     from @('ID_Start') and @('ID_Continue'),
     from which they are derived
     so that normalizing an identifier gives an identifier:
     see @(see xid)."))
  (and (consp cps)
       (xid-start-p (car cps) ver)
       (xid-continue-listp (cdr cps) ver))
  :hooks (:fix)

  ///

  (defrule xid-identifier-p-of-cons
    (equal (xid-identifier-p (cons cp cps) ver)
           (and (xid-start-p cp ver)
                (xid-continue-listp cps ver))))

  (defrule xid-identifier-p-of-append
    (equal (xid-identifier-p (append cps1 cps2) ver)
           (if (consp cps1)
               (and (xid-identifier-p cps1 ver)
                    (xid-continue-listp cps2 ver))
             (xid-identifier-p cps2 ver))))

  (defrule xid-continue-listp-when-xid-identifier-p
    (implies (xid-identifier-p cps ver)
             (xid-continue-listp cps ver))
    :rule-classes (:rewrite :forward-chaining))

  (defruled scalar-value-listp-when-xid-identifier-p
    (implies (and (xid-identifier-p cps ver)
                  (code-point-listp cps))
             (scalar-value-listp cps))
    :enable scalar-value-listp-when-xid-continue-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define optional-start-p ((cp code-point-p))
  :returns (yes/no booleanp)
  :short "Check if a code point is one of the two optional characters
          for the start of an identifier:
          the dollar sign and the underscore."
  :long
  (xdoc::topstring
   (xdoc::p
    "[UAX #31, Section 2.4, Table 3] lists these two code points,
     U+0024 DOLLAR SIGN and U+005F LOW LINE,
     as the optional characters for @('Start'),
     which is the class of the code points that can start an identifier.
     A language can add them to that class
     by declaring a profile of the default identifier syntax
     [UAX #31, UAX31-R1-2].
     Many programming languages allow an identifier
     to start with an underscore,
     and some also allow it to start with a dollar sign.")
   (xdoc::p
    "Neither of the two has the @('XID_Start') property,
     in any supported version of Unicode,
     which is why they have to be added.
     The underscore has the @('XID_Continue') property;
     the dollar sign does not.
     See @(see xid) for the names of the two properties.")
   (xdoc::p
    "The normalization forms leave these two code points alone
     at the start of a list:
     see @(see identifier-closure-with-optional-start)."))
  (or (equal cp #x24)
      (equal cp #x5F))
  :hooks nil ; done below

  ///

  ;; The fixing function maps what is not a code point to 0,
  ;; which is not one of the two.

  (fty::deffixequiv optional-start-p
    :hints (("Goal" :in-theory (enable code-point-fix))))

  (defrule not-xid-start-p-when-optional-start-p
    (implies (optional-start-p cp)
             (not (xid-start-p cp ver)))
    :enable xid-start-p-when-ascii)

  (defruled xid-continue-p-when-optional-start-p
    (implies (optional-start-p cp)
             (equal (xid-continue-p cp ver)
                    (equal cp #x5F)))
    :enable xid-continue-p-when-ascii))
