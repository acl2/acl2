; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "runs")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifier-type-tables
  :parents (tables)
  :short "The values of the @('Identifier_Type') property,
          and tables of runs of code points that have the same types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Identifier_Type') property
     of Unicode Technical Standard #39, Unicode Security Mechanisms,
     which we cite as [UTS #39],
     assigns to every code point a set of types [UTS #39, Table 1].
     A type is a reason for which a character
     is recommended, or is not recommended, for use in identifiers.
     The property is represented as a list of @(see runs)
     whose values are lists of types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum identifier-type
  :short "Fixtype of the values of the @('Identifier_Type') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "The twelve types, in the order of [UTS #39, Table 1], are:")
   (xdoc::ul
    (xdoc::li "@('Not_Character'):
               an unassigned code point, a private-use code point,
               a surrogate, or a control code that is not white space.")
    (xdoc::li "@('Deprecated'):
               a character with the @('Deprecated') property.")
    (xdoc::li "@('Default_Ignorable'):
               a character with the
               @('Default_Ignorable_Code_Point') property.")
    (xdoc::li "@('Not_NFKC'):
               a character that Normalization Form KC (NFKC),
               which is compatibility decomposition
               followed by canonical composition, changes.")
    (xdoc::li "@('Not_XID'):
               a character that does not have the @('XID_Continue')
               property, where @('ID') is short for `identifier'.")
    (xdoc::li "@('Exclusion'):
               a character of a script that is not in modern use.")
    (xdoc::li "@('Obsolete'):
               a character that is no longer in modern use.")
    (xdoc::li "@('Technical'):
               a character of specialized use, such as phonetic notation.")
    (xdoc::li "@('Uncommon_Use'):
               a character that is not in common use.")
    (xdoc::li "@('Limited_Use'):
               a character of a script in limited use.")
    (xdoc::li "@('Inclusion'):
               a character that is allowed in identifiers
               although it is not a letter or a digit,
               such as the hyphen.")
    (xdoc::li "@('Recommended'):
               a character in widespread modern use."))
   (xdoc::p
    "The last two are the types of the characters
     that are allowed in identifiers;
     the other ten are reasons for a restriction:
     see @(tsee identifier-type-allowed-p)."))
  (:not-character ())
  (:deprecated ())
  (:default-ignorable ())
  (:not-nfkc ())
  (:not-xid ())
  (:exclusion ())
  (:obsolete ())
  (:technical ())
  (:uncommon-use ())
  (:limited-use ())
  (:inclusion ())
  (:recommended ())
  :pred identifier-type-p)

;;;;;;;;;;;;;;;;;;;;

(define identifier-type-name ((type identifier-type-p))
  :returns (name stringp)
  :short "The name of a value of the @('Identifier_Type') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the name in the file @('IdentifierType.txt')
     of [UTS #39], with underscores between its words."))
  (identifier-type-case type
                        :not-character "Not_Character"
                        :deprecated "Deprecated"
                        :default-ignorable "Default_Ignorable"
                        :not-nfkc "Not_NFKC"
                        :not-xid "Not_XID"
                        :exclusion "Exclusion"
                        :obsolete "Obsolete"
                        :technical "Technical"
                        :uncommon-use "Uncommon_Use"
                        :limited-use "Limited_Use"
                        :inclusion "Inclusion"
                        :recommended "Recommended")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define identifier-type-allowed-p ((type identifier-type-p))
  :returns (yes/no booleanp)
  :short "Check if an identifier type is
          @('Inclusion') or @('Recommended')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the two types that go with
     the @('Identifier_Status') @('Allowed');
     the other ten go with the status @('Restricted')
     [UTS #39, Table 1]."))
  (identifier-type-case type
                        :inclusion t
                        :recommended t
                        :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist identifier-type-list
  :short "Fixtype of lists of identifier types."
  :elt-type identifier-type
  :true-listp t
  :elementp-of-nil nil
  :pred identifier-type-listp)

;;;;;;;;;;;;;;;;;;;;

(define identifier-type-values ()
  :returns (types identifier-type-listp)
  :short "The twelve values of the @('Identifier_Type') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "They are in the order of [UTS #39, Table 1],
     which is the order in @(tsee identifier-type).
     Every value is in the list, once."))
  (list (identifier-type-not-character)
        (identifier-type-deprecated)
        (identifier-type-default-ignorable)
        (identifier-type-not-nfkc)
        (identifier-type-not-xid)
        (identifier-type-exclusion)
        (identifier-type-obsolete)
        (identifier-type-technical)
        (identifier-type-uncommon-use)
        (identifier-type-limited-use)
        (identifier-type-inclusion)
        (identifier-type-recommended))

  ///

  (defrule no-duplicatesp-equal-of-identifier-type-values
    (no-duplicatesp-equal (identifier-type-values)))

  (defrule member-equal-of-identifier-type-fix-and-values
    (member-equal (identifier-type-fix type) (identifier-type-values))
    :use (:instance identifier-type-kind-possibilities (x type))
    :disable (identifier-type-values
              identifier-type-kind-possibilities))

  (defrulel identifier-type-p-when-member-equal-of-values
    (implies (member-equal type (identifier-type-values))
             (identifier-type-p type))
    :enable member-equal)

  (in-theory (disable (:e identifier-type-values)))

  (defrule member-equal-of-identifier-type-values
    (iff (member-equal type (identifier-type-values))
         (identifier-type-p type))
    :disable (identifier-type-values
              member-equal-of-identifier-type-fix-and-values)
    :use member-equal-of-identifier-type-fix-and-values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruns identifier-type
  :property "Identifier_Type"
  :value-type identifier-type-list
  :value-pred identifier-type-listp
  :value-fix identifier-type-list-fix
  :default (list (identifier-type-not-character))
  :elements t
  :element-pred identifier-type-p
  :element-fix identifier-type-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection identifier-type-run-table
  :short "Write a list of runs of @('Identifier_Type') compactly."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each run is written
     as the minimum code point, the maximum code point,
     and the names of the types of the set, as strings
     (see @(tsee identifier-type-name)):")
   (xdoc::codeblock
    "(identifier-type-run-table"
    " (#x0041 #x005A \"Recommended\")"
    " (#x1D00 #x1D2B \"Technical\" \"Obsolete\"))")
   (xdoc::p
    "See @(see run-tables) for what this expands to."))

  (defconst *identifier-type-constructors*
    '(("Not_Character" . identifier-type-not-character)
      ("Deprecated" . identifier-type-deprecated)
      ("Default_Ignorable" . identifier-type-default-ignorable)
      ("Not_NFKC" . identifier-type-not-nfkc)
      ("Not_XID" . identifier-type-not-xid)
      ("Exclusion" . identifier-type-exclusion)
      ("Obsolete" . identifier-type-obsolete)
      ("Technical" . identifier-type-technical)
      ("Uncommon_Use" . identifier-type-uncommon-use)
      ("Limited_Use" . identifier-type-limited-use)
      ("Inclusion" . identifier-type-inclusion)
      ("Recommended" . identifier-type-recommended)))

  (defmacro identifier-type-run-table (&rest entries)
    `(list ,@(run-table-forms entries
                              :elements
                              *identifier-type-constructors*
                              'identifier-type-run
                              'identifier-type-run-table))))
