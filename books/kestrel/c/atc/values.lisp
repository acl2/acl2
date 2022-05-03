; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integers")
(include-book "pointers")

(include-book "defthm-disjoint")

(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-values
  :parents (atc-dynamic-semantics)
  :short "A model of C values for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define fixtypes for values and related entities,
     and some basic ACL2 operations on them
     (these are not C operations, which are defined separately;
     they are just ACL2 operations on our model of values)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integer-value-disjoint-rules
  :short "Rules about disjointness of integer values."
  (defthm-disjoint *integer-value-disjoint-rules*
    ucharp
    scharp
    ushortp
    sshortp
    uintp
    sintp
    ulongp
    slongp
    ullongp
    sllongp
    pointerp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes values
  :short "Fixtypes of values."

  (fty::deftagsum value
    :short "Fixtype of values."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we only support the standard unsigned and signed integer values
       (except @('_Bool') values),
       pointer values with any referenced type,
       arrays of values of any type,
       and structures of member values of any type.")
     (xdoc::p
      "Array values are modeled as consisting of
       the element type and a non-empty list of values.
       [C:6.2.5/20] requires arrays to be non-empty.")
     (xdoc::p
      "Arrays are indexed via integers
       [C] only provides minimum requirements for the sizes of integer types,
       not maximum requirements.
       Other than practical considerations,
       nothing, mathematically, prevents some integer types
       to consists of thousands or millions of bits.
       So our model of arrays requires them to be non-empty,
       but puts no maximum limits on their length.")
     (xdoc::p
      "This definition of arrays alone does not prevent arrays
       from having values of different types.
       That all the values have the element type
       can and will be enforced in separate predicates.")
     (xdoc::p
      "Structures are modeled as consisting of a tag (identifier)
       and a non-empty list of member values.
       The tag is the one that identifies the structure type;
       we only model structures with non-anonymous types.
       [C:6.2.5/20] requires at least one member.
       The member values must have distinct names;
       we do not capture this requirement here, but we may in the future.")
     (xdoc::p
      "The requirement that the member values
       match the members of the structure type
       requires contextual information about the structure type.
       So this requirement cannot be captured in this definition of values."))
    (:uchar ((get uchar-integer)))
    (:schar ((get schar-integer)))
    (:ushort ((get ushort-integer)))
    (:sshort ((get sshort-integer)))
    (:uint ((get uint-integer)))
    (:sint ((get sint-integer)))
    (:ulong ((get ulong-integer)))
    (:slong ((get slong-integer)))
    (:ullong ((get ullong-integer)))
    (:sllong ((get sllong-integer)))
    (:pointer ((address? address-option)
               (reftype type)))
    (:array ((elemtype type)
             (elements value-list
                       :reqfix (if (consp elements)
                                   elements
                                 (list (value-fix :irrelevant)))))
     :require (consp elements))
    (:struct ((tag ident)
              (members member-value-list
                       :reqfix (if (consp members)
                                   members
                                 (list (member-value-fix :irrelevant)))))
     :require (consp members))
    :pred valuep
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist value-list
    :short "Fixtype of lists of values."
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::defprod member-value
    :short "Fixtype of member values."
    :long
    (xdoc::topstring
     (xdoc::p
      "A member value consists of a name (identifier) and a value.
       Member values are the constituents of structure values."))
    ((name ident)
     (value value))
    :tag :member-value
    :pred member-valuep
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist member-value-list
    :short "Fixtype of lists of member values."
    :elt-type member-value
    :true-listp t
    :elementp-of-nil nil
    :pred member-value-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection member-value-list->name-list (x)
  :guard (member-value-listp x)
  :returns (names ident-listp)
  :short "Lift @(tsee member-value->name) to lists."
  (member-value->name x)
  ///
  (fty::deffixequiv member-value-list->name-list
    :args ((x member-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection member-value-list->value-list (x)
  :guard (member-value-listp x)
  :returns (values value-listp)
  :short "Lift @(tsee member-value->value) to lists."
  (member-value->value x)
  ///
  (fty::deffixequiv member-value-list->value-list
    :args ((x member-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-theorems
  :extension value

  (defrule valuep-possibilities
    (implies (valuep x)
             (or (ucharp x)
                 (scharp x)
                 (ushortp x)
                 (sshortp x)
                 (uintp x)
                 (sintp x)
                 (ulongp x)
                 (slongp x)
                 (ullongp x)
                 (sllongp x)
                 (pointerp x)
                 (value-case x :array)
                 (value-case x :struct)))
    :enable (valuep
             ucharp
             scharp
             ushortp
             sshortp
             uintp
             sintp
             ulongp
             slongp
             ullongp
             sllongp
             pointerp
             value-kind)
    :rule-classes :forward-chaining)

  (defrule valuep-when-ucharp
    (implies (ucharp x)
             (valuep x))
    :enable (valuep ucharp))

  (defrule valuep-when-scharp
    (implies (scharp x)
             (valuep x))
    :enable (valuep scharp))

  (defrule valuep-when-ushortp
    (implies (ushortp x)
             (valuep x))
    :enable (valuep ushortp))

  (defrule valuep-when-sshortp
    (implies (sshortp x)
             (valuep x))
    :enable (valuep sshortp))

  (defrule valuep-when-uintp
    (implies (uintp x)
             (valuep x))
    :enable (valuep uintp))

  (defrule valuep-when-sintp
    (implies (sintp x)
             (valuep x))
    :enable (valuep sintp))

  (defrule valuep-when-ulongp
    (implies (ulongp x)
             (valuep x))
    :enable (valuep ulongp))

  (defrule valuep-when-slongp
    (implies (slongp x)
             (valuep x))
    :enable (valuep slongp))

  (defrule valuep-when-ullongp
    (implies (ullongp x)
             (valuep x))
    :enable (valuep ullongp))

  (defrule valuep-when-sllongp
    (implies (sllongp x)
             (valuep x))
    :enable (valuep sllongp))

  (defrule valuep-when-pointerp
    (implies (pointerp x)
             (valuep x))
    :enable (valuep pointerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-list-theorems
  :extension value-list

  (defrule value-listp-when-uchar-listp
    (implies (uchar-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-schar-listp
    (implies (schar-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ushort-listp
    (implies (ushort-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sshort-listp
    (implies (sshort-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-uint-listp
    (implies (uint-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sint-listp
    (implies (sint-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ulong-listp
    (implies (ulong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-slong-listp
    (implies (slong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-ullong-listp
    (implies (ullong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp)

  (defrule value-listp-when-sllong-listp
    (implies (sllong-listp x)
             (value-listp x))
    :induct (len x)
    :enable value-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult value "values"
  :enable (errorp
           valuep))

(defsection value-result-theorems
  :extension value-result

  (defruled errorp-when-value-resultp-and-not-valuep
    (implies (and (value-resultp x)
                  (not (valuep x)))
             (errorp x)))

  (defrule value-resultp-possibilities
    (implies (value-resultp x)
             (or (valuep x)
                 (errorp x)))
    :enable value-resultp
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult value-list "lists of values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption value-option
  value
  :short "Fixtype of optional values."
  :pred value-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult value-option "optional values"
  :enable (errorp
           value-optionp
           valuep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult member-value-list "lists of member values")

;;;;;;;;;;;;;;;;;;;;

(defruled not-errorp-when-member-value-listp
  (implies (member-value-listp x)
           (not (errorp x)))
  :enable (member-value-listp errorp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-array->length ((array valuep))
  :guard (value-case array :array)
  :returns (length posp)
  :short "Length of an array."
  (len (value-array->elements array))
  :hooks (:fix)
  :prepwork ((local (include-book "std/lists/len" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-signed-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a signed integer [C:6.2.5/4]."
  (or (value-case val :schar)
      (value-case val :sshort)
      (value-case val :sint)
      (value-case val :slong)
      (value-case val :sllong))
  :hooks (:fix)
  ///

  (defruled value-signed-integerp-alt-def
    (equal (value-signed-integerp val)
           (b* ((val (value-fix val)))
             (or (scharp val)
                 (sshortp val)
                 (sintp val)
                 (slongp val)
                 (sllongp val))))
    :use (:instance lemma (val (value-fix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (valuep val)
                (equal (value-signed-integerp val)
                       (or (scharp val)
                           (sshortp val)
                           (sintp val)
                           (slongp val)
                           (sllongp val))))
       :enable (valuep
                value-kind
                scharp
                sshortp
                sintp
                slongp
                sllongp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-unsigned-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an unsigned integer [C:6.2.5/6]."
  (or (value-case val :uchar)
      (value-case val :ushort)
      (value-case val :uint)
      (value-case val :ulong)
      (value-case val :ullong))
  :hooks (:fix)
  ///

  (defruled value-unsigned-integerp-alt-def
    (equal (value-unsigned-integerp val)
           (b* ((val (value-fix val)))
             (or (ucharp val)
                 (ushortp val)
                 (uintp val)
                 (ulongp val)
                 (ullongp val))))
    :use (:instance lemma (val (value-fix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (valuep val)
                (equal (value-unsigned-integerp val)
                       (or (ucharp val)
                           (ushortp val)
                           (uintp val)
                           (ulongp val)
                           (ullongp val))))
       :enable (valuep
                value-kind
                ucharp
                ushortp
                uintp
                ulongp
                ullongp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an integer [C:6.2.5/17]."
  (or (value-signed-integerp val)
      (value-unsigned-integerp val))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-realp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a real [C:6.2.5/18]."
  (value-integerp val)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-arithmeticp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is arithmetic [C:6.2.5/18]."
  (value-realp val)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-scalarp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is scalar [C:6.2.5/21]."
  (or (value-arithmeticp val)
      (pointerp (value-fix val)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-tau-rules
  :short "Some tau rules about values."

  (defrule signed-integer-value-kinds
    (implies (or (scharp x)
                 (sshortp x)
                 (sintp x)
                 (slongp x)
                 (sllongp x))
             (and (value-scalarp x)
                  (value-arithmeticp x)
                  (value-realp x)
                  (value-integerp x)
                  (value-signed-integerp x)))
    :rule-classes :tau-system
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp-alt-def))

  (defrule unsigned-integer-value-kinds
    (implies (or (ucharp x)
                 (ushortp x)
                 (uintp x)
                 (ulongp x)
                 (ullongp x))
             (and (value-scalarp x)
                  (value-arithmeticp x)
                  (value-realp x)
                  (value-integerp x)
                  (value-unsigned-integerp x)))
    :rule-classes :tau-system
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-unsigned-integerp-alt-def))

  (defrule not-errorp-when-valuep
    (implies (valuep x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable (valuep
             errorp))

  (defrule not-errorp-when-value-listp
    (implies (value-listp x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable errorp)

  (defrule not-errorp-when-value-optionp
    (implies (value-optionp x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable value-optionp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-value ((val valuep))
  :returns (type typep)
  :short "Type of a value."
  (value-case val
              :uchar (type-uchar)
              :schar (type-schar)
              :ushort (type-ushort)
              :sshort (type-sshort)
              :uint (type-uint)
              :sint (type-sint)
              :ulong (type-ulong)
              :slong (type-slong)
              :ullong (type-ullong)
              :sllong (type-sllong)
              :pointer (type-pointer val.reftype)
              :array (type-array val.elemtype)
              :struct (type-struct val.tag))
  :hooks (:fix)
  ///

  (defruled type-of-value-alt-def
    (equal (type-of-value val)
           (b* ((val (value-fix val)))
             (cond ((ucharp val) (type-uchar))
                   ((scharp val) (type-schar))
                   ((ushortp val) (type-ushort))
                   ((sshortp val) (type-sshort))
                   ((uintp val) (type-uint))
                   ((sintp val) (type-sint))
                   ((ulongp val) (type-ulong))
                   ((slongp val) (type-slong))
                   ((ullongp val) (type-ullong))
                   ((sllongp val) (type-sllong))
                   ((pointerp val) (type-pointer (pointer->reftype val)))
                   ((value-case val :array) (type-array
                                             (value-array->elemtype val)))
                   ((value-case val :struct) (type-struct
                                              (value-struct->tag val)))
                   (t (prog2$ (impossible) (irr-type))))))
    :use (:instance lemma (val (value-fix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (valuep val)
                (equal (type-of-value val)
                       (cond ((ucharp val) (type-uchar))
                             ((scharp val) (type-schar))
                             ((ushortp val) (type-ushort))
                             ((sshortp val) (type-sshort))
                             ((uintp val) (type-uint))
                             ((sintp val) (type-sint))
                             ((ulongp val) (type-ulong))
                             ((slongp val) (type-slong))
                             ((ullongp val) (type-ullong))
                             ((sllongp val) (type-sllong))
                             ((pointerp val)
                              (type-pointer (pointer->reftype val)))
                             ((value-case val :array)
                              (type-array (value-array->elemtype val)))
                             ((value-case val :struct)
                              (type-struct (value-struct->tag val)))
                             (t (prog2$ (impossible) (irr-type))))))
       :enable (type-of-value
                value-kind
                value-fix
                valuep
                ucharp
                scharp
                ushortp
                sshortp
                uintp
                sintp
                ulongp
                slongp
                ullongp
                sllongp
                pointerp
                pointer->reftype
                value-pointer->reftype
                value-array->elemtype))))

  (local (in-theory (e/d (type-of-value-alt-def) (type-of-value))))

  (defruled type-signed-integerp-of-type-of-signed-integer-value
    (implies (value-signed-integerp val)
             (type-signed-integerp (type-of-value val)))
    :enable value-signed-integerp-alt-def)

  (defruled type-unsigned-integerp-of-type-of-unsigned-integer-value
    (implies (value-unsigned-integerp val)
             (type-unsigned-integerp (type-of-value val)))
    :enable value-unsigned-integerp-alt-def)

  (defruled type-integerp-of-type-of-integer-value
    (implies (value-integerp val)
             (type-integerp (type-of-value val)))
    :enable (value-integerp
             value-signed-integerp-alt-def
             value-unsigned-integerp-alt-def))

  (defruled type-realp-of-type-of-real-value
    (implies (value-realp val)
             (type-realp (type-of-value val)))
    :enable (value-realp
             value-integerp
             value-signed-integerp-alt-def
             value-unsigned-integerp-alt-def))

  (defruled type-arithmeticp-of-type-of-arithmetic-value
    (implies (value-arithmeticp val)
             (type-arithmeticp (type-of-value val)))
    :enable (value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp-alt-def
             value-unsigned-integerp-alt-def))

  (defruled type-scalarp-of-type-of-scalar-value
    (implies (value-scalarp val)
             (type-scalarp (type-of-value val)))
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp-alt-def
             value-unsigned-integerp-alt-def
             type-scalarp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-value-option ((val? value-optionp))
  :returns (type typep)
  :short "Type of an optional value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the value if the value is present,
     while it is @('void') if the value is absent.
     This is a handy extension of @(tsee type-of-value),
     given that, in the dynamic semantics,
     we model computations that may return @('void') (e.g. function calls)
     as returning optional values, with @('nil') for no value."))
  (value-option-case val?
                     :some (type-of-value val?.val)
                     :none (type-void))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-list-of-value-list (x)
  :guard (value-listp x)
  :returns (types type-listp)
  :short "Lift @(tsee type-of-value) to lists."
  (type-of-value x)
  ///
  (fty::deffixequiv type-list-of-value-list
    :args ((x value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-predicates-to-type-of-value-equalities
  :short "Rules that rewrite predicates for values
          to equalities of the types of the values."

  (local (in-theory (enable type-of-value-alt-def)))

  (defruled ucharp-to-type-of-value
    (implies (valuep x)
             (equal (ucharp x)
                    (equal (type-of-value x)
                           (type-uchar)))))

  (defruled scharp-to-type-of-value
    (implies (valuep x)
             (equal (scharp x)
                    (equal (type-of-value x)
                           (type-schar)))))

  (defruled ushortp-to-type-of-value
    (implies (valuep x)
             (equal (ushortp x)
                    (equal (type-of-value x)
                           (type-ushort)))))

  (defruled sshortp-to-type-of-value
    (implies (valuep x)
             (equal (sshortp x)
                    (equal (type-of-value x)
                           (type-sshort)))))

  (defruled uintp-to-type-of-value
    (implies (valuep x)
             (equal (uintp x)
                    (equal (type-of-value x)
                           (type-uint)))))

  (defruled sintp-to-type-of-value
    (implies (valuep x)
             (equal (sintp x)
                    (equal (type-of-value x)
                           (type-sint)))))

  (defruled ulongp-to-type-of-value
    (implies (valuep x)
             (equal (ulongp x)
                    (equal (type-of-value x)
                           (type-ulong)))))

  (defruled slongp-to-type-of-value
    (implies (valuep x)
             (equal (slongp x)
                    (equal (type-of-value x)
                           (type-slong)))))

  (defruled ullongp-to-type-of-value
    (implies (valuep x)
             (equal (ullongp x)
                    (equal (type-of-value x)
                           (type-ullong)))))

  (defruled sllongp-to-type-of-value
    (implies (valuep x)
             (equal (sllongp x)
                    (equal (type-of-value x)
                           (type-sllong)))))

  (defruled pointerp-to-type-of-value
    (implies (valuep x)
             (equal (pointerp x)
                    (equal (type-of-value x)
                           (type-pointer (pointer->reftype x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection value-predicates-to-type-of-value-forward
  :short "Forward-chaining rules from predicates for values
          to equalities of the types of the values."

  (local (in-theory (enable type-of-value-alt-def)))

  (defruled type-of-value-when-ucharp-forward
    (implies (ucharp x)
             (equal (type-of-value x)
                    (type-uchar))))

  (defruled type-of-value-when-scharp-forward
    (implies (scharp x)
             (equal (type-of-value x)
                    (type-schar))))

  (defruled type-of-value-when-ushortp-forward
    (implies (ushortp x)
             (equal (type-of-value x)
                    (type-ushort))))

  (defruled type-of-value-when-sshortp-forward
    (implies (sshortp x)
             (equal (type-of-value x)
                    (type-sshort))))

  (defruled type-of-value-when-uintp-forward
    (implies (uintp x)
             (equal (type-of-value x)
                    (type-uint))))

  (defruled type-of-value-when-sintp-forward
    (implies (sintp x)
             (equal (type-of-value x)
                    (type-sint))))

  (defruled type-of-value-when-ulongp-forward
    (implies (ulongp x)
             (equal (type-of-value x)
                    (type-ulong))))

  (defruled type-of-value-when-slongp-forward
    (implies (slongp x)
             (equal (type-of-value x)
                    (type-slong))))

  (defruled type-of-value-when-ullongp-forward
    (implies (ullongp x)
             (equal (type-of-value x)
                    (type-ullong))))

  (defruled type-of-value-when-sllongp-forward
    (implies (sllongp x)
             (equal (type-of-value x)
                    (type-sllong)))))
