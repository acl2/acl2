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

(include-book "integer-ranges")
(include-book "object-designators")
(include-book "types")

(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values
  :parents (language)
  :short "A model of C values."
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

(fty::deftypes values/membervalues
  :short "Fixtypes of values and member values."

  (fty::deftagsum value
    :short "Fixtype of values."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we only support the standard unsigned and signed integer values
       (except @('_Bool') values),
       pointer values with any referenced type,
       arrays of values of any type,
       and structures of member values of any type.
       Note that plain @('char') values are not
       standard unsigned or signed integer values [C:6.2.5/7];
       currently we do not cover plain @('char') values.")
     (xdoc::p
      "Pointers are mentioned in several places in [C],
       but there seems to be no specific place in [C] that defines them.
       Nonetheless, we can get a precise picture from various places.
       [C:6.2.5/20] says that pointer types describe objects
       whose values provide references to entities.
       [C:6.3.2.3] specifies several things about pointers;
       in particular, it talks about null pointers.
       Thus, the picture is the following:
       a pointer is either an object designator or a null pointer
       (see the discussion in @(see object-designators)
       about lower-level addresses vs. higher-level object designators).
       In our defensive dynamic semantics,
       where values are tagged by their types,
       we also include, as part of the pointer,
       the type of its referenced value.")
     (xdoc::p
      "Thus, we define a pointer as consisting of
       an optional object designator and a type.
       The object designator is absent for a null pointer;
       note that [C] does not prescribe 0 to represent a null pointer,
       even though 0 is used in null pointer constants [C:6.3.2.3/3].
       The type is not the pointer type, but the referenced type;
       this way, we avoid having to constrain the type to be a pointer type.")
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
    (:pointer ((designator? objdesign-option)
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

(defresult value "values"
  :enable (errorp
           valuep))

(defsection value-result-theorems
  :extension value-result

  (defrule not-errorp-when-valuep
    (implies (valuep x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable (valuep
             errorp))

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

(defsection value-list-result-theorems
  :extension value-list-result

  (defrule not-errorp-when-value-listp
    (implies (value-listp x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable errorp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult member-value-list "lists of member values")

(defsection member-value-list-result-theorems
  :extension member-value-list-result

  (defruled not-errorp-when-member-value-listp
    (implies (member-value-listp x)
             (not (errorp x)))
    :enable (member-value-listp errorp)))

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

(defsection value-option-result-theorems
  :extension value-option

  (defrule not-errorp-when-value-optionp
    (implies (value-optionp x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable value-optionp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bounds-of-integer-values
  :short "Linear rules about the bounds of the integer values."

  (defrule value-schar->get-bound
    (and (<= (schar-min) (value-schar->get x))
         (<= (value-schar->get x) (schar-max)))
    :rule-classes :linear
    :use schar-integerp-of-value-schar->get
    :disable schar-integerp-of-value-schar->get
    :enable schar-integerp-alt-def)

  (defrule value-uchar->get-bound
    (and (<= 0 (value-uchar->get x))
         (<= (value-uchar->get x) (uchar-max)))
    :rule-classes :linear
    :use uchar-integerp-of-value-uchar->get
    :disable uchar-integerp-of-value-uchar->get
    :enable uchar-integerp-alt-def)

  (defrule value-sshort->get-bound
    (and (<= (sshort-min) (value-sshort->get x))
         (<= (value-sshort->get x) (sshort-max)))
    :rule-classes :linear
    :use sshort-integerp-of-value-sshort->get
    :disable sshort-integerp-of-value-sshort->get
    :enable sshort-integerp-alt-def)

  (defrule value-ushort->get-bound
    (and (<= 0 (value-ushort->get x))
         (<= (value-ushort->get x) (ushort-max)))
    :rule-classes :linear
    :use ushort-integerp-of-value-ushort->get
    :disable ushort-integerp-of-value-ushort->get
    :enable ushort-integerp-alt-def)

  (defrule value-sint->get-bound
    (and (<= (sint-min) (value-sint->get x))
         (<= (value-sint->get x) (sint-max)))
    :rule-classes :linear
    :use sint-integerp-of-value-sint->get
    :disable sint-integerp-of-value-sint->get
    :enable sint-integerp-alt-def)

  (defrule value-uint->get-bound
    (and (<= 0 (value-uint->get x))
         (<= (value-uint->get x) (uint-max)))
    :rule-classes :linear
    :use uint-integerp-of-value-uint->get
    :disable uint-integerp-of-value-uint->get
    :enable uint-integerp-alt-def)

  (defrule value-slong->get-bound
    (and (<= (slong-min) (value-slong->get x))
         (<= (value-slong->get x) (slong-max)))
    :rule-classes :linear
    :use slong-integerp-of-value-slong->get
    :disable slong-integerp-of-value-slong->get
    :enable slong-integerp-alt-def)

  (defrule value-ulong->get-bound
    (and (<= 0 (value-ulong->get x))
         (<= (value-ulong->get x) (ulong-max)))
    :rule-classes :linear
    :use ulong-integerp-of-value-ulong->get
    :disable ulong-integerp-of-value-ulong->get
    :enable ulong-integerp-alt-def)

  (defrule value-sllong->get-bound
    (and (<= (sllong-min) (value-sllong->get x))
         (<= (value-sllong->get x) (sllong-max)))
    :rule-classes :linear
    :use sllong-integerp-of-value-sllong->get
    :disable sllong-integerp-of-value-sllong->get
    :enable sllong-integerp-alt-def)

  (defrule value-ullong->get-bound
    (and (<= 0 (value-ullong->get x))
         (<= (value-ullong->get x) (ullong-max)))
    :rule-classes :linear
    :use ullong-integerp-of-value-ullong->get
    :disable ullong-integerp-of-value-ullong->get
    :enable ullong-integerp-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum init-value
  :short "Fixtype of initializer values."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a notion of values for "
    (xdoc::seetopic "initer" "initializers")
    ". An initializer value has the same structure as an initializer,
     but expressions are replaced with (their) values.")
   (xdoc::p
    "As our model of initializers is extended,
     out model of initializer values will be extended accordingly."))
  (:single ((get value)))
  (:list ((get value-list)))
  :pred init-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-signed-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a signed integer [C:6.2.5/4]."
  (or (value-case val :schar)
      (value-case val :sshort)
      (value-case val :sint)
      (value-case val :slong)
      (value-case val :sllong))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-unsigned-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an unsigned integer [C:6.2.5/6]."
  (or (value-case val :uchar)
      (value-case val :ushort)
      (value-case val :uint)
      (value-case val :ulong)
      (value-case val :ullong))
  :hooks (:fix))

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
      (value-case val :pointer))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-value ((val valuep))
  :returns (type typep)
  :short "Type of a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is straightforward, as values carry type information.
     For an array value, we always return an array type with a size,
     which is the length of the array, which is always positive."))
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
              :array (make-type-array :of val.elemtype
                                      :size (len val.elements))
              :struct (type-struct val.tag))
  :guard-hints (("Goal" :in-theory (enable acl2::pos-optionp)))
  :hooks (:fix)
  :prepwork ((local (include-book "std/lists/len" :dir :system)))
  ///

  (defrule type-kind-of-type-of-value
    (equal (type-kind (type-of-value val))
           (value-kind val)))

  (defrule type-signed-integerp-of-type-of-value
    (equal (type-signed-integerp (type-of-value val))
           (value-signed-integerp val))
    :enable (value-signed-integerp
             type-signed-integerp))

  (defrule type-unsigned-integerp-of-type-of-value
    (equal (type-unsigned-integerp (type-of-value val))
           (value-unsigned-integerp val))
    :enable (value-unsigned-integerp
             type-unsigned-integerp))

  (defrule type-integerp-of-type-of-value
    (equal (type-integerp (type-of-value val))
           (value-integerp val))
    :enable (value-integerp
             value-signed-integerp
             value-unsigned-integerp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp))

  (defrule type-realp-of-type-of-value
    (equal (type-realp (type-of-value val))
           (value-realp val))
    :enable (value-realp
             value-integerp
             value-signed-integerp
             value-unsigned-integerp
             type-realp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp))

  (defrule type-arithmeticp-of-type-of-value
    (equal (type-arithmeticp (type-of-value val))
           (value-arithmeticp val))
    :enable (value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp
             value-unsigned-integerp
             type-arithmeticp
             type-realp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp))

  (defrule type-scalarp-of-type-of-value
    (equal (type-scalarp (type-of-value val))
           (value-scalarp val))
    :enable (value-scalarp
             value-arithmeticp
             value-realp
             value-integerp
             value-signed-integerp
             value-unsigned-integerp
             type-scalarp
             type-arithmeticp
             type-realp
             type-integerp
             type-signed-integerp
             type-unsigned-integerp))

  (defrule type-nonchar-integerp-of-type-of-value
    (equal (type-nonchar-integerp (type-of-value val))
           (value-integerp val))
    :enable (value-integerp
             value-signed-integerp
             value-unsigned-integerp
             type-nonchar-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection type-list-of-value-list (x)
  :guard (value-listp x)
  :returns (types type-listp)
  :short "Lift @(tsee type-of-value) to lists."
  (type-of-value x)
  ///
  (fty::deffixequiv type-list-of-value-list
    :args ((x value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define member-type-of-member-value ((member member-valuep))
  :returns (memtype member-typep)
  :short "Member type of a member value."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @(tsee member-type) is the static counterpart of
     a @(tsee member-value)."))
  (make-member-type :name (member-value->name member)
                    :type (type-of-value (member-value->value member)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection member-types-of-member-values (x)
  :guard (member-value-listp x)
  :returns (memtypes member-type-listp)
  :short "Lift @(tsee member-type-of-member-value) to lists."
  (member-type-of-member-value x)
  ///
  (fty::deffixequiv member-types-of-member-values
    :args ((x member-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-type-of-init-value ((ival init-valuep))
  :returns (itype init-typep)
  :short "Initialization type of an initialization value."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @(tsee init-type) is the static counterpart of
     an @(tsee init-value)."))
  (init-value-case ival
                   :single (init-type-single (type-of-value ival.get))
                   :list (init-type-list (type-list-of-value-list ival.get)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult init-value "initialization values"
  :enable (errorp init-valuep))

(defsection init-value-result-theorems
  :extension init-value-result

  (defrule not-errorp-when-init-valuep
    (implies (init-valuep x)
             (not (errorp x)))
    :rule-classes :tau-system
    :enable (init-valuep
             errorp)))
