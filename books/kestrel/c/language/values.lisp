; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "errors")
(include-book "integer-ranges")
(include-book "object-designators")
(include-book "types")

(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

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

(fty::deftagsum pointer
  :short "Fixtype of pointers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Pointers are mentioned in several places in [C17],
     but there seems to be no specific place in [C17] that defines them.
     Nonetheless, we can get a precise picture from various places.
     [C17:6.2.5/20] says that pointer types describe objects
     whose values provide references to entities.
     [C17:6.3.2.3] specifies several things about pointers;
     in particular, it talks about null pointers.
     Thus, the picture is the following:
     a pointer is either an object designator or a null pointer
     (see the discussion in @(see object-designators)
     about lower-level addresses vs. higher-level object designators).
     However, in our defensive semantics, we also distinguish between
     non-null pointers that designate existing objects
     and non-null pointers that designate non-existing objects:
     the latter arise when such objects disappear,
     e.g. because they are in allocated storage and @('free') is called,
     or because they are in automatic storage
     and their scope or frame that is popped.
     If the object no longer exists in this sense,
     the pointer is dangling.
     A C implementation has no direct information about
     whether a non-null pointer is valid or dangling,
     but our C model, which includes metadata, does.")
   (xdoc::p
    "Thus, we formalize a pointer as being
     either null
     or dangling
     or validly designating an object.
     The term `valid' here is perhaps not ideal,
     because in a sense a null pointer is a perfectly ``valid'' value,
     which may be used in well-written C code,
     so long as it is not deferenced.
     We may find a better term in the future,
     but for now here `valid' should be interpreted as
     `valid for dereferencing'.")
   (xdoc::p
    "The notion of pointer defined here is slighly different from
     the notion of pointer value defined in @(tsee value).
     The latter consists of a pointer as defined here, plus a (referenced) type.
     Nonetheless, the pointer as defined here is the core of a pointer value,
     with the type being additional metadata.
     Thus, when clear from context, sometimes we will call `pointers'
     what are actually pointer values."))
  (:null ())
  (:dangling ())
  (:valid ((get objdesign)))
  :pred pointerp)

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
       standard unsigned or signed integer values [C17:6.2.5/7];
       currently we do not cover plain @('char') values.")
     (xdoc::p
      "As mentioned in @(tsee pointer),
       we define a pointer value as consisting of
       a pointer (as defined there) and a type.
       Note that [C17] does not prescribe 0 to represent a null pointer,
       even though 0 is used in null pointer constants [C17:6.3.2.3/3].
       The type is not the pointer type, but the referenced type;
       this way, we avoid having to constrain the type to be a pointer type.")
     (xdoc::p
      "Array values are modeled as consisting of
       the element type and a non-empty list of values.
       [C17:6.2.5/20] requires arrays to be non-empty.")
     (xdoc::p
      "Arrays are indexed via integers
       [C17] only provides minimum requirements for the sizes of integer types,
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
      "Structures are modeled as consisting of a tag (identifier),
       a non-empty list of member values,
       and a flag saying whether the structure has a flexible array member
       [C17:6.7.2.1/18].
       The tag is the one that identifies the structure type;
       we only model structures with non-anonymous types.
       [C17:6.2.5/20] requires at least one member,
       which we capture with an invariant.
       If the flexible array member flag is set,
       there must be at least two members
       (i.e. one besides the flexible array member),
       and the last member must be an array;
       we do not capture these requirements here, but we may in the future.
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
    (:pointer ((core pointer)
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
                                 (list (member-value-fix :irrelevant))))
              (flexiblep bool))
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
    :measure (two-nats-measure (acl2-count x) 0))

  :prepwork ((local (in-theory (enable nfix)))))

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

;;;;;;;;;;;;;;;;;;;;

(defsection value-result-theorems
  :extension value-result

  (defruled not-errorp-when-valuep
    (implies (valuep x)
             (not (errorp x)))
    :enable (valuep
             errorp))

  (defruled errorp-when-value-resultp-and-not-valuep
    (implies (and (value-resultp x)
                  (not (valuep x)))
             (errorp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult value-list "lists of values")

;;;;;;;;;;;;;;;;;;;;

(defsection value-list-result-theorems
  :extension value-list-result

  (defruled not-errorp-when-value-listp
    (implies (value-listp x)
             (not (errorp x)))
    :enable errorp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult member-value-list "lists of member values")

;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;

(defsection value-option-result-theorems
  :extension value-option

  (defruled not-errorp-when-value-optionp
    (implies (value-optionp x)
             (not (errorp x)))
    :enable value-optionp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod expr-value
  :short "Fixtype of expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "An expression may yield a value or designate an object [C17:6.5/1]
     (unless the expression has @('void') type).
     In our model, we have object designators to designate objects;
     see @(tsee objdesign).
     When an expression designates an object, that object should exist:
     in our defensive dynamic semantics of C,
     we want in fact to ensure that that is the case:
     thus, when we evaluate an expression that designates an object
     (as opposed to an expression that just returns a value),
     in our dynamic semantics we also retrieve the value,
     to ensure that it exists,
     and to ensure that any subsequent operation is type-safe.")
   (xdoc::p
    "Thus, we introduce a notion of expression value
     as the thing returned by evaluating an expression
     in our dynamic semantics.
     An expression value consists of a value
     and an optional object designator:
     an expression that returns just a value in C
     returns an expression value without object designator in our model;
     an expression that designates an object in C
     returns an expression value with an object designator in our model,
     along with the value of the object.
     Having the value, in addition to the object designator,
     makes it convenient to access the value,
     without having to read it from the computation state.")
   (xdoc::p
    "[C17] does not provide a specific term to denote
     something returned by an expression,
     i.e. something that is either a value or an object designator.
     In our model, we formalize that as an expression value,
     which is essentially an extended notion of value
     as it pertains to expressions,
     which includes values proper and object designators."))
  ((value value)
   (object objdesign-option))
  :pred expr-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult expr-value "expression values")

;;;;;;;;;;;;;;;;;;;;

(defsection expr-value-result-theorems
  :extension expr-value-result

  (defruled not-errorp-when-expr-valuep
    (implies (expr-valuep x)
             (not (errorp x)))
    :enable (expr-valuep errorp)))

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

(defsection signed/unsigned-byte-p-of-integer-values
  :short "Theorems saying that the integer values
          satisfy @(tsee signed-byte-p) and @(tsee unsigned-byte-p)."

  (local (in-theory (enable signed-byte-p
                            unsigned-byte-p
                            integer-range-p)))

  (defruled signed-byte-p-of-value-schar->get
    (signed-byte-p (char-bits) (value-schar->get val))
    :enable (schar-min schar-max))

  (defruled signed-byte-p-of-value-sshort->get
    (signed-byte-p (short-bits) (value-sshort->get val))
    :enable (sshort-min sshort-max))

  (defruled signed-byte-p-of-value-sint->get
    (signed-byte-p (int-bits) (value-sint->get val))
    :enable (sint-min sint-max))

  (defruled signed-byte-p-of-value-slong->get
    (signed-byte-p (long-bits) (value-slong->get val))
    :enable (slong-min slong-max))

  (defruled signed-byte-p-of-value-sllong->get
    (signed-byte-p (llong-bits) (value-sllong->get val))
    :enable (sllong-min sllong-max))

  (defruled unsigned-byte-p-of-value-uchar->get
    (unsigned-byte-p (char-bits) (value-uchar->get val))
    :enable (uchar-max))

  (defruled unsigned-byte-p-of-value-ushort->get
    (unsigned-byte-p (short-bits) (value-ushort->get val))
    :enable (ushort-max))

  (defruled unsigned-byte-p-of-value-uint->get
    (unsigned-byte-p (int-bits) (value-uint->get val))
    :enable (uint-max))

  (defruled unsigned-byte-p-of-value-ulong->get
    (unsigned-byte-p (long-bits) (value-ulong->get val))
    :enable (ulong-max))

  (defruled unsigned-byte-p-of-value-ullong->get
    (unsigned-byte-p (llong-bits) (value-ullong->get val))
    :enable (ullong-max)))

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
  :short "Check if a value is a signed integer [C17:6.2.5/4]."
  (or (value-case val :schar)
      (value-case val :sshort)
      (value-case val :sint)
      (value-case val :slong)
      (value-case val :sllong))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-unsigned-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an unsigned integer [C17:6.2.5/6]."
  (or (value-case val :uchar)
      (value-case val :ushort)
      (value-case val :uint)
      (value-case val :ulong)
      (value-case val :ullong))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-integerp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is an integer [C17:6.2.5/17]."
  (or (value-signed-integerp val)
      (value-unsigned-integerp val))
  :hooks (:fix)

  ///

  (defruled value-kind-not-array-when-value-integerp
    (implies (value-integerp val)
             (not (equal (value-kind val) :array)))
    :enable (value-signed-integerp
             value-unsigned-integerp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-realp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a real [C17:6.2.5/18]."
  (value-integerp val)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-arithmeticp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is arithmetic [C17:6.2.5/18]."
  (value-realp val)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-scalarp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is scalar [C17:6.2.5/21]."
  (or (value-arithmeticp val)
      (value-case val :pointer))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-promoted-arithmeticp ((val valuep))
  :returns (yes/no booleanp)
  :short "Check if a value is a promoted arithmetic value."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, an arithmetic value whose type is a "
    (xdoc::seetopic "type-promoted-arithmeticp"
                    "promoted arithmetic type")))
  (and (value-arithmeticp val)
       (not (value-case val :schar))
       (not (value-case val :uchar))
       (not (value-case val :sshort))
       (not (value-case val :ushort)))
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
  :guard-hints (("Goal" :in-theory (enable pos-optionp posp)))
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

  (defrule type-promoted-arithmeticp-of-type-of-value
    (equal (type-promoted-arithmeticp (type-of-value val))
           (value-promoted-arithmeticp val))
    :enable (value-promoted-arithmeticp
             value-arithmeticp
             value-realp
             value-integerp
             value-unsigned-integerp
             value-signed-integerp
             type-promoted-arithmeticp
             type-arithmeticp
             type-realp
             type-integerp
             type-unsigned-integerp
             type-signed-integerp))

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

;;;;;;;;;;;;;;;;;;;;

(defsection init-value-result-theorems
  :extension init-value-result

  (defruled not-errorp-when-init-valuep
    (implies (init-valuep x)
             (not (errorp x)))
    :enable (init-valuep
             errorp)))
