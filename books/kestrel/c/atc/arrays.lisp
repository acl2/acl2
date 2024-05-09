; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/array-operations")

(include-book "types")

(include-book "symbolic-execution-rules/integers")

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-arrays
  :parents (shallow-embedding)
  :short "A model of shallowly embedded C arrays for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We represent arrays as
     sequences of values that can be read and written.
     These array representations can be passed around, and manipulated by,
     ACL2 functions that represent C functions,
     and ATC translates those to corresponding array manipulations.")
   (xdoc::p
    "We represent arrays as values of fixtypes that wrap lists of C values.
     We provide operations to read and write elements,
     essentially wrappers of @(tsee nth) and @(tsee update-nth).")
   (xdoc::p
    "Besides the list of C values,
     each array fixtype includes the type of the element.
     This is redundant information,
     but it is needed so that arrays thus modeled
     are a subset of the values in the C deep embedding.")
   (xdoc::p
    "This fairly simple model should suffice to generate C code
     that manipulates arrays in some interesting ways.
     The model should suffice to represent C functions
     that receive arrays from external callers,
     and possibly update them.
     However, we may need to extend the model in the future;
     in particular, we may provide operations to create arrays.")
   (xdoc::p
    "This array model is similar to "
    (xdoc::seetopic "java::atj-java-primitive-array-model"
                    "ATJ's model of Java primitive arrays")
    ". But C arrays differ from Java arrays:
     in particular, Java arrays are self-contained objects,
     whose length and other attributes can be programmatically queried;
     in contrast, C arrays are a ``view'' of certain memory regions.
     Nonetheless, at the level of ACL2 manipulations,
     the two kinds of arrays differ less (at least for certain mundane uses),
     because, even though C does not provide ``direct access'' to
     an array's length and other attributes,
     there is nonetheless an implicit notion of array,
     with its length and other attributes,
     that is conceptually created and passed around and manipulated.")
   (xdoc::p
    "Similarly to the use of the Java array model in ATJ,
     the C arrays modeled here have to be treated in a stobj-like manner
     by the ACL2 functions to be translated to C by ATC.
     In general, each of these ACL2 functions
     takes zero or more arrays as inputs (possibly among other inputs),
     and must return, in an @(tsee mv),
     all the arrays that it possibly modifies,
     along with the regular return result of the function (if any);
     the arrays that are only read by the function do not have to be returned.
     Inside the function, the arrays must be updated (if at all)
     in a single-threaded way, analogously to stobjs.
     ATC ensures that this discipline is followed, analogously to ATJ.")
   (xdoc::p
    "Our model of arrays assumes that different arrays do not overlap.
     That is,
     either two arrays are the same array (when they have the same pointer),
     or they are completely disjoint.
     The model does not capture
     the situation of an array being a subarray of another one.
     We may extend the model in the future.")
   (xdoc::p
    "We provide a model of arrays of all the integer types
     supported in ATC's model of C,
     i.e. arrays of @('unsigned chars')s, arrays of @('int')s, etc.
     [C:6.5.2.1/2] explains that array indexing @('a[i]') boils down to
     addition between the pointer @('a') and the integer @('i'),
     and [C:6.5.6/2] allows the integer to have any integer type.
     This means that, for each possible array type,
     any integer type is allowed as index.
     We define operations that take indices of type @(tsee cinteger),
     one operation per element array type;
     note that the type of the index does not affect the result,
     so having operations that take indices of all C integer types
     does not require a weakening or complication of the return types.
     We also have operations that take specific integer types as indices;
     these will be removed, using instead the aforementioned ones
     that take indices of any C integer types.
     We also have operations that take ACL2 integers as indices,
     in terms of which the ones that take specific integer types are defined;
     the ones that take ACL2 integers will be also removed.
     Since all these functions follow a common pattern,
     we generate array types and functions programmatically,
     as done for the "
    (xdoc::seetopic "representation-of-integers" "integers")
    ".")
   (xdoc::p
    "[C:6.2.5/20] requires arrays to be non-empty,
     i.e. to contain at least one element,
     i.e. to have positive length.
     As noted above, arrays are indexed via integers.
     [C] only provides minimum requirements for the sizes of integer types,
     not maximum requirements:
     other than practical considerations,
     nothing, mathematically, prevents some integer types
     to consists of thousands or millions of bits.
     So our model of arrays requires them to be non-empty
     but puts no maximum limits on their length.")
   (xdoc::p
    "For each integer type @('<type>'),
     besides the fixtype of arrays of that type,
     we generate functions
     @('<type>-array-read') and @('<type>-array-write')
     that take C integers as indices.
     We also generate convenience functions
     to test whether indices are in range
     and to return the length of the arrays:
     these do not represent C constructs,
     but are useful in guards for example."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate the model of arrays of an integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate the fixtype
     and the operatiosn that take indices of any C integer types.
     Note that indices are 0-based.
     We also generate the function that returns the length of an array,
     as an ACL2 integer.")
   (xdoc::p
    "We also generate theorems @('...-alt-def') that provide
     alternative definitions for the functions related to arrays.
     We plan to reformulate the definition of these shallowly embedded arrays
     to be like the aforementioned @('...-alt-def') theorems,
     in which case the theorems will be of course eliminated.
     We use the @('...-alt-def') theorems in certain proofs."))

  (b* ((type-string (integer-type-xdoc-string type))
       (<type> (integer-type-to-fixtype type))
       (<type>p (pack <type> 'p))
       (<type>-fix (pack <type> '-fix))
       (<type>-from-integer (pack <type> '-from-integer))
       (<type>-list (pack <type> '-list))
       (<type>-listp (pack <type> '-listp))
       (<type>-array (pack <type> '-array))
       (<type>-arrayp (pack <type>-array 'p))
       (<type>-arrayp-alt-def (pack <type>-arrayp '-alt-def))
       (<type>-array-of (pack <type>-array '-of))
       (<type>-array-of-alt-def (pack <type>-array-of '-alt-def))
       (<type>-array-fix (pack <type>-array '-fix))
       (<type>-array->elemtype (pack <type>-array '->elemtype))
       (<type>-array->elements (pack <type>-array '->elements))
       (<type>-array->elements-alt-def (pack <type>-array->elements '-alt-def))
       (<type>-array-length (pack <type>-array '-length))
       (<type>-array-length-alt-def (pack <type>-array-length '-alt-def))
       (<type>-array-integer-index-okp (pack <type> '-array-integer-index-okp))
       (<type>-array-integer-read (pack <type>-array '-integer-read))
       (<type>-array-integer-read-alt-def (pack <type>-array-integer-read
                                                '-alt-def))
       (<type>-array-integer-write (pack <type>-array '-integer-write))
       (<type>-array-integer-write-alt-def (pack <type>-array-integer-write
                                                 '-alt-def))
       (<type>-array-index-okp (pack <type> '-array-index-okp))
       (<type>-array-read (pack <type>-array '-read))
       (<type>-array-read-alt-def (pack <type>-array '-read-alt-def))
       (<type>-array-write (pack <type>-array '-write))
       (<type>-array-write-alt-def (pack <type>-array '-write-alt-def))
       (<type>-array-of-of-<type>-array->elements
        (pack <type>-array-of '-of- <type>-array->elements))
       (len-of-<type>-array->elements-of-<type>-array-integer-write
        (pack 'len-of- <type>-array->elements '-of- <type>-array-integer-write))
       (len-of-<type>-array->elements-of-<type>-array-write
        (pack 'len-of- <type>-array->elements '-of- <type>-array-write))
       (<type>-array-length-of-<type>-array-integer-write
        (pack <type> '-array-length-of- <type>-array-integer-write))
       (<type>-array-length-of-<type>-array-write
        (pack <type> '-array-length-of- <type>-array-write))
       (type-of-value-when-<type>p (pack 'type-of-value-when- <type>p))
       (<type>-array-write-to-integer-write
        (pack <type>-array-write '-to-integer-write))
       (value-listp-when-<type>-listp (pack 'value-listp-when- <type>-listp))
       (valuep-when-<type>p (pack 'valuep-when- <type>p)))

    `(progn

       ,@(and (type-case type :char)
              (raise "Type ~x0 not supported." type))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defprod ,<type>-array
         :short ,(str::cat "Fixtype of (ATC's model of) arrays of "
                           type-string
                           ".")
         ((elemtype type :reqfix (if (type-case elemtype ,(type-kind type))
                                     elemtype
                                   ,(type-to-maker type)))
          (elements ,<type>-list :reqfix (if (consp elements)
                                             elements
                                           (list (,<type>-from-integer 0)))))
         :require (and (type-case elemtype ,(type-kind type))
                       (consp elements))
         :layout :list
         :tag :array
         :pred ,<type>-arrayp)

       (defsection ,(pack <type>-array '-ext)
         :extension ,<type>-array

         (defruled ,<type>-arrayp-alt-def
           (equal (,<type>-arrayp x)
                  (and (valuep x)
                       (value-case x :array)
                       (equal (value-array->elemtype x)
                              ,(type-to-maker type))
                       (,<type>-listp (value-array->elements x))))
           :enable (,<type>-arrayp
                    valuep
                    value-kind
                    value-array->elemtype
                    value-array->elements))

         (defruled ,<type>-array->elements-alt-def
           (implies (,<type>-arrayp array)
                    (equal (,<type>-array->elements array)
                           (value-array->elements array)))
           :enable (,<type>-array->elements
                    value-array->elements
                    ,<type>-arrayp
                    valuep
                    value-kind
                    ,value-listp-when-<type>-listp)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-of ((elements ,<type>-listp))
         :guard (consp elements)
         :returns (array ,<type>-arrayp)
         :short ,(str::cat "Build an array of "
                           type-string
                           "from a list of its elements.")
         (,<type>-array ,(type-to-maker type) elements)
         :hooks (:fix)
         ///

         (defrule ,<type>-array-of-of-<type>-array->elements
           (equal (,<type>-array-of (,<type>-array->elements array))
                  (,<type>-array-fix array))
           :enable ,<type>-array->elemtype)

         (defruled ,<type>-array-of-alt-def
           (implies (and (,<type>-listp elems)
                         (consp elems))
                    (equal (,<type>-array-of elems)
                           (make-value-array :elemtype ,(type-to-maker type)
                                             :elements elems)))
           :enable (,<type>-array-of
                    ,<type>-array
                    value-array->elemtype
                    value-array->elements
                    valuep
                    value-kind)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-length ((array ,<type>-arrayp))
         :returns (length posp
                          :rule-classes (:rewrite :type-prescription)
                          :hints (("Goal" :in-theory (enable posp))))
         :short ,(str::cat "Length of an array of "
                           type-string
                           ".")
         (len (,<type>-array->elements array))
         :hooks (:fix)
         ///

         (more-returns
          (length natp))

         (defruled ,<type>-array-length-alt-def
           (implies (,<type>-arrayp array)
                    (equal (,<type>-array-length array)
                           (value-array->length array)))
           :enable (,<type>-array-length
                    value-array->length
                    ,<type>-array->elements-alt-def)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-integer-index-okp ((array ,<type>-arrayp)
                                                (index integerp))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if an ACL2 integer is
                            a valid index (i.e. in range)
                            for an array of "
                           type-string
                           ".")
         (integer-range-p 0 (,<type>-array-length array) (ifix index))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-index-okp ((array ,<type>-arrayp)
                                        (index cintegerp))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if a C integer is
                            a valid index (i.e. in range)
                            for an array of "
                           type-string
                           ".")
         (integer-range-p 0
                          (,<type>-array-length array)
                          (integer-from-cinteger index))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-integer-read ((array ,<type>-arrayp)
                                           (index integerp))
         :guard (,<type>-array-integer-index-okp array index)
         :returns (element ,<type>p)
         :short ,(str::cat "Read an element from an array of "
                           type-string
                           ", using an ACL2 integer index.")
         (,<type>-fix (nth index (,<type>-array->elements array)))
         :guard-hints (("Goal" :in-theory (enable
                                           ,<type>-array-integer-index-okp
                                           ,<type>-array-length
                                           nfix
                                           ifix
                                           integer-range-p)))
         ///

         (fty::deffixequiv ,<type>-array-integer-read
           :hints (("Goal" :in-theory (enable ifix nth))))

         (defruled ,<type>-array-integer-read-alt-def
           (implies (and (,<type>-arrayp array)
                         (integerp index)
                         (,<type>-array-integer-index-okp array index))
                    (equal (,<type>-array-integer-read array index)
                           (value-array-read index array)))
           :enable (,<type>-array-integer-read
                    value-array-read
                    ,<type>-array->elements-alt-def
                    ,<type>-array-integer-index-okp
                    ,<type>-array-length-alt-def
                    value-array->length
                    ,<type>-arrayp-alt-def
                    nfix
                    ifix
                    integer-range-p)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-read ((array ,<type>-arrayp)
                                   (index cintegerp))
         :guard (,<type>-array-index-okp array index)
         :returns (element ,<type>p)
         :short ,(str::cat "Read an element from an array of "
                           type-string
                           ", using a C integer index.")
         (,<type>-fix (nth (integer-from-cinteger index)
                           (,<type>-array->elements array)))
         :guard-hints (("Goal" :in-theory (enable
                                           ,<type>-array-index-okp
                                           ,<type>-array-length
                                           integer-range-p)))
         :hooks (:fix)
         ///

         (defruled ,<type>-array-read-alt-def
           (implies (and (,<type>-arrayp array)
                         (cintegerp index)
                         (,<type>-array-index-okp array index))
                    (equal (,<type>-array-read array index)
                           (value-array-read (integer-from-cinteger index)
                                             array)))
           :enable (,<type>-array-read
                    value-array-read
                    ,<type>-array->elements-alt-def
                    ,<type>-array-index-okp
                    ,<type>-array-length-alt-def
                    value-array->length
                    ,<type>-arrayp-alt-def
                    integer-range-p)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-integer-write ((array ,<type>-arrayp)
                                            (index integerp)
                                            (element ,<type>p))
         :guard (,<type>-array-integer-index-okp array index)
         :returns (new-array ,<type>-arrayp)
         :short ,(str::cat "Write an element to an array of "
                           type-string
                           ", using an ACL2 integer index.")
         (b* ((array (,<type>-array-fix array))
              (index (ifix index))
              (element (,<type>-fix element)))
           (if (mbt (,<type>-array-integer-index-okp array index))
               (,<type>-array-of (update-nth index
                                             element
                                             (,<type>-array->elements array)))
             array))
         :guard-hints (("Goal" :in-theory (enable
                                           ,<type>-array-integer-index-okp
                                           ,<type>-array-length
                                           nfix
                                           integer-range-p)))
         :hooks (:fix)

         ///

         (defrule ,len-of-<type>-array->elements-of-<type>-array-integer-write
           (equal (len (,<type>-array->elements
                        (,<type>-array-integer-write array index element)))
                  (len (,<type>-array->elements array)))
           :enable (,<type>-array-integer-index-okp
                    ,<type>-array-length
                    ,<type>-array-of
                    nfix
                    ifix
                    integer-range-p
                    max))

         (defrule ,<type>-array-length-of-<type>-array-integer-write
           (equal (,<type>-array-length
                   (,<type>-array-integer-write array index element))
                  (,<type>-array-length array))
           :enable (,<type>-array-integer-index-okp
                    ,<type>-array-length
                    ,<type>-array-of
                    nfix
                    ifix
                    integer-range-p
                    max))

         (defruled ,<type>-array-integer-write-alt-def
           (implies (and (,<type>-arrayp array)
                         (integerp index)
                         (,<type>p elem)
                         (,<type>-array-integer-index-okp array index))
                    (equal (,<type>-array-integer-write array index elem)
                           (value-array-write index elem array)))
           :enable (,<type>-array-integer-write
                    value-array-write
                    ,<type>-arrayp-alt-def
                    ,<type>-array-of-alt-def
                    ,<type>-array-length-alt-def
                    ,<type>-array->elements-alt-def
                    ,<type>-array-integer-index-okp
                    value-array->length
                    ,type-of-value-when-<type>p
                    remove-flexible-array-member
                    flexible-array-member-p
                    nfix
                    ifix
                    integer-range-p
                    ,valuep-when-<type>p)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-write ((array ,<type>-arrayp)
                                    (index cintegerp)
                                    (element ,<type>p))
         :guard (,<type>-array-index-okp array index)
         :returns (new-array ,<type>-arrayp)
         :short ,(str::cat "Write an element to an array of "
                           type-string
                           ", using a c integer index.")
         (if (mbt (,<type>-array-index-okp array index))
             (,<type>-array-of (update-nth (integer-from-cinteger index)
                                           (,<type>-fix element)
                                           (,<type>-array->elements array)))
           (,<type>-array-fix array))
         :guard-hints (("Goal" :in-theory (enable
                                           ,<type>-array-index-okp
                                           ,<type>-array-length
                                           integer-range-p)))
         :hooks (:fix)

         ///

         (defrule ,len-of-<type>-array->elements-of-<type>-array-write
           (equal (len (,<type>-array->elements
                        (,<type>-array-write array index element)))
                  (len (,<type>-array->elements array)))
           :enable (,<type>-array-index-okp
                    ,<type>-array-length
                    ,<type>-array-of
                    integer-range-p
                    max))

         (defrule ,<type>-array-length-of-<type>-array-write
           (equal (,<type>-array-length
                   (,<type>-array-write array index element))
                  (,<type>-array-length array))
           :enable (,<type>-array-index-okp
                    ,<type>-array-length
                    ,<type>-array-of
                    integer-range-p
                    max))

         (defruled ,<type>-array-write-to-integer-write
           (equal (,<type>-array-write array index val)
                  (,<type>-array-integer-write array
                                               (integer-from-cinteger index)
                                               val))
           :enable (,<type>-array-integer-write
                    ,<type>-array-index-okp
                    ,<type>-array-integer-index-okp
                    ifix))

         (defruled ,<type>-array-write-alt-def
           (implies (and (,<type>-arrayp array)
                         (cintegerp index)
                         (,<type>p elem)
                         (,<type>-array-index-okp array index))
                    (equal (,<type>-array-write array index elem)
                           (value-array-write (integer-from-cinteger index)
                                              elem
                                              array)))
           :enable (,<type>-array-write
                    value-array-write
                    ,<type>-arrayp-alt-def
                    ,<type>-array-of-alt-def
                    ,<type>-array-length-alt-def
                    ,<type>-array->elements-alt-def
                    ,<type>-array-index-okp
                    value-array->length
                    ,type-of-value-when-<type>p
                    remove-flexible-array-member
                    flexible-array-member-p
                    integer-range-p
                    ,value-listp-when-<type>-listp
                    ,valuep-when-<type>p)))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

     )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays-loop ((etypes type-listp))
  :guard (type-nonchar-integer-listp etypes)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the model of arrays
          for the given array element types."
  (cond ((endp etypes) nil)
        (t (append (list (atc-def-integer-arrays (car etypes)))
                   (atc-def-integer-arrays-loop (cdr etypes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(progn ,@(atc-def-integer-arrays-loop *nonchar-integer-types*)))
