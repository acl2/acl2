; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integer-operations")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-arrays
  :parents (atc-shallow-embedding)
  :short "A model of C arrays for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "At this time, we represent arrays as
     sequences of values that can be read and written.
     These array representations can be passed around, and manipulated by,
     ACL2 functions that represent C functions,
     and ATC translates those to corresponding array manipulations.")
   (xdoc::p
    "We represent arrays as values of fixtypes that wrap lists of C values.
     We provide operations to read and write elements,
     essentially wrappers of @(tsee nth) and @(tsee update-nth).")
   (xdoc::p
    "This fairly simple model should suffice to generate C code
     that manipulates arrays in some interesting ways.
     It should suffice to represent C functions
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
     in contrast, C arrays are more of a ``view'' of certain memory regions.
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
     by the ACL2 functions to be translated to C.
     In general, each of these ACL2 functions
     takes zero or more arrays as inputs (possibly among other inputs),
     and must return, in an @(tsee mv),
     all the arrays that it possibly modifies,
     along with the regular return result of the function (if any);
     the arrays that are only read by the function do not have to be returned.
     Inside the function, the arrays must be updated (if at all)
     in a single-threaded way, analogously to stobjs.
     Upcoming extensions of ATC will ensure that this discipline is followed,
     analogously to what ATJ does.")
   (xdoc::p
    "Our initial model of arrays assumes that different arrays do not overlap.
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
     there are versions of the read and write operations (which use indices)
     for all the integer types supported in ATC's model of C.
     Since all these functions follow a common pattern,
     we generate arary types and functions programmatically,
     as done for the "
    (xdoc::seetopic "atc-integers" "integers")
    ".")
   (xdoc::p
    "[C:6.2.5/20] requires arrays to be non-empty,
     i.e. to contain at least one element,
     i.e. to have positive length.
     As noted in @(see atc-arrays), arrays are indexed via integers.
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
     that take ACL2 integers as indices;
     these functions do not directly represent C constructs,
     but are useful to make the definition of the ones that do more concise.
     We generate functions
     @('<type>-array-read-<type1>') and @('<type>-array-write-<type1>'),
     which represent C constructs:
     that convert the index to an ACL2 integer
     and then call the two functions above.
     We also generate convenience functions
     to test whether indices are in range
     and to return the length of the arrays:
     these do not represent C constructs,
     but are useful in guards for example."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays ((type typep))
  :guard (type-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate the core model of arrays of an integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we generate the fixtype,
     and the internally used functions
     that use ACL2 integers as indices.
     Note that indices are 0-indexed.
     We also generate the function that returns the length of an array,
     as an ACL2 integer."))

  (b* ((type-string (atc-integer-type-string type))
       (<type> (atc-integer-type-fixtype type))
       (<type>p (pack <type> 'p))
       (<type>-fix (pack <type> '-fix))
       (<type>-list (pack <type> '-list))
       (<type>-listp (pack <type>-list 'p))
       (<type>-array (pack <type> '-array))
       (<type>-arrayp (pack <type>-array 'p))
       (<type>-array-fix (pack <type>-array '-fix))
       (<type>-array->elements (pack <type>-array '->elements))
       (<type>-array-length (pack <type>-array '-length))
       (<type>-array-index-okp (pack <type> '-array-index-okp))
       (<type>-array-read (pack <type>-array '-read))
       (<type>-array-write (pack <type>-array '-write))
       (len-of-<type>-array->elements-of-<type>-array-write
        (pack 'len-of- <type>-array->elements '-of- <type>-array-write)))

    `(progn

       ,@(and (type-case type :char)
              (raise "Type ~x0 not supported." type))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defprod ,<type>-array
         :short ,(str::cat "Fixtype of (ATC's model of) arrays of "
                           type-string
                           ".")
         ((elements ,<type>-list :reqfix (if (consp elements)
                                             elements
                                           (list (,<type> 0)))))
         :require (consp elements)
         :pred ,<type>-arrayp)

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-length ((array ,<type>-arrayp))
         :returns (length natp :rule-classes (:rewrite :type-prescription))
         :short ,(str::cat "Length of an array of "
                           type-string
                           ".")
         (len (,<type>-array->elements array))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-index-okp ((array ,<type>-arrayp) (index integerp))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if an integer is
                            a valid index (i.e. in range)
                            for an array of "
                           type-string
                           ".")
         (integer-range-p 0 (len (,<type>-array->elements array)) (ifix index))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-read ((array ,<type>-arrayp) (index integerp))
         :guard (,<type>-array-index-okp array index)
         :returns (element ,<type>p)
         :short ,(str::cat "Read an element from an array of "
                           type-string
                           ", using an integer index.")
         (,<type>-fix (nth index (,<type>-array->elements array)))
         :guard-hints (("Goal" :in-theory (enable ,<type>-array-index-okp)))
         :hooks (:fix)

         :prepwork
         ;; to generate theorems about NTH:
         ((local (include-book "std/lists/nth" :dir :system))
          (local (fty::deflist ,<type>-list
                   :elt-type ,<type>
                   :true-listp t
                   :elementp-of-nil nil
                   :pred ,<type>-listp))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>-array-write ((array ,<type>-arrayp)
                                    (index integerp)
                                    (element ,<type>p))
         :guard (,<type>-array-index-okp array index)
         :returns (new-array ,<type>-arrayp)
         :short ,(str::cat "Write an element to an array of"
                           type-string
                           ", using an integer index.")
         (b* ((array (,<type>-array-fix array))
              (index (ifix index))
              (element (,<type>-fix element)))
           (if (mbt (,<type>-array-index-okp array index))
               (,<type>-array (update-nth index
                                          element
                                          (,<type>-array->elements array)))
             array))
         :guard-hints (("Goal" :in-theory (enable ,<type>-array-index-okp)))
         :hooks (:fix)

         :prepwork
         ;; to generate theorems about UPDATE-NTH:
         ((local (include-book "std/lists/update-nth" :dir :system))
          (local (fty::deflist ,<type>-list
                   :elt-type ,<type>
                   :true-listp t
                   :elementp-of-nil nil
                   :pred ,<type>-listp)))

         ///

         (defrule ,len-of-<type>-array->elements-of-<type>-array-write
           (equal (len (,<type>-array->elements
                        (,<type>-array-write array index element)))
                  (len (,<type>-array->elements array)))
           :enable ,<type>-array-index-okp))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays-indices ((etype typep) (itype typep))
  :guard (and (type-integerp etype)
              (type-integerp itype))
  :returns (event pseudo-event-formp)
  :short "Event to generate the part of the model of arrays of an integer type
          that involves indices of an integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here @('etype') is the type of the array elements,
     while @('itype') is the type of the array indices."))

  (b* ((etype-string (atc-integer-type-string etype))
       (itype-string (atc-integer-type-string itype))
       (<etype> (atc-integer-type-fixtype etype))
       (<itype> (atc-integer-type-fixtype itype))
       (<etype>p (pack <etype> 'p))
       (<itype>p (pack <itype> 'p))
       (<etype>-array (pack <etype> '-array))
       (<etype>-arrayp (pack <etype>-array 'p))
       (<etype>-array->elements (pack <etype>-array '->elements))
       (<etype>-array-index-okp (pack <etype> '-array-index-okp))
       (<etype>-array-read (pack <etype>-array '-read))
       (<etype>-array-write (pack <etype>-array '-write))
       (<itype>-integer-value (pack <itype> '-integer-value))
       (<etype>-array-<itype>-index-okp (pack
                                         <etype> '-array- <itype> '-index-okp))
       (<etype>-array-read-<itype> (pack <etype> '-array-read- <itype>))
       (<etype>-array-write-<itype> (pack <etype> '-array-write- <itype>))
       (len-of-<etype>-array->elements-of-<etype>-array-write-<itype>
        (pack
         'len-of- <etype>-array->elements '-of- <etype>-array-write-<itype>)))

    `(progn

       ,@(and (type-case etype :char)
              (raise "Type ~x0 not supported." etype))

       ,@(and (type-case itype :char)
              (raise "Type ~x0 not supported." itype))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<etype>-array-<itype>-index-okp ((array ,<etype>-arrayp)
                                                 (index ,<itype>p))
         :returns (yes/no booleanp)
         :short ,(str::cat "Check if an index of "
                           itype-string
                           " is valid for an array of type "
                           etype-string
                           ".")
         (,<etype>-array-index-okp array (,<itype>-integer-value index))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<etype>-array-read-<itype> ((array ,<etype>-arrayp)
                                            (index ,<itype>p))
         :guard (,<etype>-array-<itype>-index-okp array index)
         :returns (element ,<etype>p)
         :short ,(str::cat "Read an element from an array of "
                           etype-string
                           ", using an index of "
                           itype-string
                           ".")
         (,<etype>-array-read array (,<itype>-integer-value index))
         :guard-hints (("Goal"
                        :in-theory (enable ,<etype>-array-<itype>-index-okp)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<etype>-array-write-<itype> ((array ,<etype>-arrayp)
                                             (index ,<itype>p)
                                             (element ,<etype>p))
         :guard (,<etype>-array-<itype>-index-okp array index)
         :returns (new-array ,<etype>-arrayp)
         :short ,(str::cat "Write an element to an array of "
                           etype-string
                           ", using an index of "
                           itype-string
                           ".")
         (,<etype>-array-write array (,<itype>-integer-value index) element)
         :guard-hints (("Goal"
                        :in-theory (enable ,<etype>-array-<itype>-index-okp)))
         :hooks (:fix)

         ///

         (defrule ,len-of-<etype>-array->elements-of-<etype>-array-write-<itype>
           (equal
            (len (,<etype>-array->elements
                  (,<etype>-array-write-<itype> array index element)))
            (len (,<etype>-array->elements array)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays-loop-inner ((etype typep) (itypes type-listp))
  :guard (and (type-integerp etype)
              (type-integer-listp itypes))
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the array operations that involve indices,
          for a given array element type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inner loop for generating our model of arrays."))
  (cond ((endp itypes) nil)
        (t (cons (atc-def-integer-arrays-indices etype (car itypes))
                 (atc-def-integer-arrays-loop-inner etype (cdr itypes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-arrays-loop-outer ((etypes type-listp)
                                           (itypes type-listp))
  :guard (and (type-integer-listp etypes)
              (type-integer-listp itypes))
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the model of arrays
          for the given array element types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the outer loop for generating our model of arrays."))
  (cond ((endp etypes) nil)
        (t (append (list (atc-def-integer-arrays (car etypes)))
                   (atc-def-integer-arrays-loop-inner (car etypes) itypes)
                   (atc-def-integer-arrays-loop-outer (cdr etypes) itypes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* ((types (list (type-schar)
                   (type-uchar)
                   (type-sshort)
                   (type-ushort)
                   (type-sint)
                   (type-uint)
                   (type-slong)
                   (type-ulong)
                   (type-sllong)
                   (type-ullong))))
   `(progn ,@(atc-def-integer-arrays-loop-outer types types))))
