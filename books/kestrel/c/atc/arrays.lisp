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

(include-book "integers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-arrays
  :parents (atc-dynamic-semantics)
  :short "A model of C arrays for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "At this time, we plan to represent arrays as sequences of values
     that can read and written.
     These array representations can be passed around, and manipulated by,
     ACL2 functions that represent C functions,
     and ATC will translate those to corresponding array manipulations.")
   (xdoc::p
    "We represent arrays as values of fixtypes that wrap lists of C values.
     We provide operations to read and write elements,
     essentially wrappers of @(tsee nth) and @(tsee update-nth).")
   (xdoc::p
    "Initially we are providing a model of arrays of @('unsigned char')s,
     which are very common (at least in our envisioned initial use cases).
     We will provide models of arrays of other types, as needed.")
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
    ". C arrays differ from Java arrays:
     in particular, Java arrays are self-contained objects,
     whose length and other attributes can be programmatically queried;
     in contrast, C arrays are more of a ``view'' of certain memory regions.
     Nonetheless, at the level of ACL2 manipulations,
     the two kinds of array differ less (at least for certain mundane uses),
     because, even though C does not provide ``direct access'' to
     an array's length and other attributes,
     there is nonetheless an implicit notion of array,
     with its length and other attributes,
     that is conceptually created and passed around and manipulated.")
   (xdoc::p
    "Similarly to the use of the Java array model in ATJ,
     the C arrays modeled here will have to be treated in a stobj-like manner
     by the ACL2 functions to be translated to C.
     In general, each of these ACL2 functions
     will take zero or more arrays as inputs (possibly among other inputs),
     and will have to return, in an @(tsee mv),
     all the arrays that it possibly modifies,
     along with the regular return result of the function;
     the arrays that are only read by the function
     do not have to be returned.
     Inside the function, the arrays must be udpated (if at all)
     in a single-threaded way, analogously to stobjs.
     Upcoming extensions of ATC will ensure that this discipline is followed,
     analogously to what ATJ does."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod uchar-array
  :short "Fixtype of (ATC's model of) C @('unsigned char') arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C:6.2.5/20] requires arrays to be non-empty,
     i.e. to contain at least one element,
     i.e. to have positive length.")
   (xdoc::p
    "[C] does not appear to impose any upper limit on the length of an array.
     [C:6.5.2.1/2] explains that array indexing @('a[i]') boils down to
     addition between the pointer @('a') and the integer @('i'),
     and [C:6.5.6/2] allows the integer to have any integer type.
     Integer types consist of not just @('int'),
     but also the standard ones (e.g. @('unsigned short'))
     and the extended ones
     [C:6.2.5/4-7].
     [C] only provides minimum requirements for the sizes of integer types,
     not maximum requirements:
     other than practical considerations,
     mathematically nothing prevents some integer types
     to consists of thousands of millions of bits.")
   (xdoc::p
    "Because of all of the above,
     our model of C arrays puts no length constraints on arrays.
     (This is in contrast with Java,
     where arrays have a bounded length and may be also empty.)
     We model arrays as (wrappers of) lists of arbitrary positive length.")
   (xdoc::p
    "This is sufficient to represent all the actual arrays of interest, clearly.
     If one uses an @('int') to access an array
     whose length exceeds the maximum value of @('int'),
     that simply means that the access can only apply to part of the array.")
   (xdoc::p
    "So this fixtype is just a wrapper of lists,
     with a non-emptiness requirement.
     The wrapper provides better abstraction,
     and facilitates changes."))
  ((elements uchar-list :reqfix (if (consp elements)
                                    elements
                                  (list (uchar 0)))))
  :require (consp elements)
  :pred uchar-arrayp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-array-sint-index-okp ((array uchar-arrayp) (index sintp))
  :returns (yes/no booleanp)
  :short "Check if a C @('int') is a valid index (i.e. in range)
          for a C @('unsigned char') array."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used as guard for array read and write operations
     that use @('int')s as indices.")
   (xdoc::p
    "Since arrays are zero-indexed in C,
     the index is valid if it is non-negative and below the length."))
  (integer-range-p 0 (len (uchar-array->elements array)) (sint->get index))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-array-read-sint ((array uchar-arrayp) (index sintp))
  :guard (uchar-array-sint-index-okp array index)
  :returns (element ucharp)
  :short "Read an element in an @('unsigned char') array,
          using an @('int') index."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(tsee uchar-array),
     [C] allows any integer type for array indices.
     Given our strictly typed model of C for ATC,
     we provide separate array read operations
     not only for different array types, but also for different index types.
     We start with this operation for @('int') indices, which are common.
     We may add more as needed."))
  (uchar-fix (nth (sint->get index) (uchar-array->elements array)))
  :guard-hints (("Goal" :in-theory (enable uchar-array-sint-index-okp)))
  :hooks (:fix)

  :prepwork
  ;; to generate theorems about NTH:
  ((local (include-book "std/lists/nth" :dir :system))
   (local (fty::deflist uchar-list
            :elt-type uchar
            :true-listp t
            :elementp-of-nil nil
            :pred uchar-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define uchar-array-write-sint ((array uchar-arrayp)
                                (index sintp)
                                (element ucharp))
  :guard (uchar-array-sint-index-okp array index)
  :returns (new-array uchar-arrayp)
  :short "Write an element in an @('unsigned char') array,
          using an @('int') index."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(tsee uchar-array),
     [C] allows any integer type for array indices.
     Given our strictly typed model of C for ATC,
     we provide separate array write operations
     not only for different array types, but also for different index types.
     We start with this operation for @('int') indices, which are common.
     We may add more as needed."))
  (make-uchar-array :elements (update-nth (sint->get index)
                                          (uchar-fix element)
                                          (uchar-array->elements array)))
  :guard-hints (("Goal" :in-theory (enable uchar-array-sint-index-okp)))
  :hooks (:fix)

  :prepwork
  ;; to generate theorems about UPDATE-NTH:
  ((local (include-book "std/lists/update-nth" :dir :system))
   (local (fty::deflist uchar-list
            :elt-type uchar
            :true-listp t
            :elementp-of-nil nil
            :pred uchar-listp))))
