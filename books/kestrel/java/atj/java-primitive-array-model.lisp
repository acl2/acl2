; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../language/primitive-values")

(include-book "kestrel/fty/ubyte16-list" :dir :system)
(include-book "kestrel/fty/sbyte8-list" :dir :system)
(include-book "kestrel/fty/sbyte16-list" :dir :system)
(include-book "kestrel/fty/sbyte32-list" :dir :system)
(include-book "kestrel/fty/sbyte64-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-primitive-array-model
  :parents (atj-implementation)
  :short "ATJ's model of Java primitive arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the purpose of generating Java code
     that manipulates Java primitive arrays,
     we introduce an ACL2 representation of Java primitive arrays
     and of operations on such arrays.
     This is currently not part of our Java language formalization,
     but it may eventually be replaced with
     a perhaps more general model from the Java language formalization.
     The current model only serves ATJ's needs;
     it is not meant to model all aspects of Java primitive arrays.
     ATJ's use of this model of Java primitive arrays
     is described in @(see atj-java-primitive-arrays).")
   (xdoc::p
    "We model a Java primitive array essentially as
     a list of Java primitive values whose length is below @($2^{31}$).
     This length limit is derived from the fact that
     the @('length') field of an array has type @('int') [JLS:10.7],
     and the maximum integer representable with @('int') is @($2^{31}-1$).
     We tag the list, via @(tsee fty::defprod),
     with an indication of the primitive types.")
   (xdoc::p
    "We introduce the following functions,
     eight of each kind, for the eight Java primitive types:")
   (xdoc::ul
    (xdoc::li
     "Operations to read components of Java primitive arrays:
      these model array accesses whose results are used as values.
      The index is (our ACL2 model of) a Java @('int'),
      and the result is (our ACL2 model of) the array component type.")
    (xdoc::li
     "Operations to obtain the lengths of Java primitive arrays:
      these model accesses of the @('length') field of arrays.
      The result is (our ACL2 model of) a Java @('int').")
    (xdoc::li
     "Operations to write components of Java primitive arrays:
      these model the assignment of values
      to array access expressions whose results are used as variables
      (these operations functionally return updated arrays).
      The index is (our ACL2 model of) a Java @('int'),
      the new component value is (our ACL2 model of) the array component type,
      and the result is the new Java primitive array.")
    (xdoc::li
     "Operations to create new Java primitive arrays of given lengths
      (and with every component the default value for the component type,
      i.e. @('false') for @('boolean') and 0 for the integral types
      [JLS:4.12.5]):
      these model array creation expressions
      with lengths and without initializers.
      The size is (our ACL2 model of) a Java @('int'),
      and the result is the newly created Java primitive array.")
    (xdoc::li
     "Operations to create new Java primitive arrays with given components:
      these model array creation expressions
      without lengths and with initializers.
      The inputs are lists of (our ACL2 models of) Java primitive values
      (of the arrays' component types),
      and the outputs are the newly created Java primitive arrays.
      These operations are the same as the constructors of the array fixtypes,
      but introducing them provides future flexibility,
      should the definition of the fixtype change in some way.")
    (xdoc::li
     "Operations to convert from Java primitive arrays to ACL2 lists,
      component-wise:
      a Java @('boolean') array is converted to
      the list of corresponding ACL2 @(tsee booleanp) values;
      a Java @('char') array is converted to
      the list of corresponding ACL2 @(tsee ubyte16p) values;
      a Java @('byte') array is converted to
      the list of corresponding ACL2 @(tsee sbyte8p) values;
      a Java @('short') array is converted to
      the list of corresponding ACL2 @(tsee sbyte16p) values;
      a Java @('int') array is converted to
      the list of corresponding ACL2 @(tsee sbyte32p) values; and
      a Java @('long') array is converted to
      the list of corresponding ACL2 @(tsee sbyte64p) values.")
    (xdoc::li
     "Operations to convert to Java primitive arrays from ACL2 lists,
      component-wise; these are the inverse conversions of
      those described just above."))
   (xdoc::p
    "Note that the convertions between Java arrays and ACL2 lists
     involve lists of ACL2 values, not of Java primitive values.
     The reason is that ACL2 lists of (our model of) Java primitive values
     do not really have a place in the generated Java code,
     which separates Java primitive values and arrays from built-in ACL2 values,
     through the ATJ types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod boolean-array
  :short "Fixtype of (our model of) Java @('boolean') arrays."
  ((components boolean-value-list :reqfix (if (< (len components) (expt 2 31))
                                              components
                                            nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :boolean-array
  ///

  (defrule len-of-boolean-array->components-upper-bound
    (< (len (boolean-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable boolean-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char-array
  :short "Fixtype of (our model of) Java @('char') arrays."
  ((components char-value-list :reqfix (if (< (len components) (expt 2 31))
                                           components
                                         nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :char-array
  ///

  (defrule len-of-char-array->components-upper-bound
    (< (len (char-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable char-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod byte-array
  :short "Fixtype of (our model of) Java @('byte') arrays."
  ((components byte-value-list :reqfix (if (< (len components) (expt 2 31))
                                           components
                                         nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :byte-array
  ///

  (defrule len-of-byte-array->components-upper-bound
    (< (len (byte-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable byte-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod short-array
  :short "Fixtype of (our model of) Java @('short') arrays."
  ((components short-value-list :reqfix (if (< (len components) (expt 2 31))
                                           components
                                         nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :short-array
  ///

  (defrule len-of-short-array->components-upper-bound
    (< (len (short-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable short-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod int-array
  :short "Fixtype of (our model of) Java @('int') arrays."
  ((components int-value-list :reqfix (if (< (len components) (expt 2 31))
                                           components
                                         nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :int-array
  ///

  (defrule len-of-int-array->components-upper-bound
    (< (len (int-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable int-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod long-array
  :short "Fixtype of (our model of) Java @('long') arrays."
  ((components long-value-list :reqfix (if (< (len components) (expt 2 31))
                                           components
                                         nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :long-array
  ///

  (defrule len-of-long-array->components-upper-bound
    (< (len (long-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable long-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod float-array
  :short "Fixtype of (our model of) Java @('float') arrays."
  ((components float-value-list :reqfix (if (< (len components) (expt 2 31))
                                           components
                                         nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :float-array
  ///

  (defrule len-of-float-array->components-upper-bound
    (< (len (float-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable float-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod double-array
  :short "Fixtype of (our model of) Java @('double') arrays."
  ((components double-value-list :reqfix (if (< (len components) (expt 2 31))
                                           components
                                         nil)))
  :require (< (len components) (expt 2 31))
  :layout :list
  :tag :double-array
  ///

  (defrule len-of-double-array->components-upper-bound
    (< (len (double-array->components array))
       (expt 2 31))
    :rule-classes :linear
    :enable double-array->components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-index-in-range-p ((array boolean-array-p)
                                        (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('boolean') array."
  (integer-range-p 0
                   (len (boolean-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-index-in-range-p ((array char-array-p)
                                     (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('char') array."
  (integer-range-p 0
                   (len (char-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-index-in-range-p ((array byte-array-p)
                                     (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('byte') array."
  (integer-range-p 0
                   (len (byte-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-index-in-range-p ((array short-array-p)
                                      (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('short') array."
  (integer-range-p 0
                   (len (short-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-index-in-range-p ((array int-array-p)
                                    (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('int') array."
  (integer-range-p 0
                   (len (int-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-index-in-range-p ((array long-array-p)
                                     (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('long') array."
  (integer-range-p 0
                   (len (long-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-index-in-range-p ((array float-array-p)
                                      (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('float') array."
  (integer-range-p 0
                   (len (float-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-index-in-range-p ((array double-array-p)
                                       (index int-value-p))
  :returns (yes/no booleanp)
  :short "Check if a Java @('int') is
          a valid index (i.e. in range) for a @('double') array."
  (integer-range-p 0
                   (len (double-array->components array))
                   (int-value->int index)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-read ((array boolean-array-p) (index int-value-p))
  :guard (boolean-array-index-in-range-p array index)
  :returns (component boolean-value-p)
  :short "Read a component from a Java @('boolean') array."
  (boolean-value-fix
   (nth (int-value->int index) (boolean-array->components array)))
  :guard-hints (("Goal" :in-theory (enable boolean-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist boolean-value-list
                      :elt-type boolean-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred boolean-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-read ((array char-array-p) (index int-value-p))
  :guard (char-array-index-in-range-p array index)
  :returns (component char-value-p)
  :short "Read a component from a Java @('char') array."
  (char-value-fix
   (nth (int-value->int index) (char-array->components array)))
  :guard-hints (("Goal" :in-theory (enable char-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist char-value-list
                      :elt-type char-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred char-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-read ((array byte-array-p) (index int-value-p))
  :guard (byte-array-index-in-range-p array index)
  :returns (component byte-value-p)
  :short "Read a component from a Java @('byte') array."
  (byte-value-fix
   (nth (int-value->int index) (byte-array->components array)))
  :guard-hints (("Goal" :in-theory (enable byte-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist byte-value-list
                      :elt-type byte-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred byte-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-read ((array short-array-p) (index int-value-p))
  :guard (short-array-index-in-range-p array index)
  :returns (component short-value-p)
  :short "Read a component from a Java @('short') array."
  (short-value-fix
   (nth (int-value->int index) (short-array->components array)))
  :guard-hints (("Goal" :in-theory (enable short-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist short-value-list
                      :elt-type short-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred short-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-read ((array int-array-p) (index int-value-p))
  :guard (int-array-index-in-range-p array index)
  :returns (component int-value-p)
  :short "Read a component from a Java @('int') array."
  (int-value-fix
   (nth (int-value->int index) (int-array->components array)))
  :guard-hints (("Goal" :in-theory (enable int-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist int-value-list
                      :elt-type int-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred int-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-read ((array long-array-p) (index int-value-p))
  :guard (long-array-index-in-range-p array index)
  :returns (component long-value-p)
  :short "Read a component from a Java @('long') array."
  (long-value-fix
   (nth (int-value->int index) (long-array->components array)))
  :guard-hints (("Goal" :in-theory (enable long-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist long-value-list
                      :elt-type long-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred long-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-read ((array float-array-p) (index int-value-p))
  :guard (float-array-index-in-range-p array index)
  :returns (component float-value-p)
  :short "Read a component from a Java @('float') array."
  (float-value-fix
   (nth (int-value->int index) (float-array->components array)))
  :guard-hints (("Goal" :in-theory (enable float-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist float-value-list
                      :elt-type float-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred float-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-read ((array double-array-p) (index int-value-p))
  :guard (double-array-index-in-range-p array index)
  :returns (component double-value-p)
  :short "Read a component from a Java @('double') array."
  (double-value-fix
   (nth (int-value->int index) (double-array->components array)))
  :guard-hints (("Goal" :in-theory (enable double-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist double-value-list
                      :elt-type double-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred double-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-length ((array boolean-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('boolean') array."
  (int-value (len (boolean-array->components array)))
  :guard-hints (("Goal" :in-theory (enable boolean-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-length ((array char-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('char') array."
  (int-value (len (char-array->components array)))
  :guard-hints (("Goal" :in-theory (enable char-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-length ((array byte-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('byte') array."
  (int-value (len (byte-array->components array)))
  :guard-hints (("Goal" :in-theory (enable byte-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-length ((array short-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('short') array."
  (int-value (len (short-array->components array)))
  :guard-hints (("Goal" :in-theory (enable short-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-length ((array int-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('int') array."
  (int-value (len (int-array->components array)))
  :guard-hints (("Goal" :in-theory (enable int-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-length ((array long-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('long') array."
  (int-value (len (long-array->components array)))
  :guard-hints (("Goal" :in-theory (enable long-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-length ((array float-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('float') array."
  (int-value (len (float-array->components array)))
  :guard-hints (("Goal" :in-theory (enable float-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-length ((array double-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('double') array."
  (int-value (len (double-array->components array)))
  :guard-hints (("Goal" :in-theory (enable double-array->components
                                           sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-write ((array boolean-array-p)
                             (index int-value-p)
                             (component boolean-value-p))
  :guard (boolean-array-index-in-range-p array index)
  :returns (new-array boolean-array-p)
  :short "Write a component to a Java @('boolean') array."
  (if (mbt (boolean-array-index-in-range-p array index))
      (boolean-array (update-nth (int-value->int index)
                                 component
                                 (boolean-array->components array)))
    (boolean-array-fix array))
  :guard-hints (("Goal" :in-theory (enable boolean-array->components
                                           boolean-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist boolean-value-list
                      :elt-type boolean-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred boolean-value-listp)))
  ///

  (defret len-of-components-of-boolean-array-write
    (equal (len (boolean-array->components new-array))
           (len (boolean-array->components array)))
    :hints (("Goal" :in-theory (enable boolean-array->components
                                       boolean-array-index-in-range-p
                                       boolean-array
                                       boolean-array-fix))))

  (defret boolean-array-index-in-range-p-of-boolean-array-write
    (equal (boolean-array-index-in-range-p new-array index1)
           (boolean-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable boolean-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-write ((array char-array-p)
                          (index int-value-p)
                          (component char-value-p))
  :guard (char-array-index-in-range-p array index)
  :returns (new-array char-array-p)
  :short "Write a component to a Java @('char') array."
  (if (mbt (char-array-index-in-range-p array index))
      (char-array (update-nth (int-value->int index)
                              component
                              (char-array->components array)))
    (char-array-fix array))
  :guard-hints (("Goal" :in-theory (enable char-array->components
                                           char-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist char-value-list
                      :elt-type char-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred char-value-listp)))
  ///

  (defret len-of-components-of-char-array-write
    (equal (len (char-array->components new-array))
           (len (char-array->components array)))
    :hints (("Goal" :in-theory (enable char-array->components
                                       char-array-index-in-range-p
                                       char-array
                                       char-array-fix))))

  (defret char-array-index-in-range-p-of-char-array-write
    (equal (char-array-index-in-range-p new-array index1)
           (char-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable char-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-write ((array byte-array-p)
                          (index int-value-p)
                          (component byte-value-p))
  :guard (byte-array-index-in-range-p array index)
  :returns (new-array byte-array-p)
  :short "Write a component to a Java @('byte') array."
  (if (mbt (byte-array-index-in-range-p array index))
      (byte-array (update-nth (int-value->int index)
                              component
                              (byte-array->components array)))
    (byte-array-fix array))
  :guard-hints (("Goal" :in-theory (enable byte-array->components
                                           byte-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist byte-value-list
                      :elt-type byte-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred byte-value-listp)))
  ///

  (defret len-of-components-of-byte-array-write
    (equal (len (byte-array->components new-array))
           (len (byte-array->components array)))
    :hints (("Goal" :in-theory (enable byte-array->components
                                       byte-array-index-in-range-p
                                       byte-array
                                       byte-array-fix))))

  (defret byte-array-index-in-range-p-of-byte-array-write
    (equal (byte-array-index-in-range-p new-array index1)
           (byte-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable byte-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-write ((array short-array-p)
                           (index int-value-p)
                           (component short-value-p))
  :guard (short-array-index-in-range-p array index)
  :returns (new-array short-array-p)
  :short "Write a component to a Java @('short') array."
  (if (mbt (short-array-index-in-range-p array index))
      (short-array (update-nth (int-value->int index)
                               component
                               (short-array->components array)))
    (short-array-fix array))
  :guard-hints (("Goal" :in-theory (enable short-array->components
                                           short-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist short-value-list
                      :elt-type short-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred short-value-listp)))
  ///

  (defret len-of-components-of-short-array-write
    (equal (len (short-array->components new-array))
           (len (short-array->components array)))
    :hints (("Goal" :in-theory (enable short-array->components
                                       short-array-index-in-range-p
                                       short-array
                                       short-array-fix))))

  (defret short-array-index-in-range-p-of-short-array-write
    (equal (short-array-index-in-range-p new-array index1)
           (short-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable short-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-write ((array int-array-p)
                         (index int-value-p)
                         (component int-value-p))
  :guard (int-array-index-in-range-p array index)
  :returns (new-array int-array-p)
  :short "Write a component to a Java @('int') array."
  (if (mbt (int-array-index-in-range-p array index))
      (int-array (update-nth (int-value->int index)
                             component
                             (int-array->components array)))
    (int-array-fix array))
  :guard-hints (("Goal" :in-theory (enable int-array->components
                                           int-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist int-value-list
                      :elt-type int-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred int-value-listp)))
  ///

  (defret len-of-components-of-int-array-write
    (equal (len (int-array->components new-array))
           (len (int-array->components array)))
    :hints (("Goal" :in-theory (enable int-array->components
                                       int-array-index-in-range-p
                                       int-array
                                       int-array-fix))))

  (defret int-array-index-in-range-p-of-int-array-write
    (equal (int-array-index-in-range-p new-array index1)
           (int-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable int-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-write ((array long-array-p)
                          (index int-value-p)
                          (component long-value-p))
  :guard (long-array-index-in-range-p array index)
  :returns (new-array long-array-p)
  :short "Write a component to a Java @('long') array."
  (if (mbt (long-array-index-in-range-p array index))
      (long-array (update-nth (int-value->int index)
                              component
                              (long-array->components array)))
    (long-array-fix array))
  :guard-hints (("Goal" :in-theory (enable long-array->components
                                           long-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist long-value-list
                      :elt-type long-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred long-value-listp)))
  ///

  (defret len-of-components-of-long-array-write
    (equal (len (long-array->components new-array))
           (len (long-array->components array)))
    :hints (("Goal" :in-theory (enable long-array->components
                                       long-array-index-in-range-p
                                       long-array
                                       long-array-fix))))

  (defret long-array-index-in-range-p-of-long-array-write
    (equal (long-array-index-in-range-p new-array index1)
           (long-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable long-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-write ((array float-array-p)
                           (index int-value-p)
                           (component float-value-p))
  :guard (float-array-index-in-range-p array index)
  :returns (new-array float-array-p)
  :short "Write a component to a Java @('float') array."
  (if (mbt (float-array-index-in-range-p array index))
      (float-array (update-nth (int-value->int index)
                               component
                               (float-array->components array)))
    (float-array-fix array))
  :guard-hints (("Goal" :in-theory (enable float-array->components
                                           float-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist float-value-list
                      :elt-type float-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred float-value-listp)))
  ///

  (defret len-of-components-of-float-array-write
    (equal (len (float-array->components new-array))
           (len (float-array->components array)))
    :hints (("Goal" :in-theory (enable float-array->components
                                       float-array-index-in-range-p
                                       float-array
                                       float-array-fix))))

  (defret float-array-index-in-range-p-of-float-array-write
    (equal (float-array-index-in-range-p new-array index1)
           (float-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable float-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-write ((array double-array-p)
                            (index int-value-p)
                            (component double-value-p))
  :guard (double-array-index-in-range-p array index)
  :returns (new-array double-array-p)
  :short "Write a component to a Java @('double') array."
  (if (mbt (double-array-index-in-range-p array index))
      (double-array (update-nth (int-value->int index)
                                component
                                (double-array->components array)))
    (double-array-fix array))
  :guard-hints (("Goal" :in-theory (enable double-array->components
                                           double-array-index-in-range-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist double-value-list
                      :elt-type double-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred double-value-listp)))
  ///

  (defret len-of-components-of-double-array-write
    (equal (len (double-array->components new-array))
           (len (double-array->components array)))
    :hints (("Goal" :in-theory (enable double-array->components
                                       double-array-index-in-range-p
                                       double-array
                                       double-array-fix))))

  (defret double-array-index-in-range-p-of-double-array-write
    (equal (double-array-index-in-range-p new-array index1)
           (double-array-index-in-range-p array index1))
    :hints (("Goal" :in-theory (enable double-array-index-in-range-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array boolean-array-p)
  :short "Construct a Java @('boolean') array with the given length
          and with @('false') as every component."
  (boolean-array (repeat (int-value->int length) (boolean-value nil)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist boolean-value-list
                      :elt-type boolean-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred boolean-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array char-array-p)
  :short "Construct a Java @('char') array with the given length
          and with 0 as every component."
  (char-array (repeat (int-value->int length) (char-value 0)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist char-value-list
                      :elt-type char-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred char-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array byte-array-p)
  :short "Construct a Java @('byte') array with the given length
          and with 0 as every component."
  (byte-array (repeat (int-value->int length) (byte-value 0)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist byte-value-list
                      :elt-type byte-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred byte-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array short-array-p)
  :short "Construct a Java @('short') array with the given length
          and with 0 as every component."
  (short-array (repeat (int-value->int length) (short-value 0)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist short-value-list
                      :elt-type short-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred short-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array int-array-p)
  :short "Construct a Java @('int') array with the given length
          and with 0 as every component."
  (int-array (repeat (int-value->int length) (int-value 0)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist int-value-list
                      :elt-type int-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred int-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array long-array-p)
  :short "Construct a Java @('long') array with the given length
          and with 0 as every component."
  (long-array (repeat (int-value->int length) (long-value 0)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist long-value-list
                      :elt-type long-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred long-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array float-array-p)
  :short "Construct a Java @('float') array with the given length
          and with positive 0 as every component."
  (float-array (repeat (int-value->int length)
                       (float-value (float-value-abs-pos-zero))))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist float-value-list
                      :elt-type float-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred float-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-new-len ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array double-array-p)
  :short "Construct a Java @('double') array with the given length
          and with positive 0 as every component."
  (double-array (repeat (int-value->int length)
                        (double-value (double-value-abs-pos-zero))))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist double-value-list
                      :elt-type double-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred double-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-new-init ((comps boolean-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array boolean-array-p)
  :short "Construct a Java @('boolean') array
          with the given initializer (i.e. components)."
  (boolean-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-new-init ((comps char-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array char-array-p)
  :short "Construct a Java @('char') array
          with the given initializer (i.e. components)."
  (char-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-new-init ((comps byte-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array byte-array-p)
  :short "Construct a Java @('byte') array
          with the given initializer (i.e. components)."
  (byte-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-new-init ((comps short-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array short-array-p)
  :short "Construct a Java @('short') array
          with the given initializer (i.e. components)."
  (short-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-new-init ((comps int-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array int-array-p)
  :short "Construct a Java @('int') array
          with the given initializer (i.e. components)."
  (int-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-new-init ((comps long-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array long-array-p)
  :short "Construct a Java @('long') array
          with the given initializer (i.e. components)."
  (long-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-new-init ((comps float-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array float-array-p)
  :short "Construct a Java @('float') array
          with the given initializer (i.e. components)."
  (float-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-new-init ((comps double-value-listp))
  :guard (< (len comps) (expt 2 31))
  :returns (array double-array-p)
  :short "Construct a Java @('double') array
          with the given initializer (i.e. components)."
  (double-array comps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-to-boolean-list ((array boolean-array-p))
  :returns (list boolean-listp)
  :short "Convert a Java @('boolean') array to an ACL2 list of booleans."
  (boolean-array-to-boolean-list-aux (boolean-array->components array))

  :prepwork
  ((define boolean-array-to-boolean-list-aux ((comps boolean-value-listp))
     :returns (list boolean-listp)
     (cond ((endp comps) nil)
           (t (cons (boolean-value->bool (car comps))
                    (boolean-array-to-boolean-list-aux (cdr comps)))))
     ///
     (defret len-of-boolean-array-to-boolean-list-aux
       (equal (len list)
              (len comps)))))

  ///

  (defret len-of-boolean-array-to-boolean-list
    (equal (len list)
           (len (boolean-array->components array)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-to-ubyte16-list ((array char-array-p))
  :returns (list ubyte16-listp)
  :short "Convert a Java @('char') array to
          an ACL2 list of unsigned 16-bit integers."
  (char-array-to-ubyte16-list-aux (char-array->components array))

  :prepwork
  ((define char-array-to-ubyte16-list-aux ((comps char-value-listp))
     :returns (list ubyte16-listp)
     (cond ((endp comps) nil)
           (t (cons (char-value->nat (car comps))
                    (char-array-to-ubyte16-list-aux (cdr comps)))))
     ///
     (defret len-of-char-array-to-ubyte16-list-aux
       (equal (len list)
              (len comps)))))

  ///

  (defret len-of-char-array-to-ubyte16-list
    (equal (len list)
           (len (char-array->components array)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-to-sbyte8-list ((array byte-array-p))
  :returns (list sbyte8-listp)
  :short "Convert a Java @('byte') array to
          an ACL2 list of signed 8-bit integers."
  (byte-array-to-sbyte8-list-aux (byte-array->components array))

  :prepwork
  ((define byte-array-to-sbyte8-list-aux ((comps byte-value-listp))
     :returns (list sbyte8-listp)
     (cond ((endp comps) nil)
           (t (cons (byte-value->int (car comps))
                    (byte-array-to-sbyte8-list-aux (cdr comps)))))
     ///
     (defret len-of-byte-array-to-sbyte8-list-aux
       (equal (len list)
              (len comps)))))

  ///

  (defret len-of-byte-array-to-sbyte8-list
    (equal (len list)
           (len (byte-array->components array)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-to-sbyte16-list ((array short-array-p))
  :returns (list sbyte16-listp)
  :short "Convert a Java @('short') array to
          an ACL2 list of signed 16-bit integers."
  (short-array-to-sbyte16-list-aux (short-array->components array))

  :prepwork
  ((define short-array-to-sbyte16-list-aux ((comps short-value-listp))
     :returns (list sbyte16-listp)
     (cond ((endp comps) nil)
           (t (cons (short-value->int (car comps))
                    (short-array-to-sbyte16-list-aux (cdr comps)))))
     ///
     (defret len-of-short-array-to-sbyte16-list-aux
       (equal (len list)
              (len comps)))))

  ///

  (defret len-of-short-array-to-sbyte16-list
    (equal (len list)
           (len (short-array->components array)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-to-sbyte32-list ((array int-array-p))
  :returns (list sbyte32-listp)
  :short "Convert a Java @('int') array to
          an ACL2 list of signed 32-bit integers."
  (int-array-to-sbyte32-list-aux (int-array->components array))

  :prepwork
  ((define int-array-to-sbyte32-list-aux ((comps int-value-listp))
     :returns (list sbyte32-listp)
     (cond ((endp comps) nil)
           (t (cons (int-value->int (car comps))
                    (int-array-to-sbyte32-list-aux (cdr comps)))))
     ///
     (defret len-of-int-array-to-sbyte32-list-aux
       (equal (len list)
              (len comps)))))

  ///

  (defret len-of-int-array-to-sbyte32-list
    (equal (len list)
           (len (int-array->components array)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-to-sbyte64-list ((array long-array-p))
  :returns (list sbyte64-listp)
  :short "Convert a Java @('long') array to
          an ACL2 list of signed 64-bit integers."
  (long-array-to-sbyte64-list-aux (long-array->components array))

  :prepwork
  ((define long-array-to-sbyte64-list-aux ((comps long-value-listp))
     :returns (list sbyte64-listp)
     (cond ((endp comps) nil)
           (t (cons (long-value->int (car comps))
                    (long-array-to-sbyte64-list-aux (cdr comps)))))
     ///
     (defret len-of-long-array-to-sbyte64-list-aux
       (equal (len list)
              (len comps)))))

  ///

  (defret len-of-long-array-to-sbyte64-list
    (equal (len list)
           (len (long-array->components array)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-from-boolean-list ((list boolean-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array boolean-array-p)
  :short "Convert an ACL2 list of booleans to a Java @('boolean') array."
  (boolean-array (boolean-array-from-boolean-list-aux list))

  :prepwork
  ((define boolean-array-from-boolean-list-aux ((list boolean-listp))
     :returns (comps boolean-value-listp)
     (cond ((endp list) nil)
           (t (cons (boolean-value (car list))
                    (boolean-array-from-boolean-list-aux (cdr list)))))
     ///
     (defret len-of-boolean-array-from-boolean-list-aux
       (equal (len comps)
              (len list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-from-ubyte16-list ((list ubyte16-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array char-array-p)
  :short "Convert an ACL2 list of unsigned 16-bit integers
          to a Java @('char') array."
  (char-array (char-array-from-ubyte16-list-aux list))

  :prepwork
  ((define char-array-from-ubyte16-list-aux ((list ubyte16-listp))
     :returns (comps char-value-listp)
     (cond ((endp list) nil)
           (t (cons (char-value (car list))
                    (char-array-from-ubyte16-list-aux (cdr list)))))
     ///
     (defret len-of-char-array-from-ubyte16-list-aux
       (equal (len comps)
              (len list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-from-sbyte8-list ((list sbyte8-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array byte-array-p)
  :short "Convert an ACL2 list of signed 8-bit integers
          to a Java @('byte') array."
  (byte-array (byte-array-from-sbyte8-list-aux list))

  :prepwork
  ((define byte-array-from-sbyte8-list-aux ((list sbyte8-listp))
     :returns (comps byte-value-listp)
     (cond ((endp list) nil)
           (t (cons (byte-value (car list))
                    (byte-array-from-sbyte8-list-aux (cdr list)))))
     ///
     (defret len-of-byte-array-from-sbyte8-list-aux
       (equal (len comps)
              (len list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-from-sbyte16-list ((list sbyte16-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array short-array-p)
  :short "Convert an ACL2 list of signed 16-bit integers
          to a Java @('short') array."
  (short-array (short-array-from-sbyte16-list-aux list))

  :prepwork
  ((define short-array-from-sbyte16-list-aux ((list sbyte16-listp))
     :returns (comps short-value-listp)
     (cond ((endp list) nil)
           (t (cons (short-value (car list))
                    (short-array-from-sbyte16-list-aux (cdr list)))))
     ///
     (defret len-of-short-array-from-sbyte16-list-aux
       (equal (len comps)
              (len list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-from-sbyte32-list ((list sbyte32-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array int-array-p)
  :short "Convert an ACL2 list of signed 32-bit integers
          to a Java @('int') array."
  (int-array (int-array-from-sbyte32-list-aux list))

  :prepwork
  ((define int-array-from-sbyte32-list-aux ((list sbyte32-listp))
     :returns (comps int-value-listp)
     (cond ((endp list) nil)
           (t (cons (int-value (car list))
                    (int-array-from-sbyte32-list-aux (cdr list)))))
     ///
     (defret len-of-int-array-from-sbyte32-list-aux
       (equal (len comps)
              (len list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-from-sbyte64-list ((list sbyte64-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array long-array-p)
  :short "Convert an ACL2 list of signed 64-bit integers
          to a Java @('long') array."
  (long-array (long-array-from-sbyte64-list-aux list))

  :prepwork
  ((define long-array-from-sbyte64-list-aux ((list sbyte64-listp))
     :returns (comps long-value-listp)
     (cond ((endp list) nil)
           (t (cons (long-value (car list))
                    (long-array-from-sbyte64-list-aux (cdr list)))))
     ///
     (defret len-of-long-array-from-sbyte64-list-aux
       (equal (len comps)
              (len list))))))
