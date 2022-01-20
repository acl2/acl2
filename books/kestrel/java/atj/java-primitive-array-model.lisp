; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
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
      the list of corresponding ACL2 @(tsee sbyte64p) values.
      No conversion operations for @('float') and @('double') arrays
      are defined here,
      because we have an abstract model of those two primitive types.")
    (xdoc::li
     "Operations to convert to Java primitive arrays from ACL2 lists,
      component-wise; these are the inverse conversions of
      those described just above."))
   (xdoc::p
    "Note that the conversions between Java arrays and ACL2 lists
     involve lists of ACL2 values, not of Java primitive values.
     The reason is that ACL2 lists of (our model of) Java primitive values
     do not really have a place in the generated Java code,
     which separates Java primitive values and arrays from built-in ACL2 values,
     through the ATJ types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-def-java-primitive-array-model
  :short "Macro to define the models of Java primitive arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "The models vary slightly across the eight Java primitive array types,
     but they have a lot of common structure, which is captured via this macro.
     We define this macro and then we call it eight times.")
   (xdoc::p
    "This macro introduces, for each Java primitive (array) type:")
   (xdoc::ul
    (xdoc::li
     "A fixtype for the arrays of that type.
      This is a product type with one field,
      namely the list of primitive values that are the array's components.
      The fixtype includes the length requirement.")
    (xdoc::li
     "A predicate to check whether a Java @('int')
      is a valid index in an array.")
    (xdoc::li
     "The operations described in @(see atj-java-primitive-array-model)."))
   (xdoc::@def "atj-def-java-primitive-array-model"))

  (defmacro atj-def-java-primitive-array-model (type)

    (declare (xargs :guard (member-eq type '(boolean
                                             char
                                             byte
                                             short
                                             int
                                             long
                                             float
                                             double))))

    (b* ((type-name (symbol-name type))
         (type-doc (str::cat "@('" (str::downcase-string type-name) "')"))
         (jwit (pkg-witness "JAVA"))
         (type-value (packn-pos (list type '-value) jwit))
         (type-valuep (packn-pos (list type '-valuep) jwit))
         (type-value-fix (packn-pos (list type '-value-fix) jwit))
         (type-value->get (case type
                            (boolean 'boolean-value->bool)
                            (char 'char-value->nat)
                            (byte 'byte-value->int)
                            (short 'short-value->int)
                            (int 'int-value->int)
                            (long 'long-value->int)
                            (t nil))) ; for float or double -- not used
         (type-value-list (packn-pos (list type '-value-list) jwit))
         (type-value-listp (packn-pos (list type '-value-listp) jwit))
         (type-array (packn-pos (list type '-array) jwit))
         (type-arrayp (packn-pos (list type-array 'p) jwit))
         (type-array-fix (packn-pos (list type-array '-fix) jwit))
         (type-array->components (packn-pos (list type-array '->components)
                                            jwit))
         (type-array-index-in-range-p (packn-pos (list type
                                                       '-array-index-in-range-p)
                                                 jwit))
         (type-array-read (packn-pos (list type '-array-read) jwit))
         (type-array-length (packn-pos (list type '-array-length) jwit))
         (type-array-write (packn-pos (list type '-array-write) jwit))
         (type-array-new-len (packn-pos (list type '-array-new-len) jwit))
         (type-array-new-init (packn-pos (list type '-array-new-init) jwit))
         (acl2type (case type
                     (boolean 'boolean)
                     (char 'ubyte16)
                     (byte 'sbyte8)
                     (short 'sbyte16)
                     (int 'sbyte32)
                     (long 'sbyte64)
                     (t nil))) ; for float or double -- not used
         (acl2type-listp (case type
                           (boolean 'boolean-listp)
                           (char 'ubyte16-listp)
                           (byte 'sbyte8-listp)
                           (short 'sbyte16-listp)
                           (int 'sbyte32-listp)
                           (long 'sbyte64-listp)
                           (t nil))) ; for float or double -- not used
         (acl2type-doc (case type
                         (boolean "booleans")
                         (char "unsigned 16-bit integers")
                         (byte "signed 8-bit integers")
                         (short "signed 16-bit integers")
                         (int "signed 32-bit integers")
                         (long "signed 64-bit integers")
                         (t ""))) ; for float or double -- not used
         (type-array-to-list (packn-pos (list type-array
                                              '-to-
                                              acl2type
                                              '-list)
                                        jwit))
         (type-array-to-list-aux (packn-pos (list type-array-to-list '-aux)
                                            jwit))
         (type-array-from-list (packn-pos (list type-array
                                                '-from-
                                                acl2type
                                                '-list)
                                          jwit))
         (type-array-from-list-aux (packn-pos (list type-array-from-list '-aux)
                                              jwit)))

      `(progn

         ;; fixtype:

         (fty::defprod ,type-array
           :short ,(str::cat
                    "Fixtype of (our model of) Java " type-doc " arrays.")
           ((components ,type-value-list
                        :reqfix (if (< (len components) (expt 2 31))
                                    components
                                  nil)))
           :require (< (len components) (expt 2 31))
           :layout :list
           :tag ,(intern (symbol-name type-array) "KEYWORD")
           :pred ,type-arrayp
           ///
           (defrule ,(packn-pos (list 'len-of-
                                      type-array->components
                                      '-upper-bound)
                                jwit)
             (< (len (,type-array->components array))
                (expt 2 31))
             :rule-classes :linear
             :enable ,type-array->components))

         ;; predicate to check int index in range:

         (define ,type-array-index-in-range-p ((array ,type-arrayp)
                                               (index int-valuep))
           :returns (yes/no booleanp)
           :short ,(str::cat "Check if a Java @('int') is a valid index
                              (i.e. in range) for a " type-doc " array.")
           (integer-range-p 0
                            (len (,type-array->components array))
                            (int-value->int index)))

         ;; array read:

         (define ,type-array-read ((array ,type-arrayp) (index int-valuep))
           :guard (,type-array-index-in-range-p array index)
           :returns (component ,type-valuep)
           :short ,(str::cat "Read a component from a Java " type-doc " array.")
           (,type-value-fix
            (nth (int-value->int index) (,type-array->components array)))
           :guard-hints (("Goal" :in-theory (enable
                                             ,type-array-index-in-range-p)))
           :prepwork ((local (include-book "std/lists/nth" :dir :system))
                      ;; generates theorems about NTH:
                      (local (fty::deflist ,type-value-list
                               :elt-type ,type-value
                               :true-listp t
                               :elementp-of-nil nil
                               :pred ,type-value-listp))))

         ;; array length:

         (define ,type-array-length ((array ,type-arrayp))
           :returns (length int-valuep)
           :short ,(str::cat "Obtain the length of a Java " type-doc " array.")
           (int-value (len (,type-array->components array)))
           :guard-hints (("Goal" :in-theory (enable ,type-array->components
                                                    sbyte32p))))

         ;; array write:

         (define ,type-array-write ((array ,type-arrayp)
                                    (index int-valuep)
                                    (component ,type-valuep))
           :guard (,type-array-index-in-range-p array index)
           :returns (new-array ,type-arrayp)
           :short ,(str::cat "Write a component to a Java " type-doc " array.")
           (if (mbt (,type-array-index-in-range-p array index))
               (,type-array (update-nth (int-value->int index)
                                        component
                                        (,type-array->components array)))
             (,type-array-fix array))
           :guard-hints (("Goal" :in-theory (enable
                                             ,type-array->components
                                             ,type-array-index-in-range-p)))
           :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
                      ;; generates theorems about UPDATE-NTH:
                      (local (fty::deflist ,type-value-list
                               :elt-type ,type-value
                               :true-listp t
                               :elementp-of-nil nil
                               :pred ,type-value-listp)))
           ///

           (defret ,(packn-pos (list 'len-of-components-of- type-array-write)
                               jwit)
             (equal (len (,type-array->components new-array))
                    (len (,type-array->components array)))
             :hints (("Goal" :in-theory (enable ,type-array->components
                                                ,type-array-index-in-range-p
                                                ,type-array
                                                ,type-array-fix))))

           (defret ,(packn-pos (list type-array-index-in-range-p
                                     '-of-
                                     type-array-write)
                               jwit)
             (equal (,type-array-index-in-range-p new-array index1)
                    (,type-array-index-in-range-p array index1))
             :hints (("Goal" :in-theory (enable
                                         ,type-array-index-in-range-p)))))

         ;; new array with length:

         (define ,type-array-new-len ((length int-valuep))
           :guard (>= (int-value->int length) 0)
           :returns (array ,type-arrayp)
           :short ,(str::cat "Construct a Java " type-doc " array
                              with the given length
                              and with default components.")
           (,type-array (repeat (int-value->int length)
                                ,(case type
                                   (boolean '(boolean-value nil))
                                   (char '(char-value 0))
                                   (byte '(byte-value 0))
                                   (short '(short-value 0))
                                   (int '(int-value 0))
                                   (long '(long-value 0))
                                   (float '(float-value
                                            (float-value-abs-pos-zero)))
                                   (double '(double-value
                                             (double-value-abs-pos-zero)))
                                   (t (impossible)))))
           :prepwork ((local (include-book "std/lists/repeat" :dir :system))
                      ;; generates theorems about REPEAT:
                      (local (fty::deflist ,type-value-list
                               :elt-type ,type-value
                               :true-listp t
                               :elementp-of-nil nil
                               :pred ,type-value-listp))))

         ;; new array with initializer:

         (define ,type-array-new-init ((comps ,type-value-listp))
           :guard (< (len comps) (expt 2 31))
           :returns (array ,type-arrayp)
           :short ,(str::cat "Construct a Java " type-doc " array
                              with the given initializer (i.e. components).")
           (,type-array comps))

         ;; conversion to lists:

         ,@(and
            acl2type
            `((define ,type-array-to-list ((array ,type-arrayp))
                :returns (list ,acl2type-listp)
                :short ,(str::cat "Convert a Java " type-doc " array to
                              an ACL2 list of " acl2type-doc ".")
                (,type-array-to-list-aux (,type-array->components array))
                :prepwork
                ((define ,type-array-to-list-aux ((comps ,type-value-listp))
                   :returns (list ,acl2type-listp)
                   :parents nil
                   (cond ((endp comps) nil)
                         (t (cons (,type-value->get (car comps))
                                  (,type-array-to-list-aux (cdr comps)))))
                   ///
                   (defret ,(packn-pos (list 'len-of- type-array-to-list-aux)
                                       jwit)
                     (equal (len list)
                            (len comps)))))
                ///
                (defret ,(packn-pos (list 'len-of- type-array-to-list) jwit)
                  (equal (len list)
                         (len (,type-array->components array)))))))

         ;; conversion from lists:

         ,@(and
            acl2type
            `((define ,type-array-from-list ((list ,acl2type-listp))
                :guard (< (len list) (expt 2 31))
                :returns (array ,type-arrayp)
                :short ,(str::cat "Convert an ACL2 list of " acl2type-doc
                                  " to a Java @('boolean') array.")
                (,type-array (,type-array-from-list-aux list))
                :prepwork
                ((define ,type-array-from-list-aux ((list ,acl2type-listp))
                   :returns (comps ,type-value-listp)
                   :parents nil
                   (cond ((endp list) nil)
                         (t (cons (,type-value (car list))
                                  (,type-array-from-list-aux (cdr list)))))
                   ///
                   (defret ,(packn-pos (list 'len-of- type-array-from-list-aux)
                                       jwit)
                     (equal (len comps)
                            (len list))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(atj-def-java-primitive-array-model boolean)

(atj-def-java-primitive-array-model char)

(atj-def-java-primitive-array-model byte)

(atj-def-java-primitive-array-model short)

(atj-def-java-primitive-array-model int)

(atj-def-java-primitive-array-model long)

(atj-def-java-primitive-array-model float)

(atj-def-java-primitive-array-model double)
