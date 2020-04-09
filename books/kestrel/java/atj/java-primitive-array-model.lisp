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
     ATJ's use of this model of Java primitive arrays is described "
    (xdoc::seetopic "atj-java-primitive-arrays" "here")
    ".")
   (xdoc::p
    "We model a Java primitive array as a list of Java primitive values
     whose length is below @($2^{31}$).
     This length limit is derived from the fact that
     the @('length') field of an array has type @('int') [JLS:10.7],
     and the maximum integer representable with @('int') is @($2^{31}-1$).")
   (xdoc::p
    "We introduce the following functions,
     eight of each kind, for the eight Java primitive types
     (with an exception noted below):")
   (xdoc::ul
    (xdoc::li
     "Recognizers for the lists just described,
      i.e. for (ATJ's ACL2 model of) Java primitive arrays.
      Here we really model just the component of the arrays,
      and none of the additional information
      that is part of every Java object (e.g. locks),
      but that is adequate for ATJ's code generation purpose.
      (Recall that arrays are object in Java.)")
    (xdoc::li
     "Operations to read components of Java primitive arrays.
      The index is (our ACL2 model of) a Java @('int'),
      and the result is (our ACL2 model of) the array component type.")
    (xdoc::li
     "Operations to obtain the lengths of Java primitive arrays.
      The result is (our ACL2 model of) a Java @('int').")
    (xdoc::li
     "Operations to write components of Java primitive arrays.
      The index is (our ACL2 model of) a Java @('int'),
      the new component value is (our ACL2 model of) the array component type,
      and the result is the new Java primitive array.")
    (xdoc::li
     "Operations to construct Java primitive arrays from lists.
      These are currently identity operations,
      but their explicit presence can be recognized by ATJ
      and translated into array creation expressions with initializers
      under suitable conditions,
      where the components of the array initializers
      are derived from the list elements.
      Furthermore, the ``abstraction'' provided by these functions
      allows us to change the model of arrays in the future, if desired.")
    (xdoc::li
     "Operations to construct Java primitive arrays of given sizes
      and with every component the default value for the component type,
      i.e. @('false') for @('boolean') and 0 for the integral types
      [JLS:4.12.5].
      The size is (our ACL2 model of) a Java @('int').
      These operations can be recognized by ATJ
      and translated to array creation expressions without initializers.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection boolean-array
  :short "Fixtype of (our model of) Java @('boolean') arrays."

  (define boolean-array-p (x)
    :returns (yes/no booleanp)
    :parents (boolean-array)
    :short "Recognizer for @(tsee boolean-array)."
    (and (boolean-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule boolean-value-listp-when-boolean-array-p
      (implies (boolean-array-p x)
               (boolean-value-listp x))))

  (std::deffixer boolean-array-fix
    :pred boolean-array-p
    :body-fix nil
    :parents (boolean-array)
    :short "Fixer for @(tsee boolean-array).")

  (fty::deffixtype boolean-array
    :pred boolean-array-p
    :fix boolean-array-fix
    :equiv boolean-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection char-array
  :short "Fixtype of (our model of) Java @('char') arrays."

  (define char-array-p (x)
    :returns (yes/no booleanp)
    :parents (boolean-array)
    :short "Recognizer for @(tsee char-array)."
    (and (char-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule char-value-listp-when-char-array-p
      (implies (char-array-p x)
               (char-value-listp x))))

  (std::deffixer char-array-fix
    :pred char-array-p
    :body-fix nil
    :parents (char-array)
    :short "Fixer for @(tsee char-array).")

  (fty::deffixtype char-array
    :pred char-array-p
    :fix char-array-fix
    :equiv char-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection byte-array
  :short "Fixtype of (our model of) Java @('byte') arrays."

  (define byte-array-p (x)
    :returns (yes/no booleanp)
    :parents (byte-array)
    :short "Recognizer for @(tsee byte-array)."
    (and (byte-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule byte-value-listp-when-byte-array-p
      (implies (byte-array-p x)
               (byte-value-listp x))))

  (std::deffixer byte-array-fix
    :pred byte-array-p
    :body-fix nil
    :parents (byte-array)
    :short "Fixer for @(tsee byte-array).")

  (fty::deffixtype byte-array
    :pred byte-array-p
    :fix byte-array-fix
    :equiv byte-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection short-array
  :short "Fixtype of (our model of) Java @('short') arrays."

  (define short-array-p (x)
    :returns (yes/no booleanp)
    :parents (short-array)
    :short "Recognizer for @(tsee short-array)."
    (and (short-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule short-value-listp-when-short-array-p
      (implies (short-array-p x)
               (short-value-listp x))))

  (std::deffixer short-array-fix
    :pred short-array-p
    :body-fix nil
    :parents (short-array)
    :short "Fixer for @(tsee short-array).")

  (fty::deffixtype short-array
    :pred short-array-p
    :fix short-array-fix
    :equiv short-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection int-array
  :short "Fixtype of (our model of) Java @('int') arrays."

  (define int-array-p (x)
    :returns (yes/no booleanp)
    :parents (int-array)
    :short "Recognizer for @(tsee int-array)."
    (and (int-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule int-value-listp-when-int-array-p
      (implies (int-array-p x)
               (int-value-listp x))))

  (std::deffixer int-array-fix
    :pred int-array-p
    :body-fix nil
    :parents (int-array)
    :short "Fixer for @(tsee int-array).")

  (fty::deffixtype int-array
    :pred int-array-p
    :fix int-array-fix
    :equiv int-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection long-array
  :short "Fixtype of (our model of) Java @('long') arrays."

  (define long-array-p (x)
    :returns (yes/no booleanp)
    :parents (long-array)
    :short "Recognizer for @(tsee long-array)."
    (and (long-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule long-value-listp-when-long-array-p
      (implies (long-array-p x)
               (long-value-listp x))))

  (std::deffixer long-array-fix
    :pred long-array-p
    :body-fix nil
    :parents (long-array)
    :short "Fixer for @(tsee long-array).")

  (fty::deffixtype long-array
    :pred long-array-p
    :fix long-array-fix
    :equiv long-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection float-array
  :short "Fixtype of (our model of) Java @('float') arrays."
  :long
  (xdoc::topstring-p
   "The components of a @('float') array
    are always in the float value set [JLS:10].
    Thus, we use @(tsee float-value) for the components,
    not @(tsee floatx-value).")

  (define float-array-p (x)
    :returns (yes/no booleanp)
    :parents (float-array)
    :short "Recognizer for @(tsee float-array)."
    (and (float-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule float-value-listp-when-float-array-p
      (implies (float-array-p x)
               (float-value-listp x))))

  (std::deffixer float-array-fix
    :pred float-array-p
    :body-fix nil
    :parents (float-array)
    :short "Fixer for @(tsee float-array).")

  (fty::deffixtype float-array
    :pred float-array-p
    :fix float-array-fix
    :equiv float-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection double-array
  :short "Fixtype of (our model of) Java @('double') arrays."
  :long
  (xdoc::topstring-p
   "The components of a @('double') array
     are always in the double value set [JLS:10].
     Thus, we use @(tsee double-value) for the components,
     not @(tsee doublex-value).")

  (define double-array-p (x)
    :returns (yes/no booleanp)
    :parents (double-array)
    :short "Recognizer for @(tsee double-array)."
    (and (double-value-listp x)
         (< (len x) (expt 2 31)))
    ///
    (defrule double-value-listp-when-double-array-p
      (implies (double-array-p x)
               (double-value-listp x))))

  (std::deffixer double-array-fix
    :pred double-array-p
    :body-fix nil
    :parents (double-array)
    :short "Fixer for @(tsee double-array).")

  (fty::deffixtype double-array
    :pred double-array-p
    :fix double-array-fix
    :equiv double-array-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-read ((array boolean-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component boolean-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable boolean-array-p))))
  :short "Read a component from a Java @('boolean') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable boolean-array-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist boolean-value-list
                      :elt-type boolean-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred boolean-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-read ((array char-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component char-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable char-array-p))))
  :short "Read a component from a Java @('char') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable char-array-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist char-value-list
                      :elt-type char-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred char-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-read ((array byte-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component byte-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable byte-array-p))))
  :short "Read a component from a Java @('byte') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable byte-array-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist byte-value-list
                      :elt-type byte-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred byte-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-read ((array short-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component short-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable short-array-p))))
  :short "Read a component from a Java @('short') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable short-array-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist short-value-list
                      :elt-type short-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred short-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-read ((array int-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component int-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable int-array-p))))
  :short "Read a component from a Java @('int') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable int-array-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist int-value-list
                      :elt-type int-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred int-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-read ((array long-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component long-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable long-array-p))))
  :short "Read a component from a Java @('long') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable long-array-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist long-value-list
                      :elt-type long-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred long-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-read ((array float-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component float-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable float-array-p))))
  :short "Read a component from a Java @('float') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable float-array-p)))
  :prepwork ((local (include-book "std/lists/nth" :dir :system))
             ;; generates theorems about NTH:
             (local (fty::deflist float-value-list
                      :elt-type float-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred float-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-read ((array double-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component double-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable double-array-p))))
  :short "Read a component from a Java @('double') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable double-array-p)))
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
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable boolean-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-length ((array char-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('char') array."
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable char-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-length ((array byte-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('byte') array."
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable byte-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-length ((array short-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('short') array."
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable short-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-length ((array int-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('int') array."
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable int-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-length ((array long-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('long') array."
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable long-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-length ((array float-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('float') array."
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable float-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-length ((array double-array-p))
  :returns (length int-value-p)
  :short "Obtain the length of a Java @('double') array."
  (int-value (len array))
  :guard-hints (("Goal" :in-theory (enable double-array-p sbyte32p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-write ((array boolean-array-p)
                             (index int-value-p)
                             (component boolean-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array boolean-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable boolean-array-p))))
  :short "Write a component to a Java @('boolean') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable boolean-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist boolean-value-list
                      :elt-type boolean-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred boolean-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-write ((array char-array-p)
                          (index int-value-p)
                          (component char-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array char-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable char-array-p))))
  :short "Write a component to a Java @('char') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable char-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist char-value-list
                      :elt-type char-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred char-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-write ((array byte-array-p)
                          (index int-value-p)
                          (component byte-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array byte-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable byte-array-p))))
  :short "Write a component to a Java @('byte') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable byte-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist byte-value-list
                      :elt-type byte-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred byte-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-write ((array short-array-p)
                           (index int-value-p)
                           (component short-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array short-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable short-array-p))))
  :short "Write a component to a Java @('short') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable short-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist short-value-list
                      :elt-type short-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred short-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-write ((array int-array-p)
                         (index int-value-p)
                         (component int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array int-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable int-array-p))))
  :short "Write a component to a Java @('int') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable int-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist int-value-list
                      :elt-type int-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred int-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-write ((array long-array-p)
                          (index int-value-p)
                          (component long-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array long-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable long-array-p))))
  :short "Write a component to a Java @('long') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable long-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist long-value-list
                      :elt-type long-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred long-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-write ((array float-array-p)
                           (index int-value-p)
                           (component float-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array float-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable float-array-p))))
  :short "Write a component to a Java @('float') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable float-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist float-value-list
                      :elt-type float-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred float-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-write ((array double-array-p)
                            (index int-value-p)
                            (component double-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (new-array double-array-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable double-array-p))))
  :short "Write a component to a Java @('double') array."
  (update-nth (int-value->int index) component array)
  :guard-hints (("Goal" :in-theory (enable double-array-p)))
  :prepwork ((local (include-book "std/lists/update-nth" :dir :system))
             ;; generates theorems about UPDATE-NTH:
             (local (fty::deflist double-value-list
                      :elt-type double-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred double-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-with-comps ((list boolean-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array boolean-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable boolean-array-p))))
  :short "Construct a Java @('boolean') array
          from a list of @('boolean') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-with-comps ((list char-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array char-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable char-array-p))))
  :short "Construct a Java @('char') array
          from a list of @('char') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-with-comps ((list byte-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array byte-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable byte-array-p))))
  :short "Construct a Java @('byte') array
          from a list of @('byte') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-with-comps ((list short-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array short-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable short-array-p))))
  :short "Construct a Java @('short') array
          from a list of @('short') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-with-comps ((list int-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array int-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable int-array-p))))
  :short "Construct a Java @('int') array
          from a list of @('int') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-with-comps ((list long-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array long-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable long-array-p))))
  :short "Construct a Java @('long') array
          from a list of @('long') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-with-comps ((list float-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array float-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable float-array-p))))
  :short "Construct a Java @('float') array
          from a list of @('float') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-with-comps ((list double-value-listp))
  :guard (< (len list) (expt 2 31))
  :returns (array double-array-p
                  :hyp :guard
                  :hints (("Goal" :in-theory (enable double-array-p))))
  :short "Construct a Java @('double') array
          from a list of @('double') values."
  list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array boolean-array-p
                  :hints (("Goal" :in-theory (enable boolean-array-p))))
  :short "Construct a Java @('boolean') array with the given size
          and with @('false') as every component."
  (repeat (int-value->int length) (boolean-value nil))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist boolean-value-list
                      :elt-type boolean-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred boolean-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array char-array-p
                  :hints (("Goal" :in-theory (enable char-array-p))))
  :short "Construct a Java @('char') array with the given size
          and with 0 as every component."
  (repeat (int-value->int length) (char-value 0))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist char-value-list
                      :elt-type char-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred char-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array byte-array-p
                  :hints (("Goal" :in-theory (enable byte-array-p))))
  :short "Construct a Java @('byte') array with the given size
          and with 0 as every component."
  (repeat (int-value->int length) (byte-value 0))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist byte-value-list
                      :elt-type byte-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred byte-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array short-array-p
                  :hints (("Goal" :in-theory (enable short-array-p))))
  :short "Construct a Java @('short') array with the given size
          and with 0 as every component."
  (repeat (int-value->int length) (short-value 0))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist short-value-list
                      :elt-type short-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred short-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array int-array-p
                  :hints (("Goal" :in-theory (enable int-array-p))))
  :short "Construct a Java @('int') array with the given size
          and with 0 as every component."
  (repeat (int-value->int length) (int-value 0))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist int-value-list
                      :elt-type int-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred int-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array long-array-p
                  :hints (("Goal" :in-theory (enable long-array-p))))
  :short "Construct a Java @('long') array with the given size
          and with 0 as every component."
  (repeat (int-value->int length) (long-value 0))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist long-value-list
                      :elt-type long-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred long-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array float-array-p
                  :hints (("Goal" :in-theory (enable float-array-p))))
  :short "Construct a Java @('float') array with the given size
          and with positive 0 as every component."
  (repeat (int-value->int length) (float-value (float-value-abs-pos-zero)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist float-value-list
                      :elt-type float-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred float-value-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-of-length ((length int-value-p))
  :guard (>= (int-value->int length) 0)
  :returns (array double-array-p
                  :hints (("Goal" :in-theory (enable double-array-p))))
  :short "Construct a Java @('double') array with the given size
          and with positive 0 as every component."
  (repeat (int-value->int length) (double-value (double-value-abs-pos-zero)))
  :prepwork ((local (include-book "std/lists/repeat" :dir :system))
             ;; generates theorems about REPEAT:
             (local (fty::deflist double-value-list
                      :elt-type double-value
                      :true-listp t
                      :elementp-of-nil nil
                      :pred double-value-listp))))
