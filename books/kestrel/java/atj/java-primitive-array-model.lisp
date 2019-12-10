; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../language/primitive-values")

; these are so that the FTY::DEFLISTs in this file
; can generate theorems about NTH and UPDATE-NTH:
(include-book "std/lists/nth" :dir :system)
(include-book "std/lists/update-nth" :dir :system)

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
     eight of each kind, for the eight Java primitive types:")
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
      and the result is the new Java primitive array.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist boolean-value-list
  :short "Fixtype of true lists of Java @('boolean') values."
  :elt-type boolean-value
  :true-listp t
  :elementp-of-nil nil
  :pred boolean-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char-value-list
  :short "Fixtype of true lists of Java @('char') values."
  :elt-type char-value
  :true-listp t
  :elementp-of-nil nil
  :pred char-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist byte-value-list
  :short "Fixtype of true lists of Java @('byte') values."
  :elt-type byte-value
  :true-listp t
  :elementp-of-nil nil
  :pred byte-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist short-value-list
  :short "Fixtype of true lists of Java @('short') values."
  :elt-type short-value
  :true-listp t
  :elementp-of-nil nil
  :pred short-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist int-value-list
  :short "Fixtype of true lists of Java @('int') values."
  :elt-type int-value
  :true-listp t
  :elementp-of-nil nil
  :pred int-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist long-value-list
  :short "Fixtype of true lists of Java @('long') values."
  :elt-type long-value
  :true-listp t
  :elementp-of-nil nil
  :pred long-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist float-value-list
  :short "Fixtype of true lists of Java @('float') values."
  :elt-type float-value
  :true-listp t
  :elementp-of-nil nil
  :pred float-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist double-value-list
  :short "Fixtype of true lists of Java @('double') values."
  :elt-type double-value
  :true-listp t
  :elementp-of-nil nil
  :pred double-value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('boolean') arrays."
  (and (boolean-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('char') arrays."
  (and (char-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('byte') arrays."
  (and (byte-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('short') arrays."
  (and (short-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('int') arrays."
  (and (int-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('long') arrays."
  (and (long-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('float') arrays."
  :long
  (xdoc::topstring-p
   "The components of a @('float') array
    are always in the float value set [JLS:10].
    Thus, we use @(tsee float-value) for the components,
    not @(tsee floatx-value).")
  (and (float-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-p (x)
  :returns (yes/no booleanp)
  :short "Recognize (our model of) Java @('double') arrays."
  :long
  (xdoc::topstring-p
   "The components of a @('double') array
     are always in the double value set [JLS:10].
     Thus, we use @(tsee double-value) for the components,
     not @(tsee doublex-value).")
  (and (double-value-listp x)
       (< (len x) (expt 2 31))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-array-read ((array boolean-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component boolean-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable boolean-array-p))))
  :short "Read a component from a Java @('boolean') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable boolean-array-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-array-read ((array char-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component char-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable char-array-p))))
  :short "Read a component from a Java @('char') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable char-array-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define byte-array-read ((array byte-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component byte-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable byte-array-p))))
  :short "Read a component from a Java @('byte') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable byte-array-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define short-array-read ((array short-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component short-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable short-array-p))))
  :short "Read a component from a Java @('short') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable short-array-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-array-read ((array int-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component int-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable int-array-p))))
  :short "Read a component from a Java @('int') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable int-array-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define long-array-read ((array long-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component long-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable long-array-p))))
  :short "Read a component from a Java @('long') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable long-array-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-array-read ((array float-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component float-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable float-array-p))))
  :short "Read a component from a Java @('float') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable float-array-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define double-array-read ((array double-array-p) (index int-value-p))
  :guard (integer-range-p 0 (len array) (int-value->int index))
  :returns (component double-value-p
                      :hyp :guard
                      :hints (("Goal" :in-theory (enable double-array-p))))
  :short "Read a component from a Java @('double') array."
  (nth (int-value->int index) array)
  :guard-hints (("Goal" :in-theory (enable double-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable boolean-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable char-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable byte-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable short-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable int-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable long-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable float-array-p))))

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
  :guard-hints (("Goal" :in-theory (enable double-array-p))))
