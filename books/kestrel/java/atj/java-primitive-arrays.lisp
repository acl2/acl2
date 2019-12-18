; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "types")

(include-book "kestrel/std/system/function-name-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-primitive-arrays
  :parents (atj-implementation)
  :short "ATJ's representation of Java primitive arrays and operations on them."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to have ATJ generate Java code
     that manipulates Java primitive arrays,
     we use an approach similar to "
    (xdoc::seetopic "atj-java-primitives" "the one for Java primitive values")
    ". We use ACL2 functions that correspond to
     the Java primitive arrays and operations on them:
     when ATJ encounters these specific ACL2 functions,
     it translates them to corresponding Java constructs
     that operate on Java primitive arrays;
     this happens only when @(':deep') is @('nil') and @(':guards') is @('t').")
   (xdoc::p
    "The discussion "
    (xdoc::seetopic "atj-java-primitives" "here")
    " about derivations targeting
     the ACL2 functions that represent Java primitive values
     applies to Java primitive arrays as well.")
   (xdoc::p
    "As discussed "
    (xdoc::seetopic "atj-java-primitive-array-model" "here")
    ", currently the ACL2 functions that represent Java primitive arrays
     are part of ATJ, but (perhaps some generalization of them) could be
     part of the "
    (xdoc::seetopic "language" "language formalization")
    " at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-reads*
  :short "List of (the names of) the ACL2 functions that model
          the reading of components from Java primitive arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the readers
     for all the Java primitive array types
     except @('float[]') and @('double[]'),
     which are currently not supported by ATJ."))
  '(boolean-array-read
    char-array-read
    byte-array-read
    short-array-read
    int-array-read
    long-array-read))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-lengths*
  :short "List of (the names of) the ACL2 functions that model
          the retrieval of lengths of Java primitive arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the length functions
     for all the Java primitive array types
     except @('float[]') and @('double[]'),
     which are currently not supported by ATJ."))
  '(boolean-array-length
    char-array-length
    byte-array-length
    short-array-length
    int-array-length
    long-array-length))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-constructors*
  :short "List of (the names of) the ACL2 functions that model
          the construction of Java primitive arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the functions to construct arrays
     of given sizes with default component values,
     for all the Java primitive types
     except @('float[]') and @('double[]'),
     which currently are not supported by ATJ."))
  '(boolean-array-of-length
    char-array-of-length
    byte-array-of-length
    short-array-of-length
    int-array-of-length
    long-array-of-length))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-constructors-init*
  :short "List of (the names of) the ACL2 functions that model
          the construction of Java primitive arrays with initializers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the functions to construct arrays
     with given component values,
     for all the Java primitive types
     except @('float[]') and @('double[]'),
     which currently are not supported by ATJ."))
  '(boolean-array
    char-array
    byte-array
    short-array
    int-array
    long-array))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-java-primarray-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive array operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This just consists of the read and length functions for now.
     More will be added in the future."))
  (append *atj-java-primarray-reads*
          *atj-java-primarray-lengths*
          *atj-java-primarray-constructors*
          *atj-java-primarray-constructors-init*)
  ///
  (assert-event (function-name-listp *atj-java-primarray-fns* (w state)))
  (assert-event (no-duplicatesp-eq *atj-java-primarray-fns*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-types-for-java-primitive-arrays
  :short "ATJ types for the Java primitive array operations."

  ;; read operations:

  (def-atj-main-function-type boolean-array-read (:jboolean[] :jint) :jboolean)

  (def-atj-main-function-type char-array-read (:jchar[] :jint) :jchar)

  (def-atj-main-function-type byte-array-read (:jbyte[] :jint) :jbyte)

  (def-atj-main-function-type short-array-read (:jshort[] :jint) :jshort)

  (def-atj-main-function-type int-array-read (:jint[] :jint) :jint)

  (def-atj-main-function-type long-array-read (:jlong[] :jint) :jlong)

  ;; length operations:

  (def-atj-main-function-type boolean-array-length (:jboolean[]) :jint)

  (def-atj-main-function-type char-array-length (:jchar[]) :jint)

  (def-atj-main-function-type byte-array-length (:jbyte[]) :jint)

  (def-atj-main-function-type short-array-length (:jshort[]) :jint)

  (def-atj-main-function-type int-array-length (:jint[]) :jint)

  (def-atj-main-function-type long-array-length (:jlong[]) :jint)

  ;; constructors from length:

  (def-atj-main-function-type boolean-array-of-length (:jint) :jboolean[])

  (def-atj-main-function-type char-array-of-length (:jint) :jchar[])

  (def-atj-main-function-type byte-array-of-length (:jint) :jbyte[])

  (def-atj-main-function-type short-array-of-length (:jint) :jshort[])

  (def-atj-main-function-type int-array-of-length (:jint) :jint[])

  (def-atj-main-function-type long-array-of-length (:jint) :jlong[])

  ;; constructors from components:

  (def-atj-main-function-type boolean-array (:avalue) :jboolean[])

  (def-atj-main-function-type char-array (:avalue) :jchar[])

  (def-atj-main-function-type byte-array (:avalue) :jbyte[])

  (def-atj-main-function-type short-array (:avalue) :jshort[])

  (def-atj-main-function-type int-array (:avalue) :jint[])

  (def-atj-main-function-type long-array (:avalue) :jlong[]))
