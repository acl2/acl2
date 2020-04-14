; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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

(defval *atj-jprimarr-constrs*
  :short "List of (the names of) the ACL2 functions that model
          the construction of Java primitive arrays from their components."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the argument of one of these constructors is
     a list of calls of primitive value constructors on suitable constants,
     the call of the array constructor models
     the construction of a Java primitive array with initializer.
     For instance, a call
     @('(byte-array (list (byte-value 1) (byte-value 2) (byte-value 3)))')
     models the Java expression @('new byte[]{1, 2, 3}').
     In fact, for now this kind of calls of these constructors
     are the only allowed uses of these constructors.")
   (xdoc::p
    "We exclude the constructors for @('float') and @('double') arrays
     from this list for now,
     because our model of those two Java types is still abstract
     and thus we cannot support calls of the form just described."))
  '(boolean-array
    char-array
    byte-array
    short-array
    int-array
    long-array))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-reads*
  :short "List of (the names of) the ACL2 functions that model
          the reading of components from Java primitive arrays."
  '(boolean-array-read
    char-array-read
    byte-array-read
    short-array-read
    int-array-read
    long-array-read
    float-array-read
    double-array-read))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-lengths*
  :short "List of (the names of) the ACL2 functions that model
          the retrieval of lengths of Java primitive arrays."
  '(boolean-array-length
    char-array-length
    byte-array-length
    short-array-length
    int-array-length
    long-array-length
    float-array-length
    double-array-length))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-writes*
  :short "List of (the names of) the ACL2 functions that model
          the writing of components from Java primitive arrays."
  '(boolean-array-write
    char-array-write
    byte-array-write
    short-array-write
    int-array-write
    long-array-write
    float-array-write
    double-array-write))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-lenconstrs*
  :short "List of (the names of) the ACL2 functions that model
          the construction of Java primitive arrays from lengths."
  '(boolean-array-of-length
    char-array-of-length
    byte-array-of-length
    short-array-of-length
    int-array-of-length
    long-array-of-length
    float-array-of-length
    double-array-of-length))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive array operations."
  (append *atj-jprimarr-constrs*
          *atj-jprimarr-reads*
          *atj-jprimarr-lengths*
          *atj-jprimarr-writes*
          *atj-jprimarr-lenconstrs*)
  ///
  (assert-event (function-name-listp *atj-jprimarr-fns* (w state)))
  (assert-event (no-duplicatesp-eq *atj-jprimarr-fns*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-java-primarray-constr-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the construction of Java primitive arrays from components."
  (and (member-eq fn *atj-jprimarr-constrs*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-java-primarray-read-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the reading of components from Java primitive arrays."
  (and (member-eq fn *atj-jprimarr-reads*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-java-primarray-length-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the retrieval of lengths of Java primitive arrays."
  (and (member-eq fn *atj-jprimarr-lengths*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-java-primarray-write-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the writing of components from Java primitive arrays."
  (and (member-eq fn *atj-jprimarr-writes*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-java-primarray-lenconstr-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the construction of Java primitive arrays from lengths."
  (and (member-eq fn *atj-jprimarr-lenconstrs*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-java-primarray-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 funcion symbols that model
          Java primitive array operations."
  (and (member-eq fn *atj-jprimarr-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-types-for-java-primitive-arrays
  :short "ATJ types for the Java primitive array operations."

  ;; constructors from components:

  (atj-main-function-type boolean-array (:avalue) :jboolean[])

  (atj-main-function-type char-array (:avalue) :jchar[])

  (atj-main-function-type byte-array (:avalue) :jbyte[])

  (atj-main-function-type short-array (:avalue) :jshort[])

  (atj-main-function-type int-array (:avalue) :jint[])

  (atj-main-function-type long-array (:avalue) :jlong[])

  ;; read operations:

  (atj-main-function-type boolean-array-read (:jboolean[] :jint) :jboolean)

  (atj-main-function-type char-array-read (:jchar[] :jint) :jchar)

  (atj-main-function-type byte-array-read (:jbyte[] :jint) :jbyte)

  (atj-main-function-type short-array-read (:jshort[] :jint) :jshort)

  (atj-main-function-type int-array-read (:jint[] :jint) :jint)

  (atj-main-function-type long-array-read (:jlong[] :jint) :jlong)

  (atj-main-function-type float-array-read (:jfloat[] :jint) :jfloat)

  (atj-main-function-type double-array-read (:jdouble[] :jint) :jdouble)

  ;; length operations:

  (atj-main-function-type boolean-array-length (:jboolean[]) :jint)

  (atj-main-function-type char-array-length (:jchar[]) :jint)

  (atj-main-function-type byte-array-length (:jbyte[]) :jint)

  (atj-main-function-type short-array-length (:jshort[]) :jint)

  (atj-main-function-type int-array-length (:jint[]) :jint)

  (atj-main-function-type long-array-length (:jlong[]) :jint)

  (atj-main-function-type float-array-length (:jfloat[]) :jint)

  (atj-main-function-type double-array-length (:jdouble[]) :jint)

  ;; write operations:

  (atj-main-function-type boolean-array-write
                          (:jboolean[] :jint :jboolean)
                          (array :jboolean[]))

  (atj-main-function-type char-array-write
                          (:jchar[] :jint :jchar)
                          (array :jchar[]))

  (atj-main-function-type byte-array-write
                          (:jbyte[] :jint :jbyte)
                          (array :jbyte[]))

  (atj-main-function-type short-array-write
                          (:jshort[] :jint :jshort)
                          (array :jshort[]))

  (atj-main-function-type int-array-write
                          (:jint[] :jint :jint)
                          (array :jint[]))

  (atj-main-function-type long-array-write
                          (:jlong[] :jint :jlong)
                          (array :jlong[]))

  (atj-main-function-type float-array-write
                          (:jfloat[] :jint :jfloat)
                          (array :jfloat[]))

  (atj-main-function-type double-array-write
                          (:jdouble[] :jint :jdouble)
                          (array :jdouble[]))

  ;; constructors from length:

  (atj-main-function-type boolean-array-of-length (:jint) :jboolean[])

  (atj-main-function-type char-array-of-length (:jint) :jchar[])

  (atj-main-function-type byte-array-of-length (:jint) :jbyte[])

  (atj-main-function-type short-array-of-length (:jint) :jshort[])

  (atj-main-function-type int-array-of-length (:jint) :jint[])

  (atj-main-function-type long-array-of-length (:jint) :jlong[])

  (atj-main-function-type float-array-of-length (:jint) :jfloat[])

  (atj-main-function-type double-array-of-length (:jint) :jdouble[]))
