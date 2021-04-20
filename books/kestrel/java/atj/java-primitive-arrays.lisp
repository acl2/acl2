; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "type-macros")

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
    "The discussion in @(see atj-java-primitives)
     about derivations targeting
     the ACL2 functions that represent Java primitive values
     applies to Java primitive arrays as well.")
   (xdoc::p
    "As discussed in @(see atj-java-primitive-array-model),
     currently the ACL2 functions that represent Java primitive arrays
     are part of ATJ, but (perhaps some generalization of them) could be
     part of the "
    (xdoc::seetopic "language" "language formalization")
    " at some point."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-read-fns*
  :short "List of (the names of) the ACL2 functions that model
          the reading of components of Java primitive arrays."
  '(boolean-array-read
    char-array-read
    byte-array-read
    short-array-read
    int-array-read
    long-array-read
    float-array-read
    double-array-read))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-length-fns*
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

(defval *atj-jprimarr-write-fns*
  :short "List of (the names of) the ACL2 functions that model
          the writing of components of Java primitive arrays."
  '(boolean-array-write
    char-array-write
    byte-array-write
    short-array-write
    int-array-write
    long-array-write
    float-array-write
    double-array-write))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-new-len-fns*
  :short "List of (the names of) the ACL2 functions that model
          the creation of Java primitive arrays from lengths."
  '(boolean-array-new-len
    char-array-new-len
    byte-array-new-len
    short-array-new-len
    int-array-new-len
    long-array-new-len
    float-array-new-len
    double-array-new-len))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-new-init-fns*
  :short "List of (the names of) the ACL2 functions that model
          the creation of Java primitive arrays from components."
  :long
  (xdoc::topstring-p
   "We exclude the functions that model
    the construction of @('float') and @('double') values,
    because we only have abstract models of those values for now.")
  '(boolean-array-new-init
    char-array-new-init
    byte-array-new-init
    short-array-new-init
    int-array-new-init
    long-array-new-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-conv-tolist-fns*
  :short "List of (the names of) the ACL2 functions that model
          the conversion from Java primitive arrays to ACL2 lists."
  '(boolean-array-to-boolean-list
    char-array-to-ubyte16-list
    byte-array-to-sbyte8-list
    short-array-to-sbyte16-list
    int-array-to-sbyte32-list
    long-array-to-sbyte64-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-conv-fromlist-fns*
  :short "List of (the names of) the ACL2 functions that model
          the conversion to Java primitive arrays from ACL2 lists."
  '(boolean-array-from-boolean-list
    char-array-from-ubyte16-list
    byte-array-from-sbyte8-list
    short-array-from-sbyte16-list
    int-array-from-sbyte32-list
    long-array-from-sbyte64-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprimarr-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive array operations."
  (append *atj-jprimarr-read-fns*
          *atj-jprimarr-length-fns*
          *atj-jprimarr-write-fns*
          *atj-jprimarr-new-len-fns*
          *atj-jprimarr-new-init-fns*
          *atj-jprimarr-conv-tolist-fns*
          *atj-jprimarr-conv-fromlist-fns*)
  ///
  (assert-event (function-name-listp *atj-jprimarr-fns* (w state)))
  (assert-event (no-duplicatesp-eq *atj-jprimarr-fns*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-read-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the reading of components from Java primitive arrays."
  (and (member-eq fn *atj-jprimarr-read-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-length-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the retrieval of lengths of Java primitive arrays."
  (and (member-eq fn *atj-jprimarr-length-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-write-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the writing of components from Java primitive arrays."
  (and (member-eq fn *atj-jprimarr-write-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-new-len-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the creation of Java primitive arrays from lengths."
  (and (member-eq fn *atj-jprimarr-new-len-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-new-init-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the creation of Java primitive arrays from components."
  (and (member-eq fn *atj-jprimarr-new-init-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-conv-tolist-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the conversions from Java primitive arrays to ACL2 lists."
  (and (member-eq fn *atj-jprimarr-conv-tolist-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-conv-fromlist-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognizer the ACL2 function symbols that model
          the conversions to Java primitive arrays from ACL2 lists."
  (and (member-eq fn *atj-jprimarr-conv-fromlist-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 function symbols that model
          Java primitive array operations."
  (and (member-eq fn *atj-jprimarr-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-types-for-java-primitive-arrays
  :short "ATJ types for the Java primitive array operations."

  ;; read:

  (atj-main-function-type boolean-array-read (:jboolean[] :jint) :jboolean)

  (atj-main-function-type char-array-read (:jchar[] :jint) :jchar)

  (atj-main-function-type byte-array-read (:jbyte[] :jint) :jbyte)

  (atj-main-function-type short-array-read (:jshort[] :jint) :jshort)

  (atj-main-function-type int-array-read (:jint[] :jint) :jint)

  (atj-main-function-type long-array-read (:jlong[] :jint) :jlong)

  (atj-main-function-type float-array-read (:jfloat[] :jint) :jfloat)

  (atj-main-function-type double-array-read (:jdouble[] :jint) :jdouble)

  ;; length:

  (atj-main-function-type boolean-array-length (:jboolean[]) :jint)

  (atj-main-function-type char-array-length (:jchar[]) :jint)

  (atj-main-function-type byte-array-length (:jbyte[]) :jint)

  (atj-main-function-type short-array-length (:jshort[]) :jint)

  (atj-main-function-type int-array-length (:jint[]) :jint)

  (atj-main-function-type long-array-length (:jlong[]) :jint)

  (atj-main-function-type float-array-length (:jfloat[]) :jint)

  (atj-main-function-type double-array-length (:jdouble[]) :jint)

  ;; write:

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

  ;; creation with length:

  (atj-main-function-type boolean-array-new-len (:jint) :jboolean[])

  (atj-main-function-type char-array-new-len (:jint) :jchar[])

  (atj-main-function-type byte-array-new-len (:jint) :jbyte[])

  (atj-main-function-type short-array-new-len (:jint) :jshort[])

  (atj-main-function-type int-array-new-len (:jint) :jint[])

  (atj-main-function-type long-array-new-len (:jint) :jlong[])

  (atj-main-function-type float-array-new-len (:jint) :jfloat[])

  (atj-main-function-type double-array-new-len (:jint) :jdouble[])

  ;; creation with initializer:

  (atj-main-function-type boolean-array-new-init (:avalue) :jboolean[])

  (atj-main-function-type char-array-new-init (:avalue) :jchar[])

  (atj-main-function-type byte-array-new-init (:avalue) :jbyte[])

  (atj-main-function-type short-array-new-init (:avalue) :jshort[])

  (atj-main-function-type int-array-new-init (:avalue) :jint[])

  (atj-main-function-type long-array-new-init (:avalue) :jlong[])

  (atj-main-function-type float-array-new-init (:avalue) :jfloat[])

  (atj-main-function-type double-array-new-init (:avalue) :jdouble[])

  ;; conversion to list:

  (atj-main-function-type boolean-array-to-boolean-list (:jboolean[]) :avalue)

  (atj-main-function-type char-array-to-ubyte16-list (:jchar[]) :avalue)

  (atj-main-function-type byte-array-to-sbyte8-list (:jbyte[]) :avalue)

  (atj-main-function-type short-array-to-sbyte16-list (:jshort[]) :avalue)

  (atj-main-function-type int-array-to-sbyte32-list (:jint[]) :avalue)

  (atj-main-function-type long-array-to-sbyte64-list (:jlong[]) :avalue)

  ;; conversion from list:

  (atj-main-function-type boolean-array-from-boolean-list (:avalue) :jboolean[])

  (atj-main-function-type char-array-from-ubyte16-list (:avalue) :jchar[])

  (atj-main-function-type byte-array-from-sbyte8-list (:avalue) :jbyte[])

  (atj-main-function-type short-array-from-sbyte16-list (:avalue) :jshort[])

  (atj-main-function-type int-array-from-sbyte32-list (:avalue) :jint[])

  (atj-main-function-type long-array-from-sbyte64-list (:avalue) :jlong[]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-new-init-fn-to-ptype ((fn atj-jprimarr-new-init-fn-p))
  :returns (ptype primitive-typep)
  :short "Map an ACL2 function that models
          a Java primitive array constructor with initializer
          to the corresponding primitive type."
  (case fn
    (boolean-array-new-init (primitive-type-boolean))
    (char-array-new-init (primitive-type-char))
    (byte-array-new-init (primitive-type-byte))
    (short-array-new-init (primitive-type-short))
    (int-array-new-init (primitive-type-int))
    (long-array-new-init (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-new-init-fn-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-conv-fromlist-fn-to-ptype
  ((fn atj-jprimarr-conv-fromlist-fn-p))
  :returns (ptype primitive-typep)
  :short "Map a list-to-array conversion function
          to the corresponding Java primitive type."
  (case fn
    (boolean-array-from-boolean-list (primitive-type-boolean))
    (char-array-from-ubyte16-list (primitive-type-char))
    (byte-array-from-sbyte8-list (primitive-type-byte))
    (short-array-from-sbyte16-list (primitive-type-short))
    (int-array-from-sbyte32-list (primitive-type-int))
    (long-array-from-sbyte64-list (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-conv-fromlist-fn-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprimarr-conv-tolist-fn-to-ptype
  ((fn atj-jprimarr-conv-tolist-fn-p))
  :returns (ptype primitive-typep)
  :short "Map an array-to-list conversion function
          to the corresponding Java primitive type."
  (case fn
    (boolean-array-to-boolean-list (primitive-type-boolean))
    (char-array-to-ubyte16-list (primitive-type-char))
    (byte-array-to-sbyte8-list (primitive-type-byte))
    (short-array-to-sbyte16-list (primitive-type-short))
    (int-array-to-sbyte32-list (primitive-type-int))
    (long-array-to-sbyte64-list (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprimarr-conv-tolist-fn-p)))
  :hooks (:fix))
