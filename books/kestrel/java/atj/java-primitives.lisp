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

(include-book "../language/primitive-operations")
(include-book "../language/primitive-conversions")

(include-book "kestrel/std/system/function-name-listp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-primitives
  :parents (atj-implementation)
  :short "Representation of Java primitive types and operations for ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to have ATJ generate Java code
     that manipulates Java primitive values,
     we use ACL2 functions that correspond to
     the Java primitive values and operations:
     when ATJ encounters these specific ACL2 functions,
     it translates them to corresponding Java constructs
     that operate on primitive types;
     this happens only when @(':deep') is @('nil') and @(':guards') is @('t').")
   (xdoc::p
    "When deriving a Java implementation from a specification,
     where ATJ is used as the last step of the derivation,
     the steps just before the last one can refine the ACL2 code
     to use the aforementioned ACL2 functions,
     ideally using " (xdoc::seetopic "apt::apt" "APT") " transformations,
     so that ATJ can produce Java code
     that operates on primitive values where needed.
     Such refinement steps could perhaps be somewhat automated,
     and incorporated into a code generation step that actually encompasses
     some APT transformation steps
     before the final ATJ code generation step.")
   (xdoc::p
    "The natural place for the aforementioned ACL2 functions
     that correspond to Java primitive values and operations is the "
    (xdoc::seetopic "language" "language formalization")
    " that is being developed.
     So ATJ recognizes those functions from the language formalization,
     and translates them to Java code that manipulates Java primitive values.")
   (xdoc::p
    "Needless to say, here `primitive' refers to
     Java primitive types, values, and operations.
     It has nothing to do with the ACL2 primitive functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprim-constr-fns*
  :short "List of (the names of) the ACL2 functions that model
          the construction of Java primitive values."
  :long
  (xdoc::topstring-p
   "We exclude the functions that model
    the construction of @('float') and @('double') values,
    because we only have abstract models of those values for now.")
  '(boolean-value
    char-value
    byte-value
    short-value
    int-value
    long-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprim-deconstr-fns*
  :short "List of (the names of) the ACL2 functions that model
          the deconstruction of Java primitive values."
  :long
  (xdoc::topstring-p
   "These are the inverses of the functions
    that model the construction of primitive values.
    These deconstructors essentially convert the Java primitive values
    to the corresponding ACL2 values (symbols and integers).")
  '(boolean-value->bool$inline
    char-value->nat$inline
    byte-value->int$inline
    short-value->int$inline
    int-value->int$inline
    long-value->int$inline))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprim-unop-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive unary operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the unary
     boolean, integer, and floating-point operations."))
  '(;; unary boolean operations:
    boolean-not
    ;; unary integer operations:
    int-plus
    long-plus
    int-minus
    long-minus
    int-not
    long-not
    ;; unary floating-point operations:
    float-plus
    double-plus
    float-minus
    double-minus))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprim-binop-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive binary operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the binary
     boolean, integer, and floating-point operations."))
  '(;; binary boolean operations:
    boolean-and
    boolean-xor
    boolean-ior
    boolean-eq
    boolean-neq
    ;; binary integer operations:
    int-add
    long-add
    int-sub
    long-sub
    int-mul
    long-mul
    int-div
    long-div
    int-rem
    long-rem
    int-and
    long-and
    int-xor
    long-xor
    int-ior
    long-ior
    int-eq
    long-eq
    int-neq
    long-neq
    int-less
    long-less
    int-lesseq
    long-lesseq
    int-great
    long-great
    int-greateq
    long-greateq
    int-int-shiftl
    long-long-shiftl
    long-int-shiftl
    int-long-shiftl
    int-int-shiftr
    long-long-shiftr
    long-int-shiftr
    int-long-shiftr
    int-int-ushiftr
    long-long-ushiftr
    long-int-ushiftr
    int-long-ushiftr
    ;; binary floating-point operations:
    float-add
    double-add
    float-sub
    double-sub
    float-mul
    double-mul
    float-div
    double-div
    float-rem
    double-rem
    float-eq
    double-eq
    float-neq
    double-neq
    float-less
    double-less
    float-lesseq
    double-lesseq
    float-great
    double-great
    float-greateq
    double-greateq))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprim-conv-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive conversions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the conversions between primitive types."))
  '(;; widening conversions:
    byte-to-short
    byte-to-int
    byte-to-long
    byte-to-float
    byte-to-double
    short-to-int
    short-to-long
    short-to-float
    short-to-double
    char-to-int
    char-to-long
    char-to-float
    char-to-double
    int-to-long
    int-to-float
    int-to-double
    long-to-float
    long-to-double
    float-to-double
    ;; narrowing conversions:
    short-to-byte
    short-to-char
    char-to-byte
    char-to-short
    int-to-byte
    int-to-short
    int-to-char
    long-to-byte
    long-to-short
    long-to-char
    long-to-int
    float-to-byte
    float-to-short
    float-to-char
    float-to-int
    float-to-long
    double-to-byte
    double-to-short
    double-to-char
    double-to-int
    double-to-long
    double-to-float
    ;; widening and narrowing conversions:
    byte-to-char))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-jprim-fns*
  :short "List of (the names of) the ACL2 functions that model
          Java primitive value constructions and operations."
  (append *atj-jprim-constr-fns*
          *atj-jprim-deconstr-fns*
          *atj-jprim-unop-fns*
          *atj-jprim-binop-fns*
          *atj-jprim-conv-fns*)
  ///
  (assert-event (function-name-listp *atj-jprim-fns* (w state)))
  (assert-event (no-duplicatesp-eq *atj-jprim-fns*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-constr-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 function symbols that model
          the construction of Java primitive types."
  (and (member-eq fn *atj-jprim-constr-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-deconstr-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 function symbols that model
          the deconstruction of Java primitive types."
  (and (member-eq fn *atj-jprim-deconstr-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-unop-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 function symbols that model
          the Java primitive unary operations."
  (and (member-eq fn *atj-jprim-unop-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-binop-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 function symbols that model
          the Java primitive binary operations."
  (and (member-eq fn *atj-jprim-binop-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-conv-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 function symbols that model
          the Java primitive conversions."
  (and (member-eq fn *atj-jprim-conv-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-fn-p (fn)
  :returns (yes/no booleanp)
  :short "Recognize the ACL2 function symbols that model
          the Java primitive value constructions, operations, and conversions."
  (and (member-eq fn *atj-jprim-fns*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-types-for-java-primitives
  :short "ATJ types for the Java primitive constructors and operations."

  ;; constructors:

  (atj-main-function-type boolean-value (:aboolean) :jboolean)

  (atj-main-function-type char-value (:ainteger) :jchar)

  (atj-main-function-type byte-value (:ainteger) :jbyte)

  (atj-main-function-type short-value (:ainteger) :jshort)

  (atj-main-function-type int-value (:ainteger) :jint)

  (atj-main-function-type long-value (:ainteger) :jlong)

  ;; deconstructors:

  (atj-main-function-type boolean-value->bool$inline (:jboolean) :aboolean)

  (atj-main-function-type char-value->nat$inline (:jchar) :ainteger)

  (atj-main-function-type byte-value->int$inline (:jbyte) :ainteger)

  (atj-main-function-type short-value->int$inline (:jshort) :ainteger)

  (atj-main-function-type int-value->int$inline (:jint) :ainteger)

  (atj-main-function-type long-value->int$inline (:jlong) :ainteger)

  ;; boolean operations:

  (atj-main-function-type boolean-not (:jboolean) :jboolean)

  (atj-main-function-type boolean-and (:jboolean :jboolean) :jboolean)

  (atj-main-function-type boolean-xor (:jboolean :jboolean) :jboolean)

  (atj-main-function-type boolean-ior (:jboolean :jboolean) :jboolean)

  (atj-main-function-type boolean-eq (:jboolean :jboolean) :jboolean)

  (atj-main-function-type boolean-neq (:jboolean :jboolean) :jboolean)

  ;; integer operations:

  (atj-main-function-type int-plus (:jint) :jint)

  (atj-main-function-type long-plus (:jlong) :jlong)

  (atj-main-function-type int-minus (:jint) :jint)

  (atj-main-function-type long-minus (:jlong) :jlong)

  (atj-main-function-type int-add (:jint :jint) :jint)

  (atj-main-function-type long-add (:jlong :jlong) :jlong)

  (atj-main-function-type int-sub (:jint :jint) :jint)

  (atj-main-function-type long-sub (:jlong :jlong) :jlong)

  (atj-main-function-type int-mul (:jint :jint) :jint)

  (atj-main-function-type long-mul (:jlong :jlong) :jlong)

  (atj-main-function-type int-div (:jint :jint) :jint)

  (atj-main-function-type long-div (:jlong :jlong) :jlong)

  (atj-main-function-type int-rem (:jint :jint) :jint)

  (atj-main-function-type long-rem (:jlong :jlong) :jlong)

  (atj-main-function-type int-not (:jint) :jint)

  (atj-main-function-type long-not (:jlong) :jlong)

  (atj-main-function-type int-and (:jint :jint) :jint)

  (atj-main-function-type long-and (:jlong :jlong) :jlong)

  (atj-main-function-type int-xor (:jint :jint) :jint)

  (atj-main-function-type long-xor (:jlong :jlong) :jlong)

  (atj-main-function-type int-ior (:jint :jint) :jint)

  (atj-main-function-type long-ior (:jlong :jlong) :jlong)

  (atj-main-function-type int-eq (:jint :jint) :jboolean)

  (atj-main-function-type long-eq (:jlong :jlong) :jboolean)

  (atj-main-function-type int-neq (:jint :jint) :jboolean)

  (atj-main-function-type long-neq (:jlong :jlong) :jboolean)

  (atj-main-function-type int-less (:jint :jint) :jboolean)

  (atj-main-function-type long-less (:jlong :jlong) :jboolean)

  (atj-main-function-type int-lesseq (:jint :jint) :jboolean)

  (atj-main-function-type long-lesseq (:jlong :jlong) :jboolean)

  (atj-main-function-type int-great (:jint :jint) :jboolean)

  (atj-main-function-type long-great (:jlong :jlong) :jboolean)

  (atj-main-function-type int-greateq (:jint :jint) :jboolean)

  (atj-main-function-type long-greateq (:jlong :jlong) :jboolean)

  (atj-main-function-type int-int-shiftl (:jint :jint) :jint)

  (atj-main-function-type long-long-shiftl (:jlong :jlong) :jlong)

  (atj-main-function-type long-int-shiftl (:jlong :jint) :jlong)

  (atj-main-function-type int-long-shiftl (:jint :jlong) :jint)

  (atj-main-function-type int-int-shiftr (:jint :jint) :jint)

  (atj-main-function-type long-long-shiftr (:jlong :jlong) :jlong)

  (atj-main-function-type long-int-shiftr (:jlong :jint) :jlong)

  (atj-main-function-type int-long-shiftr (:jint :jlong) :jint)

  (atj-main-function-type int-int-ushiftr (:jint :jint) :jint)

  (atj-main-function-type long-long-ushiftr (:jlong :jlong) :jlong)

  (atj-main-function-type long-int-ushiftr (:jlong :jint) :jlong)

  (atj-main-function-type int-long-ushiftr (:jint :jlong) :jint)

  ;; floating-point operations:

  (atj-main-function-type float-plus (:jfloat) :jfloat)

  (atj-main-function-type double-plus (:jdouble) :jdouble)

  (atj-main-function-type float-minus (:jfloat) :jfloat)

  (atj-main-function-type double-minus (:jdouble) :jdouble)

  (atj-main-function-type float-add (:jfloat :jfloat) :jfloat)

  (atj-main-function-type double-add (:jdouble :jdouble) :jdouble)

  (atj-main-function-type float-sub (:jfloat :jfloat) :jfloat)

  (atj-main-function-type double-sub (:jdouble :jdouble) :jdouble)

  (atj-main-function-type float-mul (:jfloat :jfloat) :jfloat)

  (atj-main-function-type double-mul (:jdouble :jdouble) :jdouble)

  (atj-main-function-type float-div (:jfloat :jfloat) :jfloat)

  (atj-main-function-type double-div (:jdouble :jdouble) :jdouble)

  (atj-main-function-type float-rem (:jfloat :jfloat) :jfloat)

  (atj-main-function-type double-rem (:jdouble :jdouble) :jdouble)

  (atj-main-function-type float-eq (:jfloat :jfloat) :jboolean)

  (atj-main-function-type double-eq (:jdouble :jdouble) :jboolean)

  (atj-main-function-type float-neq (:jfloat :jfloat) :jboolean)

  (atj-main-function-type double-neq (:jdouble :jdouble) :jboolean)

  (atj-main-function-type float-less (:jfloat :jfloat) :jboolean)

  (atj-main-function-type double-less (:jdouble :jdouble) :jboolean)

  (atj-main-function-type float-lesseq (:jfloat :jfloat) :jboolean)

  (atj-main-function-type double-lesseq (:jdouble :jdouble) :jboolean)

  (atj-main-function-type float-great (:jfloat :jfloat) :jboolean)

  (atj-main-function-type double-great (:jdouble :jdouble) :jboolean)

  (atj-main-function-type float-greateq (:jfloat :jfloat) :jboolean)

  (atj-main-function-type double-greateq (:jdouble :jdouble) :jboolean)

  ;; widening conversions:

  (atj-main-function-type byte-to-short (:jbyte) :jshort)

  (atj-main-function-type byte-to-int (:jbyte) :jint)

  (atj-main-function-type byte-to-long (:jbyte) :jlong)

  (atj-main-function-type byte-to-float (:jbyte) :jfloat)

  (atj-main-function-type byte-to-double (:jbyte) :jdouble)

  (atj-main-function-type short-to-int (:jshort) :jint)

  (atj-main-function-type short-to-long (:jshort) :jlong)

  (atj-main-function-type short-to-float (:jshort) :jfloat)

  (atj-main-function-type short-to-double (:jshort) :jdouble)

  (atj-main-function-type char-to-int (:jchar) :jint)

  (atj-main-function-type char-to-long (:jchar) :jlong)

  (atj-main-function-type char-to-float (:jchar) :jfloat)

  (atj-main-function-type char-to-double (:jchar) :jdouble)

  (atj-main-function-type int-to-long (:jint) :jlong)

  (atj-main-function-type int-to-float (:jint) :jfloat)

  (atj-main-function-type int-to-double (:jint) :jdouble)

  (atj-main-function-type long-to-float (:jlong) :jfloat)

  (atj-main-function-type long-to-double (:jlong) :jdouble)

  (atj-main-function-type float-to-double (:jfloat) :jdouble)

  ;; narrowing conversions:

  (atj-main-function-type short-to-byte (:jshort) :jbyte)

  (atj-main-function-type short-to-char (:jshort) :jchar)

  (atj-main-function-type char-to-byte (:jchar) :jbyte)

  (atj-main-function-type char-to-short (:jchar) :jshort)

  (atj-main-function-type int-to-byte (:jint) :jbyte)

  (atj-main-function-type int-to-short (:jint) :jshort)

  (atj-main-function-type int-to-char (:jint) :jchar)

  (atj-main-function-type long-to-byte (:jlong) :jbyte)

  (atj-main-function-type long-to-short (:jlong) :jshort)

  (atj-main-function-type long-to-char (:jlong) :jchar)

  (atj-main-function-type long-to-int (:jlong) :jint)

  (atj-main-function-type float-to-byte (:jfloat) :jbyte)

  (atj-main-function-type float-to-short (:jfloat) :jshort)

  (atj-main-function-type float-to-char (:jfloat) :jchar)

  (atj-main-function-type float-to-int (:jfloat) :jint)

  (atj-main-function-type float-to-long (:jfloat) :jlong)

  (atj-main-function-type double-to-byte (:jdouble) :jbyte)

  (atj-main-function-type double-to-short (:jdouble) :jshort)

  (atj-main-function-type double-to-char (:jdouble) :jchar)

  (atj-main-function-type double-to-int (:jdouble) :jint)

  (atj-main-function-type double-to-long (:jdouble) :jlong)

  (atj-main-function-type double-to-float (:jdouble) :jfloat)

  ;; widening and narrowing conversions:

  (atj-main-function-type byte-to-char (:jbyte) :jchar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-constr-fn-to-ptype ((fn atj-jprim-constr-fn-p))
  :returns (ptype primitive-typep)
  :short "Map an ACL2 function that models a Java primitive constructor
          to the corresponding Java primitive type."
  (case fn
    (boolean-value (primitive-type-boolean))
    (char-value (primitive-type-char))
    (byte-value (primitive-type-byte))
    (short-value (primitive-type-short))
    (int-value (primitive-type-int))
    (long-value (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-constr-fn-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jprim-deconstr-fn-to-ptype ((fn atj-jprim-deconstr-fn-p))
  :returns (ptype primitive-typep)
  :short "Map an ACL2 function that models a Java primitive deconstructor
          to the corresponding Java primitive type."
  (case fn
    (boolean-value->bool$inline (primitive-type-boolean))
    (char-value->nat$inline (primitive-type-char))
    (byte-value->int$inline (primitive-type-byte))
    (short-value->int$inline (primitive-type-short))
    (int-value->int$inline (primitive-type-int))
    (long-value->int$inline (primitive-type-long))
    (t (prog2$ (impossible) (ec-call (primitive-type-fix :irrelevant)))))
  :guard-hints (("Goal" :in-theory (enable atj-jprim-deconstr-fn-p)))
  :hooks (:fix))
