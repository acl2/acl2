; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primitives")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the tested functions.

;; boolean operations:

(java::atj-main-function-type test-boolean-not (:jboolean) :jboolean)

(java::atj-main-function-type test-boolean-and (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-xor (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-ior (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-eq (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type test-boolean-neq (:jboolean :jboolean) :jboolean)

;; integer operations:

(java::atj-main-function-type test-int-plus (:jint) :jint)

(java::atj-main-function-type test-long-plus (:jlong) :jlong)

(java::atj-main-function-type test-int-minus (:jint) :jint)

(java::atj-main-function-type test-long-minus (:jlong) :jlong)

(java::atj-main-function-type test-int-not (:jint) :jint)

(java::atj-main-function-type test-long-not (:jlong) :jlong)

(java::atj-main-function-type test-int-add (:jint :jint) :jint)

(java::atj-main-function-type test-long-add (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-sub (:jint :jint) :jint)

(java::atj-main-function-type test-long-sub (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-mul (:jint :jint) :jint)

(java::atj-main-function-type test-long-mul (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-div (:jint :jint) :jint)

(java::atj-main-function-type test-long-div (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-rem (:jint :jint) :jint)

(java::atj-main-function-type test-long-rem (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-and (:jint :jint) :jint)

(java::atj-main-function-type test-long-and (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-xor (:jint :jint) :jint)

(java::atj-main-function-type test-long-xor (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-ior (:jint :jint) :jint)

(java::atj-main-function-type test-long-ior (:jlong :jlong) :jlong)

(java::atj-main-function-type test-int-eq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-eq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-neq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-neq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-less (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-less (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-lesseq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-lesseq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-great (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-great (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-greateq (:jint :jint) :jboolean)

(java::atj-main-function-type test-long-greateq (:jlong :jlong) :jboolean)

(java::atj-main-function-type test-int-int-shiftl (:jint :jint) :jint)

(java::atj-main-function-type test-long-long-shiftl (:jlong :jlong) :jlong)

(java::atj-main-function-type test-long-int-shiftl (:jlong :jint) :jlong)

(java::atj-main-function-type test-int-long-shiftl (:jint :jlong) :jint)

(java::atj-main-function-type test-int-int-shiftr (:jint :jint) :jint)

(java::atj-main-function-type test-long-long-shiftr (:jlong :jlong) :jlong)

(java::atj-main-function-type test-long-int-shiftr (:jlong :jint) :jlong)

(java::atj-main-function-type test-int-long-shiftr (:jint :jlong) :jint)

(java::atj-main-function-type test-int-int-ushiftr (:jint :jint) :jint)

(java::atj-main-function-type test-long-long-ushiftr (:jlong :jlong) :jlong)

(java::atj-main-function-type test-long-int-ushiftr (:jlong :jint) :jlong)

(java::atj-main-function-type test-int-long-ushiftr (:jint :jlong) :jint)

(java::atj-main-function-type f-boolean (:jboolean :jboolean) :jboolean)

(java::atj-main-function-type g-boolean
                              (:jboolean :jboolean :jboolean)
                              :jboolean)

;; widening conversions:

(java::atj-main-function-type test-byte-to-short (:jbyte) :jshort)

(java::atj-main-function-type test-byte-to-int (:jbyte) :jint)

(java::atj-main-function-type test-byte-to-long (:jbyte) :jlong)

(java::atj-main-function-type test-short-to-int (:jshort) :jint)

(java::atj-main-function-type test-short-to-long (:jshort) :jlong)

(java::atj-main-function-type test-int-to-long (:jint) :jlong)

(java::atj-main-function-type test-char-to-int (:jchar) :jint)

(java::atj-main-function-type test-char-to-long (:jchar) :jlong)

;; narrowing conversions:

(java::atj-main-function-type test-short-to-byte (:jshort) :jbyte)

(java::atj-main-function-type test-int-to-byte (:jint) :jbyte)

(java::atj-main-function-type test-long-to-byte (:jlong) :jbyte)

(java::atj-main-function-type test-char-to-byte (:jchar) :jbyte)

(java::atj-main-function-type test-int-to-short (:jint) :jshort)

(java::atj-main-function-type test-long-to-short (:jlong) :jshort)

(java::atj-main-function-type test-char-to-short (:jchar) :jshort)

(java::atj-main-function-type test-long-to-int (:jlong) :jint)

(java::atj-main-function-type test-short-to-char (:jshort) :jchar)

(java::atj-main-function-type test-int-to-char (:jint) :jchar)

(java::atj-main-function-type test-long-to-char (:jlong) :jchar)

;; widening and narrowing conversions:

(java::atj-main-function-type test-byte-to-char (:jbyte) :jchar)

;; other functions:

(java::atj-main-function-type f-int (:jint :jint) :jint)

(java::atj-main-function-type g-int (:jint :jint :jint) :jint)

(java::atj-main-function-type h-int (:jint) :jint)

(java::atj-main-function-type f-long (:jlong :jlong) :jlong)

(java::atj-main-function-type g-long (:jlong :jlong :jlong) :jlong)

(java::atj-main-function-type h-long (:jlong) :jlong)

(java::atj-main-function-type f-float (:jfloat :jfloat :jfloat) :jfloat)

(java::atj-main-function-type f-double (:jdouble :jdouble :jdouble) :jdouble)

(java::atj-main-function-type f-conv (:jbyte :jshort :jlong) :jint)

(java::atj-main-function-type g-conv (:jfloat :jdouble) :jdouble)

;; factorial:

(java::atj-main-function-type factorial-int (:jint) :jint)

(java::atj-main-function-type factorial-long (:jlong) :jlong)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the tested functions, with testing code.

(java::atj test-boolean-not
           test-boolean-and
           test-boolean-xor
           test-boolean-ior
           test-boolean-eq
           test-boolean-neq
           test-int-plus
           test-long-plus
           test-int-minus
           test-long-minus
           test-int-not
           test-long-not
           test-int-add
           test-long-add
           test-int-sub
           test-long-sub
           test-int-mul
           test-long-mul
           test-int-div
           test-long-div
           test-int-rem
           test-long-rem
           test-int-and
           test-long-and
           test-int-xor
           test-long-xor
           test-int-ior
           test-long-ior
           test-int-eq
           test-long-eq
           test-int-neq
           test-long-neq
           test-int-less
           test-long-less
           test-int-lesseq
           test-long-lesseq
           test-int-great
           test-long-great
           test-int-greateq
           test-long-greateq
           test-int-int-shiftl
           test-long-long-shiftl
           test-long-int-shiftl
           test-int-long-shiftl
           test-int-int-shiftr
           test-long-long-shiftr
           test-long-int-shiftr
           test-int-long-shiftr
           test-int-int-ushiftr
           test-long-long-ushiftr
           test-long-int-ushiftr
           test-int-long-ushiftr
           test-byte-to-short
           test-byte-to-int
           test-byte-to-long
           test-short-to-int
           test-short-to-long
           test-int-to-long
           test-char-to-int
           test-char-to-long
           test-short-to-byte
           test-int-to-byte
           test-long-to-byte
           test-char-to-byte
           test-int-to-short
           test-long-to-short
           test-char-to-short
           test-long-to-int
           test-short-to-char
           test-int-to-char
           test-long-to-char
           test-byte-to-char
           f-boolean
           g-boolean
           f-int
           g-int
           h-int
           f-long
           g-long
           h-long
           f-float
           f-double
           f-conv
           g-conv
           factorial-int
           factorial-long
           :deep nil
           :guards t
           :java-class "PrimitivesShallowGuarded"
           :tests *shallow-guarded-tests*)
