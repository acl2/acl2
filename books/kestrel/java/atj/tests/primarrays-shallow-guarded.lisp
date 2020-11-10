; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primarrays")

(include-book "../atj" :ttags (:open-output-channel! :oslib :quicklisp :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the tested functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; read:

(java::atj-main-function-type test-boolean-array-read
                              (:jboolean[] :jint) :jboolean)

(java::atj-main-function-type test-char-array-read
                              (:jchar[] :jint) :jchar)

(java::atj-main-function-type test-byte-array-read
                              (:jbyte[] :jint) :jbyte)

(java::atj-main-function-type test-short-array-read
                              (:jshort[] :jint) :jshort)

(java::atj-main-function-type test-int-array-read
                              (:jint[] :jint) :jint)

(java::atj-main-function-type test-long-array-read
                              (:jlong[] :jint) :jlong)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; length:

(java::atj-main-function-type test-boolean-array-length (:jboolean[]) :jint)

(java::atj-main-function-type test-char-array-length (:jchar[]) :jint)

(java::atj-main-function-type test-byte-array-length (:jbyte[]) :jint)

(java::atj-main-function-type test-short-array-length (:jshort[]) :jint)

(java::atj-main-function-type test-int-array-length (:jint[]) :jint)

(java::atj-main-function-type test-long-array-length (:jlong[]) :jint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write:

(java::atj-main-function-type test-boolean-array-write
                              (:jboolean[] :jint :jboolean)
                              (a :jboolean[]))

(java::atj-main-function-type test-char-array-write
                              (:jchar[] :jint :jchar)
                              (a :jchar[]))

(java::atj-main-function-type test-byte-array-write
                              (:jbyte[] :jint :jbyte)
                              (a :jbyte[]))

(java::atj-main-function-type test-short-array-write
                              (:jshort[] :jint :jshort)
                              (a :jshort[]))

(java::atj-main-function-type test-int-array-write
                              (:jint[] :jint :jint)
                              (a :jint[]))

(java::atj-main-function-type test-long-array-write
                              (:jlong[] :jint :jlong)
                              (a :jlong[]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creation with length:

(java::atj-main-function-type test-boolean-array-new-len (:jint) :jboolean[])

(java::atj-main-function-type test-char-array-new-len (:jint) :jchar[])

(java::atj-main-function-type test-byte-array-new-len (:jint) :jbyte[])

(java::atj-main-function-type test-short-array-new-len (:jint) :jshort[])

(java::atj-main-function-type test-int-array-new-len (:jint) :jint[])

(java::atj-main-function-type test-long-array-new-len (:jint) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; creation with initializer:

(java::atj-main-function-type test-boolean-array-new-init-0
                              () :jboolean[])

(java::atj-main-function-type test-char-array-new-init-0
                              () :jchar[])

(java::atj-main-function-type test-byte-array-new-init-0
                              () :jbyte[])

(java::atj-main-function-type test-short-array-new-init-0
                              () :jshort[])

(java::atj-main-function-type test-int-array-new-init-0
                              () :jint[])

(java::atj-main-function-type test-long-array-new-init-0
                              () :jlong[])

(java::atj-main-function-type test-boolean-array-new-init-1
                              (:jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-init-1
                              (:jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-init-1
                              (:jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-init-1
                              (:jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-init-1
                              (:jint) :jint[])

(java::atj-main-function-type test-long-array-new-init-1
                              (:jlong) :jlong[])

(java::atj-main-function-type test-boolean-array-new-init-2
                              (:jboolean :jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-init-2
                              (:jchar :jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-init-2
                              (:jbyte :jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-init-2
                              (:jshort :jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-init-2
                              (:jint :jint) :jint[])

(java::atj-main-function-type test-long-array-new-init-2
                              (:jlong :jlong) :jlong[])

(java::atj-main-function-type test-boolean-array-new-init-3
                              (:jboolean :jboolean :jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-init-3
                              (:jchar :jchar :jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-init-3
                              (:jbyte :jbyte :jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-init-3
                              (:jshort :jshort :jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-init-3
                              (:jint :jint :jint) :jint[])

(java::atj-main-function-type test-long-array-new-init-3
                              (:jlong :jlong :jlong) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; conversion to list:

(java::atj-main-function-type test-boolean-array-to-boolean-list
                              (:jboolean[]) :avalue)

(java::atj-main-function-type test-char-array-to-ubyte16-list
                              (:jchar[]) :avalue)

(java::atj-main-function-type test-byte-array-to-sbyte8-list
                              (:jbyte[]) :avalue)

(java::atj-main-function-type test-short-array-to-sbyte16-list
                              (:jshort[]) :avalue)

(java::atj-main-function-type test-int-array-to-sbyte32-list
                              (:jint[]) :avalue)

(java::atj-main-function-type test-long-array-to-sbyte64-list
                              (:jlong[]) :avalue)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; conversion from list:

(java::atj-main-function-type test-boolean-array-from-boolean-list
                              (:avalue) :jboolean[])

(java::atj-main-function-type test-char-array-from-ubyte16-list
                              (:avalue) :jchar[])

(java::atj-main-function-type test-byte-array-from-sbyte8-list
                              (:avalue) :jbyte[])

(java::atj-main-function-type test-short-array-from-sbyte16-list
                              (:avalue) :jshort[])

(java::atj-main-function-type test-int-array-from-sbyte32-list
                              (:avalue) :jint[])

(java::atj-main-function-type test-long-array-from-sbyte64-list
                              (:avalue) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; other functions:

(java::atj-main-function-type f (:jint[] :jint :jint) :jint)

(java::atj-main-function-type g (:jbyte[] :jshort[]) :jint)

(java::atj-main-function-type h (:jbyte) :jchar[])

(java::atj-main-function-type i (:jfloat[] :jdouble[] :jint :jint) :jdouble)

(java::atj-main-function-type j
                              (:jbyte[] :jbyte[] :jint :jint)
                              ((bytes1 :jbyte[]) (bytes2 :jbyte[])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the tested functions.
; The automatic generation of tests is not supported yet.

(java::atj test-boolean-array-read
           test-char-array-read
           test-byte-array-read
           test-short-array-read
           test-int-array-read
           test-long-array-read
           test-boolean-array-length
           test-char-array-length
           test-byte-array-length
           test-short-array-length
           test-int-array-length
           test-long-array-length
           test-boolean-array-write
           test-char-array-write
           test-byte-array-write
           test-short-array-write
           test-int-array-write
           test-long-array-write
           test-boolean-array-new-len
           test-char-array-new-len
           test-byte-array-new-len
           test-short-array-new-len
           test-int-array-new-len
           test-long-array-new-len
           test-boolean-array-new-init-0
           test-char-array-new-init-0
           test-byte-array-new-init-0
           test-short-array-new-init-0
           test-int-array-new-init-0
           test-long-array-new-init-0
           test-boolean-array-new-init-1
           test-char-array-new-init-1
           test-byte-array-new-init-1
           test-short-array-new-init-1
           test-int-array-new-init-1
           test-long-array-new-init-1
           test-boolean-array-new-init-2
           test-char-array-new-init-2
           test-byte-array-new-init-2
           test-short-array-new-init-2
           test-int-array-new-init-2
           test-long-array-new-init-2
           test-boolean-array-new-init-3
           test-char-array-new-init-3
           test-byte-array-new-init-3
           test-short-array-new-init-3
           test-int-array-new-init-3
           test-long-array-new-init-3
           test-boolean-array-to-boolean-list
           test-char-array-to-ubyte16-list
           test-byte-array-to-sbyte8-list
           test-short-array-to-sbyte16-list
           test-int-array-to-sbyte32-list
           test-long-array-to-sbyte64-list
           test-boolean-array-from-boolean-list
           test-char-array-from-ubyte16-list
           test-byte-array-from-sbyte8-list
           test-short-array-from-sbyte16-list
           test-int-array-from-sbyte32-list
           test-long-array-from-sbyte64-list
           f
           g
           h
           i
           j
           :deep nil
           :guards t
           :java-class "PrimarraysShallowGuarded"
           :tests *shallow-guarded-tests*)
