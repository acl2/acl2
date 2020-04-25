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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the tested functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; constructors from components, applied to LIST calls:

(java::atj-main-function-type test-boolean-array-new-with-components-0
                              () :jboolean[])

(java::atj-main-function-type test-char-array-new-with-components-0
                              () :jchar[])

(java::atj-main-function-type test-byte-array-new-with-components-0
                              () :jbyte[])

(java::atj-main-function-type test-short-array-new-with-components-0
                              () :jshort[])

(java::atj-main-function-type test-int-array-new-with-components-0
                              () :jint[])

(java::atj-main-function-type test-long-array-new-with-components-0
                              () :jlong[])

(java::atj-main-function-type test-boolean-array-new-with-components-1
                              (:jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-with-components-1
                              (:jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-with-components-1
                              (:jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-with-components-1
                              (:jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-with-components-1
                              (:jint) :jint[])

(java::atj-main-function-type test-long-array-new-with-components-1
                              (:jlong) :jlong[])

(java::atj-main-function-type test-boolean-array-new-with-components-2
                              (:jboolean :jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-with-components-2
                              (:jchar :jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-with-components-2
                              (:jbyte :jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-with-components-2
                              (:jshort :jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-with-components-2
                              (:jint :jint) :jint[])

(java::atj-main-function-type test-long-array-new-with-components-2
                              (:jlong :jlong) :jlong[])

(java::atj-main-function-type test-boolean-array-new-with-components-3
                              (:jboolean :jboolean :jboolean) :jboolean[])

(java::atj-main-function-type test-char-array-new-with-components-3
                              (:jchar :jchar :jchar) :jchar[])

(java::atj-main-function-type test-byte-array-new-with-components-3
                              (:jbyte :jbyte :jbyte) :jbyte[])

(java::atj-main-function-type test-short-array-new-with-components-3
                              (:jshort :jshort :jshort) :jshort[])

(java::atj-main-function-type test-int-array-new-with-components-3
                              (:jint :jint :jint) :jint[])

(java::atj-main-function-type test-long-array-new-with-components-3
                              (:jlong :jlong :jlong) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; read operations:

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

; length operations:

(java::atj-main-function-type test-boolean-array-length (:jboolean[]) :jint)

(java::atj-main-function-type test-char-array-length (:jchar[]) :jint)

(java::atj-main-function-type test-byte-array-length (:jbyte[]) :jint)

(java::atj-main-function-type test-short-array-length (:jshort[]) :jint)

(java::atj-main-function-type test-int-array-length (:jint[]) :jint)

(java::atj-main-function-type test-long-array-length (:jlong[]) :jint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write operations:

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

; constructors from length:

(java::atj-main-function-type test-boolean-array-new-with-length
                              (:jint) :jboolean[])

(java::atj-main-function-type test-char-array-new-with-length
                              (:jint) :jchar[])

(java::atj-main-function-type test-byte-array-new-with-length
                              (:jint) :jbyte[])

(java::atj-main-function-type test-short-array-new-with-length
                              (:jint) :jshort[])

(java::atj-main-function-type test-int-array-new-with-length
                              (:jint) :jint[])

(java::atj-main-function-type test-long-array-new-with-length
                              (:jint) :jlong[])

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
           test-boolean-array-new-with-length
           test-char-array-new-with-length
           test-byte-array-new-with-length
           test-short-array-new-with-length
           test-int-array-new-with-length
           test-long-array-new-with-length
           test-boolean-array-new-with-components-0
           test-char-array-new-with-components-0
           test-byte-array-new-with-components-0
           test-short-array-new-with-components-0
           test-int-array-new-with-components-0
           test-long-array-new-with-components-0
           test-boolean-array-new-with-components-1
           test-char-array-new-with-components-1
           test-byte-array-new-with-components-1
           test-short-array-new-with-components-1
           test-int-array-new-with-components-1
           test-long-array-new-with-components-1
           test-boolean-array-new-with-components-2
           test-char-array-new-with-components-2
           test-byte-array-new-with-components-2
           test-short-array-new-with-components-2
           test-int-array-new-with-components-2
           test-long-array-new-with-components-2
           test-boolean-array-new-with-components-3
           test-char-array-new-with-components-3
           test-byte-array-new-with-components-3
           test-short-array-new-with-components-3
           test-int-array-new-with-components-3
           test-long-array-new-with-components-3
           f
           g
           h
           i
           j
           :deep nil
           :guards t
           :java-class "PrimarraysShallowGuarded"
           :tests *shallow-guarded-tests*)
