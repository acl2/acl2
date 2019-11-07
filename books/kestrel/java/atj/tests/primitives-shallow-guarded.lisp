; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primitives")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the tested functions.

(java::def-atj-main-function-type test-boolean-not (:jboolean) :jboolean)

(java::def-atj-main-function-type test-boolean-and
                                  (:jboolean :jboolean) :jboolean)

(java::def-atj-main-function-type test-boolean-xor
                                  (:jboolean :jboolean) :jboolean)

(java::def-atj-main-function-type test-boolean-ior
                                  (:jboolean :jboolean) :jboolean)

(java::def-atj-main-function-type test-boolean-eq
                                  (:jboolean :jboolean) :jboolean)

(java::def-atj-main-function-type test-boolean-neq
                                  (:jboolean :jboolean) :jboolean)

(java::def-atj-main-function-type test-int-plus (:jint) :jint)

(java::def-atj-main-function-type test-int-minus (:jint) :jint)

(java::def-atj-main-function-type test-int-not (:jint) :jint)

(java::def-atj-main-function-type test-int-add (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-sub (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-mul (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-div (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-rem (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-and (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-xor (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-ior (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-eq (:jint :jint) :jboolean)

(java::def-atj-main-function-type test-int-neq (:jint :jint) :jboolean)

(java::def-atj-main-function-type test-int-less (:jint :jint) :jboolean)

(java::def-atj-main-function-type test-int-lesseq (:jint :jint) :jboolean)

(java::def-atj-main-function-type test-int-great (:jint :jint) :jboolean)

(java::def-atj-main-function-type test-int-greateq (:jint :jint) :jboolean)

(java::def-atj-main-function-type test-int-int-shiftl (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-int-shiftr (:jint :jint) :jint)

(java::def-atj-main-function-type test-int-int-ushiftr (:jint :jint) :jint)

(java::def-atj-main-function-type f-boolean
                                  (:jboolean :jboolean) :jboolean)

(java::def-atj-main-function-type g-boolean
                                  (:jboolean :jboolean :jboolean) :jboolean)

(java::def-atj-main-function-type f-int (:jint :jint) :jint)

(java::def-atj-main-function-type g-int (:jint :jint :jint) :jint)

(java::def-atj-main-function-type h-int (:jint) :jint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the tested functions, with testing code.

(java::atj test-boolean-not
           test-boolean-and
           test-boolean-xor
           test-boolean-ior
           test-boolean-eq
           test-boolean-neq
           test-int-plus
           test-int-minus
           test-int-not
           test-int-add
           test-int-sub
           test-int-mul
           test-int-div
           test-int-rem
           test-int-and
           test-int-xor
           test-int-ior
           test-int-eq
           test-int-neq
           test-int-less
           test-int-lesseq
           test-int-great
           test-int-greateq
           test-int-int-shiftl
           test-int-int-shiftr
           test-int-int-ushiftr
           f-boolean
           g-boolean
           f-int
           g-int
           h-int
           :deep nil
           :guards t
           :java-class "PrimitivesShallowGuarded"
           :tests *shallow-guarded-tests*)
