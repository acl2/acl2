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

; Generate Java code for the functions that manipulate Java primitive values.
; Generation of testing code is not supported yet.

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
           :deep t
           :guards nil
           :java-class "PrimitivesDeepUnguarded")
