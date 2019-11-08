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
           f-boolean
           g-boolean
           f-int
           g-int
           h-int
           f-long
           g-long
           h-long
           :deep t
           :guards t
           :java-class "PrimitivesDeepGuarded")
