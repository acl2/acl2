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

(include-book "../atj" :ttags (:open-output-channel! :oslib :quicklisp :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the functions that manipulate Java primitive values.

(java::atj test-boolean-value
           test-char-value
           test-byte-value
           test-short-value
           test-int-value
           test-long-value
           test-boolean-value->bool
           test-char-value->nat
           test-byte-value->int
           test-short-value->int
           test-int-value->int
           test-long-value->int
           test-boolean-not
           test-int-plus
           test-long-plus
           test-int-minus
           test-long-minus
           test-int-not
           test-long-not
           test-boolean-and
           test-boolean-xor
           test-boolean-ior
           test-boolean-eq
           test-boolean-neq
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
           f-conv
           factorial-int
           factorial-long
           :deep t
           :guards t
           :java-class "PrimitivesDeepGuarded")
