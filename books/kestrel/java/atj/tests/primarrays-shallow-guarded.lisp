; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "primarrays")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the tested functions.

(java::def-atj-main-function-type read-from-array (:jint[] :jint :jint) :jint)

(java::def-atj-main-function-type add-lengths-of-arrays
                                  (:jbyte[] :jshort[]) :jint)

(java::def-atj-main-function-type create-array-of-length (:jbyte) :jchar[])

(java::def-atj-main-function-type create-array-with-components
                                  (:jlong :jlong :jlong) :jlong[])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the tested functions.
; The automatic generation of tests is not supported yet.

(java::atj read-from-array
           add-lengths-of-arrays
           create-array-of-length
           create-array-with-components
           :deep nil
           :guards t
           :java-class "PrimarraysShallowGuarded")
