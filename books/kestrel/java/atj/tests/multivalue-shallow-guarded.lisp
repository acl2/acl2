; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "multivalue")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types for the multi-value ACL2 functions.

(java::atj-main-function-type add-sub
                              (:ainteger :ainteger)
                              (:ainteger :ainteger))

(java::atj-main-function-type diff-types
                              (:acharacter)
                              (:ainteger :astring :acharacter))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the multi-value ACL2 functions.

(java::atj add-sub
           diff-types
           :deep nil
           :guards t
           :java-class "MultivalueShallowGuarded"
           :tests *tests*)
