; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "booleans")

(include-book "../atj" :ttags (:open-output-channel! :oslib :quicklisp :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the factorial functions.

(java::atj-main-function-type negation (:aboolean) :aboolean)

(java::atj-main-function-type conjunction (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type disjunction (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type equality (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type nonequality (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type project1 (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type project2 (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type addition
                              (:aboolean :aboolean)
                              (:aboolean :aboolean))

(java::atj-main-function-type tosymbol (:aboolean) :astring)

(java::atj-main-function-type fromsymbol (:asymbol) :aboolean)

(java::atj-main-function-type tovalue (:aboolean :aboolean) :acons)

(java::atj-main-function-type fromvalue (:avalue) :aboolean)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the functions on ACL2 booleans, with testing code.

(java::atj negation
           conjunction
           disjunction
           equality
           nonequality
           project1
           project2
           addition
           tosymbol
           fromsymbol
           tovalue
           fromvalue
           :deep nil
           :guards t
           :java-class "BooleansShallowGuarded"
           :tests *boolean-tests*)
