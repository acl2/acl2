; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fibonacci")

(include-book "../atj" :ttags (:open-output-channel! :oslib :quicklisp :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of the Fibonacci function.

(java::atj-main-function-type fib (:ainteger) :ainteger)

(java::atj-main-function-type fib-tail
                              (:ainteger :ainteger :ainteger)
                              :ainteger)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the Fibonacci function, with testing code.

(java::atj fib
           fib-tail
           :deep nil
           :guards t
           :java-class "FibonacciShallowGuarded"
           :tests *fib-tests*)
