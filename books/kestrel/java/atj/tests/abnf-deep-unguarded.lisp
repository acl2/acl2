; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "abnf")

(include-book "../atj" :ttags (:open-output-channel! :oslib :quicklisp :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the parser, without tests.
; Currently, attempting to generate tests
; for the grammar files ./abnf-files/*.txt
; results in Java code whose test methods are too large to compile
; (they exceed the maximum size allowed by the JVM),
; because the contents of those files are built as lists of natural numbers.
; Thus, for now we have handwritten Java files to test the ABNF parser.

(java::atj parse-grammar
           :deep t
           :guards nil
           :java-class "ABNFDeepUnguarded")
