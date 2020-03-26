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

(include-book "../types-for-built-ins")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of a library function
; (this should be moved to a more central file, ideally).

(java::atj-main-function-type char-fix$inline (:avalue) :acharacter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of some of the ABNF parser's functions.

(java::atj-main-function-type downcase$inline (:acharacter) :acharacter)

(java::atj-main-function-type upcase$inline (:acharacter) :acharacter)

(java::atj-main-function-type nat-match-insensitive-char-p
                              (:ainteger :acharacter)
                              :asymbol)

(java::atj-main-function-type parse-exact
                              (:ainteger :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type parse-in-range
                              (:ainteger :ainteger :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type parse-in-either-range
                              (:ainteger
                               :ainteger
                               :ainteger
                               :ainteger
                               :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type parse-*-in-either-range
                              (:ainteger
                               :ainteger
                               :ainteger
                               :ainteger
                               :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type parse-ichar
                              (:acharacter :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type parse-ichars
                              (:acharacter :acharacter :avalue)
                              (:avalue :avalue :avalue))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the parser, without tests.
; Currently, attempting to generate tests
; for the grammar files ./abnf-files/*.txt
; results in Java code whose test methods are too large to compile
; (they exceed the maximum size allowed by the JVM),
; because the contents of those files are built as lists of natural numbers.
; Thus, for now we have handwritten Java files to test the ABNF parser.

(java::atj parse-grammar
           :deep nil
           :guards t
           :java-class "ABNFShallowGuarded")
