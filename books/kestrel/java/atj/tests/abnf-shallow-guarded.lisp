; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
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

(java::def-atj-function-type char-fix$inline (:value) :character)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize the input and output types of some of the ABNF parser's functions.

(java::def-atj-function-type downcase$inline (:character) :character)

(java::def-atj-function-type upcase$inline (:character) :character)

(java::def-atj-function-type nat-match-insensitive-char-p
                             (:integer :character)
                             :symbol)

(java::def-atj-function-type parse-exact (:integer :value) :value)

(java::def-atj-function-type parse-in-range (:integer :integer :value) :value)

(java::def-atj-function-type parse-in-either-range
                             (:integer :integer :integer :integer :value)
                             :value)

(java::def-atj-function-type parse-*-in-either-range
                             (:integer :integer :integer :integer :value)
                             :value)

(java::def-atj-function-type parse-ichar (:character :value) :value)

(java::def-atj-function-type parse-ichars (:character :character :value) :value)

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
