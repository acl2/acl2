; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../atj" :ttags ((:open-output-channel!) (:oslib) (:quicklisp) :quicklisp.osicat))

(include-book "kestrel/abnf/parser" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file tests the (verified) ABNF grammar parser in the ABNF library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize input and output types, for shallow embedding with guards.

(java::atj-main-function-type char-fix$inline
                              (:avalue)
                              :acharacter)

(java::atj-main-function-type str::downcase-char$inline
                              (:acharacter)
                              :acharacter)

(java::atj-main-function-type str::upcase-char$inline
                              (:acharacter)
                              :acharacter)

(java::atj-main-function-type abnf::nat-match-insensitive-char-p
                              (:ainteger :acharacter)
                              :aboolean)

(java::atj-main-function-type abnf::parse-exact
                              (:ainteger :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type abnf::parse-in-range
                              (:ainteger :ainteger :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type abnf::parse-in-either-range
                              (:ainteger
                               :ainteger
                               :ainteger
                               :ainteger
                               :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type abnf::parse-*-in-either-range
                              (:ainteger
                               :ainteger
                               :ainteger
                               :ainteger
                               :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type abnf::parse-ichar
                              (:acharacter :avalue)
                              (:avalue :avalue :avalue))

(java::atj-main-function-type abnf::parse-ichar2
                              (:acharacter :acharacter :avalue)
                              (:avalue :avalue :avalue))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code, assuming guards, and without tests.

; Since PARSE-ANY fixes its input to NAT-LISTP (via MBE),
; Java code generated not assuming guards would be unduly slow.
; So we only generate Java code assuming guards.

; Currently, attempting to generate tests
; for grammar file of reasonable size
; results in Java code whose test methods are too large to compile
; (they exceed the maximum size allowed by the JVM),
; because the contents of those files are built as lists of natural numbers.
; Thus, for now we have handwritten Java files to test the ABNF parser.

(java::atj abnf::parse-grammar
           :deep t
           :guards t
           :java-class "ABNFDeepGuarded")

(java::atj abnf::parse-grammar
           :deep nil
           :guards t
           :java-class "ABNFShallowGuarded")
