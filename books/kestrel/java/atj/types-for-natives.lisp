; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file proves and records ATJ types (see the file types.lisp)
; for the ACL2 functions that are implemented natively in AIJ.
; Currently these are all the ACL2 primitive functions (see :DOC PRIMITIVE),
; except for BAD-ATOM<= because its guard is not satisfied by any ATJ type
; (or by any constructible ACL2 value).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atj-function-type acl2-numberp (:value) :symbol)

(def-atj-function-type binary-* (:number :number) :number)

(def-atj-function-type binary-+ (:number :number) :number)

(def-atj-function-type unary-- (:number) :number)

(def-atj-function-type unary-/ (:number) :number)

(def-atj-function-type < (:number :number) :symbol)

(def-atj-function-type car (:value) :value)

(def-atj-function-type cdr (:value) :value)

(def-atj-function-type char-code (:character) :number)

(def-atj-function-type characterp (:value) :symbol)

(def-atj-function-type code-char (:number) :character)

(def-atj-function-type complex (:number :number) :number)

(def-atj-function-type complex-rationalp (:value) :symbol)

(def-atj-function-type coerce (:value :symbol) :value)

(def-atj-function-type cons (:value :value) :value)

(def-atj-function-type consp (:value) :symbol)

(def-atj-function-type denominator (:number) :number)

(def-atj-function-type equal (:value :value) :symbol)

(def-atj-function-type if (:value :value :value) :value)

(def-atj-function-type imagpart (:number) :number)

(def-atj-function-type integerp (:value) :symbol)

(def-atj-function-type intern-in-package-of-symbol (:string :symbol) :symbol)

(def-atj-function-type numerator (:number) :number)

(def-atj-function-type pkg-imports (:string) :value)

(def-atj-function-type pkg-witness (:string) :symbol)

(def-atj-function-type rationalp (:value) :symbol)

(def-atj-function-type realpart (:number) :number)

(def-atj-function-type stringp (:value) :symbol)

(def-atj-function-type symbol-name (:symbol) :string)

(def-atj-function-type symbol-package-name (:symbol) :string)

(def-atj-function-type symbolp (:value) :symbol)
