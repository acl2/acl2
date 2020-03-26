; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for (atj-main-function-type < ...) in ACL2(r):
; cert_param: (non-acl2r)

(include-book "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file proves and records ATJ types (see the file types.lisp)
; for the ACL2 functions that are implemented natively in AIJ.
; We exclude BAD-ATOM<= because its guard is not satisfied by any ATJ type
; (or by any constructible ACL2 value).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primary types:

(atj-main-function-type acl2-numberp (:avalue) :asymbol)

(atj-main-function-type binary-* (:anumber :anumber) :anumber)

(atj-main-function-type binary-+ (:anumber :anumber) :anumber)

(atj-main-function-type unary-- (:anumber) :anumber)

(atj-main-function-type unary-/ (:anumber) :anumber)

(atj-main-function-type < (:arational :arational) :asymbol)

(atj-main-function-type car (:avalue) :avalue)

(atj-main-function-type cdr (:avalue) :avalue)

(atj-main-function-type char-code (:acharacter) :ainteger)

(atj-main-function-type characterp (:avalue) :asymbol)

(atj-main-function-type code-char (:ainteger) :acharacter)

(atj-main-function-type complex (:arational :arational) :anumber)

(atj-main-function-type complex-rationalp (:avalue) :asymbol)

(atj-main-function-type coerce (:avalue :asymbol) :avalue)

(atj-main-function-type cons (:avalue :avalue) :acons)

(atj-main-function-type consp (:avalue) :asymbol)

(atj-main-function-type denominator (:arational) :ainteger)

(atj-main-function-type equal (:avalue :avalue) :asymbol)

(atj-main-function-type if (:avalue :avalue :avalue) :avalue)

(atj-main-function-type imagpart (:anumber) :arational)

(atj-main-function-type integerp (:avalue) :asymbol)

(atj-main-function-type intern-in-package-of-symbol
                        (:astring :asymbol)
                        :asymbol)

(atj-main-function-type numerator (:arational) :ainteger)

(atj-main-function-type pkg-imports (:astring) :avalue)

(atj-main-function-type pkg-witness (:astring) :asymbol)

(atj-main-function-type rationalp (:avalue) :asymbol)

(atj-main-function-type realpart (:anumber) :arational)

(atj-main-function-type stringp (:avalue) :asymbol)

(atj-main-function-type symbol-name (:asymbol) :astring)

(atj-main-function-type symbol-package-name (:asymbol) :astring)

(atj-main-function-type symbolp (:avalue) :asymbol)

(atj-main-function-type nonnegative-integer-quotient
                        (:ainteger :ainteger)
                        :ainteger)

(atj-main-function-type string-append (:astring :astring) :astring)

(atj-main-function-type len (:avalue) :ainteger)

; secondary types:

(atj-other-function-type binary-+ (:arational :arational) :arational)
(atj-other-function-type binary-+ (:ainteger :ainteger) :ainteger)

(atj-other-function-type binary-* (:arational :arational) :arational)
(atj-other-function-type binary-* (:ainteger :ainteger) :ainteger)

(atj-other-function-type unary-- (:arational) :arational)
(atj-other-function-type unary-- (:ainteger) :ainteger)

(atj-other-function-type unary-/ (:arational) :arational)
