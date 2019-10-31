; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; Avoid failure for (def-atj-main-function-type < ...) in ACL2(r):
; cert_param: (non-acl2r)

(include-book "types")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file proves and records ATJ types (see the file types.lisp)
; for the ACL2 functions that are implemented natively in AIJ.
; Currently these are all the ACL2 primitive functions (see :DOC PRIMITIVE),
; except for BAD-ATOM<= because its guard is not satisfied by any ATJ type
; (or by any constructible ACL2 value).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primary types:

(def-atj-main-function-type acl2-numberp (:avalue) :asymbol)

(def-atj-main-function-type binary-* (:anumber :anumber) :anumber)

(def-atj-main-function-type binary-+ (:anumber :anumber) :anumber)

(def-atj-main-function-type unary-- (:anumber) :anumber)

(def-atj-main-function-type unary-/ (:anumber) :anumber)

(def-atj-main-function-type < (:arational :arational) :asymbol)

(def-atj-main-function-type car (:avalue) :avalue)

(def-atj-main-function-type cdr (:avalue) :avalue)

(def-atj-main-function-type char-code (:acharacter) :ainteger)

(def-atj-main-function-type characterp (:avalue) :asymbol)

(def-atj-main-function-type code-char (:ainteger) :acharacter)

(def-atj-main-function-type complex (:arational :arational) :anumber)

(def-atj-main-function-type complex-rationalp (:avalue) :asymbol)

(def-atj-main-function-type coerce (:avalue :asymbol) :avalue)

(def-atj-main-function-type cons (:avalue :avalue) :acons)

(def-atj-main-function-type consp (:avalue) :asymbol)

(def-atj-main-function-type denominator (:arational) :ainteger)

(def-atj-main-function-type equal (:avalue :avalue) :asymbol)

(def-atj-main-function-type if (:avalue :avalue :avalue) :avalue)

(def-atj-main-function-type imagpart (:anumber) :arational)

(def-atj-main-function-type integerp (:avalue) :asymbol)

(def-atj-main-function-type intern-in-package-of-symbol
  (:astring :asymbol) :asymbol)

(def-atj-main-function-type numerator (:arational) :ainteger)

(def-atj-main-function-type pkg-imports (:astring) :avalue)

(def-atj-main-function-type pkg-witness (:astring) :asymbol)

(def-atj-main-function-type rationalp (:avalue) :asymbol)

(def-atj-main-function-type realpart (:anumber) :arational)

(def-atj-main-function-type stringp (:avalue) :asymbol)

(def-atj-main-function-type symbol-name (:asymbol) :astring)

(def-atj-main-function-type symbol-package-name (:asymbol) :astring)

(def-atj-main-function-type symbolp (:avalue) :asymbol)

; secondary types:

; (these are temporarily commented out
; while support for generating overloaded methods is being added)

;; (def-atj-other-function-type binary-+ (:arational :arational) :arational)
;; (def-atj-other-function-type binary-+ (:ainteger :ainteger) :ainteger)

;; (def-atj-other-function-type binary-* (:arational :arational) :arational)
;; (def-atj-other-function-type binary-* (:ainteger :ainteger) :ainteger)

;; (def-atj-other-function-type unary-- (:arational) :arational)
;; (def-atj-other-function-type unary-- (:ainteger) :ainteger)
