; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "type-macros")

(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)
(include-book "kestrel/bv-lists/bvchop-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file proves and records ATJ types (see the file types.lisp)
; for some ACL2 functions in the BV library; more can be added as needed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primary types:

(atj-main-function-type
 acl2::bvcat (:ainteger :ainteger :ainteger :ainteger) :ainteger)

(atj-main-function-type acl2::bvchop (:ainteger :ainteger) :ainteger)

(atj-main-function-type acl2::bvchop-list (:ainteger :avalue) :avalue)

(atj-main-function-type acl2::bvchop-list-exec (:ainteger :avalue) :avalue)

(atj-main-function-type acl2::slice (:ainteger :ainteger :ainteger) :ainteger)
