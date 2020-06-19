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

(include-book "ihs/basic-definitions" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file proves and records ATJ types (see the file types.lisp)
; for some ACL2 functions in the IHS library; more can be added as needed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primary types:

(atj-main-function-type acl2::logapp (:ainteger :ainteger :ainteger) :ainteger)

(atj-main-function-type acl2::loghead$inline (:ainteger :ainteger) :ainteger)

(atj-main-function-type acl2::logtail$inline (:ainteger :ainteger) :ainteger)
