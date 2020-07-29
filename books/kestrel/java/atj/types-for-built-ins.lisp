; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "types-for-natives")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file proves and records ATJ types (see the file types.lisp)
; for some ACL2 built-in functions that are not implemented natively in Java;
; more can be added as needed.
; ATJ types for the ACL2 functions that are implemented natively in Java
; are in types-for-natives.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; primary types:

(atj-main-function-type = (:anumber :anumber) :aboolean)

(atj-main-function-type ash (:ainteger :ainteger) :ainteger)

(atj-main-function-type atom (:avalue) :aboolean)

(atj-main-function-type acl2::binary-logand (:ainteger :ainteger) :ainteger)

(atj-main-function-type acl2::binary-logior (:ainteger :ainteger) :ainteger)

(atj-main-function-type endp (:avalue) :aboolean)

(atj-main-function-type eq (:avalue :avalue) :aboolean)

(atj-main-function-type eql (:avalue :avalue) :aboolean)

(atj-main-function-type evenp (:ainteger) :aboolean)

(atj-main-function-type expt (:anumber :ainteger) :anumber)

(atj-main-function-type first-n-ac (:ainteger :avalue :avalue) :avalue)

(atj-main-function-type fix (:avalue) :anumber)

(atj-main-function-type floor (:arational :arational) :ainteger)

(atj-main-function-type ifix (:avalue) :ainteger)

(atj-main-function-type integer-length (:ainteger) :ainteger)

(atj-main-function-type integer-range-p (:ainteger :ainteger :avalue) :aboolean)

(atj-main-function-type lognot (:ainteger) :ainteger)

(atj-main-function-type max (:arational :arational) :arational)

(atj-main-function-type min (:arational :arational) :arational)

(atj-main-function-type mod (:arational :arational) :arational)

(atj-main-function-type mv-nth (:ainteger :avalue) :avalue)

(atj-main-function-type nfix (:avalue) :ainteger)

(atj-main-function-type not (:avalue) :aboolean)

(atj-main-function-type nth (:ainteger :avalue) :avalue)

(atj-main-function-type null (:avalue) :aboolean)

(atj-main-function-type signed-byte-p (:avalue :avalue) :aboolean)

(atj-main-function-type take (:ainteger :avalue) :avalue)

(atj-main-function-type unsigned-byte-p (:avalue :avalue) :aboolean)

(atj-main-function-type update-nth (:ainteger :avalue :avalue) :avalue)

(atj-main-function-type zip (:ainteger) :aboolean)

(atj-main-function-type zp (:ainteger) :aboolean)

; secondary types:

(atj-other-function-type max (:ainteger :ainteger) :ainteger)

(atj-other-function-type min (:ainteger :ainteger) :ainteger)

(atj-other-function-type mod (:ainteger :ainteger) :ainteger)

(atj-other-function-type not (:aboolean) :aboolean)
