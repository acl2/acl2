; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is the unsigned version of acl2::the-fixnum.
(defmacro the-u-fixnum (n)
  (list 'the *u-fixnum-type* n))

;; Recognizes values of type acl2::*fixnum-type*. The bounds are written with
;; acl2::fixnum-bound, which expands to a literal, so that the compiler sees
;; constant comparisons and can derive the fixnum type.
(define fixnump (x)
  :returns (yes/no booleanp)
  (and (integerp x)
       (<= (- -1 (acl2::fixnum-bound)) x)
       (<= x (acl2::fixnum-bound)))
  :inline t)

(defrule fixnump-compound-recognizer
  (implies (fixnump x)
           (integerp x))
  :rule-classes :compound-recognizer
  :enable fixnump)

(defrule signed-byte-p-when-fixnump
  (implies (fixnump x)
           (signed-byte-p *fixnum-bits* x))
  :enable fixnump)
