; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "add-suffix-to-fn-or-const")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (add-suffix-to-fn-or-const 'fn "MORE") 'fnmore)

(assert-equal (add-suffix-to-fn-or-const '*const* "MORE") '*constmore*)

(assert-equal (add-suffix-to-fn-or-const 'std::fn "MORE") 'std::fnmore)

(assert-equal (add-suffix-to-fn-or-const 'std::*const* "MORE") 'std::*constmore*)

(assert-equal (add-suffix-to-fn-or-const 'common-lisp::fn "MORE") 'acl2::fnmore)

(assert-equal (add-suffix-to-fn-or-const 'common-lisp::*const* "MORE")
              'acl2::*constmore*)
