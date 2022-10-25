; Standard System Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "term-guard-obligation")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (term-guard-obligation 'x t state)
              ''t)

(assert-equal (term-guard-obligation 'x :limited state)
              ''t)

(assert-equal (term-guard-obligation '(binary-+ x '4) t state)
              '(acl2-numberp x))

(assert-equal (term-guard-obligation '(binary-+ x '4) :limited state)
              '(acl2-numberp x))

(assert-equal (term-guard-obligation '(< (len x) '17) t state)
              ''t)

(assert-equal (term-guard-obligation '(< (len x) '17) :limited state)
              '(rationalp (len x)))
