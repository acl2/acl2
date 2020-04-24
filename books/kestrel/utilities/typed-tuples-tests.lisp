; Typed Tuples -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "typed-tuples")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (typed-tuplep))

(assert! (typed-tuplep nil))

(assert! (not (typed-tuplep t)))

(assert! (not (typed-tuplep #\a)))

(assert! (not (typed-tuplep '(1 2 3))))

(assert! (typed-tuplep natp '(3)))

(assert! (not (typed-tuplep natp 3)))

(assert! (typed-tuplep stringp rationalp characterp '("ab" 3/4 #\1)))

(assert! (not (typed-tuplep stringp rationalp '(3/4 "ab"))))

(assert! (typed-tuplep (lambda (x) (unsigned-byte-p 8 x)) integerp '(55 -2)))

(assert! (not (typed-tuplep (lambda (x) (unsigned-byte-p 8 x)) '(1 1))))

(assert! (booleanp (typed-tuplep (lambda (x) (member-eq x '(a b c))) 'a)))
