; Keyword-Value Lists -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "keyword-value-lists")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (keyword-value-list-to-alist nil) nil)

(assert-equal (keyword-value-list-to-alist '(:one 1 :two 2 :three 3))
              '((:one . 1) (:two . 2) (:three . 3)))

(assert-equal (keyword-value-list-to-alist '(:one 1 :one 2 :three 3))
              '((:one . 1) (:one . 2) (:three . 3)))

(assert-equal (keyword-value-list-to-alist '(:x :abc :y #\9))
              '((:x . :abc) (:y . #\9)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (make-keyword-value-list-from-keys-and-value nil 255) nil)

(assert-equal (make-keyword-value-list-from-keys-and-value '(:one) "aaa")
              '(:one "aaa"))

(assert-equal (make-keyword-value-list-from-keys-and-value '(:a :b) '(1 2 3))
              '(:a (1 2 3) :b (1 2 3)))
