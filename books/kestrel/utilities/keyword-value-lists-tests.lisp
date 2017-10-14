; Keyword-Value Lists -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "keyword-value-lists")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (keyword-value-list-to-alist nil) nil)

(assert-equal (keyword-value-list-to-alist '(:one 1 :two 2 :three 3))
              '((:one . 1) (:two . 2) (:three . 3)))

(assert-equal (keyword-value-list-to-alist '(:one 1 :one 2 :three 3))
              '((:one . 1) (:one . 2) (:three . 3)))

(assert-equal (keyword-value-list-to-alist '(:x :abc :y #\9))
              '((:x . :abc) (:y . #\9)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (strip-keywords nil) nil)

(assert-equal (strip-keywords '(:one 1 :two 2 :three 3))
              '(:one :two :three))

(assert-equal (strip-keywords '(:one 1 :one 2 :three 3))
              '(:one :one :three))

(assert-equal (strip-keywords '(:x :abc :y #\9))
              '(:x :y))
