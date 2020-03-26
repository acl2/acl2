; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "keyword-symbol-alistp")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (keyword-symbol-alistp nil))

(assert! (keyword-symbol-alistp '((:a . b))))

(assert! (keyword-symbol-alistp '((:a . x) (:b . y) (:c . z))))

(assert! (keyword-symbol-alistp '((:t . :kwd) (:logic . :program))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (keyword-symbol-alistp 3)))

(assert! (not (keyword-symbol-alistp 55)))

(assert! (not (keyword-symbol-alistp '(3))))

(assert! (not (keyword-symbol-alistp '((:x . y) (2/3 . nil)))))

(assert! (not (keyword-symbol-alistp '((xx . yy) (:a . sym)))))

(assert! (not (keyword-symbol-alistp '((:a . "x") (:b . y)))))

(assert! (not (keyword-symbol-alistp '((:a . x) ("b" . y)))))
