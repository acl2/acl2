; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "keyword-to-keyword-value-list-alistp")

(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (keyword-to-keyword-value-list-alistp nil))

(assert! (keyword-to-keyword-value-list-alistp '((:a . nil))))

(assert! (keyword-to-keyword-value-list-alistp '((:a . (:x 3 :y #\c :z "abc"))
                                                 (:b . nil)
                                                 (:c . (:kwd (1 2 3))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (keyword-to-keyword-value-list-alistp 3)))

(assert! (not (keyword-to-keyword-value-list-alistp '(3))))

(assert! (not (keyword-to-keyword-value-list-alistp '((:x . nil) (x . nil)))))

(assert! (not (keyword-to-keyword-value-list-alistp
               '((:xx . (:a "yy" :b :b))
                 (:yy . (:k 23 6 :j (1 (2 3))))))))
