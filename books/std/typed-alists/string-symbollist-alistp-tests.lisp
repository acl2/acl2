; Standard Typed Alists Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "string-symbollist-alistp")

(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (string-symbollist-alistp nil))

(assert! (string-symbollist-alistp '(("AZ" . nil) ("" . (x y)))))

(assert! (not (string-symbollist-alistp #c(1 1))))

(assert! (not (string-symbollist-alistp '("a" (b)))))

(assert! (not (string-symbollist-alistp '(("a" . (b)) (3 . nil)))))

(assert! (not (string-symbollist-alistp '(("a" . (b)) ("str" . ("s" "t"))))))
