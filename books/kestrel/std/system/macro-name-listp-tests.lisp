; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macro-name-listp")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (macro-name-listp nil (w state)))

(assert! (macro-name-listp '(append + * *) (w state)))

(assert! (not (macro-name-listp '(append binary-+) (w state))))

(must-succeed*
 (defmacro m (x) `(list ,x))
 (defmacro n (x) `(cons ,x ,x))
 (assert! (macro-name-listp '(m n append) (w state))))

(assert! (not (macro-name-listp 33 (w state))))

(assert! (not (macro-name-listp '(1 2 3) (w state))))

(assert! (not (macro-name-listp "ab" (w state))))
