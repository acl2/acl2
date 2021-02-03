; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "if-tree-leaf-terms")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (if-tree-leaf-terms 'x)
              '(x))

(assert-equal (if-tree-leaf-terms '(quote 1))
              '((quote 1)))

(assert-equal (if-tree-leaf-terms '(f x y))
              '((f x y)))

(assert-equal (if-tree-leaf-terms '(if a b c))
              '(b c))

(assert-equal (if-tree-leaf-terms '(if (if x y z) b c))
              '(b c))

(assert-equal (if-tree-leaf-terms '(if a (if x y z) c))
              '(y z c))

(assert-equal (if-tree-leaf-terms '(if a (if x y z) c))
              '(y z c))
