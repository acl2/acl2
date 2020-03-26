; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "apply-fn-into-ifs")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (apply-fn-into-ifs 'f 'var) '(f var))

(assert-equal (apply-fn-into-ifs 'f '(quote :const)) '(f ':const))

(assert-equal (apply-fn-into-ifs 'f '(g x y)) '(f (g x y)))

(assert-equal (apply-fn-into-ifs 'f '(if a b c)) '(if a (f b) (f c)))

(assert-equal (apply-fn-into-ifs 'f '(if a (if b c d) e))
              '(if a (if b (f c) (f d)) (f e)))
