; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "measured-subset-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (measured-subset+ 'len (w state)) '(x))

(assert-equal (measured-subset+ 'binary-append (w state)) '(x))

(must-succeed*
 (defun f (x)
   (declare (xargs :measure (nfix (- 10 x))))
   (if (and (natp x) (< x 10))
       (f (1+ x))
     nil))
 (assert-equal (measured-subset+ 'f (w state)) '(x)))

(must-succeed*
 (defun f (x y z)
   (declare (xargs :measure (nfix (- 10 y))))
   (if (and (natp y) (< y 10))
       (f x (1+ y) z)
     (cons x z)))
 (assert-equal (measured-subset+ 'f (w state)) '(y)))
