; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ruler-extenders-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ruler-extenders+ 'len (w state)) '(mv-list return-last))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders (cons)))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (ruler-extenders+ 'f (w state)) '(cons)))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders :all))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (ruler-extenders+ 'f (w state)) :all))

(must-succeed*
 (defun fact (n)
   (declare (xargs :ruler-extenders (:lambdas)))
   (the (integer 1 *)
        (if (posp n)
            (* n (fact (1- n)))
          1)))
 (assert-equal (ruler-extenders+ 'fact (w state)) '(:lambdas)))
