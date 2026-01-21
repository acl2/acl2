; Standard System Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-ruler-extenders-plus")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (get-ruler-extenders+ 'len (w state)) *basic-ruler-extenders*)

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders (cons)))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (get-ruler-extenders+ 'f (w state)) '(cons)))

(must-succeed*
 (defun f (x)
   (declare (xargs :ruler-extenders :all))
   (cons 3
         (if (consp x)
             (f (cdr x))
           nil)))
 (assert-equal (get-ruler-extenders+ 'f (w state)) :all))

(must-succeed*
 (defun fact (n)
   (declare (xargs :ruler-extenders (:lambdas)))
   (the (integer 1 *)
        (if (posp n)
            (* n (fact (1- n)))
          1)))
 (assert-equal (get-ruler-extenders+ 'fact (w state)) '(:lambdas)))
