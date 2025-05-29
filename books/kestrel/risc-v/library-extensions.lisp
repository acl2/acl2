; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled integerp-of-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (+ x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled integerp-of-*
  (implies (and (integerp x)
                (integerp y))
           (integerp (* x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled integerp-of-unary-minus
  (implies (integerp x)
           (integerp (- x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule loghead-of-ifix
  (equal (loghead size (ifix i))
         (loghead size i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logext-of-ifix
  (equal (logext size (ifix i))
         (logext size i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logext-of-loghead-same-pos-size
  (implies (posp size)
           (equal (logext size (loghead size i))
                  (logext size i)))
  :enable (ifix
           nfix
           fix
           logbitp
           oddp
           evenp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logext-smaller-of-loghead-larger
  (implies (and (posp size)
                (posp size1)
                (< size1 size))
           (equal (logext size1 (loghead size i))
                  (logext size1 i)))
  :enable (logbitp
           oddp
           evenp
           ifix
           nfix
           fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable loghead logext))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun logappn-fn (args)
  (cond ((endp args) 0)
        ((endp (cdr args)) 0)
        (t `(logapp ,(car args) ,(cadr args) ,(logappn-fn (cddr args))))))

(defmacro logappn (&rest args)
  (logappn-fn args))
