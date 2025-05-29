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
(include-book "kestrel/fty/sbyte32" :dir :system)
(include-book "kestrel/fty/sbyte64" :dir :system)
(include-book "kestrel/fty/ubyte3" :dir :system)
(include-book "kestrel/fty/ubyte5" :dir :system)
(include-book "kestrel/fty/ubyte6" :dir :system)
(include-book "kestrel/fty/ubyte7" :dir :system)
(include-book "kestrel/fty/ubyte8" :dir :system)
(include-book "kestrel/fty/ubyte16" :dir :system)
(include-book "kestrel/fty/ubyte32" :dir :system)
(include-book "kestrel/fty/ubyte64" :dir :system)

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

(defrule ubyte5p-of-loghead-of-5
  (ubyte5p (loghead 5 x))
  :enable ubyte5p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ubyte6p-of-loghead-of-6
  (ubyte6p (loghead 6 x))
  :enable ubyte6p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ubyte8p-of-loghead-of-8
  (ubyte8p (loghead 8 x))
  :enable ubyte8p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ubyte16p-of-loghead-of-16
  (ubyte16p (loghead 16 x))
  :enable ubyte16p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ubyte32p-of-loghead-of-32
  (ubyte32p (loghead 32 x))
  :enable ubyte32p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule ubyte64p-of-loghead-of-64
  (ubyte64p (loghead 64 x))
  :enable ubyte64p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule sbyte32p-of-logext-of-32
  (sbyte32p (logext 32 x))
  :enable sbyte32p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule sbyte64p-of-logext-of-64
  (sbyte64p (logext 64 x))
  :enable sbyte64p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule loghead-3-of-ubyte3
  (implies (ubyte3p x)
           (equal (loghead 3 x)
                  x))
  :enable ubyte3p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule loghead-7-of-ubyte7
  (implies (ubyte7p x)
           (equal (loghead 7 x)
                  x))
  :enable ubyte7p)

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
