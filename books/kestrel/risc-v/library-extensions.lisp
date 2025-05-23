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
(include-book "kestrel/fty/ubyte5" :dir :system)
(include-book "kestrel/fty/ubyte6" :dir :system)
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

(defrule loghead-of-ifix
  (equal (loghead size (ifix i))
         (loghead size i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logext-of-ifix
  (equal (logext size (ifix i))
         (logext size i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable loghead logext))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun logappn-fn (args)
  (cond ((endp args) 0)
        ((endp (cdr args)) 0)
        (t `(logapp ,(car args) ,(cadr args) ,(logappn-fn (cddr args))))))

(defmacro logappn (&rest args)
  (logappn-fn args))
