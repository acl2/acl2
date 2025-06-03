; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule loghead-of-ifix
  (equal (loghead size (ifix i))
         (loghead size i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logext-of-ifix
  (equal (logext size (ifix i))
         (logext size i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logext-of-loghead
  (implies (and (posp size)
                (posp size1)
                (<= size1 size))
           (equal (logext size1 (loghead size i))
                  (logext size1 i)))
  :enable (logbitp
           oddp
           evenp
           ifix
           nfix
           fix)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled logext-of-logext-plus-logext
  (equal (logext n (+ (logext n x) (logext n y)))
         (logext n (+ (ifix x) (ifix y))))
  :enable (logext
           loghead
           oddp)
  :prep-books
  ((include-book "kestrel/arithmetic-light/even-and-odd" :dir :system)
   (include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;

(defruled logext-of-logext-minus-logext
  (equal (logext n (- (logext n x) (logext n y)))
         (logext n (- (ifix x) (ifix y))))
  :enable (logext
           loghead
           oddp
           ifix
           logbitp)
  :prep-books
  ((include-book "kestrel/arithmetic-light/even-and-odd" :dir :system)
   (include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled loghead-of-logext-plus-logext
  (equal (loghead n (+ (logext n x) (logext n y)))
         (loghead n (+ (ifix x) (ifix y))))
  :use ((:instance bitops::cancel-logext-under-loghead
                   (x (+ (logext n x)
                         (logext n y)))
                   (m n)
                   (n n))
        (:instance bitops::cancel-logext-under-loghead
                   (x (+ x y))
                   (m n)
                   (n n)))
  :enable logext-of-logext-plus-logext
  :disable bitops::cancel-loghead-under-logext
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)))

;;;;;;;;;;;;;;;;;;;;

(defruled loghead-of-logext-minus-logext
  (equal (loghead n (- (logext n x) (logext n y)))
         (loghead n (- (ifix x) (ifix y))))
  :use ((:instance bitops::cancel-logext-under-loghead
                   (x (- (logext n x)
                         (logext n y)))
                   (m n)
                   (n n))
        (:instance bitops::cancel-logext-under-loghead
                   (x (- x y))
                   (m n)
                   (n n)))
  :enable logext-of-logext-minus-logext
  :disable bitops::cancel-loghead-under-logext
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule loghead-of-1-of-logbit
  (equal (loghead 1 (logbit i x))
         (logbit i x))
  :enable acl2::bool->bit
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable loghead logext))
