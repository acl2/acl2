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
(include-book "std/basic/arith-equiv-defs" :dir :system)
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

(defrule bitp-of-bool->bit
  (bitp (bool->bit x)))

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

(defruled loghead-of-1-when-bitp
  (implies (bitp b)
           (equal (loghead 1 b)
                  b))
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logapp-1-of-bool->bit-logbitp-and-logtail
  (implies (and (natp i)
                (equal j (1+ i))
                (integerp x))
           (equal (logapp 1 (bool->bit (logbitp i x)) (logtail j x))
                  (logtail i x)))
  :cases ((logbitp i x))
  :enable (logtail
           logapp
           logbitp
           ifix
           fix
           oddp
           evenp)
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)
               (include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logapp-m-of-logtail-n-and-logtail-p-when-p-is-m+n
  (implies (and (natp m)
                (natp n)
                (natp p)
                (equal p (+ m n)))
           (equal (logapp m (logtail n x) (logtail p x))
                  (logtail n x)))
  :enable (logapp
           logtail
           loghead
           ifix)
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)
               (include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logapp-m-of-bound-logtail-n-and-logtail-p-when-p-is-m+n
  (implies (and (equal bound (loghead m (logtail n x)))
                (natp m)
                (natp n)
                (natp p)
                (equal p (+ m n)))
           (equal (logapp m bound (logtail p x))
                  (logtail n x)))
  :use logapp-m-of-logtail-n-and-logtail-p-when-p-is-m+n
  :disable logapp-m-of-logtail-n-and-logtail-p-when-p-is-m+n
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)
               (include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logapp-m-of-logtail-n-and-bound-logtail-p-when-p-is-m+n
  (implies (and (equal bound (logtail p x))
                (natp m)
                (natp n)
                (natp p)
                (equal p (+ m n)))
           (equal (logapp m (logtail n x) bound)
                  (logtail n x)))
  :use logapp-m-of-logtail-n-and-logtail-p-when-p-is-m+n
  :disable logapp-m-of-logtail-n-and-logtail-p-when-p-is-m+n
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)
               (include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule bool->bit-logbitp-to-logtail-when-unsigned-byte-p
  (implies (unsigned-byte-p (1+ size) x)
           (equal (bool->bit (logbitp size x))
                  (logtail size x)))
  :enable (logtail
           bool->bit
           logbitp
           unsigned-byte-p
           nfix)
  :prep-books ((include-book "centaur/bitops/ihsext-basics" :dir :system)
               (include-book "arithmetic-5/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule unsigned-byte-p-size-when-logtail-size-is-zero
  (implies (and (integerp x)
                (posp size)
                (equal (logtail size x) 0))
           (unsigned-byte-p size x))
  :enable (unsigned-byte-p
           integer-range-p
           logtail)
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule logapp-of-bound-loghead-n-and-logtail
  (implies (equal bound (loghead n x))
           (equal (logapp n bound (logtail n x))
                  (ifix x)))
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable loghead logext))
