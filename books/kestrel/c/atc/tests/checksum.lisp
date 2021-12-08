; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This example is inspired by a checksum computation,
; where bytes are read in pairs from a byte array,
; each pair is turned into a 16-bit value (with a high byte and a low byte),
; and the latter is added to the current checksum modulo 2^16.

; We have a legacy version of this example that uses C int values,
; which was created when ATC only supported int values.
; In this legacy version, we use guards to constrain
; the current checksum to be 16 bits,
; the high byte to be 8 bits, and
; the low byte to be 8 bits.

; We also have a newer version that uses
; C unsigned char values for the two bytes
; and an unsigned int value for the checksum.
; For generality, we use guards to constrain
; the high byte to be 8 bits and
; the low byte to be 8 bits.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (set-default-hints '((nonlinearp-default-hint
                         stable-under-simplificationp
                         hist
                         pspv))))

  (defrulel sint-max->=-200k
    (>= (c::sint-max) 200000)
    :rule-classes :linear
    :enable (c::sint-max c::int-bits))

  (defun |legacy| (|current| |hibyte| |lobyte|)
    (declare (xargs :guard (and (c::sintp |current|)
                                (c::sintp |hibyte|)
                                (c::sintp |lobyte|)
                                ;; 0 <= current <= 65635:
                                (<= 0 (c::sint->get |current|))
                                (<= (c::sint->get |current|) 65535)
                                ;; 0 <= hibyte <= 255:
                                (<= 0 (c::sint->get |hibyte|))
                                (<= (c::sint->get |hibyte|) 255)
                                ;; 0 <= lobyte <= 255:
                                (<= 0 (c::sint->get |lobyte|))
                                (<= (c::sint->get |lobyte|) 255))
                    :guard-hints (("Goal"
                                   :in-theory (enable c::sint-integerp-alt-def
                                                      c::add-sint-sint-okp
                                                      c::shl-sint-sint-okp
                                                      c::shl-sint-okp
                                                      c::add-sint-sint
                                                      c::shl-sint-sint
                                                      c::shl-sint
                                                      c::bitand-sint-sint)))))
    (c::bitand-sint-sint
     (c::add-sint-sint
      |current|
      (c::add-sint-sint (c::shl-sint-sint |hibyte|
                                          (c::sint-dec-const 8))
                        |lobyte|))
     (c::sint-dec-const 65535))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()

  (defrulel uint-max->=-200k
    (>= (c::uint-max) 200000)
    :rule-classes :linear
    :enable (c::uint-max c::int-bits))

  (defun |checksum| (|current| |hibyte| |lobyte|)
    (declare (xargs :guard (and (c::uintp |current|)
                                (c::ucharp |hibyte|)
                                (c::ucharp |lobyte|)
                                ;; current <= 65635:
                                (<= (c::uint->get |current|) 65535)
                                ;; hibyte <= 255:
                                (<= (c::uchar->get |hibyte|) 255)
                                ;; lobyte <= 255:
                                (<= (c::uchar->get |lobyte|) 255))
                    :guard-hints (("Goal"
                                   :in-theory (enable c::shl-uint-sint-okp
                                                      c::shl-uint-okp)))))
    (c::bitand-uint-uint
     (c::add-uint-uint
      |current|
      (c::add-uint-uint (c::shl-uint-sint (c::uint-from-uchar |hibyte|)
                                          (c::sint-dec-const 8))
                        (c::uint-from-uchar |lobyte|)))
     (c::uint-dec-const 65535))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |legacy| |checksum| :output-file "checksum.c")
