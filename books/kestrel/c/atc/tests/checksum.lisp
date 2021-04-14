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
; For now we use C int values because this is what C currently supports,
; and we use guards to constrain
; the current checksum to be 16 bits,
; the high byte to be 8 bits, and
; the low byte to be 8 bits.
; When ATC supports additional integer types,
; we will change this example, or create a new one,
; that uses unsigned types of the appropriate sizes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (set-default-hints '((nonlinearp-default-hint
                         stable-under-simplificationp
                         hist
                         pspv))))

  (defun |checksum| (|current| |hibyte| |lobyte|)
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
                                                      c::sint-add-okp
                                                      c::sint-shl-sint-okp
                                                      c::sint-shl-okp
                                                      c::sint-add
                                                      c::sint-shl-sint
                                                      c::sint-shl
                                                      c::sint-bitand
                                                      (:e c::sint-max))))))
    (c::sint-bitand (c::sint-add |current|
                                 (c::sint-add (c::sint-shl-sint |hibyte|
                                                                (c::sint-const
                                                                 8))
                                              |lobyte|))
                    (c::sint-const 65535))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |checksum| :output-file "checksum.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o checksum checksum.c checksum-test.c
  ./checksum

|#
