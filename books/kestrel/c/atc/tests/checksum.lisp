; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "atc" :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!)))

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
                                   :in-theory (enable sbyte32p
                                                      sbyte32-fix
                                                      c::sintp
                                                      c::sint-add-okp
                                                      c::sint-shl-sint-okp
                                                      c::sint-add
                                                      c::sint-shl-sint
                                                      c::sint-bitand
                                                      c::sint->get)))))
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
