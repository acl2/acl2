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

; A modular factorial.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (local (include-book "arithmetic-3/top" :dir :system))
  (defun |f$loop| (|n| |r|)
    (declare (xargs :guard (and (c::uintp |n|)
                                (c::uintp |r|))
                    :guard-hints (("Goal" :in-theory (enable c::declar
                                                             c::assign)))
                    :measure (c::uint->get |n|)
                    :hints (("Goal" :in-theory (enable c::assign
                                                       c::ne-uint-uint
                                                       c::sub-uint-uint
                                                       c::uint-integer-fix
                                                       c::uint-mod)))))
    (if (c::boolean-from-sint (c::ne-uint-uint |n| (c::uint-dec-const 0)))
        (let* ((|r| (c::assign (c::mul-uint-uint |r| |n|)))
               (|n| (c::assign (c::sub-uint-uint |n| (c::uint-dec-const 1)))))
          (|f$loop| |n| |r|))
      (mv |n| |r|))))

(encapsulate
  ()
  (set-ignore-ok t)
  (defun |f| (|n|)
    (declare (xargs :guard (c::uintp |n|)))
    (let ((|r| (c::declar (c::uint-dec-const 1))))
      (mv-let (|n| |r|)
        (|f$loop| |n| |r|)
        |r|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |f$loop| |f| :output-file "loops.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o loops loops.c loops-test.c
  ./f

|#
