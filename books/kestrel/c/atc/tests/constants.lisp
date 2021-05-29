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

; Examples of integer constants.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_int_decimal| ()
  (declare (xargs :guard t))
  (c::sint-dec-const 89))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_int_octal| ()
  (declare (xargs :guard t))
  (c::sint-oct-const 255))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_int_hexadecimal| ()
  (declare (xargs :guard t))
  (c::sint-hex-const #xAAAA88))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_int_decimal| ()
  (declare (xargs :guard t))
  (c::uint-dec-const 89))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_int_octal| ()
  (declare (xargs :guard t))
  (c::uint-oct-const 255))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_int_hexadecimal| ()
  (declare (xargs :guard t))
  (c::uint-hex-const #xAAAA88))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_long_decimal| ()
  (declare (xargs :guard t))
  (c::slong-dec-const 89))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_long_octal| ()
  (declare (xargs :guard t))
  (c::slong-oct-const 255))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_long_hexadecimal| ()
  (declare (xargs :guard t))
  (c::slong-hex-const #xAAAA88))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_long_decimal| ()
  (declare (xargs :guard t))
  (c::ulong-dec-const 89))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_long_octal| ()
  (declare (xargs :guard t))
  (c::ulong-oct-const 255))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_long_hexadecimal| ()
  (declare (xargs :guard t))
  (c::ulong-hex-const #xAAAA88))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_long_long_decimal| ()
  (declare (xargs :guard t))
  (c::sllong-dec-const 89))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_long_long_octal| ()
  (declare (xargs :guard t))
  (c::sllong-oct-const 255))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |signed_long_long_hexadecimal| ()
  (declare (xargs :guard t))
  (c::sllong-hex-const #xAAAA88))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_long_long_decimal| ()
  (declare (xargs :guard t))
  (c::ullong-dec-const 89))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_long_long_octal| ()
  (declare (xargs :guard t))
  (c::ullong-oct-const 255))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun |unsigned_long_long_hexadecimal| ()
  (declare (xargs :guard t))
  (c::ullong-hex-const #xAAAA88))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |signed_int_decimal|
        |signed_int_octal|
        |signed_int_hexadecimal|
        |unsigned_int_decimal|
        |unsigned_int_octal|
        |unsigned_int_hexadecimal|
        |signed_long_decimal|
        |signed_long_octal|
        |signed_long_hexadecimal|
        |unsigned_long_decimal|
        |unsigned_long_octal|
        |unsigned_long_hexadecimal|
        |signed_long_long_decimal|
        |signed_long_long_octal|
        |signed_long_long_hexadecimal|
        |unsigned_long_long_decimal|
        |unsigned_long_long_octal|
        |unsigned_long_long_hexadecimal|
        :output-file "constants.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

On macOS or Linux, you can compile and run this code as follows:

  gcc -o constants constants.c constants-test.c
  ./f

|#
