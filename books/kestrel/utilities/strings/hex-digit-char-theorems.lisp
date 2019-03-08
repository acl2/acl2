; String Utilities -- Theorems about Hexadecimal Digit Characters
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/strings/hex" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hex-digit-char-theorems
  :parents (strings str::hex-digit-val str::hex-digit-to-char)
  :short "Some theorems about the library functions
          @(tsee str::hex-digit-val) and @(tsee str::hex-digit-to-char)."

  (defrule str::hex-digit-val-of-hex-digit-to-char
    (implies (integer-range-p 0 16 n)
             (equal (str::hex-digit-val (str::hex-digit-to-char n))
                    n)))

  (defrule str::hex-digit-to-char-of-hex-digit-val
    (implies (str::hex-digitp char)
             (equal (str::hex-digit-to-char (str::hex-digit-val char))
                    (str::upcase-char char)))
    :prep-books ((include-book "arithmetic-5/top" :dir :system))
    :enable (str::hex-digit-val
             str::hex-digitp)))
