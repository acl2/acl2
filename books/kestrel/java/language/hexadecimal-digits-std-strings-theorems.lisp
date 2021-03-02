; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "hexadecimal-digits")

(include-book "std/strings/hex" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hexadecimal-digits-std/strings-theorems
  :parents (hexadecimal-digits)
  :short (xdoc::topstring
          "Theorems about Java hexadecimal digits and functions in "
          (xdoc::seetopic "acl2::std/strings" "Std/strings") ".")

  (defrule hex-digitp-of-char-code
    (equal (hex-digitp (char-code char))
           (str::hex-digit-char-p char))
    :enable (hex-digitp str::hex-digit-char-p))

  (defrule hex-digit-listp-of-chars=>nats
    (equal (hex-digit-listp (chars=>nats chars))
           (str::hex-digit-char-listp chars))
    :enable chars=>nats))
