; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "octal-digits")

(include-book "std/strings/octal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection octal-digits-std/strings-theorems
  :parents (octal-digits)
  :short (xdoc::topstring
          "Theorems about Java octal digits and functions in "
          (xdoc::seetopic "acl2::std/strings" "Std/strings") ".")

  (defrule oct-digitp-of-char-code
    (equal (oct-digitp (char-code char))
           (str::oct-digit-char-p char))
    :enable (oct-digitp str::oct-digit-char-p))

  (defrule oct-digit-listp-of-chars=>nats
    (equal (oct-digit-listp (chars=>nats chars))
           (str::oct-digit-char-listp chars))
    :enable chars=>nats))
