; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "decimal-digits")

(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection decimal-digits-std/strings-theorems
  :parents (decimal-digits)
  :short (xdoc::topstring
          "Theorems about Java decimal digits and functions in "
          (xdoc::seetopic "acl2::std/strings" "Std/strings") ".")

  (defrule dec-digitp-of-char-code
    (equal (dec-digitp (char-code char))
           (str::dec-digit-char-p char))
    :enable (dec-digitp str::dec-digit-char-p))

  (defrule dec-digit-listp-of-chars=>nats
    (equal (dec-digit-listp (chars=>nats chars))
           (str::dec-digit-char-listp chars))
    :enable chars=>nats))
