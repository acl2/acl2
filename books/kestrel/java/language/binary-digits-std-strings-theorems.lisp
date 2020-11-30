; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "binary-digits")

(include-book "std/strings/binary" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection binary-digits-std/strings-theorems
  :parents (binary-digits)
  :short (xdoc::topstring
          "Theorems about Java binary digits and functions in "
          (xdoc::seetopic "acl2::std/strings" "Std/strings") ".")

  (defrule bin-digitp-of-char-code
    (equal (bin-digitp (char-code char))
           (str::bin-digit-char-p char))
    :enable (bin-digitp str::bin-digit-char-p))

  (defrule bin-digit-listp-of-chars=>nats
    (equal (bin-digit-listp (chars=>nats chars))
           (str::bin-digit-char-listp chars))
    :enable chars=>nats))
