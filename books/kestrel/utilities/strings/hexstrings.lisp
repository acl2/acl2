; String Utilities -- Conversions from 8-Bit Bytes to Hex Strings
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "hexchars")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 8bitbytes-hexstrings-conversions
  :parents (string-utilities)
  :short "Conversions from 8-bit bytes to strings of hex character digits.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte8s=>hexstring ((bytes (unsigned-byte-listp 8 bytes)))
  :returns (string str::hex-digit-string-p)
  :parents (8bitbytes-hexstrings-conversions)
  :short "Convert a list of natural numbers below 256
          to a string of hexadecimal digits."
  :long
  (xdoc::topp
   "Each input natural number is converted to two hexadecimal digits,
    with a leading 0 digit if needed.
    The hexadecimal digits above 9 are upper case letters.
    The result is the string of all these digits.")
  (implode (ubyte8s=>hexchars bytes))

  ///

  (defrule ubyte8s=>hexstring-of-unsigned-byte-list-fix
    (equal (ubyte8s=>hexstring (unsigned-byte-list-fix 8 bytes))
           (ubyte8s=>hexstring bytes)))

  (defrule evenp-of-length-of-ubyte8s=>hexstring
    (evenp (length (ubyte8s=>hexstring bytes)))
    :disable evenp))
