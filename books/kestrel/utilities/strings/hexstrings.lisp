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
  (xdoc::topstring-p
   "Each input natural number is converted to two hexadecimal digits,
    with a leading 0 digit if needed.
    The hexadecimal digits above 9 are upper case letters.
    The result is the string of all these digits.
    The result has always an even length.")
  (implode (ubyte8s=>hexchars bytes))

  ///

  (defrule ubyte8s=>hexstring-of-unsigned-byte-list-fix
    (equal (ubyte8s=>hexstring (unsigned-byte-list-fix 8 bytes))
           (ubyte8s=>hexstring bytes)))

  (defrule evenp-of-length-of-ubyte8s=>hexstring
    (evenp (length (ubyte8s=>hexstring bytes)))
    :disable evenp)

  (defrule ubyte8s=>hexstring-of-append
    (equal (ubyte8s=>hexstring (append bytes1 bytes2))
           (string-append (ubyte8s=>hexstring bytes1)
                          (ubyte8s=>hexstring bytes2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hexstring=>ubyte8s ((string (and (stringp string)
                                         (str::hex-digit-string-p string)
                                         (evenp (length string)))))
  :returns (bytes (unsigned-byte-listp 8 bytes))
  :parents (8bitbytes-hexstrings-conversions)
  :short "Convert an even-length string of hexadecimal digit characters
          to a list of natural numbers below 256."
  :long
  (xdoc::topstring-p
   "Each pair of hexadecimal digit characters is turned into sa number.
    Each such two-digit hexadecimal notation is treated as big endian,
    i.e. the most significant digit appears first.")
  (hexchars=>ubyte8s (explode string))

  ///

  (defrule hexstring=>ubyte8s-of-string-append
    (implies (evenp (length string1))
             (equal (hexstring=>ubyte8s (string-append string1 string2))
                    (append (hexstring=>ubyte8s string1)
                            (hexstring=>ubyte8s string2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ubyte8s<=>hexstring-inverses-theorems
  :parents (ubyte8s=>hexstring hexstring=>ubyte8s)
  :short "@(tsee ubyte8s=>hexstring) and @(tsee hexstring=>ubyte8s)
          are mutual inverses."

  (defrule hexstring=>ubyte8s-of-ubyte8s=>hexstring
    (equal (hexstring=>ubyte8s (ubyte8s=>hexstring bytes))
           (unsigned-byte-list-fix 8 bytes))
    :enable (ubyte8s=>hexstring
             hexstring=>ubyte8s))

  (defrule ubyte8s=>hexstring-of-hexstring=>ubyte8s
    (implies (and (stringp string)
                  (str::hex-digit-char-listp (explode string))
                  (evenp (length string)))
             (equal (ubyte8s=>hexstring (hexstring=>ubyte8s string))
                    (str::upcase-string string)))
    :enable (hexstring=>ubyte8s
             ubyte8s=>hexstring
             str::upcase-string)))
