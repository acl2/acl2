; String Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)
(include-book "characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc string-utilities
  :parents (kestrel-utilities)
  :short "Utilities for @(see strings).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nonempty-stringp (x)
  :returns (yes/no booleanp)
  :parents (string-utilities)
  :short "Recognize non-empty strings."
  (not (equal (str-fix x) ""))
  ///

  (defrule stringp-when-nonempty-stringp
    (implies (nonempty-stringp x)
             (stringp x))))

(std::deflist nonempty-string-listp (x)
  (nonempty-stringp x)
  :parents (string-utilities)
  :short "Recognize true lists of nonempty strings."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>string ((nats (unsigned-byte-listp 8 nats)))
  :returns (string stringp)
  :parents (string-utilities)
  :short "Convert a true list of natural numbers below 256
          to the corresponding string."
  (implode (nats=>chars nats)))

(define string=>nats ((string stringp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (string-utilities)
  :short "Convert a string
          to the corresponding true list of natural numbers below 256."
  (chars=>nats (explode string))
  ///

  (more-returns
   (nats nat-listp
         :name nat-listp-of-string=>nats))

  (defrule len-of-string=>nats
    (implies (stringp string)
             (equal (len (string=>nats string))
                    (length string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte8s=>hexstring ((bytes (unsigned-byte-listp 8 bytes)))
  :returns (string stringp)
  :parents (string-utilities)
  :short "Convert a list of natural numbers below 256
          to a string of hexadecimal digits."
  :long
  "<p>
   Each input natural number is converted to two hexadecimal digits,
   with a leading 0 digit if needed.
   The hexadecimal digits above 9 are upper case letters.
   The result is the string of all these digits.
   </p>"
  (implode (ubyte8s=>hexchars bytes)))
