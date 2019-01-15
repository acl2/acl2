; String Utilities -- Conversions from 8-Bit Bytes to Hex Characters
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)
(include-book "std/strings/hex" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 8bitbytes-hexchars-conversions
  :parents (string-utilities)
  :short "Conversions from 8-bit bytes to lists of hex character digits.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte8s=>hexchars ((bytes (unsigned-byte-listp 8 bytes)))
  :returns (chars character-listp)
  :parents (8bitbytes-hexchars-conversions)
  :short "Convert a list of natural numbers below 256
          to a sequence of hexadecimal digit characters."
  :long
  (xdoc::topp
   "Each input natural number is converted to two hexadecimal digits,
    with a leading 0 digit if needed.
    The hexadecimal digits above 9 are upper case letters.
    The result is the concatenation of all these digits.")
  (mbe :logic (cond ((endp bytes) nil)
                    (t (b* ((byte (if (unsigned-byte-p 8 (car bytes))
                                      (car bytes)
                                    0)) ; fix if not 8-bit byte
                            (digits (str::natchars16 byte))
                            (digits (if (= (len digits) 2)
                                        digits
                                      (cons #\0 digits))))
                         (append digits
                                 (ubyte8s=>hexchars (cdr bytes))))))
       :exec (ubyte8s=>hexchars-aux bytes nil))

  :prepwork
  ((define ubyte8s=>hexchars-aux ((bytes (unsigned-byte-listp 8 bytes))
                                  (rev-chars character-listp))
     (cond ((endp bytes) (rev rev-chars))
           (t (b* ((digits (str::natchars16 (car bytes)))
                   (digits (if (= (len digits) 2)
                               digits
                             (cons #\0 digits))))
                (ubyte8s=>hexchars-aux (cdr bytes)
                                       (append (rev digits) rev-chars)))))
     :enabled t))

  :verify-guards nil ; done below

  ///

  (defrulel verify-guards-lemma
    (implies (unsigned-byte-listp 8 bytes)
             (equal (ubyte8s=>hexchars-aux bytes rev-chars)
                    (revappend rev-chars (ubyte8s=>hexchars bytes)))))

  (verify-guards ubyte8s=>hexchars))
