; String Utilities -- Conversions from 8-Bit Bytes to Hex Characters
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/unsigned-byte-list-fixing" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/strings/hex" :dir :system)
(include-book "hex-digit-char-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 8bitbytes-hexchars-conversions
  :parents (string-utilities)
  :short "Conversions from 8-bit bytes to lists of hex character digits.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte8=>hexchars ((byte (unsigned-byte-p 8 byte)))
  :returns (mv (hi-char str::hex-digit-char-p)
               (lo-char str::hex-digit-char-p))
  :parents (8bitbytes-hexchars-conversions)
  :short "Convert an unsigned 8-bit byte to two hexadecimal digit characters."
  :long
  (xdoc::topstring-p
   "The most significant digit comes first,
    followed by the least significant one.
    If the byte is below 16, the first digit is zero.
    The hexadecimal digits above 9 are uppercase letters.")
  (b* ((byte (mbe :logic (unsigned-byte-fix 8 byte) :exec byte)))
    (mv (str::hex-digit-to-char (floor byte 16))
        (str::hex-digit-to-char (mod byte 16))))
  :verify-guards nil ; done below (needs arithmetic)
  ///

  (local (include-book "arithmetic-5/top" :dir :system))

  (verify-guards ubyte8=>hexchars)

  (defrule mv-nth-0-of-ubyte8=>hexchars-of-unsigned-byte-fix
    (equal (mv-nth 0 (ubyte8=>hexchars (unsigned-byte-fix 8 byte)))
           (mv-nth 0 (ubyte8=>hexchars byte))))

  (defrule mv-nth-1-of-ubyte8=>hexchars-of-unsigned-byte-fix
    (equal (mv-nth 1 (ubyte8=>hexchars (unsigned-byte-fix 8 byte)))
           (mv-nth 1 (ubyte8=>hexchars byte)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hexchars=>ubyte8 ((hi-char str::hex-digit-char-p)
                          (lo-char str::hex-digit-char-p))
  :returns (byte (unsigned-byte-p 8 byte))
  :parents (8bitbytes-hexchars-conversions)
  :short "Convert two hexadecimal digit characters to an unsigned 8-bit byte."
  :long
  (xdoc::topstring-p
   "The most significant digit comes first,
    followed by the least significant one.")
  (b* ((hi-digit (str::hex-digit-char-value hi-char))
       (lo-digit (str::hex-digit-char-value lo-char)))
    (+ (* 16 hi-digit) lo-digit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ubyte8<=>hexchars-inverses-theorems
  :parents (ubyte8=>hexchars hexchars=>ubyte8)
  :short "@(tsee ubyte8=>hexchars) and @(tsee hexchars=>ubyte8)
          are mutual inverses."

  (defrule hexchars=>ubyte8-of-ubyte8=>hexchars
    (b* (((mv hi-char lo-char) (ubyte8=>hexchars byte)))
      (equal (hexchars=>ubyte8 hi-char lo-char)
             (unsigned-byte-fix 8 byte)))
    :prep-books ((include-book "arithmetic-5/top" :dir :system))
    :enable (ubyte8=>hexchars
             hexchars=>ubyte8)
    :disable str::hex-digit-to-char)

  (defrule ubyte8=>hexchars-of-hexchars=>ubyte8
    (implies (and (str::hex-digit-char-p hi-char)
                  (str::hex-digit-char-p lo-char))
             (b* ((byte (hexchars=>ubyte8 hi-char lo-char)))
               (and (equal (mv-nth 0 (ubyte8=>hexchars byte))
                           (str::upcase-char hi-char))
                    (equal (mv-nth 1 (ubyte8=>hexchars byte))
                           (str::upcase-char lo-char)))))
    :prep-books ((include-book "arithmetic-5/top" :dir :system))
    :enable (ubyte8=>hexchars
             hexchars=>ubyte8)
    :disable str::hex-digit-to-char))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte8s=>hexchars ((bytes (unsigned-byte-listp 8 bytes)))
  :returns (chars str::hex-digit-char-listp)
  :parents (8bitbytes-hexchars-conversions)
  :short "Convert a list of unsigned 8-bit bytes
          to a sequence of hexadecimal digit characters."
  :long
  (xdoc::topstring-p
   "Each input natural number is converted to two hexadecimal digits,
    with a leading 0 digit if needed.
    The hexadecimal digits above 9 are uppercase letters.
    The result is the concatenation of all these digits.
    The result has always an even length.")
  (mbe :logic (cond ((endp bytes) nil)
                    (t (b* (((mv hi-char lo-char)
                             (ubyte8=>hexchars (car bytes))))
                         (list* hi-char
                                lo-char
                                (ubyte8s=>hexchars (cdr bytes))))))
       :exec (ubyte8s=>hexchars-aux bytes nil))

  :prepwork
  ((define ubyte8s=>hexchars-aux ((bytes (unsigned-byte-listp 8 bytes))
                                  (rev-chars str::hex-digit-char-listp))
     (cond ((endp bytes) (rev rev-chars))
           (t (b* (((mv hi-char lo-char) (ubyte8=>hexchars (car bytes))))
                (ubyte8s=>hexchars-aux (cdr bytes)
                                       (list* lo-char hi-char rev-chars)))))
     :enabled t))

  :verify-guards nil ; done below

  ///

  (defrulel verify-guards-lemma
    (implies (unsigned-byte-listp 8 bytes)
             (equal (ubyte8s=>hexchars-aux bytes rev-chars)
                    (revappend rev-chars (ubyte8s=>hexchars bytes)))))

  (verify-guards ubyte8s=>hexchars)

  (defrule ubyte8s=>hexchars-of-unsigned-byte-list-fix
    (equal (ubyte8s=>hexchars (unsigned-byte-list-fix 8 bytes))
           (ubyte8s=>hexchars bytes))
    :disable unsigned-byte-fix)

  (defrule evenp-of-len-of-ubyte8s=>hexchars
    (evenp (len (ubyte8s=>hexchars bytes))))

  (defrule ubyte8s=>hexchars-of-append
    (equal (ubyte8s=>hexchars (append bytes1 bytes2))
           (append (ubyte8s=>hexchars bytes1)
                   (ubyte8s=>hexchars bytes2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hexchars=>ubyte8s ((chars (and (str::hex-digit-char-listp chars)
                                       (true-listp chars)
                                       (evenp (len chars)))))
  :returns (bytes (unsigned-byte-listp 8 bytes))
  :parents (8bitbytes-hexchars-conversions)
  :short "Convert an even-length sequence of hexadecimal digit characters
          to a list of unsigned 8-bit bytes."
  :long
  (xdoc::topstring-p
   "Each pair of hexadecimal digit characters is turned into a number.
    Each such two-digit hexadecimal notation is treated as big endian,
    i.e. the most significant digit appears first.")
  (mbe :logic (cond ((endp chars) nil)
                    (t (b* ((byte (hexchars=>ubyte8 (car chars) (cadr chars)))
                            (bytes (hexchars=>ubyte8s (cddr chars))))
                         (cons byte bytes))))
       :exec (hexchars=>ubyte8s-aux chars nil))

  :prepwork
  ((define hexchars=>ubyte8s-aux ((chars (and (str::hex-digit-char-listp chars)
                                              (true-listp chars)
                                              (evenp (len chars))))
                                  (rev-bytes (unsigned-byte-listp 8 rev-bytes)))
     (cond ((endp chars) (rev rev-bytes))
           (t (b* ((byte (hexchars=>ubyte8 (car chars) (cadr chars))))
                (hexchars=>ubyte8s-aux (cddr chars) (cons byte rev-bytes)))))
     :enabled t))

  :verify-guards nil ; done below

  ///

  (defrulel verify-guards-lemma
    (implies (and (str::hex-digit-char-listp chars)
                  (true-listp chars)
                  (evenp (len chars)))
             (equal (hexchars=>ubyte8s-aux chars rev-bytes)
                    (revappend rev-bytes (hexchars=>ubyte8s chars)))))

  (verify-guards hexchars=>ubyte8s)

  (defrule hexchars=>ubyte8s-of-append
    (implies (evenp (len chars1))
             (equal (hexchars=>ubyte8s (append chars1 chars2))
                    (append (hexchars=>ubyte8s chars1)
                            (hexchars=>ubyte8s chars2))))
    :induct (hexchars=>ubyte8s chars1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ubyte8s<=>hexchars-inverses-theorems
  :parents (ubyte8s=>hexchars hexchars=>ubyte8s)
  :short "@(tsee ubyte8s=>hexchars) and @(tsee hexchars=>ubyte8s)
          are mutual inverses."

  (defrule hexchars=>ubyte8s-of-ubyte8s=>hexchars
    (equal (hexchars=>ubyte8s (ubyte8s=>hexchars bytes))
           (unsigned-byte-list-fix 8 bytes))
    :enable (ubyte8s=>hexchars
             hexchars=>ubyte8s
             unsigned-byte-list-fix))

  (defrule ubyte8s=>hexchars-of-hexchars=>ubyte8s
    (implies (and (str::hex-digit-char-listp chars)
                  (true-listp chars)
                  (evenp (len chars)))
             (equal (ubyte8s=>hexchars (hexchars=>ubyte8s chars))
                    (str::upcase-charlist chars)))
    :enable (hexchars=>ubyte8s
             ubyte8s=>hexchars)
    :induct (hexchars=>ubyte8s chars)))
