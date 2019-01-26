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
(include-book "std/strings/hex" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 8bitbytes-hexchars-conversions
  :parents (string-utilities)
  :short "Conversions from 8-bit bytes to lists of hex character digits.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte8s=>hexchars ((bytes (unsigned-byte-listp 8 bytes)))
  :returns (chars str::hex-digit-listp)
  :parents (8bitbytes-hexchars-conversions)
  :short "Convert a list of natural numbers below 256
          to a sequence of hexadecimal digit characters."
  :long
  (xdoc::topp
   "Each input natural number is converted to two hexadecimal digits,
    with a leading 0 digit if needed.
    The hexadecimal digits above 9 are upper case letters.
    The result is the concatenation of all these digits.
    The result has always an even length.")
  (mbe :logic (cond ((endp bytes) nil)
                    (t (b* ((byte (unsigned-byte-fix 8 (car bytes)))
                            (digits (str::natchars16 byte))
                            (digits (if (= (len digits) 2)
                                        digits
                                      (cons #\0 digits))))
                         (append digits
                                 (ubyte8s=>hexchars (cdr bytes))))))
       :exec (ubyte8s=>hexchars-aux bytes nil))

  :prepwork
  ((define ubyte8s=>hexchars-aux ((bytes (unsigned-byte-listp 8 bytes))
                                  (rev-chars str::hex-digit-listp))
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

  (verify-guards ubyte8s=>hexchars)

  (defrule ubyte8s=>hexchars-of-unsigned-byte-list-fix
    (equal (ubyte8s=>hexchars (unsigned-byte-list-fix 8 bytes))
           (ubyte8s=>hexchars bytes)))

  (defrule evenp-of-len-of-ubyte8s=>hexchars
    (evenp (len (ubyte8s=>hexchars bytes)))

    :prep-lemmas

    ((defrule basic-natchars16-lemma
       (implies (unsigned-byte-p 8 byte)
                (<= (len (str::basic-natchars16 byte))
                    2))
       :rule-classes :linear
       :enable str::basic-natchars16
       :prep-books ((include-book "arithmetic-5/top" :dir :system)))

     (defrule natchars16-lemma
       (implies (unsigned-byte-p 8 byte)
                (and (<= 1
                         (len (str::natchars16 byte)))
                     (<= (len (str::natchars16 byte))
                         2)))
       :rule-classes :linear
       :enable str::natchars16
       :prep-books ((include-book "std/lists/len" :dir :system)))))

  (defrule ubyte8s=>hexchars-of-append
    (equal (ubyte8s=>hexchars (append bytes1 bytes2))
           (append (ubyte8s=>hexchars bytes1)
                   (ubyte8s=>hexchars bytes2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hexchars=>ubyte8s ((chars (and (str::hex-digit-listp chars)
                                       (true-listp chars)
                                       (evenp (len chars)))))
  :returns (bytes (unsigned-byte-listp 8 bytes))
  :parents (8bitbytes-hexchars-conversions)
  :short "Convert an even-length sequence of hexadecimal digit characters
          to a list of natural numbers below 256."
  :long
  (xdoc::topp
   "Each pair of hexadecimal digit characters is turned into sa number.
    Each such two-digit hexadecimal notation is treated as big endian,
    i.e. the most significant digit appears first.")
  (mbe :logic (cond ((endp chars) nil)
                    (t (b* ((hi-digit (str::hex-digit-val (car chars)))
                            (lo-digit (str::hex-digit-val (cadr chars)))
                            (byte (+ (* hi-digit 16) lo-digit))
                            (bytes (hexchars=>ubyte8s (cddr chars))))
                         (cons byte bytes))))
       :exec (hexchars=>ubyte8s-aux chars nil))

  :prepwork
  ((define hexchars=>ubyte8s-aux ((chars (and (str::hex-digit-listp chars)
                                              (true-listp chars)
                                              (evenp (len chars))))
                                  (rev-bytes (unsigned-byte-listp 8 rev-bytes)))
     (cond ((endp chars) (rev rev-bytes))
           (t (b* ((hi-digit (str::hex-digit-val (car chars)))
                   (lo-digit (str::hex-digit-val (cadr chars)))
                   (byte (+ (* hi-digit 16) lo-digit)))
                (hexchars=>ubyte8s-aux (cddr chars) (cons byte rev-bytes)))))
     :enabled t))

  :verify-guards nil ; done below

  ///

  (defrulel verify-guards-lemma
    (implies (and (str::hex-digit-listp chars)
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
