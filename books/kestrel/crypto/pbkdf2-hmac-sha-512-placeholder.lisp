; Cryptography -- PBKDF2 HMAC-SHA-512 Placeholder
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/utilities/unsigned-byte-list-fixing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pbkdf2-hmac-sha-512-placeholder
  :parents (placeholders)
  :short "PBKDF2 HMAC-SHA-512 placeholder."
  :long
  (xdoc::topstring
   (xdoc::p
    "PBKDF2 is specified in the "
    (xdoc::a :href "https://tools.ietf.org/html/rfc8018" "RFC 8018 standard")
    "; it is essentially parameterized over a pseudorandom function.
     Here we use HMAC-SHA-512 as the pseudorandom function:
     see @(tsee hmac-sha-512-placeholder).")
   (xdoc::p
    "According to RFC 8018,
     the password and salt inputs are sequences of bytes,
     the iteration count is a positive integer,
     and the desired key length is a positive integer
     not above @($2^{32}-1)\\times H$),
     where @($H$) is the length of the output of the pseudorandom functions,
     which is 64 bytes for HMAC-SHA-512.
     These are formalized by the guard of the constrained function.")
   (xdoc::p
    "RFC 8018 says that the output consists of the desired key length.
     We constrain our function to return a list of 64 bytes unconditionally.")
   (xdoc::p
    "We also constrain our function to fix its inputs to
     true lists of bytes (for password and salt)
     and to positive integers (for iteration count and desired key length).")
   (xdoc::@def "pbkdf2-hmac-sha-512"))

  (encapsulate

    (((pbkdf2-hmac-sha-512 * * * *) => *
      :formals (password salt iterations length)
      :guard (and (unsigned-byte-listp 8 password)
                  (unsigned-byte-listp 8 salt)
                  (posp iterations)
                  (posp length)
                  (<= length (* (1- (expt 2 32)) 64)))))

    (local
     (defun pbkdf2-hmac-sha-512 (password salt iterations length)
       (declare (ignore password salt iterations))
       (if (posp length)
           (make-list length :initial-element 0)
         (make-list 1 :initial-element 0))))

    (defrule unsigned-byte-listp-8-of-pbkdf2-hmac-sha-512
      (unsigned-byte-listp 8 (pbkdf2-hmac-sha-512
                              password salt iterations length)))

    (defrule len-of-pbkdf2-hmac-sha-512
      (equal (len (pbkdf2-hmac-sha-512 password salt iterations length))
             (if (posp length) length 1)))

    (defrule pbkdf2-hmac-sha-512-fixes-input-password
      (equal (pbkdf2-hmac-sha-512 (unsigned-byte-list-fix 8 password)
                                  salt
                                  iterations
                                  length)
             (pbkdf2-hmac-sha-512 password salt iterations length)))

    (defrule pbkdf2-hmac-sha-512-fixes-input-salt
      (equal (pbkdf2-hmac-sha-512 password
                                  (unsigned-byte-list-fix 8 salt)
                                  iterations
                                  length)
             (pbkdf2-hmac-sha-512 password salt iterations length)))

    (defrule pbkdf2-hmac-sha-512-fixes-input-iterations
      (equal (pbkdf2-hmac-sha-512 password
                                  salt
                                  (if (posp iterations) iterations 1)
                                  length)
             (pbkdf2-hmac-sha-512 password salt iterations length)))

    (defrule pbkdf2-hmac-sha-512-fixes-input-length
      (equal (pbkdf2-hmac-sha-512 password
                                  salt
                                  iterations
                                  (if (posp length) length 1))
             (pbkdf2-hmac-sha-512 password salt iterations length))))

  (defrule true-listp-of-pbkdf2-hmac-sha-512
    (true-listp (pbkdf2-hmac-sha-512 password salt iterations length))
    :rule-classes :type-prescription
    :use (:instance acl2::true-listp-when-unsigned-byte-listp
          (width 8) (x (pbkdf2-hmac-sha-512 password salt iterations length)))
    :disable acl2::true-listp-when-unsigned-byte-listp)

  (defrule consp-of-pbkdf2-hmac-sha-512
    (true-listp (pbkdf2-hmac-sha-512 password salt iterations length))
    :rule-classes :type-prescription
    :use len-of-pbkdf2-hmac-sha-512
    :disable len-of-pbkdf2-hmac-sha-512))
