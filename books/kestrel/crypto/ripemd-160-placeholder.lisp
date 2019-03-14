; Cryptography -- RIPEMD-160 Placeholder
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

(defsection ripemd-160
  :parents (placeholders)
  :short "RIPEMD-160 placeholder."
  :long
  (xdoc::topstring
   (xdoc::p
    "RIPEMD-160 is specified in
     <a href=\"https://homes.esat.kuleuven.be/~bosselae/ripemd160/pdf/AB-9601/AB-9601.pdf\"
     >the `RIPEMD-160: A Strengthened Version of RIPEMD' document</a>.")
   (xdoc::p
    "According to the aforementioned document,
     the input of RIPEMD-256 is a sequence of any number of bits,
     or any number of bytes.
     This is formalized by the guard of the constrained function below.")
   (xdoc::p
    "According to the aforementioned document,
     the output of RIPEMD-160 is a sequence of exactly 160 bits, or 20 bytes.
     We constrain our function to return a list of 20 bytes unconditionally.")
   (xdoc::p
    "We also constrain our function to fix its argument to a list of bytes.")
   (xdoc::def "ripemd-160"))

  (encapsulate

    (((ripemd-160 *) => *
      :formals (bytes)
      :guard (unsigned-byte-listp 8 bytes)))

    (local
     (defun ripemd-160 (bytes)
       (declare (ignore bytes))
       (make-list 20 :initial-element 0)))

    (defrule unsigned-byte-listp-8-of-ripemd-160
      (unsigned-byte-listp 8 (ripemd-160 bytes)))

    (defrule len-of-ripemd-160
      (equal (len (ripemd-160 bytes))
             20))

    (defrule ripemd-160-fixes-input
      (equal (ripemd-160 (unsigned-byte-list-fix 8 bytes))
             (ripemd-160 bytes))
      :enable unsigned-byte-list-fix))

  (defrule true-listp-of-ripemd-160
    (true-listp (ripemd-160 bytes))
    :rule-classes :type-prescription
    :use (:instance acl2::true-listp-when-unsigned-byte-listp
          (width 8) (x (ripemd-160 bytes)))
    :disable acl2::true-listp-when-unsigned-byte-listp)

  (defrule consp-of-ripemd-160
    (consp (ripemd-160 bytes))
    :rule-classes :type-prescription
    :use len-of-ripemd-160
    :disable len-of-ripemd-160))
