; Cryptography -- RIPEMD-160 Placeholder
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/fty/byte-list20" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ripemd-160-placeholder
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
   (xdoc::@def "ripemd-160"))

  (encapsulate

    (((ripemd-160 *) => *
      :formals (bytes)
      :guard (byte-listp bytes)))

    (local
     (defun ripemd-160 (bytes)
       (declare (ignore bytes))
       (make-list 20 :initial-element 0)))

    (defrule byte-list20p-of-ripemd-160
      (byte-list20p (ripemd-160 bytes)))

    (defrule len-of-ripemd-160
      (equal (len (ripemd-160 bytes))
             20))

    (fty::deffixequiv ripemd-160
      :args ((bytes byte-listp))))

  (defrule true-listp-of-ripemd-160
    (true-listp (ripemd-160 bytes))
    :rule-classes :type-prescription
    :enable acl2::true-listp-when-byte-listp)

  (defrule consp-of-ripemd-160
    (consp (ripemd-160 bytes))
    :rule-classes :type-prescription
    :use len-of-ripemd-160
    :disable len-of-ripemd-160))
