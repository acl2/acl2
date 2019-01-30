; Bitcoin Library -- Bytes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/utilities/fixbytes/defbytelist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bytes
  :parents (bitcoin)
  :short "Bytes."
  :long
  (xdoc::topp
   "In Bitcoin, as in most modern contexts,
    the unqualified term `byte' denotes an (unsigned) 8-bit byte."))

(fty::defbyte 8
  :type byte
  :pred bytep
  :parents (bytes)
  :description "bytes")

(defsection byte-fix-ext
  :extension byte-fix

  (defrule natp-of-byte-fix
    (natp (byte-fix x))
    :rule-classes :type-prescription
    :enable byte-fix)

  (defrule byte-fix-upper-bound
    (< (byte-fix x) 256)
    :rule-classes :linear
    :enable (byte-fix bytep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc byte-sequences
  :parents (bytes)
  :short "Byte sequences."
  :long
  (xdoc::topp
   "These are finite lists of bytes,
    which model byte arrays in particular."))

(fty::defbytelist byte
  :pred byte-listp
  :parents (byte-sequences))

(defsection byte-listp-ext
  :extension byte-listp

  (defrule nat-listp-when-byte-listp
    (implies (byte-listp bytes)
             (nat-listp bytes))))

(defsection byte-list-fix-ext
  :extension byte-list-fix

  (defrule car-of-byte-list-fix
    (implies (consp x)
             (equal (car (byte-list-fix x))
                    (byte-fix (car x)))))

  (defrule cdr-of-byte-list-fix
    (equal (cdr (byte-list-fix x))
           (byte-list-fix (cdr x)))))
