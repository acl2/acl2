; Tests of blake2s-extended
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "blake2s-extended")
(include-book "blake2s-tests") ;todo: reduce

;; Suppresses any errors.
(defund hex-string-to-bytes! (s)
  (declare (xargs :guard (stringp s)))
  (mv-let (erp val)
    (hex-string-to-bytes s)
    (declare (ignore erp))
    val))

;; A test with no salt or personalization
(acl2::assert-equal (blake2s-extended '(0 1 2) nil nil nil  32)
                    (hex-string-to-bytes! "e8f91c6ef232a041452ab0e149070cdd7dd1769e75b3a5921be37876c45c9900"))

;; A test with a personalization
(acl2::assert-equal (blake2s-extended '(0 1 2) nil nil
                                      '(90 99 97 115 104 95 80 72)
                                      32)
                    (hex-string-to-bytes! "79e9fa3e5f9eb03e114b97a81b0104c19724726d1f23f9ec1810239195be01ca"))

;; A test with a salt
(acl2::assert-equal (blake2s-extended '(0 1 2)
                                      nil ;key
                                      '(78 97 67 108 56 56 56 56) ;salt
                                      nil ;personalization
                                      32)
                    (hex-string-to-bytes! "500b8ddc2ab792780fe152de2d99f1e97f39fafb6691ae4126168b48acf91a87"))
