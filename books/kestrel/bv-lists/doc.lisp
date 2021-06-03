; Documentation for bv-lists library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/gen-xdoc-for-file" :dir :system)

;; (depends-on "bits-to-byte.lisp")
(acl2::gen-xdoc-for-file
 "bits-to-byte.lisp"
 ((bits-to-byte "Convert list of bits to a byte (big-endian)."))
 (bv))

;; (depends-on "bits-to-byte-little.lisp")
(acl2::gen-xdoc-for-file
 "bits-to-byte-little.lisp"
 ((bits-to-byte-little "Convert list of bits to a byte (little-endian)."))
 (bv))

;; (depends-on "byte-to-bits.lisp")
(acl2::gen-xdoc-for-file
 "byte-to-bits.lisp"
 ((byte-to-bits "Convert a byte to a list of bits (big-endian)."))
 (bv))

;; (depends-on "byte-to-bits-little.lisp")
(acl2::gen-xdoc-for-file
 "byte-to-bits-little.lisp"
 ((byte-to-bits-little "Convert a byte to a list of bits (little-endian)."))
 (bv))
