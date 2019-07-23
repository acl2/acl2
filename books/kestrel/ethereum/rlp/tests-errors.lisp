; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/testing" :dir :system)

(include-book "decoding-executable")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These tests serve to check that the errors returned by parsing and decoding
; are correct.
; Note that the declarative definition of RLP decoding returns
; a single kind of errors:
; there is currently no specification of the different kinds of errors
; returned by the executable parser and decoders.
; The executable decoders are proved to return errors that are IFF-equivalent to
; the errors returned by the declaratively defined decoders.
; The more detailed error information returned by the executable decoders
; is just informative.
; Nonetheless, the following tests help establish that
; this additional information is correct.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro assert-parse-tree-error (input error)
  `(assert-equal (b* (((mv error? & &) (rlp-parse-tree ,input))) error?)
                 ,error))

(defmacro assert-decode-tree-error (input error)
  `(assert-equal (b* (((mv error? &) (rlp-decodex-tree ,input))) error?)
                 ,error))

(defmacro assert-decode-bytes-error (input error)
  `(assert-equal (b* (((mv error? &) (rlp-decodex-bytes ,input))) error?)
                 ,error))

(defmacro assert-decode-scalar-error (input error)
  `(assert-equal (b* (((mv error? &) (rlp-decodex-scalar ,input))) error?)
                 ,error))

(defmacro assert-parse/decode-tree/bytes/scalar-error (input error)
  `(progn
     (assert-parse-tree-error ,input ,error)
     (assert-decode-tree-error ,input ,error)
     (assert-decode-bytes-error ,input ,error)
     (assert-decode-scalar-error ,input ,error)))

(defmacro assert-decode-tree/bytes/scalar-error (input error)
  `(progn
     (assert-decode-tree-error ,input ,error)
     (assert-decode-bytes-error ,input ,error)
     (assert-decode-scalar-error ,input ,error)))

(defmacro assert-decode-bytes/scalar-error (input error)
  `(progn
     (assert-decode-bytes-error ,input ,error)
     (assert-decode-scalar-error ,input ,error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-parse/decode-tree/bytes/scalar-error
 ()
 (rlp-error-no-bytes))

(assert-parse/decode-tree/bytes/scalar-error
 '(#x81)
 (rlp-error-fewer-bytes-than-short-length '(#x81) 1 0))

(assert-parse/decode-tree/bytes/scalar-error
 '(#x95)
 (rlp-error-fewer-bytes-than-short-length '(#x95) 21 0))

(assert-parse/decode-tree/bytes/scalar-error
 (cons #xa0 (repeat 30 0))
 (rlp-error-fewer-bytes-than-short-length '(#xa0) 32 30))

(assert-parse/decode-tree/bytes/scalar-error
 '(#xc1)
 (rlp-error-fewer-bytes-than-short-length '(#xc1) 1 0))

(assert-parse/decode-tree/bytes/scalar-error
 '(#xd5)
 (rlp-error-fewer-bytes-than-short-length '(#xd5) 21 0))

(assert-parse/decode-tree/bytes/scalar-error
 (cons #xe0 (repeat 30 0))
 (rlp-error-fewer-bytes-than-short-length '(#xe0) 32 30))

(assert-parse/decode-tree/bytes/scalar-error
 '(#xb8)
 (rlp-error-fewer-bytes-than-length-of-length '(#xb8) 1 0))

(assert-parse/decode-tree/bytes/scalar-error
 (cons #xbf (repeat 7 1))
 (rlp-error-fewer-bytes-than-length-of-length '(#xbf) 8 7))

(assert-parse/decode-tree/bytes/scalar-error
 '(#xf8)
 (rlp-error-fewer-bytes-than-length-of-length '(#xf8) 1 0))

(assert-parse/decode-tree/bytes/scalar-error
 (cons #xff (repeat 7 1))
 (rlp-error-fewer-bytes-than-length-of-length '(#xff) 8 7))

(assert-parse/decode-tree/bytes/scalar-error
 '(#xb8 200)
 (rlp-error-fewer-bytes-than-long-length '(#xb8 200) 200 0))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xb8 200 (repeat 100 88))
 (rlp-error-fewer-bytes-than-long-length '(#xb8 200) 200 100))

(assert-parse/decode-tree/bytes/scalar-error
 '(#xf8 200)
 (rlp-error-fewer-bytes-than-long-length '(#xf8 200) 200 0))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xf8 200 (repeat 100 88))
 (rlp-error-fewer-bytes-than-long-length '(#xf8 200) 200 100))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xb9 0 100 (repeat 100 0))
 (rlp-error-leading-zeros-in-long-length '(#xb9 0 100)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xbd 0 0 0 0 0 100 (repeat 100 0))
 (rlp-error-leading-zeros-in-long-length '(#xbd 0 0 0 0 0 100)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xf9 0 100 (repeat 100 0))
 (rlp-error-leading-zeros-in-long-length '(#xf9 0 100)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xfd 0 0 0 0 0 100 (repeat 100 0))
 (rlp-error-leading-zeros-in-long-length '(#xfd 0 0 0 0 0 100)))

(assert-parse/decode-tree/bytes/scalar-error
 '(#x81 0)
 (rlp-error-non-optimal-short-length '(#x81 0)))

(assert-parse/decode-tree/bytes/scalar-error
 '(#x81 8)
 (rlp-error-non-optimal-short-length '(#x81 8)))

(assert-parse/decode-tree/bytes/scalar-error
 '(#x81 127)
 (rlp-error-non-optimal-short-length '(#x81 127)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xb8 10 (repeat 10 0))
 (rlp-error-non-optimal-long-length '(#xb8 10)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xb8 55 (repeat 55 0))
 (rlp-error-non-optimal-long-length '(#xb8 55)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xf8 10 (repeat 10 0))
 (rlp-error-non-optimal-long-length '(#xf8 10)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xf8 55 (repeat 55 0))
 (rlp-error-non-optimal-long-length '(#xf8 55)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xc8 (list* #xf8 255 (repeat 6 0)))
 (rlp-error-subtree
  (rlp-error-fewer-bytes-than-long-length '(#xf8 255) 255 6)))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xc2 (list #x81 0))
 (rlp-error-subtree
  (rlp-error-non-optimal-short-length '(#x81 0))))

(assert-parse/decode-tree/bytes/scalar-error
 (list* #xc8 (list* #xc7 '(#xf9 0 4 0 0 0 0)))
 (rlp-error-subtree
  (rlp-error-subtree
   (rlp-error-leading-zeros-in-long-length '(#xf9 0 4)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-decode-tree/bytes/scalar-error
 '(0 1 2 3)
 (rlp-error-extra-bytes '(1 2 3)))

(assert-decode-tree/bytes/scalar-error
 '(#x82 100 200 0)
 (rlp-error-extra-bytes '(0)))

(assert-decode-tree/bytes/scalar-error
 (list* #xc8 (repeat 9 #x7f))
 (rlp-error-extra-bytes '(#x7f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-decode-bytes/scalar-error
 (list* #xc8 (repeat 8 #x1a))
 (rlp-error-branch-tree '(#xc8)))

(assert-decode-bytes/scalar-error
 (list* #xf8 100 (repeat 100 8))
 (rlp-error-branch-tree '(#xf8)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-decode-scalar-error
 '(0)
 (rlp-error-leading-zeros-in-scalar '(0)))

(assert-decode-scalar-error
 '(#x82 0 10)
 (rlp-error-leading-zeros-in-scalar '(0 10)))

(assert-decode-scalar-error
 (list* #x90 0 (repeat 15 1))
 (rlp-error-leading-zeros-in-scalar (list* 0 (repeat 15 1))))
