; Ethereum Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "kestrel/utilities/testing" :dir :system)

(include-book "decoding-executable")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These are the examples in [Wiki:RLP],
; i.e. https://github.com/ethereum/wiki/wiki/RLP.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *dog-bytes*
  (string=>nats "dog"))

(defconst *dog-tree*
  (rlp-tree-leaf *dog-bytes*))

(defconst *dog-encoding*
  (list #x83 (char-code #\d) (char-code #\o) (char-code #\g)))

(assert-equal (mv-list 2 (rlp-encode-bytes *dog-bytes*))
              (list nil *dog-encoding*))

(assert-equal (mv-list 2 (rlp-encode-tree *dog-tree*))
              (list nil *dog-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-bytes *dog-encoding*))
              (list nil *dog-bytes*))

(assert-equal (mv-list 2 (rlp-decodex-tree *dog-encoding*))
              (list nil *dog-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *cat-bytes*
  (string=>nats "cat"))

(defconst *cat-tree*
  (rlp-tree-leaf *cat-bytes*))

(defconst *cat-dog-tree*
  (rlp-tree-branch (list *cat-tree* *dog-tree*)))

(defconst *cat-dog-encoding*
  (list #xc8
        #x83 (char-code #\c) (char-code #\a) (char-code #\t)
        #x83 (char-code #\d) (char-code #\o) (char-code #\g)))

(assert-equal (mv-list 2 (rlp-encode-tree *cat-dog-tree*))
              (list nil *cat-dog-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-tree *cat-dog-encoding*))
              (list nil *cat-dog-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *empty-string-bytes*
  nil)

(defconst *empty-string-tree*
  (rlp-tree-leaf *empty-string-bytes*))

(defconst *empty-string-encoding*
  (list #x80))

(assert-equal (mv-list 2 (rlp-encode-bytes *empty-string-bytes*))
              (list nil *empty-string-encoding*))

(assert-equal (mv-list 2 (rlp-encode-tree *empty-string-tree*))
              (list nil *empty-string-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-bytes *empty-string-encoding*))
              (list nil *empty-string-bytes*))

(assert-equal (mv-list 2 (rlp-decodex-tree *empty-string-encoding*))
              (list nil *empty-string-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *empty-list-tree*
  (rlp-tree-branch nil))

(defconst *empty-list-encoding*
  (list #xc0))

(assert-equal (mv-list 2 (rlp-encode-tree *empty-list-tree*))
              (list nil *empty-list-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-tree *empty-list-encoding*))
              (list nil *empty-list-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *zero-scalar*
  0)

(defconst *zero-bytes*
  (nat=>bebytes* *zero-scalar*))

(defconst *zero-tree*
  (rlp-tree-leaf *zero-bytes*))

(defconst *zero-encoding*
  (list #x80))

(assert-equal (mv-list 2 (rlp-encode-scalar *zero-scalar*))
              (list nil *zero-encoding*))

(assert-equal (mv-list 2 (rlp-encode-bytes *zero-bytes*))
              (list nil *zero-encoding*))

(assert-equal (mv-list 2 (rlp-encode-tree *zero-tree*))
              (list nil *zero-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-scalar *zero-encoding*))
              (list nil *zero-scalar*))

(assert-equal (mv-list 2 (rlp-decodex-bytes *zero-encoding*))
              (list nil *zero-bytes*))

(assert-equal (mv-list 2 (rlp-decodex-tree *zero-encoding*))
              (list nil *zero-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *encoded-0-bytes*
  (list 0))

(defconst *encoded-0-tree*
  (rlp-tree-leaf *encoded-0-bytes*))

(defconst *encoded-0-encoding*
  (list 0))

(assert-equal (mv-list 2 (rlp-encode-bytes *encoded-0-bytes*))
              (list nil *encoded-0-encoding*))

(assert-equal (mv-list 2 (rlp-encode-tree *encoded-0-tree*))
              (list nil *encoded-0-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-bytes *encoded-0-encoding*))
              (list nil *encoded-0-bytes*))

(assert-equal (mv-list 2 (rlp-decodex-tree *encoded-0-encoding*))
              (list nil *encoded-0-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *encoded-15-bytes*
  (list #x0f))

(defconst *encoded-15-tree*
  (rlp-tree-leaf *encoded-15-bytes*))

(defconst *encoded-15-encoding*
  (list #x0f))

(assert-equal (mv-list 2 (rlp-encode-bytes *encoded-15-bytes*))
              (list nil *encoded-15-encoding*))

(assert-equal (mv-list 2 (rlp-encode-tree *encoded-15-tree*))
              (list nil *encoded-15-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-bytes *encoded-15-encoding*))
              (list nil *encoded-15-bytes*))

(assert-equal (mv-list 2 (rlp-decodex-tree *encoded-15-encoding*))
              (list nil *encoded-15-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *encoded-1024-bytes*
  (list #x04 #x00))

(defconst *encoded-1024-tree*
  (rlp-tree-leaf *encoded-1024-bytes*))

(defconst *encoded-1024-encoding*
  (list #x82 #x04 #x00))

(assert-equal (mv-list 2 (rlp-encode-bytes *encoded-1024-bytes*))
              (list nil *encoded-1024-encoding*))

(assert-equal (mv-list 2 (rlp-encode-tree *encoded-1024-tree*))
              (list nil *encoded-1024-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-bytes *encoded-1024-encoding*))
              (list nil *encoded-1024-bytes*))

(assert-equal (mv-list 2 (rlp-decodex-tree *encoded-1024-encoding*))
              (list nil *encoded-1024-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *set-theory-0-tree*
  (rlp-tree-branch nil))

(defconst *set-theory-1-tree*
  (rlp-tree-branch (list *set-theory-0-tree*)))

(defconst *set-theory-2-tree*
  (rlp-tree-branch (list *set-theory-0-tree*
                         *set-theory-1-tree*)))

(defconst *set-theory-3-tree*
  (rlp-tree-branch (list *set-theory-0-tree*
                         *set-theory-1-tree*
                         *set-theory-2-tree*)))

(defconst *set-theory-3-encoding*
  (list #xc7 #xc0 #xc1 #xc0 #xc3 #xc0 #xc1 #xc0))

(assert-equal (mv-list 2 (rlp-encode-tree *set-theory-3-tree*))
              (list nil *set-theory-3-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-tree *set-theory-3-encoding*))
              (list nil *set-theory-3-tree*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *lorem-ipsum-bytes*
  (string=>nats "Lorem ipsum dolor sit amet, consectetur adipisicing elit"))

(defconst *lorem-ipsum-tree*
  (rlp-tree-leaf *lorem-ipsum-bytes*))

(defconst *lorem-ipsum-encoding*
  (list #xb8
        #x38
        (char-code #\L)
        (char-code #\o)
        (char-code #\r)
        (char-code #\e)
        (char-code #\m)
        (char-code #\Space)
        (char-code #\i)
        (char-code #\p)
        (char-code #\s)
        (char-code #\u)
        (char-code #\m)
        (char-code #\Space)
        (char-code #\d)
        (char-code #\o)
        (char-code #\l)
        (char-code #\o)
        (char-code #\r)
        (char-code #\Space)
        (char-code #\s)
        (char-code #\i)
        (char-code #\t)
        (char-code #\Space)
        (char-code #\a)
        (char-code #\m)
        (char-code #\e)
        (char-code #\t)
        (char-code #\,)
        (char-code #\Space)
        (char-code #\c)
        (char-code #\o)
        (char-code #\n)
        (char-code #\s)
        (char-code #\e)
        (char-code #\c)
        (char-code #\t)
        (char-code #\e)
        (char-code #\t)
        (char-code #\u)
        (char-code #\r)
        (char-code #\Space)
        (char-code #\a)
        (char-code #\d)
        (char-code #\i)
        (char-code #\p)
        (char-code #\i)
        (char-code #\s)
        (char-code #\i)
        (char-code #\c)
        (char-code #\i)
        (char-code #\n)
        (char-code #\g)
        (char-code #\Space)
        (char-code #\e)
        (char-code #\l)
        (char-code #\i)
        (char-code #\t)))

(assert-equal (mv-list 2 (rlp-encode-bytes *lorem-ipsum-bytes*))
              (list nil *lorem-ipsum-encoding*))

(assert-equal (mv-list 2 (rlp-encode-tree *lorem-ipsum-tree*))
              (list nil *lorem-ipsum-encoding*))

(assert-equal (mv-list 2 (rlp-decodex-bytes *lorem-ipsum-encoding*))
              (list nil *lorem-ipsum-bytes*))

(assert-equal (mv-list 2 (rlp-decodex-tree *lorem-ipsum-encoding*))
              (list nil *lorem-ipsum-tree*))
