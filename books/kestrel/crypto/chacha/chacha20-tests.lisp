; Tests for the chacha20.lisp
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CHACHA")

;; The tests mostly come from RFC 8439:
;; https://datatracker.ietf.org/doc/html/rfc8439
;; Section numbers below refer to this RFC.

(include-book "chacha20")

;; Sec 2.1
(thm
  (let* (;; (a #x11111111)
         (b #x01020304)
         (c #x77777777)
         (d #x01234567)
         (c (bvplus 32 c d)))
    (and (equal c #x789abcde)
         (let ((b (bvxor 32 b c)))
           (and (equal b #x7998bfda)
                (let ((b (leftrotate 32 7 b)))
                  (equal b #xcc5fed3c)))))))

;; Sec 2.1.1
;; Test for the quarter round
(thm
  (let ((a #x11111111)
        (b #x01020304)
        (c #x9b8d6f43)
        (d #x01234567))
    (mv-let (a b c d)
      (quarter-round a b c d)
      (and (equal a #xea2a92f4)
           (equal b #xcb1cf8ce)
           (equal c #x4581472e)
           (equal d #x5881c4bb)))))

;; Sec 2.2.1
(thm
  (equal (quarterround 2 7 8 13 (list #x879531e0 #xc5ecf37d #x516461b1 #xc9a62f8a
                                      #x44c20ef3 #x3390af7f #xd9fc690b #x2a5f714c
                                      #x53372767 #xb00a5631 #x974c541a #x359e9963
                                      #x5c971061 #x3d631689 #x2098d9d6 #x91dbd320))
         (list
           #x879531e0 #xc5ecf37d #xbdb886dc #xc9a62f8a
           #x44c20ef3 #x3390af7f #xd9fc690b #xcfacafd2
           #xe46bea80 #xb00a5631 #x974c541a #x359e9963
           #x5c971061 #xccc07c79 #x2098d9d6 #x91dbd320)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sec 2.3.2
(defconst *key* '(#x00 #x01 #x02 #x03 #x04 #x05 #x06 #x07 #x08 #x09 #x0a #x0b #x0c #x0d #x0e #x0f #x10 #x11 #x12 #x13 #x14 #x15 #x16 #x17 #x18 #x19 #x1a #x1b #x1c #x1d #x1e #x1f))

;; Sec 2.3.2
(defconst *nonce* '(#x00 #x00 #x00 #x09 #x00 #x00 #x00 #x4a #x00 #x00 #x00 #x00))

;; Sec 2.3.2
(thm
  (equal (initial-state *key* 1 *nonce* 0)
         '(#x61707865 #x3320646e #x79622d32 #x6b206574
           #x03020100 #x07060504 #x0b0a0908 #x0f0e0d0c
           #x13121110 #x17161514 #x1b1a1918 #x1f1e1d1c
           #x00000001 #x09000000 #x4a000000 #x00000000)))

;; Sec 2.3.2
(thm
  (equal (double-rounds 1 (initial-state *key* 1 *nonce* 0))
         '(#x837778ab #xe238d763 #xa67ae21e #x5950bb2f
           #xc4f2d0c7 #xfc62bb2f #x8fa018fc #x3f5ec7b7
           #x335271c2 #xf29489f3 #xeabda8fc #x82e46ebd
           #xd19c12b4 #xb04e16de #x9e83d0cb #x4e3c50a2)))

;; Sec 2.3.2
(thm
  (let* ((state (initial-state *key* 1 *nonce* 0))
         (initial-state state)
         (state (double-rounds 1 state))
         (state (bvplus-list 32 state initial-state)))
    (equal state
           '(#xe4e7f110 #x15593bd1 #x1fdd0f50 #xc47120a3
             #xc7f4d1c7 #x0368c033 #x9aaa2204 #x4e6cd4c3
             #x466482d2 #x09aa9f07 #x05d7c214 #xa2028bd9
             #xd19c12b5 #xb94e16de #xe883d0cb #x4e3c50a2))))

;; Sec 2.3.2
(thm
  (equal (chacha20-block *key* 1 *nonce* 0)
         '(#x10 #xf1 #xe7 #xe4 #xd1 #x3b #x59 #x15 #x50 #x0f #xdd #x1f #xa3 #x20 #x71 #xc4
           #xc7 #xd1 #xf4 #xc7 #x33 #xc0 #x68 #x03 #x04 #x22 #xaa #x9a #xc3 #xd4 #x6c #x4e
           #xd2 #x82 #x64 #x46 #x07 #x9f #xaa #x09 #x14 #xc2 #xd7 #x05 #xd9 #x8b #x02 #xa2
           #xb5 #x12 #x9c #xd1 #xde #x16 #x4e #xb9 #xcb #xd0 #x83 #xe8 #xa2 #x50 #x3c #x4e)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sec 2.4.2
;; The key used in this section is just *key*, defined above, but
;; this nonce is different.
(defconst *nonce2* '(#x00 #x00 #x00 #x00 #x00 #x00 #x00 #x4a #x00 #x00 #x00 #x00))

(defconst *plaintext-sunscreen*
  '(#x4c #x61 #x64 #x69 #x65 #x73 #x20 #x61 #x6e #x64 #x20 #x47 #x65 #x6e #x74 #x6c
    #x65 #x6d #x65 #x6e #x20 #x6f #x66 #x20 #x74 #x68 #x65 #x20 #x63 #x6c #x61 #x73
    #x73 #x20 #x6f #x66 #x20 #x27 #x39 #x39 #x3a #x20 #x49 #x66 #x20 #x49 #x20 #x63
    #x6f #x75 #x6c #x64 #x20 #x6f #x66 #x66 #x65 #x72 #x20 #x79 #x6f #x75 #x20 #x6f
    #x6e #x6c #x79 #x20 #x6f #x6e #x65 #x20 #x74 #x69 #x70 #x20 #x66 #x6f #x72 #x20
    #x74 #x68 #x65 #x20 #x66 #x75 #x74 #x75 #x72 #x65 #x2c #x20 #x73 #x75 #x6e #x73
    #x63 #x72 #x65 #x65 #x6e #x20 #x77 #x6f #x75 #x6c #x64 #x20 #x62 #x65 #x20 #x69
    #x74 #x2e))

(defconst *ciphertext-sunscreen*
  '(#x6e #x2e #x35 #x9a #x25 #x68 #xf9 #x80 #x41 #xba #x07 #x28 #xdd #x0d #x69 #x81
    #xe9 #x7e #x7a #xec #x1d #x43 #x60 #xc2 #x0a #x27 #xaf #xcc #xfd #x9f #xae #x0b
    #xf9 #x1b #x65 #xc5 #x52 #x47 #x33 #xab #x8f #x59 #x3d #xab #xcd #x62 #xb3 #x57
    #x16 #x39 #xd6 #x24 #xe6 #x51 #x52 #xab #x8f #x53 #x0c #x35 #x9f #x08 #x61 #xd8
    #x07 #xca #x0d #xbf #x50 #x0d #x6a #x61 #x56 #xa3 #x8e #x08 #x8a #x22 #xb6 #x5e
    #x52 #xbc #x51 #x4d #x16 #xcc #xf8 #x06 #x81 #x8c #xe9 #x1a #xb7 #x79 #x37 #x36
    #x5a #xf9 #x0b #xbf #x74 #xa3 #x5b #xe6 #xb4 #x0b #x8e #xed #xf2 #x78 #x5e #x42
    #x87 #x4d))

(thm
  (equal (chacha20 *key* 1 *nonce2* *plaintext-sunscreen* nil)
         *ciphertext-sunscreen*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests involving the carry option:

;; The 2 versions of the spec (with and without the carry option) agree for a single block:
(thm
  (equal (chacha20 (acl2::repeat 32 0) (+ -1 (expt 2 32)) (acl2::repeat 12 0) (acl2::repeat 64 0) nil)
         (chacha20 (acl2::repeat 32 0) (+ -1 (expt 2 32)) (acl2::repeat 12 0) (acl2::repeat 64 0) t)))

;; The 2 versions agree for a single block (general proof):
(local (include-book "kestrel/bv/slice" :dir :system))
(thm
  (implies (and (= 64 (len plaintext)) ; only one block
                (unsigned-byte-listp 8 key)
                (= 32 (len key))
                (unsigned-byte-p 32 counter)
                (unsigned-byte-listp 8 nonce)
                (= 12 (len nonce))
                (unsigned-byte-listp 8 plaintext)
                (booleanp carryp))
           (equal (chacha20 key counter nonce plaintext nil)
                  (chacha20 key counter nonce plaintext t)))
  :hints (("Goal" :expand ((chacha20-loop 0 key counter nonce plaintext nil nil)
                           (chacha20-loop 0 key counter nonce plaintext nil t))
           :in-theory (enable chacha20-loop))))

;; But the two versions can differ for multiple blocks, because the counter
;; increment can overflow into the nonce.  Here we use the maximum 32-bit value
;; for the counter so that incrementing it overflows (we use 0s for all other
;; inputs):
(thm
  (not
    (equal (chacha20 (acl2::repeat 32 0) (+ -1 (expt 2 32)) (acl2::repeat 12 0) (acl2::repeat 128 0) nil)
           (chacha20 (acl2::repeat 32 0) (+ -1 (expt 2 32)) (acl2::repeat 12 0) (acl2::repeat 128 0) t))))
