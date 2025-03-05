; A formal specification of the ChaCha20 hash function
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CHACHA")

;; A formalization of ChaCha20, described in RFC 8439:
;; https://datatracker.ietf.org/doc/html/rfc8439
;; Section numbers below refer to this RFC.

;; See tests in chacha20-tests.lisp

(include-book "portcullis")
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/leftrotate" :dir :system)
(include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system)
(include-book "kestrel/bv-lists/map-packbv-little" :dir :system)
(include-book "kestrel/bv-lists/map-unpackbv-little" :dir :system)
(include-book "kestrel/bv-lists/packbv-little" :dir :system)
(include-book "kestrel/bv-lists/bvplus-list" :dir :system)
(include-book "kestrel/bv-lists/bvxor-list" :dir :system)
(include-book "kestrel/typed-lists-light/all-all-integerp" :dir :system)
(include-book "kestrel/lists-light/group" :dir :system)
(include-book "kestrel/lists-light/ungroup" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/typed-lists-light/all-integerp2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(local (in-theory (e/d (acl2::all-integerp-when-nat-listp)
                       (nth update-nth len))))

(local
  (defthm all-integerp-of-firstn
    (implies (acl2::all-integerp x)
             (acl2::all-integerp (firstn n x)))
    :hints (("Goal" :in-theory (enable firstn)))))

(local
  (defthm all-all-integerp-of-group
    (implies (acl2::all-integerp x)
             (acl2::all-all-integerp (group n x)))
    :hints (("Goal" :in-theory (enable group)))))

(local
  (defthm all-integerp-of-ungroup
    (implies (and (acl2::all-all-integerp x)
                  ; (posp n)
                  (acl2::items-have-len n x)
                  )
             (acl2::all-integerp (ungroup n x)))
    :hints (("Goal" :in-theory (enable ungroup acl2::items-have-len)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sec 1.1
;; Despite the fact that the state is depicted graphically as 4x4 array, we use
;; a flat list for the state to support indexing it using indices 0 to 15.
(defun statep (state)
  (declare (xargs :guard t))
  (and (unsigned-byte-listp 32 state)
       (= (len state) 16)))

(local
  (defthm true-listp-when-statep
    (implies (statep state)
             (true-listp state))
    :hints (("Goal" :in-theory (enable statep)))))

(local
  (defthm len-when-statep
    (implies (statep state)
             (equal (len state)
                    16))
    :hints (("Goal" :in-theory (enable statep)))))

;; Sec 2.1
(defun quarter-round (a b c d)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b)
                              (unsigned-byte-p 32 c)
                              (unsigned-byte-p 32 d))))
  (let* ((a (bvplus 32 a b)) (d (bvxor 32 d a)) (d (leftrotate 32 16 d))
         (c (bvplus 32 c d)) (b (bvxor 32 b c)) (b (leftrotate 32 12 b))
         (a (bvplus 32 a b)) (d (bvxor 32 d a)) (d (leftrotate 32 8 d))
         (c (bvplus 32 c d)) (b (bvxor 32 b c)) (b (leftrotate 32 7 b)))
    (mv a b c d)))

;; Sec 2.2
(defund quarterround (x y z w state)
  (declare (xargs :guard (and (natp x)
                              (< x 16)
                              (natp y)
                              (< y 16)
                              (natp z)
                              (< z 16)
                              (natp w)
                              (< w 16)
                              (statep state))))
  (mv-let (a b c d)
    (quarter-round (nth x state)
                   (nth y state)
                   (nth z state)
                   (nth w state))
    (let* ((state (update-nth x a state))
           (state (update-nth y b state))
           (state (update-nth z c state))
           (state (update-nth w d state)))
      state)))

(defthm statep-of-quarterround
  (implies (and (natp x)
                (< x 16)
                (natp y)
                (< y 16)
                (natp z)
                (< z 16)
                (natp w)
                (< w 16)
                (statep state))
           (statep (quarterround x y z w state)))
  :hints (("Goal" :in-theory (enable quarterround))))

;; Sec 2.3
(defun initial-state (key counter nonce)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce)))))
  (append '(#x61707865 #x3320646e #x79622d32 #x6b206574) ; words 0-3
          (map-packbv-little 4 8 (group 4 key))          ; words 4-11
          (list counter)                                 ; word 12
          (map-packbv-little 4 8 (group 4 nonce))        ; words 13-15
          ))

;; Sec 2.3
;; a column round followed by a diagonal round
;; also called inner_block
(defun double-round (state)
  (declare (xargs :guard (statep state)))
  (let* ((state (quarterround 0 4  8 12 state))
         (state (quarterround 1 5  9 13 state))
         (state (quarterround 2 6 10 14 state))
         (state (quarterround 3 7 11 15 state))
         (state (quarterround 0 5 10 15 state))
         (state (quarterround 1 6 11 12 state))
         (state (quarterround 2 7  8 13 state))
         (state (quarterround 3 4  9 14 state)))
    state))

;; Sec 2.3
;; Each iteration does 2 rounds
(defund double-rounds (n state)
  (declare (xargs :guard (and (natp n)
                              (statep state))
                  :measure (nfix (+ 1 (- 10 n)))))
  (if (or (not (mbt (natp n)))
          (> n 10))
      state
    (double-rounds (+ 1 n) (double-round state))))

(defthm statep-of-double-rounds
  (implies (statep state)
           (statep (double-rounds n state)))
  :hints (("Goal" :in-theory (enable double-rounds))))

;; Sec 2.3
(defun chacha20-block (key counter nonce)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce)))))
  (let* ((state (initial-state key counter nonce))
         (initial-state state) ; saved for later
         (state (double-rounds 1 state))
         (state (bvplus-list 32 state initial-state)))
    (ungroup 4 (map-unpackbv-little 4 8 state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sec 2.4
(defun chacha20-loop (j key counter nonce plaintext encrypted-message)
  (declare (xargs :guard (and (natp j)
                              (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce))
                              (unsigned-byte-listp 8 plaintext)
                              (unsigned-byte-listp 8 encrypted-message))
                  :measure (nfix (+ 1 (- (+ (floor (/ (len plaintext) 64) 1) -1) j)))
                  :guard-hints (("Goal" :in-theory (enable acl2::unsigned-byte-listp-rewrite)))))
  (if (or (not (mbt (natp j)))
          (> j (+ (floor (/ (len plaintext) 64) 1) -1)))
      encrypted-message
    (let* ((key-stream (chacha20-block key (bvplus 32 counter j) nonce))
           (block (subrange (* j 64) (+ (* j 64) 63) plaintext))
           (encrypted-message (append encrypted-message (bvxor-list 8 block key-stream))) ;assuming "encrypted_message += means append
           )
      (chacha20-loop (+ 1 j) key counter nonce plaintext encrypted-message))))

;; Sec 2.4
(defun chacha20 (key counter nonce plaintext)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce))
                              (unsigned-byte-listp 8 plaintext))))
  (let* ((encrypted_message (chacha20-loop 0
                                           key
                                           counter
                                           nonce
                                           plaintext
                                           nil ; encrypted_message
                                           ))
         (encrypted_message (if (not (equal (mod (len plaintext) 64) 0))
                                (let* ((j (floor (/ (len plaintext) 64) 1))
                                       (key-stream (chacha20-block key (bvplus 32 counter j) nonce))
                                       (block (subrange (* j 64) (+ (len plaintext) -1) plaintext)) ; might be shorter than a full block
                                       (encrypted_message (append encrypted_message ;assuming "encrypted_message += means append
                                                                  (bvxor-list 8 block key-stream) ; stops when block is exhausted
                                                                  )))
                                  encrypted_message)
                              encrypted_message)))
    encrypted_message))
