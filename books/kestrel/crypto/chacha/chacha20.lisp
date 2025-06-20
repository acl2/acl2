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
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/typed-lists-light/all-integerp2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv-lists/packing" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

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
;; The carry here is not in the RFC but seems necessary to match what implementations actually do.
(defun initial-state (key counter nonce carry)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce))
                              (unsigned-byte-p 32 carry))))
  (append '(#x61707865 #x3320646e #x79622d32 #x6b206574) ; words 0-3
          (map-packbv-little 4 8 (group 4 key))          ; words 4-11
          (list counter)                                 ; word 12
          (let ((nonce-words (map-packbv-little 4 8 (group 4 nonce))))        ; words 13-15
            (if (not (equal 0 carry))
                (cons (bvplus 32 carry (first nonce-words)) (rest nonce-words))
              nonce-words))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sec 2.3
(defund chacha20-block (key counter nonce carry)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce))
                              (unsigned-byte-p 32 carry))))
  (let* ((state (initial-state key counter nonce carry))
         (initial-state state) ; saved for later
         (state (double-rounds 1 state))
         (state (bvplus-list 32 state initial-state)))
    (ungroup 4 (map-unpackbv-little 4 8 state))))

(defthm len-of-chacha20-block
  (implies  (and (unsigned-byte-listp 8 key)
                 (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                 (unsigned-byte-p 32 counter)
                 (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                 (= 12 (len nonce))
                 (unsigned-byte-p 32 carry))
            (equal (len (chacha20-block key counter nonce carry))
                   64))
  :hints (("Goal" :in-theory (enable chacha20-block))))

(defthm unsigned-byte-listp-8-of-chacha20-block
  (implies  (and (unsigned-byte-listp 8 key)
                 (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                 (unsigned-byte-p 32 counter)
                 (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                 (= 12 (len nonce))
                 (unsigned-byte-p 32 carry))
            (unsigned-byte-listp 8 (chacha20-block key counter nonce carry)))
  :hints (("Goal" :in-theory (enable chacha20-block acl2::unsigned-byte-listp-rewrite))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The for loop in chacha20_encrypt (2.4.1).
;; Note: It would be more idiomatic to just increment counter, instead of having a
;; separate j parameter, but here we follow the pseudocode as closely as we can.
;; Note: The term (floor (/ (len plaintext) 64) 1) could instead be written
;; (floor (len plaintext) 64), but the former seemed closer to the pseudocode,
;; with the unary floor function in the pseudocode represented by passing
;; 1 as the second of the two arguments to our floor function.
(defun chacha20-loop (j key counter nonce plaintext encrypted-message carryp)
  (declare (xargs :guard (and (natp j)
                              (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce))
                              (unsigned-byte-listp 8 plaintext)
                              (unsigned-byte-listp 8 encrypted-message)
                              (booleanp carryp))
                  :measure (nfix (+ 1 (- (+ (floor (/ (len plaintext) 64) 1) -1) j)))
                  :guard-hints (("Goal" :in-theory (enable acl2::unsigned-byte-listp-rewrite)))))
  (if (or (not (mbt (natp j)))
          (> j (+ (floor (/ (len plaintext) 64) 1) -1)) ; stop when j exceeds floor(len(plaintext)/64)-1
          )
      encrypted-message
    (let* (;; the pseudocode calls this "keystream" but it is just one block:
           (keystream-block (chacha20-block key
                                             ;; Since 2.3 indicates the block
                                             ;; count parameter is 32-bits, we
                                             ;; use a modular sum here:
                                             (bvplus 32 counter j)
                                             nonce
                                             ;; if the carry flag is set, we pass the high half of counter+j
                                             (if carryp (slice 63 32 (bvplus 64 counter j)) 0)))
           ;; the pseudocode calls this just "block":
           (plaintext-block (subrange (* j 64) (+ (* j 64) 63) plaintext))
           ;; we assume the "+=" operation on the encrypted message represents a concatenation of byte lists:
           ;; See https://www.rfc-editor.org/errata/eid5989
           (encrypted-message (append encrypted-message (bvxor-list 8 plaintext-block keystream-block))))
      ;; same key and nonce:
      (chacha20-loop (+ 1 j) key counter nonce plaintext encrypted-message carryp))))

(defthm unsigned-byte-listp-8-of-chacha20-loop
  (implies (unsigned-byte-listp 8 encrypted-message)
           (unsigned-byte-listp 8 (chacha20-loop j key counter nonce plaintext encrypted-message carryp))))

(local
  (defthmd len-of-chacha20-loop-helper
    (implies (and (natp j)
                  (<= j (floor (/ (len plaintext) 64) 1)))
             (equal (len (chacha20-loop j key counter nonce plaintext encrypted-message carryp))
                    (+ (len encrypted-message)
                       (* 64 (- (floor (/ (len plaintext) 64) 1)
                                j)))))))

(defthm len-of-chacha20-loop
  (equal (len (chacha20-loop 0 key counter nonce plaintext nil carryp))
         (* 64 (floor (/ (len plaintext) 64) 1)))
  :hints (("Goal" :use (:instance len-of-chacha20-loop-helper (j 0)
                                  (encrypted-message nil))
           :in-theory (disable len-of-chacha20-loop-helper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sec 2.4
;; WARNING: The carryp flag should be nil for RFC compliance.  However,
;; implementations tend to implement the carry!
;; Returns the ciphertext.
(defun chacha20 (key counter nonce plaintext carryp)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 32 (len key)) ; key is 32 8-bit bytes = 256 bits
                              (unsigned-byte-p 32 counter)
                              (unsigned-byte-listp 8 nonce) ; nonce is 12 8-bit bytes = 96 bits
                              (= 12 (len nonce))
                              (unsigned-byte-listp 8 plaintext)
                              (booleanp carryp))))
  (let* ((encrypted_message (chacha20-loop 0
                                           key
                                           counter
                                           nonce
                                           plaintext
                                           nil ; initial encrypted_message
                                           carryp))
         (encrypted_message
           (if (not (equal (mod (len plaintext) 64) 0))
               (let* ((j (floor (/ (len plaintext) 64) 1))
                      ;; the pseudocode calls this "keystream" but it is just one block:
                      (keystream-block (chacha20-block key
                                                        (bvplus 32 counter j)
                                                        nonce
                                                        ;; see comment above about the carry flag:
                                                        (if carryp (slice 63 32 (bvplus 64 counter j)) 0)))
                      ;; the pseudocode calls this just "block":
                      (plaintext-block (subrange (* j 64) (+ (len plaintext) -1) plaintext)) ; might be shorter than a full block
                      ;; we assume the "+=" operation on the encrypted message represents a concatenation of byte lists:
                      ;; See https://www.rfc-editor.org/errata/eid5989
                      (encrypted_message (append encrypted_message ;assuming "encrypted_message += means append
                                                 ;; note that bvxor-list stops once its first argument runs out:
                                                 ;; TODO: In the RFC, in [0..len(plaintext)%64], len(plaintext)%64 should probably be len(plaintext)%64 - 1
                                                 ;; See https://www.rfc-editor.org/errata/eid7880
                                                 (bvxor-list 8 plaintext-block keystream-block) ; stops when block is exhausted
                                                 )))
                 encrypted_message)
             encrypted_message)))
    encrypted_message))

;; chacha20 returns a list of bytes, and that list has the same length as the plaintext.
(defthm chacha20-return-type
  (and (unsigned-byte-listp 8 (chacha20 key counter nonce plaintext carryp))
       (equal (len (chacha20 key counter nonce plaintext carryp))
              (len plaintext))))
