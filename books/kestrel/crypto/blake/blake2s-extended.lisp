; A variant of blake2s that supports a salt input and a personalization input
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

;; This book formalizes a variant of BLAKE2s that, unlike the one in
;; blake2s.lisp (which follows RFC 7693), supports a salt input and a
;; personalization input.  The modeling of these additional features is
;; intended to correspond to the specification at www.blake2.net/blake2.pdf.
;; However, that specification document describes the core blake machinery
;; differently than the RFC describes it, and we have not re-specified the core
;; machinery in those terms.  Instead, we have made minimal changes/additions
;; to the specification in blake2s.lisp.  The changes in this book have to do
;; with the formation of the parameter block and the XORing of it with the
;; initialization vector.

;; In the book blake2s-extended-validation.lisp, we prove that this extended
;; variant of blake2s agrees with the non-extended blake2s when no salt or
;; personalization is used.

;; Note that this book does not formalize tree hashing, because blake2s hashes
;; data sequentially.

(include-book "blake2s")
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; Returns a list of 8 32-bit words (same shape as the IV).  Not a "block" in
;; the sense of blockp.
(defund parameter-block (digest-byte-length key-byte-length salt personalization)
  (declare (xargs :guard (and (posp digest-byte-length)
                              (<= digest-byte-length 32)
                              (natp key-byte-length)
                              (<= key-byte-length 32)
                              (true-listp salt)
                              (all-unsigned-byte-p 8 salt)
                              (equal 8 (len salt))
                              (true-listp personalization)
                              (all-unsigned-byte-p 8 personalization)
                              (equal 8 (len personalization)))))
  (bytes-to-words (append (list digest-byte-length
                                key-byte-length
                                1       ; fanout (1 for sequential mode)
                                1       ; depth (1 for sequential mode)
                                0 0 0 0 ; leaf length (0 for sequential mode)
                                0 0 0 0 0 0 ; node offset (0 for sequential mode)
                                0 ; node depth (0 for sequential mode)
                                0 ; inner length (0 for sequential mode)
                                )
                          salt
                          personalization)))

(defthm len-of-parameter-block
  (implies (and (equal 8 (len salt))
                (equal 8 (len personalization)))
           (equal (len (parameter-block digest-byte-length key-byte-length salt personalization))
                  8))
  :hints (("Goal" :in-theory (enable parameter-block))))

(defthm all-wordp-of-parameter-block
  (implies (and (posp digest-byte-length)
                (<= digest-byte-length 32)
                (natp key-byte-length)
                (<= key-byte-length 32)
                (all-unsigned-byte-p 8 salt)
                (all-unsigned-byte-p 8 personalization))
           (all-wordp (parameter-block digest-byte-length key-byte-length salt personalization)))
  :hints (("Goal" :in-theory (enable parameter-block))))

;; Xor corresponding elements of two lists of words.
(defund xor-words (words1 words2)
  (declare (xargs :guard (and (true-listp words1)
                              (all-wordp words1)
                              (true-listp words2)
                              (all-wordp words2)
                              (equal (len words1) (len words2)))))
  (if (endp words1)
      nil
    (cons (wordxor (first words1) (first words2))
          (xor-words (rest words1) (rest words2)))))

(defthm all-wordp-of-xor-words
  (implies (and (all-wordp words1)
                (all-wordp words2))
           (all-wordp (xor-words words1 words2)))
  :hints (("Goal" :in-theory (enable xor-words))))

(defthm len-of-xor-words
  (equal (len (xor-words words1 words2))
         (len words1))
  :hints (("Goal" :in-theory (enable xor-words))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This function replaces the function blake2s.
;; Returns the hash, as a list of bytes of length NN.
;; TODO: Think about the case where we have a max length message and a key
(defund blake2s-extended (data-bytes
                          key-bytes
                          salt ; a list of 8 bytes, or nil for no salt
                          personalization ; a list of 8 bytes, or nil for no personalization
                          nn ;; number of hash bytes to produce
                          )
  (declare (xargs :guard (and (all-unsigned-byte-p 8 data-bytes)
                              (true-listp data-bytes)
                              ;; NOTE: We would like to say:
                              ;; (<= (len data-bytes) *max-input-bytes*)
                              ;; but that would allow potential overflows in
                              ;; the second call of F below and in the call of
                              ;; F in LOOP1 above.
                              (<= (len data-bytes)
                                  (if (= 0 (len key-bytes))
                                      *max-input-bytes*
                                    ;; Prevents overflows in the calls of f
                                    ;; below:
                                    (- *max-input-bytes* *bb*)))
                              (all-unsigned-byte-p 8 key-bytes)
                              (true-listp key-bytes)
                              (<= (len key-bytes) *max-key-bytes*)
                              (or (null salt)
                                  (and (true-listp salt)
                                       (all-unsigned-byte-p 8 salt)
                                       (equal 8 (len salt))))
                              (or (null personalization)
                                  (and (true-listp personalization)
                                       (all-unsigned-byte-p 8 personalization)
                                       (equal 8 (len personalization))))
                              (posp nn)
                              (<= nn *max-hash-bytes*))
                  :guard-hints (("Goal" :in-theory (enable wordp natp unsigned-byte-p)))))
  (let* ((ll (len data-bytes))
         (kk (len key-bytes))
         (salt (if salt salt (repeat 8 0)))
         (personalization (if personalization personalization (repeat 8 0)))
         (parameter-block (parameter-block nn kk salt personalization))
         (d (d-blocks data-bytes key-bytes))
         (dd (len d))
         ;; XOR in the parameter block:
         (h (xor-words (iv) parameter-block)) ; this is what differs from the version in blake2s.lisp
         ;; Process padded key and data blocks:
         (h (if (> dd 1)
                ;; The FOR loop:
                (loop1 0 (- dd 2) h d)
              h))
         ;; Final block:
         (h (if (= kk 0)
                (f h (nth (- dd 1) d) ll t)
              (f h
                 (nth (- dd 1) d)
                 (+ ll *bb*)
                 t))))
    ;; Extract first nn bytes to form the returned hash:
    (take nn (words-to-bytes h))))

(defthm len-of-blake2s-extended
  (implies (and (posp nn)
                (<= nn *max-hash-bytes*))
           (equal (len (blake2s-extended data-bytes key-bytes salt personalization nn))
                  nn))
  :hints (("Goal" :in-theory (enable blake2s-extended))))

(defthm all-unsigned-byte-p-of-blake2s-extended
  (implies (<= nn *max-hash-bytes*)
           (all-unsigned-byte-p 8 (blake2s-extended data-bytes key-bytes salt personalization nn)))
  :hints (("Goal" :in-theory (enable blake2s-extended))))
