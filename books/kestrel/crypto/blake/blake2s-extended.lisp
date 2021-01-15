; A variant of blake2s that supports a salt input and a personalization input
;
; Copyright (C) 2021 Kestrel Institute
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
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system)) ;reduce, for unsigned-byte-p-of-mod-of-expt

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

;; This function replaces the function blake2s-main.
;;TODO: Consider the case when ll is the max.  Then (+ ll *bb*) is > 2^64, contrary to the documentation of f.
(defund blake2s-extended-main (d ll kk nn parameter-block)
  (declare (xargs :guard (and (true-listp d)
                              (all-blockp d)
                              (< 0 (len d))
                              (<= (len d) (/ *blake2s-max-data-byte-length* 64)) ;think about this
                              (natp ll)
                              ;; (< ll (- *blake2s-max-data-byte-length* 64))
                              (< ll *blake2s-max-data-byte-length*)
                              (natp kk)
                              (posp nn)
                              (<= nn 32)
                              (true-listp parameter-block)
                              (all-wordp parameter-block)
                              (equal (len parameter-block) 8))
                  :guard-hints (("Goal" :expand ((wordp nn)
                                                 (unsigned-byte-p 64 (+ 64 ll)))
                                 :in-theory (e/d (natp) ((:e expt)))))))
  (let* ((h (xor-words (iv) parameter-block)) ; this is what differs from the version in blake2s.lisp
         (dd (len d))
         (h (if (> dd 1)
                (loop1 0 (- dd 2) h d)
              h))
         (h (if (= kk 0)
                (f h (nth (- dd 1) d) ll t)
              (f h
                 (nth (- dd 1) d)
                 (mod (+ ll *bb*) (expt 2 (* 2 *w*)))
                 t))))
    (take nn (words-to-bytes h))))

(defthm len-of-blake2s-extended-main
  (implies (and (posp nn)
                (<= nn 32))
           (equal (len (blake2s-extended-main d ll kk nn parameter-block))
                  nn))
  :hints (("Goal" :in-theory (enable blake2s-extended-main))))

(defthm all-unsigned-byte-p-of-blake2s-extended-main
  (implies (<= nn 32)
           (all-unsigned-byte-p 8 (blake2s-extended-main d ll kk nn parameter-block)))
  :hints (("Goal" :in-theory (enable blake2s-extended-main))))

;; This function replaces the function blake2s.
;; Returns the hash, as a list of bytes of length NN.
;; TODO: Think about the case where we have a max length message and a key
(defund blake2s-extended (data-bytes
                          key-bytes
                          salt ; a list of 8 bytes, or nil for no salt
                          personalization ; a list of 8 bytes, or nil for no personalization
                          nn ;; number of hash bytes to produce
                          )
  (declare (xargs :guard (and (true-listp data-bytes)
                              (all-unsigned-byte-p 8 data-bytes)
                              ;; TODO I want to say this:
                              ;; (< (len data-bytes) *blake2s-max-data-byte-length*)
                              ;; But there are two potential issues related to
                              ;; very long messages: Adding the key block can
                              ;; make the length of d greater than expected,
                              ;; and the expression (+ ll *bb*) in blake2s-extended-main
                              ;; can overflow.
                              (< (len data-bytes) (- *blake2s-max-data-byte-length* 64))
                              (true-listp key-bytes)
                              (all-unsigned-byte-p 8 key-bytes)
                              (<= (len key-bytes) 32)
                              (or (null salt)
                                  (and (true-listp salt)
                                       (all-unsigned-byte-p 8 salt)
                                       (equal 8 (len salt))))
                              (or (null personalization)
                                  (and (true-listp personalization)
                                       (all-unsigned-byte-p 8 personalization)
                                       (equal 8 (len personalization))))
                              (posp nn)
                              (<= nn 32))))
  (let* ((ll (len data-bytes))
         (kk (len key-bytes))
         (salt (if salt salt (repeat 8 0)))
         (personalization (if personalization personalization (repeat 8 0)))
         (parameter-block (parameter-block nn kk salt personalization))
         (d (d-blocks data-bytes key-bytes)))
    (blake2s-extended-main d
                           ll
                           kk
                           nn
                           parameter-block)))

(defthm len-of-blake2s-extended
  (implies (and (posp nn)
                (<= nn 32))
           (equal (len (blake2s-extended data-bytes key-bytes salt personalization nn))
                  nn))
  :hints (("Goal" :in-theory (enable blake2s-extended))))

(defthm all-unsigned-byte-p-of-blake2s-extended
  (implies (<= nn 32)
           (all-unsigned-byte-p 8 (blake2s-extended data-bytes key-bytes salt personalization nn)))
  :hints (("Goal" :in-theory (enable blake2s-extended))))
