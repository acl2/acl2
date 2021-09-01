; Formal specification of BLAKE-256
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

;; Written from https://131002.net/blake/blake.pdf

(include-book "blake-common-32")
(include-book "blake-256-padding")
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/bytes-to-bits" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(local (in-theory (disable true-listp nth))) ;prevent induction

(local
 (defthm true-listp-when-blockp
   (implies (blockp block)
            (true-listp block))))

(defthm all-wordp-of-nthcdr
  (implies (all-wordp words)
           (all-wordp (nthcdr n words)))
  :hints (("Goal" :in-theory (enable all-wordp nthcdr))))

(defconst *c*
  '(#x243F6A88
    #x85A308D3
    #x13198A2E
    #x03707344
    #xA4093822
    #x299F31D0
    #x082EFA98
    #xEC4E6C89
    #x452821E6
    #x38D01377
    #xBE5466CF
    #x34E90C6C
    #xC0AC29B7
    #xC97C50DD
    #x3F84D5B5
    #xB5470917))

;; A chain-value is a list of 8 words.
(defund chain-valuep (cv)
  (declare (xargs :guard t))
  (and (true-listp cv)
       (= 8 (len cv))
       (all-wordp cv)))

(defthm all-wordp-when-chain-valuep
  (implies (chain-valuep cv)
           (all-wordp cv))
  :hints (("Goal" :in-theory (enable chain-valuep))))

;; A salt is a list of 4 words.
(defund saltp (salt)
  (declare (xargs :guard t))
  (and (true-listp salt)
       (= 4 (len salt))
       (all-wordp salt)))

;; A counter is a list of 2 words.
(defund counterp (counter)
  (declare (xargs :guard t))
  (and (true-listp counter)
       (= 2 (len counter))
       (all-wordp counter)))

;; A state is a list of 16 words.
(defund statep (state)
  (declare (xargs :guard t))
  (and (true-listp state)
       (= 16 (len state))
       (all-wordp state)))

(local
 (defthm true-listp-when-statep
   (implies (statep state)
            (true-listp state))
   :hints (("Goal" :in-theory (enable statep)))))

(defthm statep-of-update-nth
  (implies (and (statep block)
                (wordp word)
                (natp n)
                (< n 16))
           (statep (update-nth n word block)))
  :hints (("Goal" :in-theory (enable statep))))

(defthm wordp-of-nth-when-statep
  (implies (and (statep block)
                (natp n)
                (< n 16))
           (wordp (nth n block)))
  :hints (("Goal" :in-theory (enable statep))))

(defund word+ (x y)
  (declare (xargs :guard (and (wordp x)
                              (wordp y))))
  (acl2::bvplus 32 x y))

(defthm wordp-of-word+
  (wordp (word+ x y))
  :hints (("Goal" :in-theory (enable wordp word+))))

(defund wordxor4 (a b c d)
  (declare (xargs :guard (and (wordp a)
                              (wordp b)
                              (wordp c)
                              (wordp d))))
  (wordxor a (wordxor b (wordxor c d))))

(defthm wordp-of-wordxor4
  (wordp (wordxor4 x y z w))
  :hints (("Goal" :in-theory (enable wordp wordxor4))))

;; We use the name counter instead of t since t is not a legal variable name.
(defund initial-state (h s counter)
  (declare (xargs :guard (and (chain-valuep h)
                              (saltp s)
                              (counterp counter))
                  :guard-hints (("Goal" :in-theory (enable chain-valuep saltp counterp)))))
  (list (nth 0 h)
        (nth 1 h)
        (nth 2 h)
        (nth 3 h)
        (nth 4 h)
        (nth 5 h)
        (nth 6 h)
        (nth 7 h)
        (wordxor (nth 0 s) (nth 0 *c*))
        (wordxor (nth 1 s) (nth 1 *c*))
        (wordxor (nth 2 s) (nth 2 *c*))
        (wordxor (nth 3 s) (nth 3 *c*))
        (wordxor (nth 0 counter) (nth 4 *c*))
        (wordxor (nth 0 counter) (nth 5 *c*))
        (wordxor (nth 1 counter) (nth 6 *c*))
        (wordxor (nth 1 counter) (nth 7 *c*))))

(defthm statep-of-initial-state
  (implies (and (chain-valuep h)
                (saltp s)
                (counterp counter))
           (statep (initial-state h s counter)))
  :hints (("Goal" :in-theory (enable initial-state statep chain-valuep))))

;; Computes "G sub i".  Parameters aindex, etc. are the indices (into v) of a,
;; etc.  Returns the new value of v.
(defund apply-g (i aindex bindex cindex dindex r v m)
  (declare (xargs :guard (and (natp i)
                              (<= i 7)
                              (natp aindex)
                              (<= aindex 15)
                              (natp bindex)
                              (<= bindex 15)
                              (natp cindex)
                              (<= cindex 15)
                              (natp dindex)
                              (<= dindex 15)
                              (blockp m)
                              (natp r)
                              (<= r 13)
                              (statep v))
                  :guard-hints (("Goal" :in-theory (enable statep)))))
  (let* ((a (nth aindex v))
         (b (nth bindex v))
         (c (nth cindex v))
         (d (nth dindex v))

         (a (word+ a (word+ b (wordxor (nth (nth (* 2 i) (nth (mod r 10) (sigma))) m)
                                       (nth (nth (+ (* 2 i) 1) (nth (mod r 10) (sigma))) *c*)))))
         (d (rot-word 16 (wordxor d a)))
         (c (word+ c d))
         (b (rot-word 12 (wordxor b c)))
         (a (word+ a (word+ b (wordxor (nth (nth (+ (* 2 i) 1) (nth (mod r 10) (sigma))) m)
                                       (nth (nth (* 2 i) (nth (mod r 10) (sigma))) *c*)))))
         (d (rot-word 8 (wordxor d a)))
         (c (word+ c d))
         (b (rot-word 7 (wordxor b c)))

         (v (update-nth aindex a v))
         (v (update-nth bindex b v))
         (v (update-nth cindex c v))
         (v (update-nth dindex d v)))
    v))

(defthm statep-of-apply-g
  (implies (and (natp i)
                (<= i 7)
                (natp aindex)
                (<= aindex 15)
                (natp bindex)
                (<= bindex 15)
                (natp cindex)
                (<= cindex 15)
                (natp dindex)
                (<= dindex 15)
                (blockp m)
                (natp r)
                (<= r 14)
                (statep v))
           (statep (apply-g i aindex bindex cindex dindex r v m)))
  :hints (("Goal" :in-theory (enable apply-g))))

;; Returns v.
(defund apply-round (r v m)
  (declare (xargs :guard (and (natp r)
                              (<= r 13)
                              (statep v)
                              (blockp m))))
  (let* ((v (apply-g 0 0 4  8 12 r v m))
         (v (apply-g 1 1 5  9 13 r v m))
         (v (apply-g 2 2 6 10 14 r v m))
         (v (apply-g 3 3 7 11 15 r v m))
         (v (apply-g 4 0 5 10 15 r v m))
         (v (apply-g 5 1 6 11 12 r v m))
         (v (apply-g 6 2 7  8 13 r v m))
         (v (apply-g 7 3 4  9 14 r v m)))
    v))

(defthm statep-of-apply-round
  (implies (and (statep v)
                (natp r)
                (<= r 14)
                (blockp m))
           (statep (apply-round r v m)))
  :hints (("Goal" :in-theory (enable apply-round))))

;; Returns v.
(defun apply-rounds (r v m)
  (declare (xargs :guard (and (natp r)
                              (<= r 14)
                              (statep v)
                              (blockp m))
                  :measure (nfix (- 15 r))))
  (if (or (not (mbt (natp r)))
          (<= 14 r))
      v
    (apply-rounds (+ 1 r) (apply-round r v m) m)))

(defthm statep-of-apply-rounds
  (implies (and (statep v)
                ;; (natp r)
                (blockp m))
           (statep (apply-rounds r v m)))
  :hints (("Goal" :in-theory (enable apply-round))))

;; We use the name counter here because t is not a legal name in ACL2.  Returns
;; a new chain-value.
(defund compress (h m s counter)
  (declare (xargs :guard (and (chain-valuep h)
                              (blockp m)
                              (saltp s)
                              (counterp counter))
                  :guard-hints (("Goal" :in-theory (enable chain-valuep saltp)))))
  (let* ((v (initial-state h s counter))
         (v (apply-rounds 0 v m)))
    (list (wordxor4 (nth 0 h) (nth 0 s) (nth 0 v) (nth  8 v))
          (wordxor4 (nth 1 h) (nth 1 s) (nth 1 v) (nth  9 v))
          (wordxor4 (nth 2 h) (nth 2 s) (nth 2 v) (nth 10 v))
          (wordxor4 (nth 3 h) (nth 3 s) (nth 3 v) (nth 11 v))
          (wordxor4 (nth 4 h) (nth 0 s) (nth 4 v) (nth 12 v))
          (wordxor4 (nth 5 h) (nth 1 s) (nth 5 v) (nth 13 v))
          (wordxor4 (nth 6 h) (nth 2 s) (nth 6 v) (nth 14 v))
          (wordxor4 (nth 7 h) (nth 3 s) (nth 7 v) (nth 15 v)))))

(defthm chain-valuep-of-compress
  (chain-valuep (compress h m s counter))
  :hints (("Goal" :in-theory (enable compress chain-valuep))))

;; Divide MSG (a sequence of bits) into a sequence of 32-bit words.
;; Same as sha-256-message-words.
(defund message-words (msg)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg)
                              (true-listp msg)
                              (= 0 (mod (len msg) 32)))))
  (if (endp msg)
      nil
    (cons (packbv 32 1 (take 32 msg))
          (message-words (nthcdr 32 msg)))))

(defthm all-wordp-of-message-words
  (all-wordp (message-words msg))
  :hints (("Goal" :in-theory (enable message-words wordp))))

(defthm len-of-message-words
  (implies (force (equal (mod (len msg) 32) 0))
           (equal (len (message-words msg))
                  (floor (len msg) 32)))
  :hints (("Goal" :in-theory (enable message-words))))

;; Divide WORDS into a sequence of 512-bit blocks.
;; Same as sha-256-message-blocks.
(defund message-blocks (words)
  (declare (xargs :guard (and (all-wordp words)
                              (true-listp words)
                              (= 0 (mod (len words) 16)))))
  (if (endp words)
      nil
    (cons (take 16 words)
          (message-blocks (nthcdr 16 words)))))

;move
(defthm all-wordp-of-take
  (implies (and (all-wordp words)
                (natp n))
           (equal (all-wordp (take n words))
                  (<= n (len words))))
  :hints (("Goal" :in-theory (enable all-wordp take))))

(defthm all-blockp-of-message-blocks
  (implies (and (all-wordp words)
                (true-listp words)
                (= 0 (mod (len words) 16)))
           (all-blockp (message-blocks words)))
  :hints (("Goal" :in-theory (enable message-blocks blockp))))

(defund compress-blocks (i h m s total-bits)
  (declare (xargs :guard (and (natp i)
                              (<= i (len m))
                              (chain-valuep h)
                              (true-listp m)
                              (all-blockp m)
                              (saltp s)
                              (natp total-bits))
                  :measure (nfix (+ 1 (- (len m) i)))
                  :guard-hints (("Goal" :in-theory (enable wordp counterp)))))
  (if (or (not (mbt (natp i)))
          (>= i (len m)))
      h
    (let* ((l (if (<= total-bits (* 512 i))
                  ;; special case (no msg bits in this block):
                  0
                ;; count msg bits up through this block:
                (min total-bits (* 512 (+ 1 i)))))
           ;; TODO: The order of the two counter bytes here seems wrong (in
           ;; particular, it contradicts the endianness of conventions of FIPS
           ;; 180-2, which BLAKE-256 is specified to follow), but this order is
           ;; needed to pass the tests:
           (counter (list (slice 31 0 l)
                          (slice 63 32 l)))
           (h (compress h (nth i m) s counter)))
      (compress-blocks (+ 1 i) h m s total-bits))))

(defthm chain-valuep-of-compress-blocks
  (implies (chain-valuep h)
           (chain-valuep (compress-blocks i h m s total-bits)))
  :hints (("Goal" :in-theory (enable compress-blocks))))

;; Returns a list of bytes
(defun words-to-bytes2 (words)
  (declare (xargs :guard (and (all-wordp words)
                              (true-listp words))))
  (if (endp words)
      nil
    (append (unpackbv 4 8 (first words))
            (words-to-bytes2 (rest words)))))

;; Returns a list of bytes
(defund blake-256-with-salt (msg-bits s)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg-bits)
                              (true-listp msg-bits)
                              (< (len msg-bits) (expt 2 64))
                              (saltp s))))
  (let* ((total-bits (len msg-bits))
         (h (iv))
         (m (message-blocks (message-words (pad msg-bits))))
         (h_n (compress-blocks 0 h m s total-bits)))
    (words-to-bytes2 h_n)))

;; Uses a salt of all 0s.  Returns a list of bytes.
(defund blake-256 (msg-bits)
  (declare (xargs :guard (and (all-unsigned-byte-p 1 msg-bits)
                              (true-listp msg-bits)
                              (< (len msg-bits) (expt 2 64)))))
  (blake-256-with-salt msg-bits (list 0 0 0 0)))

;; Uses a salt of all 0s. Returns a list of bytes.
(defund blake-256-bytes (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (< (len bytes) (expt 2 61)))))
  (blake-256 (bytes-to-bits bytes)))

;(blake-256 nil)
