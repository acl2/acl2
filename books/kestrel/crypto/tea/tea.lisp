; A formal specification of the TEA block cipher
;
; Copyright (C) 2016-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;See: Wheeler, David J.; Needham, Roger M. (1994-12-16). "TEA, a tiny encryption
;algorithm". Lecture Notes in Computer Science (Leuven, Belgium: Fast Software
;Encryption: Second International Workshop) 1008:
;363 366. doi:10.1007/3-540-60590-8_29.

;; TODO: Consider making a TEA package.

(include-book "kestrel/bv/bvshl" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvminus" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/unpackbv" :dir :system)
(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
;(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/typed-lists-light/integer-listp2" :dir :system))
(local (include-book "kestrel/typed-lists-light/integer-listp" :dir :system))
(local (include-book "kestrel/bv-lists/bv-arrays" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(in-theory (disable mv-nth))

;move
;; (local
;;  (defthm unsigned-byte-listp-forward-to-all-integerp
;;    (implies (unsigned-byte-listp n x)
;;             (all-integerp x))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal" :in-theory (enable unsigned-byte-listp)))))

(defconst *delta* #x9e3779b9)

;; Calculates the value added to y or z.
;; Also used in decryption.
(defund tea-step (val ; y or z
                  sum
                  keya ; k[0] or k[2]
                  keyb ; k[1] or k[3]
                  )
  (declare (xargs :guard (and (unsigned-byte-p 32 val)
                              (unsigned-byte-p 32 sum)
                              (unsigned-byte-p 32 keya)
                              (unsigned-byte-p 32 keyb))))
  (bvxor 32
         (bvplus 32 (bvshl 32 val 4) keya)
         (bvxor 32
                (bvplus 32 val sum)
                (bvplus 32 (bvshr 32 val 5) keyb))))

;; This is separate so we can keep it closed.
;; Does not handle the update to sum.
;; Returns (mv y z).
(defund tea-encrypt-loop-body (y z sum k)
  (declare (xargs :guard (and (unsigned-byte-p 32 y)
                              (unsigned-byte-p 32 z)
                              (unsigned-byte-p 32 sum)
                              (bv-arrayp 32 4 k))))
  (let* ((y (bvplus 32 y (tea-step z sum (bv-array-read 32 4 0 k) (bv-array-read 32 4 1 k))))
         (z (bvplus 32 z (tea-step y sum (bv-array-read 32 4 2 k) (bv-array-read 32 4 3 k)))))
    (mv y z)))

(defthm tea-encrypt-loop-body-return-type
  (and (unsigned-byte-p 32 (mv-nth 0 (tea-encrypt-loop-body y z sum k)))
       (unsigned-byte-p 32 (mv-nth 1 (tea-encrypt-loop-body y z sum k))))
  :hints (("Goal" :in-theory (enable tea-encrypt-loop-body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv y z).
(defund tea-encrypt-loop (n y z sum k)
  (declare (xargs :guard (and (unsigned-byte-p 32 n) ;n<=32
                              (unsigned-byte-p 32 y)
                              (unsigned-byte-p 32 z)
                              (unsigned-byte-p 32 sum)
                              (bv-arrayp 32 4 k))))
  (if (zp n)
      (mv y z)
    (let ((n (+ -1 n))
          (sum (bvplus 32 sum *delta*)))
      (mv-let (y z)
          (tea-encrypt-loop-body y z sum k)
        (tea-encrypt-loop n y z sum k)))))

(defthm tea-encrypt-loop-return-type
  (implies (and (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 z))
           (and (unsigned-byte-p 32 (mv-nth 0 (tea-encrypt-loop n y z sum k)))
                (unsigned-byte-p 32 (mv-nth 1 (tea-encrypt-loop n y z sum k)))))
  :hints (("Goal" :in-theory (enable tea-encrypt-loop))))

(defthm tea-encrypt-loop-body-of-bvchop-32-arg3
  (equal (tea-encrypt-loop-body y z (bvchop 32 sum) k)
         (tea-encrypt-loop-body y z sum k))
  :hints (("Goal" :in-theory (enable tea-encrypt-loop-body tea-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is what the Wheeler and Needham paper calls the Encode Routine.
;; encrypt value V with key K
;; Returns an array of two bv32s.
(defund tea-encrypt (v k)
  (declare (xargs :guard (and (bv-arrayp 32 2 v)
                              (bv-arrayp 32 4 k))))
  (let* ((y (bv-array-read 32 2 0 v))
         (z (bv-array-read 32 2 1 v))
         (sum 0)
         (n 32))
    (mv-let (y z)
      (tea-encrypt-loop n y z sum k)
      (bv-array-write 32 2 0 y (bv-array-write 32 2 1 z '(0 0))))))

(defthm bv-arrayp-of-tea-encrypt
  (bv-arrayp 32 2 (tea-encrypt v k))
  :hints (("Goal" :in-theory (enable tea-encrypt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is separate so we can keep it closed.
;; Does not handle the update to sum.
;; Returns (mv y z).
(defund tea-decrypt-loop-body (y z sum k)
  (declare (xargs :guard (and (unsigned-byte-p 32 y)
                              (unsigned-byte-p 32 z)
                              (unsigned-byte-p 32 sum)
                              (bv-arrayp 32 4 k))))
  (let* ((z (bvminus 32 z (tea-step y sum (bv-array-read 32 4 2 k) (bv-array-read 32 4 3 k))))
         (y (bvminus 32 y (tea-step z sum (bv-array-read 32 4 0 k) (bv-array-read 32 4 1 k)))))
    (mv y z)))

(defthm tea-decrypt-loop-body-return-type
  (and (unsigned-byte-p 32 (mv-nth 0 (tea-decrypt-loop-body y z sum k)))
       (unsigned-byte-p 32 (mv-nth 1 (tea-decrypt-loop-body y z sum k))))
  :hints (("Goal" :in-theory (enable tea-decrypt-loop-body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv y z).
(defund tea-decrypt-loop (n y z sum k)
  (declare (xargs :guard (and (unsigned-byte-p 32 n) ;n<=32
                              (unsigned-byte-p 32 y)
                              (unsigned-byte-p 32 z)
                              (unsigned-byte-p 32 sum)
                              (bv-arrayp 32 4 k))))
  (if (zp n)
      (mv y z)
    (let ((n (+ -1 n)))
      (mv-let (y z)
          (tea-decrypt-loop-body y z sum k)
        (let ((sum (bvminus 32 sum *delta*)))
          (tea-decrypt-loop n y z sum k))))))

(defthm tea-decrypt-loop-return-type
  (implies (and (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 z))
           (and (unsigned-byte-p 32 (mv-nth 0 (tea-decrypt-loop n y z sum k)))
                (unsigned-byte-p 32 (mv-nth 1 (tea-decrypt-loop n y z sum k)))))
  :hints (("Goal" :in-theory (enable tea-decrypt-loop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is what the Wheeler and Needham paper calls the Decode Routine.
;; decrypt value V with key K
;; Returns an array of two bv32s.
(defund tea-decrypt (v k)
  (declare (xargs :guard (and (bv-arrayp 32 2 v)
                              (bv-arrayp 32 4 k))))
  (let* ((n 32)
         (y (bv-array-read 32 2 0 v))
         (z (bv-array-read 32 2 1 v))
         (sum (bvshl 32 *delta* 5) ; more generally, this is (bvmult 32 n *delta*)
           ))
    (mv-let (y z)
        (tea-decrypt-loop n y z sum k)
      (bv-array-write 32 2 0 y (bv-array-write 32 2 1 z '(0 0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I/O interface:

;takes a list of 8 bytes
(defund pack-tea-input (bytes)
  (declare (xargs :guard (and (unsigned-byte-listp 8 bytes)
                              (= 8 (len bytes)))))
  (bv-array-write 32 2 0 (packbv 4 8 (firstn 4 bytes))
                  (bv-array-write 32 2 1 (packbv 4 8 (nthcdr 4 bytes)) '(0 0))))

(defthm bv-arrayp-of-pack-tea-input
  (bv-arrayp 32 2 (pack-tea-input k))
  :hints (("Goal" :in-theory (enable pack-tea-input))))

;takes a list of 16 bytes
(defund pack-tea-key (bytes)
  (declare (xargs :guard (and (unsigned-byte-listp 8 bytes)
                              (= 16 (len bytes)))))
  (bv-array-write 32 4 0 (packbv 4 8 (firstn 4 bytes))
                  (bv-array-write 32 4 1 (packbv 4 8 (subrange 4 7 bytes))
                                  (bv-array-write 32 4 2 (packbv 4 8 (subrange 8 11 bytes))
                                                  (bv-array-write 32 4 3 (packbv 4 8 (subrange 12 15 bytes))
                                                                  '(0 0 0 0))))))
(defthm bv-arrayp-of-pack-tea-key
  (bv-arrayp 32 4 (pack-tea-key v))
  :hints (("Goal" :in-theory (enable pack-tea-key))))


;takes an array of 2 ints, returns a list of 8 bytes
(defund unpack-tea-output (ints)
  (declare (xargs :guard (bv-arrayp 32 2 ints)))
  (let ((first (bv-array-read 32 2 0 ints))
        (second (bv-array-read 32 2 1 ints)))
    (append (unpackbv 4 8 first)
            (unpackbv 4 8 second))))

(defthm unpack-tea-output-return-type
  (and (equal (len (unpack-tea-output ints)) 8)
       (unsigned-byte-listp 8 (unpack-tea-output ints)))
  :hints (("Goal" :in-theory (enable unpack-tea-output))))

;; key is a list of 16 bytes, input is a list of 8 bytes
;; Returns a list of 8 bytes.
(defun tea-encrypt-spec (key input)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 16 (len key))
                              (unsigned-byte-listp 8 input)
                              (= 8 (len input)))
                  :guard-hints (("Goal" :in-theory (enable tea-encrypt pack-tea-key pack-tea-input))) ; todo
                  ))
  (unpack-tea-output
   (tea-encrypt (pack-tea-input input)
                (pack-tea-key key))))

;; key is a list of 16 bytes, input is a list of 8 bytes
;; Returns a list of 8 bytes.
(defun tea-decrypt-spec (key input)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 16 (len key))
                              (unsigned-byte-listp 8 input)
                              (= 8 (len input)))
                  :guard-hints (("Goal" :in-theory (enable tea-decrypt pack-tea-key pack-tea-input))) ; todo
                  ))
  (unpack-tea-output
   (tea-decrypt (pack-tea-input input)
                (pack-tea-key key))))
