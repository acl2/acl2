; A formal specification of the TEA block cipher
;
; Copyright (C) 2016-2023 Kestrel Institute
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
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/unpackbv" :dir :system)
(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/bv-array-write" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/typed-lists-light/all-integerp2" :dir :system))
(local (include-book "kestrel/bv-lists/bv-arrays" :dir :system))

;move
(local
 (defthm unsigned-byte-listp-forward-to-all-integerp
   (implies (unsigned-byte-listp n x)
            (all-integerp x))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable unsigned-byte-listp)))))

(defconst *delta* #x9e3779b9)

;; Returns (mv y z).
(defun tea-encrypt-loop (n y z sum k)
  (declare (xargs :guard (and (unsigned-byte-p 32 n) ;n<=32
                              (unsigned-byte-p 32 y)
                              (unsigned-byte-p 32 z)
                              (unsigned-byte-p 32 sum)
                              (bv-arrayp 32 4 k))))
  (if (zp n)
      (mv y z)
    (let* ((n (+ -1 n))
           (sum (bvplus 32 sum *delta*))
           (y (bvplus 32 y (bvxor 32 (bvplus 32 (bvshl 32 z 4) (bv-array-read 32 4 0 k))
                                  (bvxor 32 (bvplus 32 z sum)
                                         (bvplus 32 (bvshr 32 z 5) ;unsigned right-shift
                                                 (bv-array-read 32 4 1 k))))))
           (z (bvplus 32 z (bvxor 32 (bvplus 32 (bvshl 32 y 4) (bv-array-read 32 4 2 k))
                                  (bvxor 32 (bvplus 32 y sum)
                                         (bvplus 32 (bvshr 32 y 5) ;unsigned right-shift
                                                 (bv-array-read 32 4 3 k)))))))
      (tea-encrypt-loop n y z sum k))))

;; encrypt value V with key K
(defun tea-encrypt (v k)
  (declare (xargs :guard (and (bv-arrayp 32 2 v)
                              (bv-arrayp 32 4 k))))
  (let* ((y (bv-array-read 32 2 0 v))
         (z (bv-array-read 32 2 1 v))
         (sum 0)
         (n 32))
    (mv-let (y z)
      (tea-encrypt-loop n y z sum k)
      (bv-array-write 32 2 0 y (bv-array-write 32 2 1 z '(0 0))))))

;; I/O interface:

;takes a list of 8 bytes
(defun pack-tea-input (bytes)
  (declare (xargs :guard (and (unsigned-byte-listp 8 bytes)
                              (= 8 (len bytes)))))
  (bv-array-write 32 2 0 (packbv 4 8 (firstn 4 bytes))
                  (bv-array-write 32 2 1 (packbv 4 8 (nthcdr 4 bytes)) '(0 0))))

;takes a list of 16 bytes
(defun pack-tea-key (bytes)
  (declare (xargs :guard (and (unsigned-byte-listp 8 bytes)
                              (= 16 (len bytes)))))
  (bv-array-write 32 4 0 (packbv 4 8 (firstn 4 bytes))
                  (bv-array-write 32 4 1 (packbv 4 8 (subrange 4 7 bytes))
                                  (bv-array-write 32 4 2 (packbv 4 8 (subrange 8 11 bytes))
                                                  (bv-array-write 32 4 3 (packbv 4 8 (subrange 12 15 bytes))
                                                                  '(0 0 0 0))))))

;takes an array of 2 ints, returns a list of 8 bytes
(defun unpack-tea-output (ints)
  (declare (xargs :guard (bv-arrayp 32 2 ints)))
  (let ((first (bv-array-read 32 2 0 ints))
        (second (bv-array-read 32 2 1 ints)))
    (append (unpackbv 4 8 first)
            (unpackbv 4 8 second))))

;; key is a list of 16 bytes, input is a list of 8 bytes
;; Returns a list of 8 bytes.
(defun tea-encrypt-spec (key input)
  (declare (xargs :guard (and (unsigned-byte-listp 8 key)
                              (= 16 (len key))
                              (unsigned-byte-listp 8 input)
                              (= 8 (len input)))))
  (unpack-tea-output
   (tea-encrypt (pack-tea-input input)
                (pack-tea-key key))))
