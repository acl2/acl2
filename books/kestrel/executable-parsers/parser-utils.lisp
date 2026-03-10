; Utilities for parsing x86 binaries
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)
(include-book "kestrel/bv/bvcat2" :dir :system)
(include-book "kestrel/lists-light/len-at-least" :dir :system)
(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)
(local(include-book "kestrel/bv-lists/byte-listp" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;; ;; A version of TAKE that throws an error if there are not at least N
;; ;; elements in the list.
;; (defun take-safe (n l)
;;   (declare (xargs :guard (and (natp n)
;;                               (true-listp l))))
;;   (if (> n (len l))
;;       (er hard? 'take-safe "Not enough bytes to take ~x0 of them. "n)
;;     (take n l)))


;; Returns (mv erp first-n-bytes bytes) where BYTES is the bytes that remain after parsing the first N bytes.
;; Rename, since it just takes the bytes but doesn't combine them?
(defund parse-n-bytes (n bytes)
  (declare (xargs :guard (and (natp n) ; seems good to allow 0, in case the size is not fixed
                              (byte-listp bytes))
                  :split-types t)
           (type (integer 0 *) n))
  (if (len-at-least n bytes)
      (mv nil (take n bytes) (nthcdr n bytes))
    (mv :not-enough-bytes nil bytes)))

(defthm mv-nth-0-of-parse-n-bytes-iff
  (implies (natp n)
           (iff (mv-nth 0 (parse-n-bytes n bytes))
                (< (len bytes) n)))
  :hints (("Goal" :in-theory (enable parse-n-bytes))))

(defthmd byte-listp-of-mv-nth-1-of-parse-n-bytes
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 1 (parse-n-bytes n bytes))))
  :hints (("Goal" :in-theory (enable parse-n-bytes))))

(defthm len-of-mv-nth-1-of-parse-n-bytes
  (implies (and (not (mv-nth 0 (parse-n-bytes n bytes)))
                (natp n))
           (equal (len (mv-nth 1 (parse-n-bytes n bytes)))
                  n))
  :hints (("Goal" :in-theory (enable parse-n-bytes))))

(defthm consp-of-mv-nth-1-of-parse-n-bytes
  (implies (and (not (mv-nth 0 (parse-n-bytes n bytes)))
                (natp n))
           (equal (consp (mv-nth 1 (parse-n-bytes n bytes)))
                  (< 0 n)))
  :hints (("Goal" :in-theory (enable parse-n-bytes))))

(defthm len-of-mv-nth-2-of-parse-n-bytes
  (implies (and (not (mv-nth 0 (parse-n-bytes n bytes)))
                (natp n))
           (equal (len (mv-nth 2 (parse-n-bytes n bytes)))
                  (+ (- n) (len bytes))))
  :hints (("Goal" :in-theory (enable parse-n-bytes))))

(defthmd byte-listp-of-mv-nth-2-of-parse-n-bytes
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-n-bytes n bytes))))
  :hints (("Goal" :in-theory (enable parse-n-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp byte bytes) where BYTES is the bytes that remain after parsing the byte.
(defund parse-u8 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (len-at-least 1 bytes)
      (mv nil (first bytes) (rest bytes))
    (mv :not-enough-bytes 0 bytes)))

(defthmd unsigned-byte-p-of-mv-nth-1-of-parse-u8
  (implies (byte-listp bytes)
           (unsigned-byte-p 8 (mv-nth 1 (parse-u8 bytes))))
  :hints (("Goal" :in-theory (enable parse-u8))))

(defthmd natp-of-mv-nth-1-of-parse-u8
  (implies (byte-listp bytes)
           (natp (mv-nth 1 (parse-u8 bytes))))
  :hints (("Goal" :in-theory (enable parse-u8))))

(defthmd byte-listp-of-mv-nth-2-of-parse-u8
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-u8 bytes))))
  :hints (("Goal" :in-theory (enable parse-u8))))

(defthm len-of-mv-nth-2-of-parse-u8
  (implies (not (mv-nth 0 (parse-u8 bytes)))
           (equal (len (mv-nth 2 (parse-u8 bytes)))
                  (+ -1 (len bytes))))
  :hints (("Goal" :in-theory (enable parse-u8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp uint16 bytes) where BYTES is the bytes that remain after parsing the value.
;; This is a little-endian operation, because the least significant byte comes first.
(defund parse-u16 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (len-at-least 2 bytes)
      (mv nil
          ;; second byte is most significant:
          (bvcat 8 (second bytes)
                 8 (first bytes))
          (nthcdr 2 bytes))
    (mv :not-enough-bytes 0 bytes)))

(defthmd unsigned-byte-p-of-mv-nth-1-of-parse-u16
  (implies (byte-listp bytes)
           (unsigned-byte-p 16 (mv-nth 1 (parse-u16 bytes))))
  :hints (("Goal" :in-theory (enable parse-u16))))

(defthmd natp-of-mv-nth-1-of-parse-u16
  (implies t ;(byte-listp bytes)
           (natp (mv-nth 1 (parse-u16 bytes))))
  :hints (("Goal" :in-theory (enable parse-u16))))

(defthmd byte-listp-of-mv-nth-2-of-parse-u16
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-u16 bytes))))
  :hints (("Goal" :in-theory (enable parse-u16))))

(defthm len-of-mv-nth-2-of-parse-u16
  (implies (not (mv-nth 0 (parse-u16 bytes)))
           (equal (len (mv-nth 2 (parse-u16 bytes)))
                  (+ -2 (len bytes))))
  :hints (("Goal" :in-theory (enable parse-u16))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp uint32 bytes) where BYTES is the bytes that remain after parsing the value.
;; This is a little-endian operation, because the least significant byte comes first.
;; TODO: Rename to have "little" in the name, and similarly for similar functions.
(defund parse-u32 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (len-at-least 4 bytes)
      (mv nil
          ;; fourth byte is most significant:
          (bvcat2 8 (fourth bytes)
                       8 (third bytes)
                       8 (second bytes)
                       8 (first bytes))
          (nthcdr 4 bytes))
    (mv :not-enough-bytes 0 bytes)))

(defthmd unsigned-byte-p-of-mv-nth-1-of-parse-u32
  (implies (byte-listp bytes)
           (unsigned-byte-p 32 (mv-nth 1 (parse-u32 bytes))))
  :hints (("Goal" :in-theory (enable parse-u32))))

(defthmd natp-of-mv-nth-1-of-parse-u32
  (implies t ;(byte-listp bytes)
           (natp (mv-nth 1 (parse-u32 bytes))))
  :hints (("Goal" :in-theory (enable parse-u32))))

(defthmd byte-listp-of-mv-nth-2-of-parse-u32
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-u32 bytes))))
  :hints (("Goal" :in-theory (enable parse-u32))))

(defthm len-of-mv-nth-2-of-parse-u32
  (implies (not (mv-nth 0 (parse-u32 bytes)))
           (equal (len (mv-nth 2 (parse-u32 bytes)))
                  (+ -4 (len bytes))))
  :hints (("Goal" :in-theory (enable parse-u32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp uint64 bytes) where BYTES is the bytes that remain after parsing the value.
;; This is a little-endian operation, because the least significant byte comes first.
(defund parse-u64 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (len-at-least 8 bytes)
      (mv nil
          ;; eighth byte is most significant:
          (bvcat2 8 (eighth bytes)
                  8 (seventh bytes)
                  8 (sixth bytes)
                  8 (fifth bytes)
                  8 (fourth bytes)
                  8 (third bytes)
                  8 (second bytes)
                  8 (first bytes))
          (nthcdr 8 bytes))
    (mv :not-enough-bytes 0 bytes)))

(defthmd unsigned-byte-p-of-mv-nth-1-of-parse-u64
  (implies (byte-listp bytes)
           (unsigned-byte-p 64 (mv-nth 1 (parse-u64 bytes))))
  :hints (("Goal" :in-theory (enable parse-u64))))

(defthmd natp-of-mv-nth-1-of-parse-u64
  (implies t ;(byte-listp bytes)
           (natp (mv-nth 1 (parse-u64 bytes))))
  :hints (("Goal" :in-theory (enable parse-u64))))

(defthmd byte-listp-of-mv-nth-2-of-parse-u64
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-u64 bytes))))
  :hints (("Goal" :in-theory (enable parse-u64))))

(defthm len-of-mv-nth-2-of-parse-u64
  (implies (not (mv-nth 0 (parse-u64 bytes)))
           (equal (len (mv-nth 2 (parse-u64 bytes)))
                  (+ -8 (len bytes))))
  :hints (("Goal" :in-theory (enable parse-u64))))

;; (encapsulate
;;  nil
;;  (local
;;   (defthm nthcdr-of-nil
;;     (equal (nthcdr n nil)
;;            nil)))

;;  (local
;;   (defthm equal-of-<
;;     (implies (booleanp z)
;;              (equal (equal (< x y) z)
;;                     (iff (< x y) z)))))

;;  (local
;;   (defthm consp-of-nthcdr
;;     (implies (natp n)
;;              (equal (consp (nthcdr n lst))
;;                     (< n (len lst))))
;;     :hints (("Goal" :in-theory (enable zp)))))

;; ;; todo: name clash
;; ;; ; the :logic version could be very slow if the list is long
;;  ;; (defun len-at-least (n lst)
;;  ;;   (declare (xargs :guard (and (posp n)
;;  ;;                               (true-listp lst))))
;;  ;;   (mbe :logic (<= n (len lst))
;;  ;;        :exec (consp (nthcdr (+ -1 n) lst))))
;;  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Given a BV and an alist from flag masks (values with a single bit set) to
; flag 'names', return a list of the names of the flags whose corresponding
; bits are set in the value.
(defun decode-flags-aux (val flags-alist acc)
  (declare (xargs :guard (and (integerp val)
                              (alistp flags-alist)
                              (integer-listp (strip-cars flags-alist))
                              (true-listp acc))))
  (if (endp flags-alist)
      (reverse acc)
    (let* ((entry (first flags-alist))
           (mask (car entry))
           (flag (cdr entry))
           (acc (if (not (eql 0 (logand mask val)))
                    (cons flag acc)
                  acc)))
      (decode-flags-aux val (rest flags-alist) acc))))

;flags-alist maps masks to symbolic names of flags
(defund decode-flags (val flags-alist)
  (declare (xargs :guard (and (integerp val)
                              (alistp flags-alist)
                              (integer-listp (strip-cars flags-alist)))))
  (decode-flags-aux val flags-alist nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tries to extract the first 4 bytes as a u32.
;; Returns (mv erp magic-number).
(defun parse-executable-magic-number (bytes filename)
  (declare (xargs :guard (and (byte-listp bytes)
                              (stringp filename))))
  (if (not (len-at-least 4 bytes))
      (prog2$ (er hard? 'parse-executable-magic-number "Not enough bytes in ~x0.  Result: ~x1" filename bytes)
              (mv :not-enough-bytes-for-magic-number nil))
    (mv-let (erp magic-number remaining-bytes)
      (parse-u32 bytes)
      (declare (ignore erp remaining-bytes)) ; erp will be nil because we know (len-at-least 4 bytes)
      (mv nil magic-number))))
