; Utilities for parsing x86 binaries
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
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
(include-book "ihs/basic-definitions" :dir :system) ;for logext
(include-book "kestrel/utilities/file-existsp" :dir :system)
(local (include-book "std/lists/take" :dir :system))

;; A version of TAKE that throws an error if there are not at least N
;; elements in the list.
(defun take-safe (n l)
  (declare (xargs :guard (and (natp n)
                              (true-listp l))))
  (if (> n (len l))
      (er hard? 'take-safe "Not enough bytes to take ~x0 of them. "n)
    (take n l)))

;; A version of TAKE that throws an error if there are not at least N
;; elements in the list.
(defun take-safe-ctx (n l ctx)
  (declare (xargs :guard (and (natp n)
                              (true-listp l))))
  (if (> n (len l))
      (er hard? ctx "Not enough bytes to take ~x0 of them." n)
    (take n l)))

;; Returns (mv first-n-bytes bytes)
(defun parse-n-bytes (n bytes)
  (declare (type (integer 0 *) n) ;disallow 0?
           (xargs :guard (true-listp bytes)))
  (mv (take-safe n bytes)
      (nthcdr n bytes)))

(defun parse-u8 (bytes)
  (declare (xargs :guard (true-listp bytes)))
  (let* ((val-bytes (take-safe 1 bytes))
         (val (first val-bytes)))
    (mv val (nthcdr 1 bytes))))

(defun parse-u16 (bytes)
  (declare (xargs :guard (and (integer-listp bytes)
                              (<= 2 (len bytes)))))
  (let* ((val-bytes (take-safe 2 bytes))
         ;; second byte is most significant
         (val (bvcat 8 (second val-bytes)
                     8 (first val-bytes))))
    (mv val (nthcdr 2 bytes))))

(defun parse-u32 (bytes)
  (declare (xargs :guard (and (integer-listp bytes)
                              (<= 4 (len bytes)))))
  (let* ((val-bytes (take-safe 4 bytes))
         ;; fourth byte is most significant
         (val (bvcat2 8 (fourth val-bytes)
                      8 (third val-bytes)
                      8 (second val-bytes)
                      8 (first val-bytes))))
    (mv val (nthcdr 4 bytes))))

(defun parse-u64 (bytes)
  (declare (xargs :guard (and (integer-listp bytes)
                              (<= 8 (len bytes)))))
  (let* ((val-bytes (take-safe 8 bytes))
         ;; eighth byte is most significant
         (val (bvcat2 8 (eighth val-bytes)
                      8 (seventh val-bytes)
                      8 (sixth val-bytes)
                      8 (fifth val-bytes)
                      8 (fourth val-bytes)
                      8 (third val-bytes)
                      8 (second val-bytes)
                      8 (first val-bytes)
                      )))
    (mv val (nthcdr 8 bytes))))

(encapsulate
 nil
 (local
  (defthm nthcdr-of-nil
    (equal (nthcdr n nil)
           nil)))

 (local
  (defthm equal-of-<
    (implies (booleanp z)
             (equal (equal (< x y) z)
                    (iff (< x y) z)))))

 (local
  (defthm consp-of-nthcdr
    (implies (natp n)
             (equal (consp (nthcdr n lst))
                    (< n (len lst))))
    :hints (("Goal" :in-theory (enable zp)))))

;; todo: name clash
;; ; the :logic version could be very slow if the list is long
 ;; (defun len-at-least (n lst)
 ;;   (declare (xargs :guard (and (posp n)
 ;;                               (true-listp lst))))
 ;;   (mbe :logic (<= n (len lst))
 ;;        :exec (consp (nthcdr (+ -1 n) lst))))
 )


; Given a BV and an alist from flag masks (values with a single bit set) to
; flag 'names', return a list of the names of the flags whose corresponding
; bits are set in the value.
(defun decode-flags-aux (val flags-alist acc)
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
(defun decode-flags (val flags-alist)
  (decode-flags-aux val flags-alist nil))
