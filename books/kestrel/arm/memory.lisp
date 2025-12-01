; ARM32 memory operations
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; STATUS: In-progress / incomplete

;; Reference: ARM Architecture Reference Manual ARMv7-A and ARMv7-R edition,
;; available from https://developer.arm.com/documentation/ddi0406/latest/

;; TODO: Deal with address wrap-around, alignment issues, and endianness issues.

(include-book "state")
(include-book "kestrel/bv/bvplus" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;; Reads the byte at address ADDR.
(defund read-byte (addr arm)
  (declare (xargs :guard (unsigned-byte-p 32 addr)
                  :stobjs arm))
  (bvchop 8 (ifix (memoryi (bvchop 32 addr) arm))))

;; (local
;;   (implies (and (memoryp mem)
;;                 (natp addr)
;;                 (< addr (len mem)))
;;            (integerp (nth addr mem))))

(defthm unsigned-byte-p-8-of-read-byte
  (unsigned-byte-p 8 (read-byte addr arm))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm integerp-of-read-byte-type
  (integerp (read-byte addr arm))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm integerp-of-apsr-type
  (implies (armp arm)
           (integerp (apsr arm)))
  :rule-classes :type-prescription
  :hints (("Goal" :use acl2::field-type-of-apsr
           :in-theory (disable acl2::field-type-of-apsr))))

;; ;; Read N bytes, starting at ADDR.  Unlike read, this returns a list.
;; ;; TODO: Consider putting the N parameter first
;; (defund read-bytes (n addr arm)
;;   (declare (xargs :guard (and (natp n)
;;                               (unsigned-byte-p 32 addr))
;;                   :stobjs arm))
;;   (if (zp n)
;;       nil
;;     (cons (read-byte addr arm)
;;           (read-bytes (+ -1 n) (bvplus 32 1 addr) arm))))

;; Reads an N-byte chunk starting at ADDR (in little-endian fashion).
;; Unlike read-bytes, this returns the value as a bit-vector.
(defund read (n addr arm)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p 32 addr))
                  :stobjs arm))
  (if (zp n)
      0
    (let ((addr (mbe :logic (ifix addr) :exec addr)) ; treats non-integer address as 0
          )
      (bvcat (* 8 (- n 1))
             (read (- n 1) (bvplus 32 1 addr) arm)
             8
             (read-byte addr arm)))))

(defthm unsigned-byte-p-of-read
  (implies (<= (* n 8) size)
           (equal (unsigned-byte-p size (read n addr stat))
                  (natp size)))
  :hints (("Goal" :in-theory (enable read))))
