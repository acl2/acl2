; ARM32 memory operations
;
; Copyright (C) 2025-2026 Kestrel Institute
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
(local (include-book "kestrel/bv/logtail" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund addressp (ad)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 ad))

(defthm addressp-forward-to-integerp
  (implies (addressp ad)
           (integerp ad))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable addressp))))

(defthm addressp-forward-to-unsigned-byte-p
  (implies (addressp ad)
           (unsigned-byte-p 32 ad))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable addressp))))

;; Every register's value can be used as an address.
(defthm addressp-of-reg
  (implies (and (< n 16)
                (natp n)
                (armp arm))
           (addressp (reg n arm)))
  :hints (("Goal" :in-theory (enable addressp))))

(defthm addressp-of-bvplus-32
  (addressp (bvplus 32 x y))
  :hints (("Goal" :in-theory (enable addressp))))

;strong
(defthm addressp-when-unsigned-byte-p-32
  (implies (unsigned-byte-p 32 a)
           (addressp a))
  :hints (("Goal" :in-theory (enable addressp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun CurrentModeIsNotUser ()
  (declare (xargs :guard t))
  nil ; todo
  )

(defun CurrentModeIsHyp ()
  (declare (xargs :guard t))
  nil ; todo
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; See B2.4.4 (Aligned memory accesses)
;; (defun MemA_with_priv (address size privileged wasaligned)
;;   (declare (xargs :guard (and (addressp address)
;;                               (integerp size)
;;                               (booleanp privileged)
;;                               (booleanp wasaligned))))


;; TODO: Handle alignment and privileges
(defund MemA (address size arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              )
                  :stobjs arm))
  (read size address arm))

;; (defun MemA (address size)
;;   (declare (xargs :guard (and (addressp address)
;;                               (integerp size))))
;;   (MemA_with_priv address size (CurrentModeIsNotUser) t))

(defthm unsigned-byte-p-of-MemA
  (implies (and (posp size)
                (<= (* 8 size) n)
                (natp n))
           (unsigned-byte-p n (MemA address size arm)))
  :hints (("Goal" :in-theory (enable MemA))))

(defthm addressp-of-MemA
  (addressp (MemA address 4 arm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See B2.4.5 (Unaligned memory accesses)

;; (defun MemU_with_priv (address size privileged)
;;   (declare (xargs :guard (and (addressp address)
;;                               (integerp size)
;;                               (booleanp privileged))))

;; TODO: Handle alignment and privileges
(defund MemU (address size arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              )
                  :stobjs arm))
  (read size address arm))

(defthm unsigned-byte-p-of-MemU
  (implies (and (posp size)
                (<= (* 8 size) n)
                (natp n))
           (unsigned-byte-p n (MemU address size arm)))
  :hints (("Goal" :in-theory (enable MemU))))

(defthm addressp-of-MemU
  (addressp (MemU address 4 arm)))

;; TODO: Handle alignment and privileges
(defund MemU_unpriv (address size arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              )
                  :stobjs arm))
  (read size address arm))

(defthm unsigned-byte-p-of-MemU_unpriv
  (implies (and (posp size)
                (<= (* 8 size) n)
                (natp n))
           (unsigned-byte-p n (MemU_unpriv address size arm)))
  :hints (("Goal" :in-theory (enable MemU_unpriv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the BYTE at address ADDR.
(defund write-byte (addr byte arm)
  (declare (xargs :guard (and (unsigned-byte-p 32 addr)
                              (unsigned-byte-p 8 byte))
                  :stobjs arm))
  (update-memoryi addr byte arm))

(defthm armp-of-write-byte
  (implies (and (unsigned-byte-p 32 addr)
                (unsigned-byte-p 8 byte)
                (armp arm))
           (armp (write-byte addr byte arm)))
  :hints (("Goal" :in-theory (enable write-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Writes the N-byte chunk VAL starting at ADDR (in little endian fashion).
(defund write (n addr val arm)
  (declare (xargs :guard (and (natp n)
                              (unsigned-byte-p (* 8 n) val)
                              (unsigned-byte-p 32 addr))
                  :stobjs arm))
  (if (zp n)
      arm
    (let ((arm (write-byte addr (bvchop 8 val) arm)))
      (write (+ -1 n)
             (bvplus 32 1 addr)
             (logtail 8 val) ;(slice (+ -1 (* 8 n)) 8 val)
             arm))))

(defthm armp-of-write
  (implies (and (natp n)
                (unsigned-byte-p (* 8 n) val)
                (unsigned-byte-p 32 addr)
                (armp arm))
           (armp (write n addr val arm)))
  :hints (("Goal" :in-theory (enable write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Handle alignment and privileges
(defun write_MemU_unpriv (address size val arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              (unsigned-byte-p (* 8 size) val))
                  :stobjs arm))
  ;; for now:
  (write size address val arm))

;; TODO: Handle alignment and privileges
(defun write_MemU (address size val arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              (unsigned-byte-p (* 8 size) val))
                  :stobjs arm))
  ;; for now:
  (write size address val arm))


;; TODO: Handle alignment and privileges
(defun write_MemA (address size val arm)
  (declare (xargs :guard (and (addressp address)
                              (posp size) ; restrict?
                              (unsigned-byte-p (* 8 size) val))
                  :stobjs arm))
  ;; for now:
  (write size address val arm))
