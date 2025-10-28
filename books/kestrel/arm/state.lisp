; A formal model of the ARM32 state
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; STATUS: In-progress / incomplete

(include-book "portcullis")
(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/putbits" :dir :system)
;(include-book "kestrel/alists-light/lookup-eq" :dir :system)
;(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
;(include-book "std/util/bstar" :dir :system)
;(include-book "std/testing/must-be-redundant" :dir :system)

(local
  (defthm integerp-when-unsigned-byte-p-32
    (implies (unsigned-byte-p 32 x)
             (integerp x))))

(defstobj+
  arm
  ;; ARM Core Registers:
  (registers :type (array (unsigned-byte 32) (16)) :initially 0)
  ;; Application Program Status Register:
  (apsr :type (unsigned-byte 32) :initially 0)
  ;; Execution state registers:
  (isetstate :type (unsigned-byte 2) :initially 0)
  (itstate  :type (unsigned-byte 8) :initially 0)
  (endianstate :type bit :initially 0)
  ;; TODO: SIMD / floating point registers
  ;; TODO: Exception bit?
  ;; TODO: Oracle for undefined values?
  (memory :type (array (unsigned-byte 8) (4294967296)) ; 2^32 bytes
          :initially 0)
  (error ; nil means no error, anything else is an error
    )
  ;; This avoids actually allocating 4GB of memory for the MEMORY field (even
  ;; though that only takes a few seconds).  See add-global-stobj if you want
  ;; execution for this stobj.  See also the "large stobj" discussion on Zulip.
  :non-executable t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (enable registers-length ; always 16
                   memory-length ; always 4294967296
                   ))

(defund reg (n arm)
  (declare (xargs :guard (and (natp n)
                              (<= n 15))
                  :stobjs arm))
  (registersi n arm))

;; get the stack pointer
(defun sp (arm)
  (declare (xargs :stobjs arm))
  (reg 13 arm))

(defthm unsigned-byte-p-32-of-reg
  (implies (and (< n 16)
                (natp n)
                (armp arm))
           (unsigned-byte-p 32 (reg n arm)))
  :hints (("Goal" :in-theory (enable reg))))

(defund set-reg (n val arm)
  (declare (xargs :guard (and (natp n)
                              (<= n 15)
                              (unsigned-byte-p 32 val))
                  :stobjs arm))
  (update-registersi n val arm))

;; the stack pointer is register 13
;; we regard this an abbreviation to be kept enabled
(defun sp (arm)
  (declare (xargs :stobjs arm))
  (reg 13 arm))

;; the link register is register 14
;; we regard this an abbreviation to be kept enabled
(defun lr (arm)
  (declare (xargs :stobjs arm))
  (reg 14 arm))

;; the program counter is register 15
;; we regard this an abbreviation to be kept enabled
(defun pc (arm)
  (declare (xargs :stobjs arm))
  (reg 15 arm))

;; todo: see what the system level text says about R[n] when n=15


(defun apsr.n (arm) (declare (xargs :stobjs arm)) (getbit 31 (apsr arm)))
(defun apsr.z (arm) (declare (xargs :stobjs arm)) (getbit 30 (apsr arm)))
(defun apsr.c (arm) (declare (xargs :stobjs arm)) (getbit 29 (apsr arm)))
(defun apsr.v (arm) (declare (xargs :stobjs arm)) (getbit 28 (apsr arm)))
(defun apsr.q (arm) (declare (xargs :stobjs arm)) (getbit 27 (apsr arm)))

(defun set-apsr.n (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 31 bit (apsr arm)) arm))
(defun set-apsr.z (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 30 bit (apsr arm)) arm))
(defun set-apsr.c (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 29 bit (apsr arm)) arm))
(defun set-apsr.v (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 28 bit (apsr arm)) arm))
(defun set-apsr.q (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 27 bit (apsr arm)) arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
