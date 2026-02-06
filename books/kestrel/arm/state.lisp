; A formal model of the ARM32 state
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Remove this (after testing on GCL) since we now use :non-executable for the stobj:
; Matt K. mod: An array is too big for GCL 2.7.1 (and probably any version of
; GCL starting with 2.7.0).
; cert_param: (non-gcl)

(in-package "ARM")

;; STATUS: In-progress / incomplete

(include-book "portcullis")
(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/putbits" :dir :system)
(include-book "kestrel/bv/bvplus-def" :dir :system)
(local (include-book "kestrel/bv/bvplus" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
;(include-book "kestrel/alists-light/lookup-eq" :dir :system)
;(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
;(include-book "std/util/bstar" :dir :system)
;(include-book "std/testing/must-be-redundant" :dir :system)

(local
  (defthm integerp-when-unsigned-byte-p-32
    (implies (unsigned-byte-p 32 x)
             (integerp x))))

;; The state of the ARM CPU, including registers, memory, etc.
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
  ;; This array can use a lot of memory, so we use :non-executable below:
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: use more
(defun register-numberp (n)
  (declare (xargs :guard t))
  (unsigned-byte-p 4 n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Get register N from the state
(defund reg (n arm)
  (declare (xargs :guard (and (natp n)
                              (<= n 15))
                  :stobjs arm))
  (registersi n arm))

(defthm unsigned-byte-p-32-of-reg
  (implies (and (< n 16)
                (natp n)
                (armp arm))
           (unsigned-byte-p 32 (reg n arm)))
  :hints (("Goal" :in-theory (enable reg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *sp* #b1101)
(defconst *lr* #b1110)
(defconst *pc* #b1111)

;; Gets the stack pointer (register 13 = #b1101).
;; We consider this an abbreviation to be kept enabled.
(defun sp (arm)
  (declare (xargs :stobjs arm))
  (reg *sp* arm))

;; Gets the link register (register 14 = #b1110).
;; We consider this an abbreviation to be kept enabled.
(defun lr (arm)
  (declare (xargs :stobjs arm))
  (reg *lr* arm))

;; Gets the program counter (register 15 = #b1111).
;; We consider this an abbreviation to be kept enabled.
(defun pc (arm)
  (declare (xargs :stobjs arm))
  (reg *pc* arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Sets register N to VAL.
(defund set-reg (n val arm)
  (declare (xargs :guard (and (natp n)
                              (<= n 15)
                              (unsigned-byte-p 32 val))
                  :stobjs arm))
  (update-registersi n val arm))

;; Strengthen?
(defthm armp-of-set-reg
  (implies (and (natp n)
                (<= n 15)
                (unsigned-byte-p 32 val)
                (armp arm))
           (armp (set-reg n val arm)))
  :hints (("Goal" :in-theory (enable set-reg))))

;; todo: see what the system level text says about R[n] when n=15

;; todo: have REG chop the value
(defthm reg-of-set-reg
  (implies (and (register-numberp n1)
                (register-numberp n2))
           (equal (reg n1 (set-reg n2 val arm))
                  (if (equal n1 n2)
                      val
                    (reg n1 arm))))
  :hints (("Goal" :in-theory (enable reg set-reg))))

(defthm set-reg-of-set-reg-diff
  (implies (and (syntaxp (acl2::smaller-termp n2 n1))
                (not (equal n1 n2))
                (register-numberp n1)
                (register-numberp n2))
           (equal (set-reg n1 val1 (set-reg n2 val2 arm))
                  (set-reg n2 val2 (set-reg n1 val1 arm))))
  :hints (("Goal" :in-theory (enable reg set-reg)))
  :rule-classes ((:rewrite :loop-stopper nil))
  )

(defthm set-reg-of-set-reg-same
  (equal (set-reg n val1 (set-reg n val2 arm))
         (set-reg n val1 arm))
  :hints (("Goal" :in-theory (enable set-reg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Individual status bits:
(defund apsr.n (arm) (declare (xargs :stobjs arm)) (getbit 31 (apsr arm)))
(defund apsr.z (arm) (declare (xargs :stobjs arm)) (getbit 30 (apsr arm)))
(defund apsr.c (arm) (declare (xargs :stobjs arm)) (getbit 29 (apsr arm)))
(defund apsr.v (arm) (declare (xargs :stobjs arm)) (getbit 28 (apsr arm)))
(defund apsr.q (arm) (declare (xargs :stobjs arm)) (getbit 27 (apsr arm)))

(defund set-apsr.n (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 31 bit (apsr arm)) arm))
(defund set-apsr.z (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 30 bit (apsr arm)) arm))
(defund set-apsr.c (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 29 bit (apsr arm)) arm))
(defund set-apsr.v (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 28 bit (apsr arm)) arm))
(defund set-apsr.q (bit arm) (declare (xargs :guard (bitp bit) :stobjs arm)) (update-apsr (putbit 32 27 bit (apsr arm)) arm))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm apsr-of-set-reg
  (equal (apsr (set-reg n val arm))
         (apsr arm))
  :hints (("Goal" :in-theory (enable set-reg apsr))))

(defthm error-of-set-reg
  (equal (error (set-reg n val arm))
         (error arm))
  :hints (("Goal" :in-theory (enable set-reg))))

(defthm reg-of-set-apsr.n (equal (reg n (set-apsr.n bit arm)) (reg n arm)) :hints (("Goal" :in-theory (enable set-apsr.n reg))))
(defthm reg-of-set-apsr.z (equal (reg n (set-apsr.z bit arm)) (reg n arm)) :hints (("Goal" :in-theory (enable set-apsr.z reg))))
(defthm reg-of-set-apsr.c (equal (reg n (set-apsr.c bit arm)) (reg n arm)) :hints (("Goal" :in-theory (enable set-apsr.c reg))))
(defthm reg-of-set-apsr.v (equal (reg n (set-apsr.v bit arm)) (reg n arm)) :hints (("Goal" :in-theory (enable set-apsr.v reg))))
(defthm reg-of-set-apsr.q (equal (reg n (set-apsr.q bit arm)) (reg n arm)) :hints (("Goal" :in-theory (enable set-apsr.q reg))))

(defthm error-of-set-apsr.n (equal (error (set-apsr.n bit arm)) (error arm)) :hints (("Goal" :in-theory (enable set-apsr.n reg))))
(defthm error-of-set-apsr.z (equal (error (set-apsr.z bit arm)) (error arm)) :hints (("Goal" :in-theory (enable set-apsr.z reg))))
(defthm error-of-set-apsr.c (equal (error (set-apsr.c bit arm)) (error arm)) :hints (("Goal" :in-theory (enable set-apsr.c reg))))
(defthm error-of-set-apsr.v (equal (error (set-apsr.v bit arm)) (error arm)) :hints (("Goal" :in-theory (enable set-apsr.v reg))))
(defthm error-of-set-apsr.q (equal (error (set-apsr.q bit arm)) (error arm)) :hints (("Goal" :in-theory (enable set-apsr.q reg))))

(local (include-book "kestrel/bv/trim-intro-rules" :dir :system))

(defthm set-apsr.n-of-set-reg (equal (set-apsr.n bit (set-reg n val arm)) (set-reg n val (set-apsr.n bit arm))) :hints (("Goal" :in-theory (enable set-apsr.n set-reg))))
(defthm set-apsr.z-of-set-reg (equal (set-apsr.z bit (set-reg n val arm)) (set-reg n val (set-apsr.z bit arm))) :hints (("Goal" :in-theory (enable set-apsr.z set-reg))))
(defthm set-apsr.c-of-set-reg (equal (set-apsr.c bit (set-reg n val arm)) (set-reg n val (set-apsr.c bit arm))) :hints (("Goal" :in-theory (enable set-apsr.c set-reg))))
(defthm set-apsr.v-of-set-reg (equal (set-apsr.v bit (set-reg n val arm)) (set-reg n val (set-apsr.v bit arm))) :hints (("Goal" :in-theory (enable set-apsr.v set-reg))))
(defthm set-apsr.q-of-set-reg (equal (set-apsr.q bit (set-reg n val arm)) (set-reg n val (set-apsr.q bit arm))) :hints (("Goal" :in-theory (enable set-apsr.q set-reg))))

(defthm set-apsr.n-of-set-apsr.n (equal (set-apsr.n bit1 (set-apsr.n bit2 arm)) (set-apsr.n bit1 arm)) :hints (("Goal" :in-theory (enable set-apsr.n))))
(defthm set-apsr.z-of-set-apsr.z (equal (set-apsr.z bit1 (set-apsr.z bit2 arm)) (set-apsr.z bit1 arm)) :hints (("Goal" :in-theory (enable set-apsr.z))))
(defthm set-apsr.c-of-set-apsr.c (equal (set-apsr.c bit1 (set-apsr.c bit2 arm)) (set-apsr.c bit1 arm)) :hints (("Goal" :in-theory (enable set-apsr.c))))
(defthm set-apsr.v-of-set-apsr.v (equal (set-apsr.v bit1 (set-apsr.v bit2 arm)) (set-apsr.v bit1 arm)) :hints (("Goal" :in-theory (enable set-apsr.v))))
(defthm set-apsr.q-of-set-apsr.q (equal (set-apsr.q bit1 (set-apsr.q bit2 arm)) (set-apsr.q bit1 arm)) :hints (("Goal" :in-theory (enable set-apsr.q))))

(defthm set-apsr.z-of-set-apsr.n (equal (set-apsr.z bit1 (set-apsr.n bit2 arm)) (set-apsr.n bit2 (set-apsr.z bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.n set-apsr.z))))
(defthm set-apsr.c-of-set-apsr.n (equal (set-apsr.c bit1 (set-apsr.n bit2 arm)) (set-apsr.n bit2 (set-apsr.c bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.n set-apsr.c))))
(defthm set-apsr.v-of-set-apsr.n (equal (set-apsr.v bit1 (set-apsr.n bit2 arm)) (set-apsr.n bit2 (set-apsr.v bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.n set-apsr.v))))
(defthm set-apsr.q-of-set-apsr.n (equal (set-apsr.q bit1 (set-apsr.n bit2 arm)) (set-apsr.n bit2 (set-apsr.q bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.n set-apsr.q))))

(defthm set-apsr.c-of-set-apsr.z (equal (set-apsr.c bit1 (set-apsr.z bit2 arm)) (set-apsr.z bit2 (set-apsr.c bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.z set-apsr.c))))
(defthm set-apsr.v-of-set-apsr.z (equal (set-apsr.v bit1 (set-apsr.z bit2 arm)) (set-apsr.z bit2 (set-apsr.v bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.z set-apsr.v))))
(defthm set-apsr.q-of-set-apsr.z (equal (set-apsr.q bit1 (set-apsr.z bit2 arm)) (set-apsr.z bit2 (set-apsr.q bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.z set-apsr.q))))

(defthm set-apsr.v-of-set-apsr.c (equal (set-apsr.v bit1 (set-apsr.c bit2 arm)) (set-apsr.c bit2 (set-apsr.v bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.c set-apsr.v))))
(defthm set-apsr.q-of-set-apsr.c (equal (set-apsr.q bit1 (set-apsr.c bit2 arm)) (set-apsr.c bit2 (set-apsr.q bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.c set-apsr.q))))

(defthm set-apsr.q-of-set-apsr.v (equal (set-apsr.q bit1 (set-apsr.v bit2 arm)) (set-apsr.v bit2 (set-apsr.q bit1 arm))) :hints (("Goal" :in-theory (enable set-apsr.v set-apsr.q))))

;todo: more
