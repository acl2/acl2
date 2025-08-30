; An evaluator for RISC-V code lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; change to R package?

(include-book "../evaluator-basic")
(include-book "../unguarded-built-ins") ; for nth-unguarded
(include-book "../unguarded-defuns2") ; for binary-logand-unguarded
(include-book "kestrel/risc-v/executable/decoding-executable" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(local (include-book "kestrel/bv/bitops" :dir :system))
;(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop

(local
  (in-theory (disable rational-listp
                      integer-listp
                      assoc-equal
                      min
                      max
                      integer-range-p
                      signed-byte-p
                      bvle)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund riscv::ubyte32-fix-unguarded (x)
  (declare (xargs :guard t))
  (if (riscv::ubyte32p x) x 0))

(defthm riscv::ubyte32-fix-unguarded-correct
  (equal (riscv::ubyte32-fix-unguarded x)
         (riscv::ubyte32-fix x))
  :hints (("Goal" :in-theory (enable riscv::ubyte32-fix-unguarded
                                     riscv::ubyte32-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund riscv::feat-base-kind-unguarded (x)
  (declare (xargs :guard t))
  (cond ((or (atom x)
             (eq (car x) :rv32i))
         :rv32i)
        ((eq (car x) :rv64i) :rv64i)
        ((eq (car x) :rv32e) :rv32e)
        (t :rv64e)))

(defthm riscv::feat-base-kind-unguarded-correct
  (equal (riscv::feat-base-kind-unguarded x)
         (riscv::feat-base-kind x))
  :hints (("Goal" :in-theory (enable riscv::feat-base-kind
                                     riscv::feat-base-kind-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun riscv::feat-base-fix-unguarded (x)
  (declare (xargs :guard t))
  (case (riscv::feat-base-kind-unguarded x)
    (:rv32i (cons :rv32i (list)))
    (:rv64i (cons :rv64i (list)))
    (:rv32e (cons :rv32e (list)))
    (:rv64e (cons :rv64e (list)))))

(defthm riscv::feat-base-fix-unguarded-correct
  (equal (riscv::feat-base-fix-unguarded x)
         (riscv::feat-base-fix x))
  :hints (("Goal" :in-theory (enable riscv::feat-base-fix-unguarded
                                     riscv::feat-base-fix
                                     ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund riscv::feat-endian-kind-unguarded (x)
  (declare (xargs :guard t))
  (cond ((or (atom x)
             (eq (car x) :little))
         :little)
        (t :big)))

(defthm feat-endian-kind-unguarded-correct
  (equal (riscv::feat-endian-kind-unguarded x)
         (riscv::feat-endian-kind x))
  :hints (("Goal" :in-theory (enable riscv::feat-endian-kind-unguarded
                                     riscv::feat-endian-kind))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund riscv::feat-endian-fix-unguarded (x)
  (declare (xargs :guard t))
  (case (riscv::feat-endian-kind-unguarded x)
    (:little (cons :little (list)))
    (:big (cons :big (list)))))

(defthm riscv::feat-endian-fix-unguarded-correct
  (equal (riscv::feat-endian-fix-unguarded x)
         (riscv::feat-endian-fix x))
  :hints (("Goal" :in-theory (enable riscv::feat-endian-fix-unguarded
                                     riscv::feat-endian-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun riscv::feat-fix-unguarded (x)
  (declare (xargs :guard t))
  (b* ((riscv::base (riscv::feat-base-fix-unguarded (cdr-unguarded (nth-unguarded 0 x)) ;(cdr (std::da-nth 0 x))
                                                    ))
       (riscv::endian (riscv::feat-endian-fix-unguarded (cdr-unguarded (nth-unguarded 1 x)) ; (cdr (std::da-nth 1 x))
                                                        ))
       (riscv::m (acl2::bool-fix (cdr-unguarded (nth-unguarded 2 x) ; (std::da-nth 2 x)
                                                ))))
    (list (cons 'riscv::base riscv::base)
          (cons 'riscv::endian riscv::endian)
          (cons 'riscv::m riscv::m))))

(defthm feat-fix-unguarded-correct
  (equal (riscv::feat-fix-unguarded x)
         (riscv::feat-fix x))
  :hints (("Goal" :in-theory (enable riscv::feat-fix-unguarded
                                     riscv::feat-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun riscv::decodex-unguarded (enc feat)
  (declare (xargs :guard t))
  (riscv::decodex (riscv::ubyte32-fix-unguarded enc)
                  (riscv::feat-fix-unguarded feat)))

(defthm riscv::decodex-unguarded-correct
  (equal (riscv::decodex-unguarded enc feat)
         (riscv::decodex enc feat))
  :hints (("Goal" :in-theory (enable riscv::decodex-unguarded))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: import more of these into the X package, if needed:
(defconst *axe-evaluator-risc-v-fns-and-aliases*
  (append '(implies ; push back to basic evaluator?
            (riscv::decodex riscv::decodex-unguarded)
            ;; (integer-range-p integer-range-p-unguarded)
            ;; (bitops::part-select-width-low$inline bitops::part-select-width-low$inline-unguarded)
            ;; (lookup lookup-equal-unguarded)
            ;; (loghead$inline loghead$inline-unguarded)
            ;; (logapp logapp-unguarded) ; for flags
            ;; (acl2::packbv acl2::packbv-unguarded)
            ;; (bv-array-read-chunk-little bv-array-read-chunk-little-unguarded)
            ;; power-of-2p
            ;; logmaskp
            ;; bfix$inline
            ;; bool->bit$inline
            ;; (evenp evenp-unguarded)
            ;; (logcount logcount-unguarded)
            ;; (logtail$inline logtail$inline-unguarded)
            ;; (zip zip-unguarded)
            ;; (ash ash-unguarded)
            ;; (acl2::firstn acl2::firstn-unguarded)
            ;; (logbitp logbitp-unguarded)
            (binary-logand binary-logand-unguarded)
            ;; (binary-logior binary-logior-unguarded)
            ;; (nonnegative-integer-quotient nonnegative-integer-quotient-unguarded)
            ;; (acl2::aref1 acl2::aref1-unguarded)
            ;; (acl2::negated-elems-listp acl2::negated-elems-listp-unguarded)
            )
          *axe-evaluator-basic-fns-and-aliases*))

;; Creates acl2::eval-axe-evaluator-risc-v, etc. ;; todo: package
;; Makes the evaluator (also checks that each alias given is equivalent to its function):
(make-evaluator-simple risc-v *axe-evaluator-risc-v-fns-and-aliases*)
