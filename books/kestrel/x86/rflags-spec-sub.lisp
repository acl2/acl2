; Some changes to the open-source x86 model
;
; Copyright (C) 2022 Kestrel Technology, LLC
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

;; TODO: Remove "sub" from the name of this book

;(include-book "std/basic/arith-equiv-defs" :dir :system) ; for bool->bit
(include-book "projects/x86isa/machine/rflags-spec" :dir :system)
(include-book "kestrel/bv/bvlt-def" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; These are in the X86ISA package, because we are going to suggest adding them to the model.

(local (in-theory (enable unsigned-byte-p)))

;; new flag functions that take dst and src and can be disabled to prevent
;; simplification of things like (- dst src) or (< dst src).  These could be
;; further simplified if desired.

;; todo: consider simplifying these
;; todo: more sizes of these?

(defund sub-cf-spec8 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 8 dst)
                              (unsigned-byte-p 8 src))))
  (bool->bit (< dst src)))

;; oddly, this only covers the least significant byte of the result. -- why "oddly"?
(defund sub-of-spec8 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 8 dst)
                              (unsigned-byte-p 8 src))
                  :guard-hints (("Goal" :in-theory (enable signed-byte-p)))))
  (of-spec8 (- (logext 8 dst) ;(n8-to-i8 dst)
               (logext 8 src) ;(n8-to-i8 src)
               )))

(defund sub-pf-spec8 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 8 dst)
                              (unsigned-byte-p 8 src))))
  (pf-spec8 (n-size 8 (- (logext 8 dst) ;(n8-to-i8 dst)
                         (logext 8 src) ;(n8-to-i8 src)
                         ))))

(defund sub-sf-spec8 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 8 dst)
                              (unsigned-byte-p 8 src))))
  (sf-spec8 (n-size 8 (- (logext 8 dst) ;(n8-to-i8 dst)
                         (logext 8 src) ;(n8-to-i8 src)
                         ))))

;; todo: use the same function for all sizes?
(defund sub-zf-spec8 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 8 dst)
                              (unsigned-byte-p 8 src))))
  (bool->bit (equal src dst)) ; much simpler
  ;; (zf-spec (n-size 8 (- (n8-to-i8 dst)
  ;;                        (n8-to-i8 src))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sub-cf-spec16 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 16 dst)
                              (unsigned-byte-p 16 src))))
  (bool->bit (< dst src)))

;; oddly, this only covers the least significant byte of the result.
(defund sub-of-spec16 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 16 dst)
                              (unsigned-byte-p 16 src))
                  :guard-hints (("Goal" :in-theory (enable signed-byte-p)))))
  (of-spec16 (- (n16-to-i16 dst)
                (n16-to-i16 src))))

(defund sub-pf-spec16 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 16 dst)
                              (unsigned-byte-p 16 src))))
  (pf-spec16 (n-size 16 (- (n16-to-i16 dst)
                           (n16-to-i16 src)))))

(defund sub-sf-spec16 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 16 dst)
                              (unsigned-byte-p 16 src))))
  (sf-spec16 (n-size 16 (- (n16-to-i16 dst)
                           (n16-to-i16 src)))))

;; todo: use the same function for all sizes?
(defund sub-zf-spec16 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 16 dst)
                              (unsigned-byte-p 16 src))))
  (bool->bit (equal src dst)) ; much simpler
  ;; (zf-spec (n-size 16 (- (n16-to-i16 dst)
  ;;                        (n16-to-i16 src))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sub-cf-spec32 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 32 dst)
                              (unsigned-byte-p 32 src))))
  (bool->bit (< dst src)))

;; oddly, this only covers the least significant byte of the result.
(defund sub-of-spec32 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 32 dst)
                              (unsigned-byte-p 32 src))
                  :guard-hints (("Goal" :in-theory (enable signed-byte-p)))))
  (of-spec32 (- (n32-to-i32 dst)
                (n32-to-i32 src))))

(defund sub-pf-spec32 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 32 dst)
                              (unsigned-byte-p 32 src))))
  (pf-spec32 (n-size 32 (- (n32-to-i32 dst)
                           (n32-to-i32 src)))))

(defund sub-sf-spec32 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 32 dst)
                              (unsigned-byte-p 32 src))))
  (sf-spec32 (n-size 32 (- (n32-to-i32 dst)
                           (n32-to-i32 src)))))

;; todo: use the same function for all sizes?
(defund sub-zf-spec32 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 32 dst)
                              (unsigned-byte-p 32 src))))
  (bool->bit (equal src dst)) ; much simpler
  ;; (zf-spec (n-size 32 (- (n32-to-i32 dst)
  ;;                        (n32-to-i32 src))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund sub-cf-spec64 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 64 dst)
                              (unsigned-byte-p 64 src))))
  (bool->bit (< dst src)))

(defun sub-of-spec64 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 64 dst)
                              (unsigned-byte-p 64 src))
                  :guard-hints (("Goal" :in-theory (enable SIGNED-BYTE-P)))))
  (of-spec64 (- (n64-to-i64 dst)
                (n64-to-i64 src))))

;; oddly, this only covers the least significant byte of the result.
(defund sub-pf-spec64 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 64 dst)
                              (unsigned-byte-p 64 src))))
  (pf-spec64 (n-size 64 (- (n64-to-i64 dst)
                           (n64-to-i64 src)))))

(defund sub-sf-spec64 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 64 dst)
                              (unsigned-byte-p 64 src))))
  (sf-spec64 (n-size 64 (- (n64-to-i64 dst)
                           (n64-to-i64 src)))))

(defund sub-zf-spec64 (dst src)
  (declare (xargs :guard (and (unsigned-byte-p 64 dst)
                              (unsigned-byte-p 64 src))))
  (bool->bit (equal src dst)) ; much simpler
  ;; (zf-spec (n-size 64 (- (n64-to-i64 dst)
  ;;                        (n64-to-i64 src))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: package prefixes
(defthm x86isa::bitp-of-sub-cf-spec8 (bitp (x86isa::sub-cf-spec8 dst src)))
(defthm x86isa::bitp-of-sub-cf-spec16 (bitp (x86isa::sub-cf-spec16 dst src)))
(defthm x86isa::bitp-of-sub-cf-spec32 (bitp (x86isa::sub-cf-spec32 dst src)))
(defthm x86isa::bitp-of-sub-cf-spec64 (bitp (x86isa::sub-cf-spec64 dst src)))

(defthm x86isa::bitp-of-sub-of-spec8 (bitp (x86isa::sub-of-spec8 dst src)))
(defthm x86isa::bitp-of-sub-of-spec16 (bitp (x86isa::sub-of-spec16 dst src)))
(defthm x86isa::bitp-of-sub-of-spec32 (bitp (x86isa::sub-of-spec32 dst src)))
(defthm x86isa::bitp-of-sub-of-spec64 (bitp (x86isa::sub-of-spec64 dst src)))

(defthm x86isa::bitp-of-sub-pf-spec8 (bitp (x86isa::sub-pf-spec8 dst src)))
(defthm x86isa::bitp-of-sub-pf-spec16 (bitp (x86isa::sub-pf-spec16 dst src)))
(defthm x86isa::bitp-of-sub-pf-spec32 (bitp (x86isa::sub-pf-spec32 dst src)))
(defthm x86isa::bitp-of-sub-pf-spec64 (bitp (x86isa::sub-pf-spec64 dst src)))

(defthm x86isa::bitp-of-sub-sf-spec8 (bitp (x86isa::sub-sf-spec8 dst src)))
(defthm x86isa::bitp-of-sub-sf-spec16 (bitp (x86isa::sub-sf-spec16 dst src)))
(defthm x86isa::bitp-of-sub-sf-spec32 (bitp (x86isa::sub-sf-spec32 dst src)))
(defthm x86isa::bitp-of-sub-sf-spec64 (bitp (x86isa::sub-sf-spec64 dst src)))

(defthm x86isa::bitp-of-sub-zf-spec8 (bitp (x86isa::sub-zf-spec8 dst src)))
(defthm x86isa::bitp-of-sub-zf-spec16 (bitp (x86isa::sub-zf-spec16 dst src)))
(defthm x86isa::bitp-of-sub-zf-spec32 (bitp (x86isa::sub-zf-spec32 dst src)))
(defthm x86isa::bitp-of-sub-zf-spec64 (bitp (x86isa::sub-zf-spec64 dst src)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-sub-zf-spec8
  (integerp (x86isa::sub-zf-spec8 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec8))))

(defthm integerp-of-sub-cf-spec8
  (integerp (x86isa::sub-cf-spec8 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec8))))

(defthm integerp-of-sub-pf-spec8
  (integerp (x86isa::sub-pf-spec8 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec8))))

(defthm integerp-of-sub-sf-spec8
  (integerp (x86isa::sub-sf-spec8 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-sf-spec8))))

(defthm integerp-of-sub-of-spec8
  (integerp (x86isa::sub-of-spec8 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec8))))

(defthm x86isa::unsigned-byte-p-of-sub-zf-spec8
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-zf-spec8 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec8
                                     ZF-SPEC))))

(defthm x86isa::unsigned-byte-p-of-sub-cf-spec8
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-cf-spec8 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec8
                                     CF-SPEC8))))

(defthm x86isa::unsigned-byte-p-of-sub-of-spec8
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-of-spec8 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec8
                                     OF-SPEC8))))

(defthm x86isa::unsigned-byte-p-of-sub-pf-spec8
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-pf-spec8 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec8
                                     PF-SPEC8))))

(defthm x86isa::unsigned-byte-p-of-sub-sf-spec8
  (implies (and (<= 1 size)
                (integerp size)
                (integerp dst) ;todo: why?
                )
           (unsigned-byte-p size (x86isa::sub-sf-spec8 dst src)))
  :hints (("Goal" :in-theory (e/d (x86isa::sub-sf-spec8
                                   SF-SPEC8)
                                  (;ACL2::SLICE-OF-PLUS-OF-LOGEXT-GEN-ALT ; bad forcing
                                   )))))

;drop?
(defthm sub-zf-spec8-same
  (equal (x86isa::sub-zf-spec8 x x)
         1)
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-sub-zf-spec16
  (integerp (x86isa::sub-zf-spec16 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec16))))

(defthm integerp-of-sub-cf-spec16
  (integerp (x86isa::sub-cf-spec16 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec16))))

(defthm integerp-of-sub-pf-spec16
  (integerp (x86isa::sub-pf-spec16 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec16))))

(defthm integerp-of-sub-sf-spec16
  (integerp (x86isa::sub-sf-spec16 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-sf-spec16))))

(defthm integerp-of-sub-of-spec16
  (integerp (x86isa::sub-of-spec16 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec16))))

(defthm x86isa::unsigned-byte-p-of-sub-zf-spec16
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-zf-spec16 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec16
                                     ZF-SPEC))))

(defthm x86isa::unsigned-byte-p-of-sub-cf-spec16
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-cf-spec16 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec16
                                     CF-SPEC16))))

(defthm x86isa::unsigned-byte-p-of-sub-of-spec16
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-of-spec16 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec16
                                     OF-SPEC16))))

(defthm x86isa::unsigned-byte-p-of-sub-pf-spec16
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-pf-spec16 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec16
                                     PF-SPEC16))))

(defthm x86isa::unsigned-byte-p-of-sub-sf-spec16
  (implies (and (<= 1 size)
                (integerp size)
                (integerp dst) ; todo: why?
                )
           (unsigned-byte-p size (x86isa::sub-sf-spec16 dst src)))
  :hints (("Goal" :in-theory (e/d (x86isa::sub-sf-spec16
                                   SF-SPEC16)
                                  (;ACL2::SLICE-OF-PLUS-OF-LOGEXT-GEN-ALT ; bad forcing
                                   )))))

;drop?
(defthm sub-zf-spec16-same
  (equal (x86isa::sub-zf-spec16 x x)
         1)
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec16))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-sub-zf-spec32
  (integerp (x86isa::sub-zf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32))))

(defthm integerp-of-sub-cf-spec32
  (integerp (x86isa::sub-cf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec32))))

(defthm integerp-of-sub-pf-spec32
  (integerp (x86isa::sub-pf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec32))))

(defthm integerp-of-sub-sf-spec32
  (integerp (x86isa::sub-sf-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-sf-spec32))))

(defthm integerp-of-sub-of-spec32
  (integerp (x86isa::sub-of-spec32 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec32))))

;slow!
(defthm x86isa::unsigned-byte-p-of-sub-zf-spec32
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-zf-spec32 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32
                                     ZF-SPEC))))

(defthm x86isa::unsigned-byte-p-of-sub-cf-spec32
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-cf-spec32 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec32
                                     CF-SPEC32))))

(defthm x86isa::unsigned-byte-p-of-sub-of-spec32
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-of-spec32 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec32
                                     OF-SPEC32))))

(defthm x86isa::unsigned-byte-p-of-sub-pf-spec32
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-pf-spec32 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec32
                                     PF-SPEC32))))

(defthm x86isa::unsigned-byte-p-of-sub-sf-spec32
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-sf-spec32 dst src)))
  :hints (("Goal" :in-theory (e/d (x86isa::sub-sf-spec32
                                   SF-SPEC32)
                                  (;ACL2::SLICE-OF-PLUS-OF-LOGEXT-GEN-ALT ; bad forcing
                                   )))))

;drop?
(defthm sub-zf-spec32-same
  (equal (x86isa::sub-zf-spec32 x x)
         1)
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec32))))

;;;;;;;;;;

;todo: why doesn't this get generated automatically when ACL2 generates a :type-prescription rule?
(defthm x86isa::bitp-of-sub-cf-spec64
  (bitp (x86isa::sub-cf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec64))))

(defthm x86isa::bitp-of-sub-of-spec64
  (bitp (x86isa::sub-of-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec64))))

(defthm x86isa::bitp-of-sub-pf-spec64
  (bitp (x86isa::sub-pf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec64))))

(defthm x86isa::bitp-of-sub-sf-spec64
  (bitp (x86isa::sub-sf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-sf-spec64))))

(defthm x86isa::bitp-of-sub-zf-spec64
  (bitp (x86isa::sub-zf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-sub-zf-spec64
  (integerp (x86isa::sub-zf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec64))))

(defthm integerp-of-sub-cf-spec64
  (integerp (x86isa::sub-cf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec64))))

(defthm integerp-of-sub-pf-spec64
  (integerp (x86isa::sub-pf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec64))))

(defthm integerp-of-sub-sf-spec64
  (integerp (x86isa::sub-sf-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-sf-spec64))))

(defthm integerp-of-sub-of-spec64
  (integerp (x86isa::sub-of-spec64 dst src))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec64))))

;slow!
(defthm x86isa::unsigned-byte-p-of-sub-zf-spec64
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-zf-spec64 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec64
                                     ZF-SPEC))))

(defthm x86isa::unsigned-byte-p-of-sub-cf-spec64
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-cf-spec64 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-cf-spec64
                                     CF-SPEC64))))

(defthm x86isa::unsigned-byte-p-of-sub-of-spec64
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-of-spec64 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-of-spec64
                                     OF-SPEC64))))

(defthm x86isa::unsigned-byte-p-of-sub-pf-spec64
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-pf-spec64 dst src)))
  :hints (("Goal" :in-theory (enable x86isa::sub-pf-spec64
                                     PF-SPEC64))))

(defthm x86isa::unsigned-byte-p-of-sub-sf-spec64
  (implies (and (<= 1 size)
                (integerp size))
           (unsigned-byte-p size (x86isa::sub-sf-spec64 dst src)))
  :hints (("Goal" :in-theory (e/d (x86isa::sub-sf-spec64
                                   SF-SPEC64)
                                  (;ACL2::SLICE-OF-PLUS-OF-LOGEXT-GEN-ALT ; bad forcing
                                   )))))
;drop?
;;not sure yet whether we should open sub-af-spec32
(defthm sub-af-spec32-same
  (equal (sub-af-spec32 x x)
         0)
  :hints (("Goal" :in-theory (enable SUB-AF-SPEC32))))

;drop?
(defthm sub-zf-spec64-same
  (equal (x86isa::sub-zf-spec64 x x)
         1)
  :hints (("Goal" :in-theory (enable x86isa::sub-zf-spec64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; not sure if we want this
(defthm sub-zf-spec64-when-not-equal-1
  (implies (not (equal dst src))
           (equal (sub-zf-spec64 dst src)
                  0))
  :hints (("Goal" :in-theory (enable sub-zf-spec64))))

;; not sure if we want this
(defthm sub-zf-spec64-when-not-equal-2
  (implies (not (equal src dst))
           (equal (sub-zf-spec64 dst src)
                  0))
  :hints (("Goal" :in-theory (enable sub-zf-spec64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm sub-cf-spec8-opener
  (implies (and (unsigned-byte-p 8 dst)
                (unsigned-byte-p 8 src))
           (equal (sub-cf-spec8 dst src)
                  (bool->bit (acl2::bvlt 8 dst src))))
  :hints (("Goal" :in-theory (enable sub-cf-spec8 acl2::bvlt))))

(defthm sub-cf-spec16-opener
  (implies (and (unsigned-byte-p 16 dst)
                (unsigned-byte-p 16 src))
           (equal (sub-cf-spec16 dst src)
                  (bool->bit (acl2::bvlt 16 dst src))))
  :hints (("Goal" :in-theory (enable sub-cf-spec16 acl2::bvlt))))

(defthm sub-cf-spec32-opener
  (implies (and (unsigned-byte-p 32 dst)
                (unsigned-byte-p 32 src))
           (equal (sub-cf-spec32 dst src)
                  (bool->bit (acl2::bvlt 32 dst src))))
  :hints (("Goal" :in-theory (enable sub-cf-spec32 acl2::bvlt))))

(defthm sub-cf-spec64-opener
  (implies (and (unsigned-byte-p 64 dst)
                (unsigned-byte-p 64 src))
           (equal (sub-cf-spec64 dst src)
                  (bool->bit (acl2::bvlt 64 dst src))))
  :hints (("Goal" :in-theory (enable sub-cf-spec64 acl2::bvlt))))
