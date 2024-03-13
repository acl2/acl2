; "Read over write" rules for our x86 state readers and writers
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book focues on things that are not specific to 32-bit or 64-bit mode.

;; The readers are: undef, x86p, alignment-checking-enabled-p, get-flag, 64-bit-modep, app-view, ctri, msri, segment-base-and-bounds
;; The writers are set-flag, set-undef, set-mxcsr, !rflags (currently) -- also if and myif (kind of)

(include-book "projects/x86isa/machine/state" :dir :system)
(include-book "projects/x86isa/machine/modes" :dir :system)
(include-book "projects/x86isa/machine/decoding-and-spec-utils" :dir :system) ; for alignment-checking-enabled-p
(include-book "readers-and-writers")
(include-book "flags")
(local (include-book "linear-memory"))

(defthm program-at-of-set-flag
  (implies (app-view x86)
           (equal (program-at prog-addr bytes (set-flag flag val x86))
                  (program-at prog-addr bytes x86)))
  :hints (("Goal" :in-theory (enable set-flag program-at))))

(defthm x86p-of-set-flag (implies (x86p x86) (x86p (set-flag flag val x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm x86p-of-!rflags (implies (x86p x86) (x86p (!rflags v x86))))

(defthm undef-of-!rflags (equal (undef (!rflags flags x86)) (undef x86)) :hints (("Goal" :in-theory (enable !rflags undef))))
(defthm undef-of-set-flag (equal (undef (set-flag flg val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef))))
(defthm undef-of-set-mxcsr (equal (undef (set-mxcsr mxcsr x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef))))

(defthm mxcsr-of-!rflags (equal (mxcsr (!rflags flags x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable !rflags mxcsr))))
(defthm mxcsr-of-set-flag (equal (mxcsr (set-flag flg val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr))))
(defthm mxcsr-of-set-undef (equal (mxcsr (set-undef undef x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr))))

(defthm ms-of-!rflags (equal (ms (!rflags flags x86)) (ms x86)) :hints (("Goal" :in-theory (enable !rflags ms))))
(defthm ms-of-set-flag (equal (ms (set-flag flg val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms))))
(defthm ms-of-set-undef (equal (ms (set-undef undef x86)) (ms x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm ms-of-set-mxcsr (equal (ms (set-mxcsr mxcsr x86)) (ms x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm ms-of-set-fault (equal (ms (set-fault fault x86)) (ms x86)) :hints (("Goal" :in-theory (enable set-undef))))

(defthm fault-of-!rflags (equal (fault (!rflags flags x86)) (fault x86)) :hints (("Goal" :in-theory (enable !rflags fault))))
(defthm fault-of-set-flag (equal (fault (set-flag flg val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault))))
(defthm fault-of-set-undef (equal (fault (set-undef undef x86)) (fault x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm fault-of-set-mxcsr (equal (fault (set-mxcsr mxcsr x86)) (fault x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm fault-of-set-ms (equal (fault (set-ms fault x86)) (fault x86)) :hints (("Goal" :in-theory (enable set-ms))))

(defthm get-flag-of-set-undef (equal (get-flag flag (set-undef undef x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm get-flag-of-set-mxcsr (equal (get-flag flag (set-mxcsr mxcsr x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm get-flag-of-set-ms (equal (get-flag flag (set-ms ms x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-ms))))

(defthm alignment-checking-enabled-p-of-set-undef (equal (alignment-checking-enabled-p (set-undef undef x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm alignment-checking-enabled-p-of-set-mxcsr (equal (alignment-checking-enabled-p (set-mxcsr mxcsr x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm alignment-checking-enabled-p-of-set-ms (equal (alignment-checking-enabled-p (set-ms ms x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-ms))))

;improve?
(defthm alignment-checking-enabled-p-of-!rflags-of-xr
  (implies (equal (get-flag :ac x86_1) (get-flag :ac x86_2))
           (equal (alignment-checking-enabled-p (!rflags (xr ':rflags 'nil x86_1) x86_2))
                  (alignment-checking-enabled-p x86_2)))
  :hints (("Goal" :in-theory (enable !rflags alignment-checking-enabled-p get-flag))))

(defthm 64-bit-modep-of-set-undef (equal (64-bit-modep (set-undef undef x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm 64-bit-modep-of-set-mxcsr (equal (64-bit-modep (set-mxcsr mxcsr x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm 64-bit-modep-of-set-ms (equal (64-bit-modep (set-ms ms x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-ms))))
(defthm 64-bit-modep-of-!rflags (equal (64-bit-modep (!rflags v x86)) (64-bit-modep x86)))
(defthm 64-bit-modep-of-set-flag (equal (64-bit-modep (set-flag flag val x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-flag))))

(defthm app-view-of-set-flag (equal (app-view (set-flag flag val x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm app-view-of-set-undef (equal (app-view (set-undef undef x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm app-view-of-set-mxcsr (equal (app-view (set-mxcsr mxcsr x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm app-view-of-set-ms (equal (app-view (set-ms ms x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-ms))))
(defthm app-view-of-!rflags (equal (app-view (!rflags v x86)) (app-view x86)))

(defthm ctri-of-xw-irrel
  (implies (not (equal :ctr fld))
           (equal (ctri i (xw fld index val x86))
                  (ctri i x86)))
  :hints (("Goal" :in-theory (enable ctri))))

(defthm ctri-of-set-undef (equal (ctri i (set-undef val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm ctri-of-set-mxcsr (equal (ctri i (set-mxcsr val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm ctri-of-set-ms (equal (ctri i (set-ms val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-ms))))
(defthm ctri-of-set-flag (equal (ctri i (set-flag flag val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable ctri))))
;todo: why is !rflags showing up?
(defthm ctri-of-!rflags (equal (ctri i (!rflags v x86)) (ctri i x86)))

(defthm msri-of-set-undef (equal (msri i (set-undef val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm msri-of-set-mxcsr (equal (msri i (set-mxcsr val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm msri-of-set-ms (equal (msri i (set-ms val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-ms))))
(defthm msri-of-set-flag (equal (msri i (set-flag flg val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable))))

(defthm segment-base-and-bounds-of-set-flag
  (equal (segment-base-and-bounds proc-mode seg-reg (set-flag flg val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm segment-base-and-bounds-of-set-undef (equal (segment-base-and-bounds proc-mode seg-reg (set-undef undef x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm segment-base-and-bounds-of-set-mxcsr (equal (segment-base-and-bounds proc-mode seg-reg (set-mxcsr mxcsr x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))

(defthm segment-base-and-bounds-of-set-ms
  (equal (segment-base-and-bounds proc-mode seg-reg (set-ms ms x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ms))))
