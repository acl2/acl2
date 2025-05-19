; Setters and getters for ZMM registers
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;(include-book "projects/x86isa/machine/state" :dir :system) ;for xr
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "register-readers-and-writers64")
(include-book "flags")
(include-book "read-and-write")
(include-book "readers-and-writers64") ; drop?
(include-book "readers-and-writers")
(include-book "projects/x86isa/machine/decoding-and-spec-utils" :dir :system) ; for alignment-checking-enabled-p
(local (include-book "read-over-write-rules64"))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; Get the value of ZMM register N, a 512-bit unsigned value.  We do not make
;; separate setters and getters for the ZMM registers because there are just
;; too many and they have nice, systematic names.
(defund-nx zmm (n x86)
  (declare (xargs :guard (and (natp n)
                              (< n 32))
                  :stobjs x86))
  (xr :zmm n x86))

(defthm unsigned-byte-p-of-zmm
  (implies (<= 512 size)
           (equal (unsigned-byte-p size (zmm reg x86))
                  (natp size)))
  :hints (("Goal" :use (:instance x86isa::elem-p-of-xr-zmm
                                  (i reg)
                                  (x86$a x86))
           :in-theory (e/d (zmm) (x86isa::elem-p-of-xr-zmm)))))

(defthmd xr-becomes-zmm
  (equal (xr :zmm n x86)
         (zmm n x86))
  :hints (("Goal" :in-theory (enable zmm))))

(theory-invariant (incompatible (:rewrite xr-becomes-zmm) (:definition zmm)))

(defthm zmm-of-set-rax (equal (zmm n (set-rax rax x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rbx (equal (zmm n (set-rbx rbx x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rcx (equal (zmm n (set-rcx rcx x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rdx (equal (zmm n (set-rdx rdx x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-rip (equal (zmm n (set-rip rip x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
;todo: more

(defthm zmm-of-set-flag (equal (zmm n (set-flag flag val x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))
(defthm zmm-of-set-undef (equal (zmm n (set-undef undef x86)) (zmm n x86)) :hints (("Goal" :in-theory (enable zmm))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set-zmm (n val x86)
  (declare (xargs :guard (and (natp n)
                              (< n 32)
                              (unsigned-byte-p 512 val) ; todo: tighten
                              )
                  :stobjs x86))
  (!zmmi n val x86))

(defthm set-zmm-of-set-zmm-same
  (equal (set-zmm reg val1 (set-zmm reg val2 x86))
         (set-zmm reg val1 x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm set-zmm-of-set-zmm-diff-constant-version
  (implies (and (syntaxp (and (quotep reg1)
                              (quotep reg2)))
                (< reg2 reg1))
           (equal (set-zmm reg1 val1 (set-zmm reg2 val2 x86))
                  (set-zmm reg2 val2 (set-zmm reg1 val1 x86))))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm zmm-of-set-zmm-same
  (equal (zmm reg (set-zmm reg val x86))
         (bvchop 512 val))
  :hints (("Goal" :in-theory (enable zmm set-zmm bvchop loghead))))

(defthm zmm-of-set-zmm-diff
  (implies (not (equal reg1 reg2))
           (equal (zmm reg1 (set-zmm reg2 val x86))
                  (zmm reg1 x86)))
  :hints (("Goal" :in-theory (enable zmm set-zmm))))

(defthmd xw-becomes-set-zmm
  (equal (xw :zmm n val x86)
         (set-zmm n val x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(theory-invariant (incompatible (:rewrite xw-becomes-set-zmm)
                                (:definition set-zmm)))

;; todo: more like this?
(defthm xw-zmm-of-set-rax
  (equal (set-zmm reg val (set-rax val2 x86))
         (set-rax val2 (set-zmm reg val x86)))
  :hints (("Goal" :in-theory (enable set-rax set-zmm))))

;todo: more like this
(defthm rip-of-set-zmm
  (equal (rip (set-zmm reg val x86))
         (rip x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm app-view-of-set-zmm
  (equal (app-view (set-zmm reg val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm ms-of-set-zmm
  (equal (ms (set-zmm reg val x86))
         (ms x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm alignment-checking-enabled-p-of-set-zmm
  (equal (alignment-checking-enabled-p (set-zmm reg val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm fault-of-set-zmm
  (equal (fault (set-zmm reg val x86))
         (fault x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm 64-bit-modep-of-set-zmm
  (equal (64-bit-modep (set-zmm reg val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm rsp-of-set-zmm
  (equal (rsp (set-zmm reg val x86))
         (rsp x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

;more
(defthm rax-of-set-zmm
  (equal (rax (set-zmm reg val x86))
         (rax x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm ctri-of-set-zmm
  (equal (ctri i (set-zmm reg val x86))
         (ctri i x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm read-of-set-zmm
  (equal (read n addr (set-zmm reg val x86))
         (read n addr x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm undef-of-set-zmm
  (equal (undef (set-zmm reg val x86))
         (undef x86))
  :hints (("Goal" :in-theory (enable set-zmm))))

;; strengthen?
(defthm x86p-of-set-zmm
  (implies (x86p x86)
           (x86p (set-zmm reg val x86)))
  :hints (("Goal" :in-theory (enable set-zmm))))

(defthm set-zmm-of-set-rip
  (equal (set-zmm reg val (set-rip rip x86))
         (set-rip rip (set-zmm reg val x86)))
  :hints (("Goal" :in-theory (enable set-rip set-zmm))))

(defthm set-flag-of-set-zmm
  (equal (set-flag flag fval (set-zmm reg val x86))
         (set-zmm reg val (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag set-zmm))))

(defthm set-undef-of-set-zmm
  (equal (set-undef undef (set-zmm reg val x86))
         (set-zmm reg val (set-undef undef x86)))
  :hints (("Goal" :in-theory (enable set-undef set-zmm))))

(defthm get-flag-of-set-zmm
  (equal (get-flag flag (set-zmm reg val x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-zmm))))
