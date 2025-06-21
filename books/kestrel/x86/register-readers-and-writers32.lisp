; A theory of register readers and writers (emphasis on readability of terms)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book defines readers and writers for (32-bit) x86 registers, such as
;; EAX, ESP, etc.  It aims for maximum brevity and clarity, so to access EAX,
;; one simply calls (eax <x86>).  Instead, we could define a general function,
;; get-reg, and say something like (get-reg :eax <x86>).  This would allow us
;; to prove fewer rules about "read over write" and similar properties, at the
;; cost of making proof terms a bit bigger and a bit less readable.

(include-book "projects/x86isa/machine/state" :dir :system) ;for xr
(include-book "projects/x86isa/portcullis/sharp-dot-constants" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)
(local (include-book "kestrel/bv/rules" :dir :system)) ; for bvcat-of-logext-arg4
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

(in-theory (disable xw logext))

(defthm xw-of-rgf-and-logext64
  (equal (xw :rgf reg (logext 64 val) x86)
         (xw :rgf reg val x86))
  :hints (("Goal" :in-theory (enable xw))))

(defthmd xw-rgf-when-equal-of-xr-rgf
  (implies (equal val (xr :rgf reg x86))
           (equal (xw :rgf reg val x86)
                  x86)))

(defthmd xw-rgf-when-equal-of-xr-rgf-gen
  (implies (equal (bvchop 64 val) (xr :rgf reg x86))
           (equal (xw :rgf reg val x86)
                  x86))
  :hints (("Goal" :use (:instance xw-rgf-when-equal-of-xr-rgf
                                  (val (bvchop 64 val))))))

(local (in-theory (enable acl2::bvcat-of-bvcat-tighten-arg4)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Register readers (these chop the signed-byte-64 values down to unsigned-byte-32s):
(defund eax (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rax* x86)))
(defund ebx (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rbx* x86)))
(defund ecx (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rcx* x86)))
(defund edx (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rdx* x86)))
(defund esp (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rsp* x86)))
(defund ebp (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rbp* x86)))
;; todo: esi and edi!

;; used for, for example, when FLD is :UNDEF
(defthm eax-of-xw (implies (not (equal fld :rgf)) (equal (eax (xw fld index value x86)) (eax x86))) :hints (("Goal" :in-theory (enable eax))))
(defthm ebx-of-xw (implies (not (equal fld :rgf)) (equal (ebx (xw fld index value x86)) (ebx x86))) :hints (("Goal" :in-theory (enable ebx))))
(defthm ecx-of-xw (implies (not (equal fld :rgf)) (equal (ecx (xw fld index value x86)) (ecx x86))) :hints (("Goal" :in-theory (enable ecx))))
(defthm edx-of-xw (implies (not (equal fld :rgf)) (equal (edx (xw fld index value x86)) (edx x86))) :hints (("Goal" :in-theory (enable edx))))
(defthm esp-of-xw (implies (not (equal fld :rgf)) (equal (esp (xw fld index value x86)) (esp x86))) :hints (("Goal" :in-theory (enable esp))))
(defthm ebp-of-xw (implies (not (equal fld :rgf)) (equal (ebp (xw fld index value x86)) (ebp x86))) :hints (("Goal" :in-theory (enable ebp))))

;; Helpers for expressing the high bits of the 64-bit registers (in 32-bit mode, these are usually ignored).
;; todo: just make a single one of these?
(defund rax-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rax* x86)))
(defund rbx-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rbx* x86)))
(defund rcx-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rcx* x86)))
(defund rdx-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rdx* x86)))
(defund rsp-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rsp* x86)))
(defund rbp-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rbp* x86)))

;; Introduce the register readers. These rules are disabled since they are not appropriate for 64-bit reasoning.
;; To be unconditional, these rules have to mention functions like rax-high, those we usually don't care about those bits in 32-bit mode.
(defthmd xr-becomes-eax (equal (xr :rgf *rax* x86) (logext 64 (bvcat 32 (rax-high x86) 32 (eax x86)))) :hints (("Goal" :in-theory (enable eax rax-high))))
(defthmd xr-becomes-ebx (equal (xr :rgf *rbx* x86) (logext 64 (bvcat 32 (rbx-high x86) 32 (ebx x86)))) :hints (("Goal" :in-theory (enable ebx rbx-high))))
(defthmd xr-becomes-ecx (equal (xr :rgf *rcx* x86) (logext 64 (bvcat 32 (rcx-high x86) 32 (ecx x86)))) :hints (("Goal" :in-theory (enable ecx rcx-high))))
(defthmd xr-becomes-edx (equal (xr :rgf *rdx* x86) (logext 64 (bvcat 32 (rdx-high x86) 32 (edx x86)))) :hints (("Goal" :in-theory (enable edx rdx-high))))
(defthmd xr-becomes-esp (equal (xr :rgf *rsp* x86) (logext 64 (bvcat 32 (rsp-high x86) 32 (esp x86)))) :hints (("Goal" :in-theory (enable esp rsp-high))))
(defthmd xr-becomes-ebp (equal (xr :rgf *rbp* x86) (logext 64 (bvcat 32 (rbp-high x86) 32 (ebp x86)))) :hints (("Goal" :in-theory (enable ebp rbp-high))))

(theory-invariant (incompatible (:definition eax) (:rewrite xr-becomes-eax)))
(theory-invariant (incompatible (:definition ebx) (:rewrite xr-becomes-ebx)))
(theory-invariant (incompatible (:definition ecx) (:rewrite xr-becomes-ecx)))
(theory-invariant (incompatible (:definition edx) (:rewrite xr-becomes-edx)))
(theory-invariant (incompatible (:definition esp) (:rewrite xr-becomes-esp)))
(theory-invariant (incompatible (:definition ebp) (:rewrite xr-becomes-ebp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets the 32-bit instruction pointer:
(defun eip (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rip x86)))

;; Accessing the high 16 bits of the 48-bit RIP (undefined in 32-bit mode).
(defund rip-high (x86) (declare (xargs :stobjs x86)) (slice 47 32 (rip x86)))
;; do we need a set-rip-high?

;; Introduce EIP. These rules are disabled since they are not appropriate for 64-bit reasoning:
;; To be unconditional, these rules have to mention rip-high, those we usually don't care about those high bits in 32-bit mode.
(defthmd rip-becomes-eip (equal (rip x86) (logext 48 (bvcat 16 (rip-high x86) 32 (eip x86)))) :hints (("Goal" :in-theory (enable eip rip-high))))
(defthmd xr-becomes-eip (equal (xr :rip nil x86) (logext 48 (bvcat 16 (rip-high x86) 32 (eip x86)))) :hints (("Goal" :in-theory (enable eip rip-high))))

(theory-invariant (incompatible (:rewrite rip-becomes-eip) (:definition eip)))
(theory-invariant (incompatible (:rewrite xr-becomes-eip) (:definition eip)))

;; not quite true
;; (defthm read-*ip-of-*compatibility-mode*-becomes-eip
;;   (equal (read-*ip *compatibility-mode* x86) (eip x86))
;;   :hints (("Goal" :in-theory (enable read-*ip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers for the high bits (usually unused in 32-bit mode):
(defund set-rax-high (val x86) (declare (xargs :guard (unsigned-byte-p 32 val) :stobjs x86)) (!rgfi *rax* (logext 64 (bvcat 32 val 32 (rgfi *rax* x86))) x86))
(defund set-rbx-high (val x86) (declare (xargs :guard (unsigned-byte-p 32 val) :stobjs x86)) (!rgfi *rbx* (logext 64 (bvcat 32 val 32 (rgfi *rbx* x86))) x86))
(defund set-rcx-high (val x86) (declare (xargs :guard (unsigned-byte-p 32 val) :stobjs x86)) (!rgfi *rcx* (logext 64 (bvcat 32 val 32 (rgfi *rcx* x86))) x86))
(defund set-rdx-high (val x86) (declare (xargs :guard (unsigned-byte-p 32 val) :stobjs x86)) (!rgfi *rdx* (logext 64 (bvcat 32 val 32 (rgfi *rdx* x86))) x86))
(defund set-rsp-high (val x86) (declare (xargs :guard (unsigned-byte-p 32 val) :stobjs x86)) (!rgfi *rsp* (logext 64 (bvcat 32 val 32 (rgfi *rsp* x86))) x86))
(defund set-rbp-high (val x86) (declare (xargs :guard (unsigned-byte-p 32 val) :stobjs x86)) (!rgfi *rbp* (logext 64 (bvcat 32 val 32 (rgfi *rbp* x86))) x86))

(defthm set-rax-high-does-nothing (implies (equal val (rax-high x86)) (equal (set-rax-high val x86) x86)) :hints (("Goal" :in-theory (enable xw-rgf-when-equal-of-xr-rgf-gen rax-high set-rax-high))))
(defthm set-rbx-high-does-nothing (implies (equal val (rbx-high x86)) (equal (set-rbx-high val x86) x86)) :hints (("Goal" :in-theory (enable xw-rgf-when-equal-of-xr-rgf-gen rbx-high set-rbx-high))))
(defthm set-rcx-high-does-nothing (implies (equal val (rcx-high x86)) (equal (set-rcx-high val x86) x86)) :hints (("Goal" :in-theory (enable xw-rgf-when-equal-of-xr-rgf-gen rcx-high set-rcx-high))))
(defthm set-rdx-high-does-nothing (implies (equal val (rdx-high x86)) (equal (set-rdx-high val x86) x86)) :hints (("Goal" :in-theory (enable xw-rgf-when-equal-of-xr-rgf-gen rdx-high set-rdx-high))))
(defthm set-rsp-high-does-nothing (implies (equal val (rsp-high x86)) (equal (set-rsp-high val x86) x86)) :hints (("Goal" :in-theory (enable xw-rgf-when-equal-of-xr-rgf-gen rsp-high set-rsp-high))))
(defthm set-rbp-high-does-nothing (implies (equal val (rbp-high x86)) (equal (set-rbp-high val x86) x86)) :hints (("Goal" :in-theory (enable xw-rgf-when-equal-of-xr-rgf-gen rbp-high set-rbp-high))))

(defthm set-rax-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rax-high (bvchop n val) x86) (set-rax-high val x86))) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm set-rbx-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rbx-high (bvchop n val) x86) (set-rbx-high val x86))) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm set-rcx-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rcx-high (bvchop n val) x86) (set-rcx-high val x86))) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm set-rdx-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rdx-high (bvchop n val) x86) (set-rdx-high val x86))) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm set-rsp-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rsp-high (bvchop n val) x86) (set-rsp-high val x86))) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm set-rbp-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rbp-high (bvchop n val) x86) (set-rbp-high val x86))) :hints (("Goal" :in-theory (enable set-rbp-high))))



;; ;; Helpers for the high bits (usually unused in 32-bit mode):
;; (defund set-reg-high (reg val x86)
;;   (declare (xargs :stobjs x86 :guard (and (natp reg)
;;                                           (< reg 16)
;;                                           (unsigned-byte-p 32 val))))
;;   (!rgfi reg (logext 64 (bvcat 32 val 32 (rgfi reg x86))) x86))

;; ;may not need this
;; (defthm set-reg-high-of-set-reg-high-same
;;   (equal (set-reg-high reg val1 (set-reg-high reg val2 x86))
;;          (set-reg-high reg val1 x86))
;;   :hints (("Goal" :in-theory (enable set-reg-high
;;                                      acl2::bvcat-of-bvcat-tighten-arg4))))

;; ;may not need this
;; (defthm set-reg-high-of-set-reg-high-diff
;;   (implies (< reg2 reg1)
;;            (equal (set-reg-high reg1 val1 (set-reg-high reg2 val2 x86))
;;                   (set-reg-high reg2 val2 (set-reg-high reg1 val1 x86))))
;;   :hints (("Goal" :in-theory (enable set-reg-high))))

;; (defthm set-reg-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-reg-high reg (bvchop n val) x86) (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high))))
;; (defthm set-reg-high-does-nothing (implies (equal val (slice 63 32 (rgfi reg x86))) (equal (set-reg-high reg val x86) x86)) :hints (("Goal" :in-theory (enable set-reg-high))))

;; ;; todo: either make separate set-reg-high functions for each register, or don't have separate getters like rax-high
;; (defthm set-reg-high-of-rax-does-nothing (implies (equal val (rax-high x86)) (equal (set-reg-high *rax* val x86) x86)) :hints (("Goal" :in-theory (enable rax-high set-reg-high))))
;; (defthm set-reg-high-of-rcx-does-nothing (implies (equal val (rcx-high x86)) (equal (set-reg-high *rbx* val x86) x86)) :hints (("Goal" :in-theory (enable rbx-high set-reg-high))))
;; (defthm set-reg-high-of-rcx-does-nothing (implies (equal val (rcx-high x86)) (equal (set-reg-high *rcx* val x86) x86)) :hints (("Goal" :in-theory (enable rcx-high set-reg-high))))
;; (defthm set-reg-high-of-rdx-does-nothing (implies (equal val (rdx-high x86)) (equal (set-reg-high *rdx* val x86) x86)) :hints (("Goal" :in-theory (enable rdx-high set-reg-high))))
;; (defthm set-reg-high-of-rsp-does-nothing (implies (equal val (rsp-high x86)) (equal (set-reg-high *rsp* val x86) x86)) :hints (("Goal" :in-theory (enable rsp-high set-reg-high))))
;; (defthm set-reg-high-of-rbp-does-nothing (implies (equal val (rbp-high x86)) (equal (set-reg-high *rbp* val x86) x86)) :hints (("Goal" :in-theory (enable rbp-high set-reg-high))))

;; (defthm x86p-of-set-reg-high (implies (x86p x86) (x86p (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high))))
;; (defthm eip-of-set-reg-high (equal (eip (set-reg-high reg val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-reg-high))))
;; todo: more like this?

;; (defund set-rax-high (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rax* (logext 64 (bvcat 32 val 32 (rgfi *rax* x86))) x86))
;; (defund set-rbx-high (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbx* (logext 64 (bvcat 32 val 32 (rgfi *rbx* x86))) x86))
;; (defund set-rcx-high (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rcx* (logext 64 (bvcat 32 val 32 (rgfi *rcx* x86))) x86))
;; (defund set-rdx-high (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rdx* (logext 64 (bvcat 32 val 32 (rgfi *rdx* x86))) x86))
;; (defund set-rsp-high (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rsp* (logext 64 (bvcat 32 val 32 (rgfi *rsp* x86))) x86))
;; (defund set-rbp-high (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbp* (logext 64 (bvcat 32 val 32 (rgfi *rbp* x86))) x86))

;; (defthm set-rax-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rax-high (bvchop n val) x86) (set-rax-high val x86))) :hints (("Goal" :in-theory (enable set-rax-high))))
;; (defthm set-rbx-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rbx-high (bvchop n val) x86) (set-rbx-high val x86))) :hints (("Goal" :in-theory (enable set-rbx-high))))
;; (defthm set-rcx-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rcx-high (bvchop n val) x86) (set-rcx-high val x86))) :hints (("Goal" :in-theory (enable set-rcx-high))))
;; (defthm set-rdx-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rdx-high (bvchop n val) x86) (set-rdx-high val x86))) :hints (("Goal" :in-theory (enable set-rdx-high))))
;; (defthm set-rsp-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rsp-high (bvchop n val) x86) (set-rsp-high val x86))) :hints (("Goal" :in-theory (enable set-rsp-high))))
;; (defthm set-rbp-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-rbp-high (bvchop n val) x86) (set-rbp-high val x86))) :hints (("Goal" :in-theory (enable set-rbp-high))))

;; (defthm set-rax-high-does-nothing (implies (equal val (rax-high x86)) (equal (set-rax-high val x86) x86)) :hints (("Goal" :in-theory (enable rax-high set-rax-high))))
;; (defthm set-rbx-high-does-nothing (implies (equal val (rbx-high x86)) (equal (set-rbx-high val x86) x86)) :hints (("Goal" :in-theory (enable rbx-high set-rbx-high))))
;; (defthm set-rcx-high-does-nothing (implies (equal val (rcx-high x86)) (equal (set-rcx-high val x86) x86)) :hints (("Goal" :in-theory (enable rcx-high set-rcx-high))))
;; (defthm set-rdx-high-does-nothing (implies (equal val (rdx-high x86)) (equal (set-rdx-high val x86) x86)) :hints (("Goal" :in-theory (enable rdx-high set-rdx-high))))
;; (defthm set-rsp-high-does-nothing (implies (equal val (rsp-high x86)) (equal (set-rsp-high val x86) x86)) :hints (("Goal" :in-theory (enable rsp-high set-rsp-high))))
;; (defthm set-rbp-high-does-nothing (implies (equal val (rbp-high x86)) (equal (set-rbp-high val x86) x86)) :hints (("Goal" :in-theory (enable rbp-high set-rbp-high))))

;; Introduce register writers (these only change the low 32 bits, but to make them unconditional, we have to mention functions like rax-high:
(defund set-eax (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rax* (logext 64 (bvcat 32 (rax-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-ebx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbx* (logext 64 (bvcat 32 (rbx-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-ecx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rcx* (logext 64 (bvcat 32 (rcx-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-edx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rdx* (logext 64 (bvcat 32 (rdx-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-esp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rsp* (logext 64 (bvcat 32 (rsp-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-ebp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbp* (logext 64 (bvcat 32 (rbp-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop

;; Introduce the register writers
;; The extra calls of set-rax-high, etc. should usually be irrelevant
;; These rules are disabled since they are not appropriate for 64-bit reasoning:
(defthmd xw-becomes-set-eax (equal (xw :rgf *rax* val x86) (set-eax (bvchop 32 val) (set-rax-high (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-eax rax-high set-rax-high))))
(defthmd xw-becomes-set-ebx (equal (xw :rgf *rbx* val x86) (set-ebx (bvchop 32 val) (set-rbx-high (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-ebx rbx-high set-rbx-high))))
(defthmd xw-becomes-set-ecx (equal (xw :rgf *rcx* val x86) (set-ecx (bvchop 32 val) (set-rcx-high (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-ecx rcx-high set-rcx-high))))
(defthmd xw-becomes-set-edx (equal (xw :rgf *rdx* val x86) (set-edx (bvchop 32 val) (set-rdx-high (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-edx rdx-high set-rdx-high))))
(defthmd xw-becomes-set-esp (equal (xw :rgf *rsp* val x86) (set-esp (bvchop 32 val) (set-rsp-high (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-esp rsp-high set-rsp-high))))
(defthmd xw-becomes-set-ebp (equal (xw :rgf *rbp* val x86) (set-ebp (bvchop 32 val) (set-rbp-high (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-ebp rbp-high set-rbp-high))))

(theory-invariant (incompatible (:definition set-eax) (:rewrite xw-becomes-set-eax)))
(theory-invariant (incompatible (:definition set-ebx) (:rewrite xw-becomes-set-ebx)))
(theory-invariant (incompatible (:definition set-ecx) (:rewrite xw-becomes-set-ecx)))
(theory-invariant (incompatible (:definition set-edx) (:rewrite xw-becomes-set-edx)))
(theory-invariant (incompatible (:definition set-esp) (:rewrite xw-becomes-set-esp)))
(theory-invariant (incompatible (:definition set-ebp) (:rewrite xw-becomes-set-ebp)))

(defthm set-eax-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-eax (bvchop n val) x86) (set-eax val x86))) :hints (("Goal" :in-theory (enable set-eax))))
(defthm set-ebx-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-ebx (bvchop n val) x86) (set-ebx val x86))) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm set-ecx-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-ecx (bvchop n val) x86) (set-ecx val x86))) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm set-edx-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-edx (bvchop n val) x86) (set-edx val x86))) :hints (("Goal" :in-theory (enable set-edx))))
(defthm set-esp-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-esp (bvchop n val) x86) (set-esp val x86))) :hints (("Goal" :in-theory (enable set-esp))))
(defthm set-ebp-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-ebp (bvchop n val) x86) (set-ebp val x86))) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm set-eax-when-equal-eax (implies (equal val (eax x86)) (equal (set-eax val x86) x86)) :hints (("Goal" :in-theory (enable rax-high eax set-eax))))
(defthm set-ebx-when-equal-ebx (implies (equal val (ebx x86)) (equal (set-ebx val x86) x86)) :hints (("Goal" :in-theory (enable rbx-high ebx set-ebx))))
(defthm set-ecx-when-equal-ecx (implies (equal val (ecx x86)) (equal (set-ecx val x86) x86)) :hints (("Goal" :in-theory (enable rcx-high ecx set-ecx))))
(defthm set-edx-when-equal-edx (implies (equal val (edx x86)) (equal (set-edx val x86) x86)) :hints (("Goal" :in-theory (enable rdx-high edx set-edx))))
(defthm set-esp-when-equal-esp (implies (equal val (esp x86)) (equal (set-esp val x86) x86)) :hints (("Goal" :in-theory (enable rsp-high esp set-esp))))
(defthm set-ebp-when-equal-ebp (implies (equal val (ebp x86)) (equal (set-ebp val x86) x86)) :hints (("Goal" :in-theory (enable rbp-high ebp set-ebp))))

;; todo: switch to traffic in 32-bit addresses only
(defun set-eip (eip x86)
  (declare (xargs :stobjs x86
                  :guard (signed-byte-p 48 eip))) ;todo: tighten?
  (!rip eip x86))

;; This introduces set-eip, if we want to.  We probably only want this for 32-bits!
(defthmd xw-becomes-set-eip
  (equal (xw :rip nil eip x86)
         (set-eip eip x86)))

(defthmd !rip-becomes-set-eip
  (equal (!rip eip x86)
         (set-eip eip x86)))

(theory-invariant (incompatible (:rewrite !rip-becomes-set-eip) (:definition set-eip)))
(theory-invariant (incompatible (:rewrite xw-becomes-set-eip) (:definition set-eip)))

(defthm eip-of-set-eip
  (equal (eip (set-eip eip x86))
         (bvchop 32 eip)))

(defthm set-eip-of-set-eip
  (equal (set-eip eip1 (set-eip eip2 x86))
         (set-eip eip1 x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Read of a write of the same register
(defthm eax-of-set-eax (equal (eax (set-eax val x86)) (bvchop 32 val)) :hints (("Goal" :in-theory (enable eax set-eax))))
(defthm ebx-of-set-ebx (equal (ebx (set-ebx val x86)) (bvchop 32 val)) :hints (("Goal" :in-theory (enable ebx set-ebx))))
(defthm ecx-of-set-ecx (equal (ecx (set-ecx val x86)) (bvchop 32 val)) :hints (("Goal" :in-theory (enable ecx set-ecx))))
(defthm edx-of-set-edx (equal (edx (set-edx val x86)) (bvchop 32 val)) :hints (("Goal" :in-theory (enable edx set-edx))))
(defthm esp-of-set-esp (equal (esp (set-esp val x86)) (bvchop 32 val)) :hints (("Goal" :in-theory (enable esp set-esp))))
(defthm ebp-of-set-ebp (equal (ebp (set-ebp val x86)) (bvchop 32 val)) :hints (("Goal" :in-theory (enable ebp set-ebp))))

;; Read of a write of a different register

(defthm eax-of-set-ebx (equal (eax (set-ebx val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-ebx))))
(defthm eax-of-set-ecx (equal (eax (set-ecx val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-ecx))))
(defthm eax-of-set-edx (equal (eax (set-edx val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-edx))))
(defthm eax-of-set-esp (equal (eax (set-esp val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-esp))))
(defthm eax-of-set-ebp (equal (eax (set-ebp val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-ebp))))

(defthm ebx-of-set-eax (equal (ebx (set-eax val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-eax))))
(defthm ebx-of-set-ecx (equal (ebx (set-ecx val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-ecx))))
(defthm ebx-of-set-edx (equal (ebx (set-edx val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-edx))))
(defthm ebx-of-set-esp (equal (ebx (set-esp val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-esp))))
(defthm ebx-of-set-ebp (equal (ebx (set-ebp val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-ebp))))

(defthm ecx-of-set-eax (equal (ecx (set-eax val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-eax))))
(defthm ecx-of-set-ebx (equal (ecx (set-ebx val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-ebx))))
(defthm ecx-of-set-edx (equal (ecx (set-edx val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-edx))))
(defthm ecx-of-set-esp (equal (ecx (set-esp val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-esp))))
(defthm ecx-of-set-ebp (equal (ecx (set-ebp val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-ebp))))

(defthm edx-of-set-eax (equal (edx (set-eax val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-eax))))
(defthm edx-of-set-ebx (equal (edx (set-ebx val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-ebx))))
(defthm edx-of-set-ecx (equal (edx (set-ecx val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-ecx))))
(defthm edx-of-set-esp (equal (edx (set-esp val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-esp))))
(defthm edx-of-set-ebp (equal (edx (set-ebp val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-ebp))))

(defthm esp-of-set-eax (equal (esp (set-eax val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-eax))))
(defthm esp-of-set-ebx (equal (esp (set-ebx val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-ebx))))
(defthm esp-of-set-ecx (equal (esp (set-ecx val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-ecx))))
(defthm esp-of-set-edx (equal (esp (set-edx val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-edx))))
(defthm esp-of-set-ebp (equal (esp (set-ebp val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-ebp))))

(defthm ebp-of-set-eax (equal (ebp (set-eax val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-eax))))
(defthm ebp-of-set-ebx (equal (ebp (set-ebx val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-ebx))))
(defthm ebp-of-set-ecx (equal (ebp (set-ecx val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-ecx))))
(defthm ebp-of-set-edx (equal (ebp (set-edx val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-edx))))
(defthm ebp-of-set-esp (equal (ebp (set-esp val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-esp))))


;; Read of a write of a different register

(defthm eax-of-set-rbx-high (equal (eax (set-rbx-high val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-rbx-high))))
(defthm eax-of-set-rcx-high (equal (eax (set-rcx-high val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-rcx-high))))
(defthm eax-of-set-rdx-high (equal (eax (set-rdx-high val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-rdx-high))))
(defthm eax-of-set-rsp-high (equal (eax (set-rsp-high val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-rsp-high))))
(defthm eax-of-set-rbp-high (equal (eax (set-rbp-high val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-rbp-high))))

(defthm ebx-of-set-rax-high (equal (ebx (set-rax-high val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-rax-high))))
(defthm ebx-of-set-rcx-high (equal (ebx (set-rcx-high val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-rcx-high))))
(defthm ebx-of-set-rdx-high (equal (ebx (set-rdx-high val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-rdx-high))))
(defthm ebx-of-set-rsp-high (equal (ebx (set-rsp-high val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-rsp-high))))
(defthm ebx-of-set-rbp-high (equal (ebx (set-rbp-high val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-rbp-high))))

(defthm ecx-of-set-rax-high (equal (ecx (set-rax-high val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-rax-high))))
(defthm ecx-of-set-rbx-high (equal (ecx (set-rbx-high val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-rbx-high))))
(defthm ecx-of-set-rdx-high (equal (ecx (set-rdx-high val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-rdx-high))))
(defthm ecx-of-set-rsp-high (equal (ecx (set-rsp-high val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-rsp-high))))
(defthm ecx-of-set-rbp-high (equal (ecx (set-rbp-high val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-rbp-high))))

(defthm edx-of-set-rax-high (equal (edx (set-rax-high val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-rax-high))))
(defthm edx-of-set-rbx-high (equal (edx (set-rbx-high val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-rbx-high))))
(defthm edx-of-set-rcx-high (equal (edx (set-rcx-high val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-rcx-high))))
(defthm edx-of-set-rsp-high (equal (edx (set-rsp-high val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-rsp-high))))
(defthm edx-of-set-rbp-high (equal (edx (set-rbp-high val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-rbp-high))))

(defthm esp-of-set-rax-high (equal (esp (set-rax-high val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-rax-high))))
(defthm esp-of-set-rbx-high (equal (esp (set-rbx-high val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-rbx-high))))
(defthm esp-of-set-rcx-high (equal (esp (set-rcx-high val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-rcx-high))))
(defthm esp-of-set-rdx-high (equal (esp (set-rdx-high val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-rdx-high))))
(defthm esp-of-set-rbp-high (equal (esp (set-rbp-high val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-rbp-high))))

(defthm ebp-of-set-rax-high (equal (ebp (set-rax-high val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-rax-high))))
(defthm ebp-of-set-rbx-high (equal (ebp (set-rbx-high val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-rbx-high))))
(defthm ebp-of-set-rcx-high (equal (ebp (set-rcx-high val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-rcx-high))))
(defthm ebp-of-set-rdx-high (equal (ebp (set-rdx-high val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-rdx-high))))
(defthm ebp-of-set-rsp-high (equal (ebp (set-rsp-high val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-rsp-high))))


(defthm rax-high-of-set-eip (equal (rax-high (set-eip eip x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable rax-high set-eip))))
(defthm rbx-high-of-set-eip (equal (rbx-high (set-eip eip x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable rbx-high set-eip))))
(defthm rcx-high-of-set-eip (equal (rcx-high (set-eip eip x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable rcx-high set-eip))))
(defthm rdx-high-of-set-eip (equal (rdx-high (set-eip eip x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable rdx-high set-eip))))
(defthm rsp-high-of-set-eip (equal (rsp-high (set-eip eip x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable rsp-high set-eip))))
(defthm rbp-high-of-set-eip (equal (rbp-high (set-eip eip x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable rbp-high set-eip))))

(defthm rax-high-of-set-ebx (equal (rax-high (set-ebx val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable rax-high set-ebx))))
(defthm rax-high-of-set-ecx (equal (rax-high (set-ecx val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable rax-high set-ecx))))
(defthm rax-high-of-set-edx (equal (rax-high (set-edx val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable rax-high set-edx))))
(defthm rax-high-of-set-esp (equal (rax-high (set-esp val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable rax-high set-esp))))
(defthm rax-high-of-set-ebp (equal (rax-high (set-ebp val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable rax-high set-ebp))))

(defthm rbx-high-of-set-eax (equal (rbx-high (set-eax val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable rbx-high set-eax))))
(defthm rbx-high-of-set-ecx (equal (rbx-high (set-ecx val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable rbx-high set-ecx))))
(defthm rbx-high-of-set-edx (equal (rbx-high (set-edx val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable rbx-high set-edx))))
(defthm rbx-high-of-set-esp (equal (rbx-high (set-esp val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable rbx-high set-esp))))
(defthm rbx-high-of-set-ebp (equal (rbx-high (set-ebp val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable rbx-high set-ebp))))

(defthm rcx-high-of-set-eax (equal (rcx-high (set-eax val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable rcx-high set-eax))))
(defthm rcx-high-of-set-ebx (equal (rcx-high (set-ebx val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable rcx-high set-ebx))))
(defthm rcx-high-of-set-edx (equal (rcx-high (set-edx val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable rcx-high set-edx))))
(defthm rcx-high-of-set-esp (equal (rcx-high (set-esp val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable rcx-high set-esp))))
(defthm rcx-high-of-set-ebp (equal (rcx-high (set-ebp val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable rcx-high set-ebp))))

(defthm rdx-high-of-set-eax (equal (rdx-high (set-eax val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable rdx-high set-eax))))
(defthm rdx-high-of-set-ebx (equal (rdx-high (set-ebx val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable rdx-high set-ebx))))
(defthm rdx-high-of-set-ecx (equal (rdx-high (set-ecx val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable rdx-high set-ecx))))
(defthm rdx-high-of-set-esp (equal (rdx-high (set-esp val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable rdx-high set-esp))))
(defthm rdx-high-of-set-ebp (equal (rdx-high (set-ebp val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable rdx-high set-ebp))))

(defthm rsp-high-of-set-eax (equal (rsp-high (set-eax val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable rsp-high set-eax))))
(defthm rsp-high-of-set-ebx (equal (rsp-high (set-ebx val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable rsp-high set-ebx))))
(defthm rsp-high-of-set-ecx (equal (rsp-high (set-ecx val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable rsp-high set-ecx))))
(defthm rsp-high-of-set-edx (equal (rsp-high (set-edx val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable rsp-high set-edx))))
(defthm rsp-high-of-set-ebp (equal (rsp-high (set-ebp val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable rsp-high set-ebp))))

(defthm rbp-high-of-set-eax (equal (rbp-high (set-eax val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable rbp-high set-eax))))
(defthm rbp-high-of-set-ebx (equal (rbp-high (set-ebx val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable rbp-high set-ebx))))
(defthm rbp-high-of-set-ecx (equal (rbp-high (set-ecx val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable rbp-high set-ecx))))
(defthm rbp-high-of-set-edx (equal (rbp-high (set-edx val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable rbp-high set-edx))))
(defthm rbp-high-of-set-esp (equal (rbp-high (set-esp val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable rbp-high set-esp))))

;; ;;; readers ignore set-reg-high
;; (defthm eax-of-set-reg-high (equal (eax (set-reg-high reg val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-reg-high))))
;; (defthm ebx-of-set-reg-high (equal (ebx (set-reg-high reg val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-reg-high))))
;; (defthm ecx-of-set-reg-high (equal (ecx (set-reg-high reg val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-reg-high))))
;; (defthm edx-of-set-reg-high (equal (edx (set-reg-high reg val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-reg-high))))
;; (defthm esp-of-set-reg-high (equal (esp (set-reg-high reg val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-reg-high))))
;; (defthm ebp-of-set-reg-high (equal (ebp (set-reg-high reg val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-reg-high))))

(defthm xr-of-set-eax (implies (not (equal fld :rgf)) (equal (xr fld index (set-eax eax x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-eax))))
(defthm xr-of-set-ebx (implies (not (equal fld :rgf)) (equal (xr fld index (set-ebx ebx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm xr-of-set-ecx (implies (not (equal fld :rgf)) (equal (xr fld index (set-ecx ecx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm xr-of-set-edx (implies (not (equal fld :rgf)) (equal (xr fld index (set-edx edx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-edx))))
(defthm xr-of-set-esp (implies (not (equal fld :rgf)) (equal (xr fld index (set-esp esp x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-esp))))
(defthm xr-of-set-ebp (implies (not (equal fld :rgf)) (equal (xr fld index (set-ebp ebp x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm xr-of-set-rax-high (implies (not (equal fld :rgf)) (equal (xr fld index (set-rax-high eax x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm xr-of-set-rbx-high (implies (not (equal fld :rgf)) (equal (xr fld index (set-rbx-high ebx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm xr-of-set-rcx-high (implies (not (equal fld :rgf)) (equal (xr fld index (set-rcx-high ecx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm xr-of-set-rdx-high (implies (not (equal fld :rgf)) (equal (xr fld index (set-rdx-high edx x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm xr-of-set-rsp-high (implies (not (equal fld :rgf)) (equal (xr fld index (set-rsp-high esp x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm xr-of-set-rbp-high (implies (not (equal fld :rgf)) (equal (xr fld index (set-rbp-high ebp x86)) (xr fld index x86))) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm xr-of-set-eip-irrel
  (implies (not (equal fld :rip))
           (equal (xr fld index (set-eip eip x86))
                  (xr fld index x86))))

;; ;; needed when fld is :seg-hidden-limit
;; (defthm xr-of-set-reg-high-irrel
;;   (implies (not (equal fld :rgf))
;;            (equal (xr fld index (set-reg-high reg val x86))
;;                   (xr fld index x86)))
;;   :hints (("Goal" :in-theory (enable set-reg-high))))

;drop?
(defthm xr-of-set-eip-same
  (equal (xr :rip nil (set-eip eip x86))
         (logext 48 eip))
  :hints (("Goal" :in-theory (enable set-eip))))

;;;

(defthm set-eax-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-eax eax (xw fld index val x86))
                  (xw fld index val (set-eax eax x86))))
  :hints (("Goal" :in-theory (enable set-eax rax-high
                                     ))))

(defthm set-ebx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-ebx ebx (xw fld index val x86))
                  (xw fld index val (set-ebx ebx x86))))
  :hints (("Goal" :in-theory (enable set-ebx rbx-high
                                     ))))

(defthm set-ecx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-ecx ecx (xw fld index val x86))
                  (xw fld index val (set-ecx ecx x86))))
  :hints (("Goal" :in-theory (enable set-ecx rcx-high
                                     ))))

(defthm set-edx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-edx edx (xw fld index val x86))
                  (xw fld index val (set-edx edx x86))))
  :hints (("Goal" :in-theory (enable set-edx rdx-high
                                     ))))

(defthm set-esp-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-esp esp (xw fld index val x86))
                  (xw fld index val (set-esp esp x86))))
  :hints (("Goal" :in-theory (enable set-esp rsp-high
                                     ))))

(defthm set-ebp-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-ebp ebp (xw fld index val x86))
                  (xw fld index val (set-ebp ebp x86))))
  :hints (("Goal" :in-theory (enable set-ebp rbp-high
                                     ))))

;;;
;;; sort calls to register writers
;;;

;;; bring set-eax forward

(defthm set-ebx-of-set-eax
  (equal (set-ebx ebx (set-eax eax x86))
         (set-eax eax (set-ebx ebx x86)))
  :hints (("Goal" :in-theory (enable set-eax set-ebx rax-high rbx-high))))

(defthm set-ecx-of-set-eax
  (equal (set-ecx ecx (set-eax eax x86))
         (set-eax eax (set-ecx ecx x86)))
  :hints (("Goal" :in-theory (enable set-eax set-ecx rax-high rcx-high))))

(defthm set-edx-of-set-eax
  (equal (set-edx edx (set-eax eax x86))
         (set-eax eax (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-eax set-edx rax-high rdx-high))))

(defthm set-esp-of-set-eax
  (equal (set-esp esp (set-eax eax x86))
         (set-eax eax (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-eax set-esp rax-high rsp-high))))

(defthm set-ebp-of-set-eax
  (equal (set-ebp ebp (set-eax eax x86))
         (set-eax eax (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-eax set-ebp rax-high rbp-high))))

;;; bring set-ebx forward

(defthm set-ecx-of-set-ebx
  (equal (set-ecx ecx (set-ebx ebx x86))
         (set-ebx ebx (set-ecx ecx x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-ecx rbx-high rcx-high))))

(defthm set-edx-of-set-ebx
  (equal (set-edx edx (set-ebx ebx x86))
         (set-ebx ebx (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-edx rbx-high rdx-high))))

(defthm set-esp-of-set-ebx
  (equal (set-esp esp (set-ebx ebx x86))
         (set-ebx ebx (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-esp rbx-high rsp-high))))

(defthm set-ebp-of-set-ebx
  (equal (set-ebp ebp (set-ebx ebx x86))
         (set-ebx ebx (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-ebp rbx-high rbp-high))))

;;; bring set-ecx forward

(defthm set-edx-of-set-ecx
  (equal (set-edx edx (set-ecx ecx x86))
         (set-ecx ecx (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-ecx set-edx rcx-high rdx-high))))

(defthm set-esp-of-set-ecx
  (equal (set-esp esp (set-ecx ecx x86))
         (set-ecx ecx (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-ecx set-esp rcx-high rsp-high))))

(defthm set-ebp-of-set-ecx
  (equal (set-ebp ebp (set-ecx ecx x86))
         (set-ecx ecx (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-ecx set-ebp rcx-high rbp-high))))

;;; bring set-edx forward

(defthm set-esp-of-set-edx
  (equal (set-esp esp (set-edx edx x86))
         (set-edx edx (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-edx set-esp rdx-high rsp-high))))

(defthm set-ebp-of-set-edx
  (equal (set-ebp ebp (set-edx edx x86))
         (set-edx edx (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-edx set-ebp rdx-high rbp-high))))

;;; bring set-esp forward

(defthm set-ebp-of-set-esp
  (equal (set-ebp ebp (set-esp esp x86))
         (set-esp esp (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-esp set-ebp rsp-high rbp-high))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; sort calls to register writers
;;;

;;; bring set-rax-high forward

(defthm set-rbx-high-of-set-rax-high
  (equal (set-rbx-high ebx (set-rax-high eax x86))
         (set-rax-high eax (set-rbx-high ebx x86)))
  :hints (("Goal" :in-theory (enable set-rax-high set-rbx-high rax-high rbx-high))))

(defthm set-rcx-high-of-set-rax-high
  (equal (set-rcx-high ecx (set-rax-high eax x86))
         (set-rax-high eax (set-rcx-high ecx x86)))
  :hints (("Goal" :in-theory (enable set-rax-high set-rcx-high rax-high rcx-high))))

(defthm set-rdx-high-of-set-rax-high
  (equal (set-rdx-high edx (set-rax-high eax x86))
         (set-rax-high eax (set-rdx-high edx x86)))
  :hints (("Goal" :in-theory (enable set-rax-high set-rdx-high rax-high rdx-high))))

(defthm set-rsp-high-of-set-rax-high
  (equal (set-rsp-high esp (set-rax-high eax x86))
         (set-rax-high eax (set-rsp-high esp x86)))
  :hints (("Goal" :in-theory (enable set-rax-high set-rsp-high rax-high rsp-high))))

(defthm set-rbp-high-of-set-rax-high
  (equal (set-rbp-high ebp (set-rax-high eax x86))
         (set-rax-high eax (set-rbp-high ebp x86)))
  :hints (("Goal" :in-theory (enable set-rax-high set-rbp-high rax-high rbp-high))))

;;; bring set-ebx forward

(defthm set-rcx-high-of-set-rbx-high
  (equal (set-rcx-high ecx (set-rbx-high ebx x86))
         (set-rbx-high ebx (set-rcx-high ecx x86)))
  :hints (("Goal" :in-theory (enable set-rbx-high set-rcx-high rbx-high rcx-high))))

(defthm set-rdx-high-of-set-rbx-high
  (equal (set-rdx-high edx (set-rbx-high ebx x86))
         (set-rbx-high ebx (set-rdx-high edx x86)))
  :hints (("Goal" :in-theory (enable set-rbx-high set-rdx-high rbx-high rdx-high))))

(defthm set-rsp-high-of-set-rbx-high
  (equal (set-rsp-high esp (set-rbx-high ebx x86))
         (set-rbx-high ebx (set-rsp-high esp x86)))
  :hints (("Goal" :in-theory (enable set-rbx-high set-rsp-high rbx-high rsp-high))))

(defthm set-rbp-high-of-set-rbx-high
  (equal (set-rbp-high ebp (set-rbx-high ebx x86))
         (set-rbx-high ebx (set-rbp-high ebp x86)))
  :hints (("Goal" :in-theory (enable set-rbx-high set-rbp-high rbx-high rbp-high))))

;;; bring set-rcx-high forward

(defthm set-rdx-high-of-set-rcx-high
  (equal (set-rdx-high edx (set-rcx-high ecx x86))
         (set-rcx-high ecx (set-rdx-high edx x86)))
  :hints (("Goal" :in-theory (enable set-rcx-high set-rdx-high rcx-high rdx-high))))

(defthm set-rsp-high-of-set-rcx-high
  (equal (set-rsp-high esp (set-rcx-high ecx x86))
         (set-rcx-high ecx (set-rsp-high esp x86)))
  :hints (("Goal" :in-theory (enable set-rcx-high set-rsp-high rcx-high rsp-high))))

(defthm set-rbp-high-of-set-rcx-high
  (equal (set-rbp-high ebp (set-rcx-high ecx x86))
         (set-rcx-high ecx (set-rbp-high ebp x86)))
  :hints (("Goal" :in-theory (enable set-rcx-high set-rbp-high rcx-high rbp-high))))

;;; bring set-rdx-high forward

(defthm set-rsp-high-of-set-rdx-high
  (equal (set-rsp-high esp (set-rdx-high edx x86))
         (set-rdx-high edx (set-rsp-high esp x86)))
  :hints (("Goal" :in-theory (enable set-rdx-high set-rsp-high rdx-high rsp-high))))

(defthm set-rbp-high-of-set-rdx-high
  (equal (set-rbp-high ebp (set-rdx-high edx x86))
         (set-rdx-high edx (set-rbp-high ebp x86)))
  :hints (("Goal" :in-theory (enable set-rdx-high set-rbp-high rdx-high rbp-high))))

;;; bring set-rsp-high forward

(defthm set-rbp-high-of-set-rsp-high
  (equal (set-rbp-high ebp (set-rsp-high esp x86))
         (set-rsp-high esp (set-rbp-high ebp x86)))
  :hints (("Goal" :in-theory (enable set-rsp-high set-rbp-high rsp-high rbp-high))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Write of write of the same register
(defthm set-eax-of-set-eax (equal (set-eax eax1 (set-eax eax2 x86)) (set-eax eax1 x86)) :hints (("Goal" :in-theory (enable set-eax rax-high))))
(defthm set-ebx-of-set-ebx (equal (set-ebx ebx1 (set-ebx ebx2 x86)) (set-ebx ebx1 x86)) :hints (("Goal" :in-theory (enable set-ebx rbx-high))))
(defthm set-ecx-of-set-ecx (equal (set-ecx ecx1 (set-ecx ecx2 x86)) (set-ecx ecx1 x86)) :hints (("Goal" :in-theory (enable set-ecx rcx-high))))
(defthm set-edx-of-set-edx (equal (set-edx edx1 (set-edx edx2 x86)) (set-edx edx1 x86)) :hints (("Goal" :in-theory (enable set-edx rdx-high))))
(defthm set-esp-of-set-esp (equal (set-esp esp1 (set-esp esp2 x86)) (set-esp esp1 x86)) :hints (("Goal" :in-theory (enable set-esp rsp-high))))
(defthm set-ebp-of-set-ebp (equal (set-ebp ebp1 (set-ebp ebp2 x86)) (set-ebp ebp1 x86)) :hints (("Goal" :in-theory (enable set-ebp rbp-high))))

(defthm set-rax-high-of-set-rax-high (equal (set-rax-high eax1 (set-rax-high eax2 x86)) (set-rax-high eax1 x86)) :hints (("Goal" :in-theory (enable set-rax-high rax-high))))
(defthm set-rbx-high-of-set-rbx-high (equal (set-rbx-high ebx1 (set-rbx-high ebx2 x86)) (set-rbx-high ebx1 x86)) :hints (("Goal" :in-theory (enable set-rbx-high rbx-high))))
(defthm set-rcx-high-of-set-rcx-high (equal (set-rcx-high ecx1 (set-rcx-high ecx2 x86)) (set-rcx-high ecx1 x86)) :hints (("Goal" :in-theory (enable set-rcx-high rcx-high))))
(defthm set-rdx-high-of-set-rdx-high (equal (set-rdx-high edx1 (set-rdx-high edx2 x86)) (set-rdx-high edx1 x86)) :hints (("Goal" :in-theory (enable set-rdx-high rdx-high))))
(defthm set-rsp-high-of-set-rsp-high (equal (set-rsp-high esp1 (set-rsp-high esp2 x86)) (set-rsp-high esp1 x86)) :hints (("Goal" :in-theory (enable set-rsp-high rsp-high))))
(defthm set-rbp-high-of-set-rbp-high (equal (set-rbp-high ebp1 (set-rbp-high ebp2 x86)) (set-rbp-high ebp1 x86)) :hints (("Goal" :in-theory (enable set-rbp-high rbp-high))))

;;; todo: can we get rid of these?

;; (defthm xr-of-set-esp-same
;;   (equal (xr ':rgf '4 (set-esp esp x86))
;;          (bvchop 32 esp))
;;   :hints (("Goal" :in-theory (enable set-esp rsp-high))))

;; (defthm xr-of-esp-and-set-eax
;;   (equal (xr ':rgf '4 (set-eax esp x86))
;;          (xr ':rgf '4 x86))
;;   :hints (("Goal" :in-theory (enable set-eax))))

;; (defthm xr-of-esp-and-set-ebx
;;   (equal (xr ':rgf '4 (set-ebx esp x86))
;;          (xr ':rgf '4 x86))
;;   :hints (("Goal" :in-theory (enable set-ebx))))

;; (defthm xr-of-esp-and-set-ecx
;;   (equal (xr ':rgf '4 (set-ecx esp x86))
;;          (xr ':rgf '4 x86))
;;   :hints (("Goal" :in-theory (enable set-ecx))))

;; (defthm xr-of-esp-and-set-edx
;;   (equal (xr ':rgf '4 (set-edx esp x86))
;;          (xr ':rgf '4 x86))
;;   :hints (("Goal" :in-theory (enable set-edx))))

;; (defthm xr-of-esp-and-set-ebp
;;   (equal (xr ':rgf '4 (set-ebp ebp x86))
;;          (xr ':rgf '4 x86))
;;   :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm esp-of-if
  (equal (esp (if test tp ep))
         (if test
             (esp tp)
           (esp ep)))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm rax-high-of-xw (implies (not (equal fld :rgf)) (equal (rax-high (xw fld index value x86)) (rax-high x86))) :hints (("Goal" :in-theory (enable rax-high))))
(defthm rbx-high-of-xw (implies (not (equal fld :rgf)) (equal (rbx-high (xw fld index value x86)) (rbx-high x86))) :hints (("Goal" :in-theory (enable rbx-high))))
(defthm rcx-high-of-xw (implies (not (equal fld :rgf)) (equal (rcx-high (xw fld index value x86)) (rcx-high x86))) :hints (("Goal" :in-theory (enable rcx-high))))
(defthm rdx-high-of-xw (implies (not (equal fld :rgf)) (equal (rdx-high (xw fld index value x86)) (rdx-high x86))) :hints (("Goal" :in-theory (enable rdx-high))))
(defthm rsp-high-of-xw (implies (not (equal fld :rgf)) (equal (rsp-high (xw fld index value x86)) (rsp-high x86))) :hints (("Goal" :in-theory (enable rsp-high))))
(defthm rbp-high-of-xw (implies (not (equal fld :rgf)) (equal (rbp-high (xw fld index value x86)) (rbp-high x86))) :hints (("Goal" :in-theory (enable rbp-high))))

;; read-<reg> of set-eip

(defthm eax-of-set-eip
  (equal (eax (set-eip eip x86))
         (eax x86))
  :hints (("Goal" :in-theory (enable eax))))

;;;

(defthm ebx-of-set-eip
  (equal (ebx (set-eip eip x86))
         (ebx x86))
  :hints (("Goal" :in-theory (enable ebx))))

;;;

(defthm ecx-of-set-eip
  (equal (ecx (set-eip eip x86))
         (ecx x86))
  :hints (("Goal" :in-theory (enable ecx))))

;;;

(defthm edx-of-set-eip
  (equal (edx (set-eip eip x86))
         (edx x86))
  :hints (("Goal" :in-theory (enable edx))))

;;;

(defthm esp-of-set-eip
  (equal (esp (set-eip eip x86))
         (esp x86))
  :hints (("Goal" :in-theory (enable esp))))

;;;

(defthm ebp-of-set-eip
  (equal (ebp (set-eip eip x86))
         (ebp x86))
  :hints (("Goal" :in-theory (enable ebp))))


(defthm x86p-of-set-eax (implies (x86p x86) (x86p (set-eax eax x86))) :hints (("Goal" :in-theory (enable set-eax))))
(defthm x86p-of-set-ebx (implies (x86p x86) (x86p (set-ebx ebx x86))) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm x86p-of-set-ecx (implies (x86p x86) (x86p (set-ecx ecx x86))) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm x86p-of-set-edx (implies (x86p x86) (x86p (set-edx edx x86))) :hints (("Goal" :in-theory (enable set-edx))))
(defthm x86p-of-set-esp (implies (x86p x86) (x86p (set-esp esp x86))) :hints (("Goal" :in-theory (enable set-esp))))
(defthm x86p-of-set-ebp (implies (x86p x86) (x86p (set-ebp ebp x86))) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm x86p-of-set-rax-high (implies (x86p x86) (x86p (set-rax-high eax x86))) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm x86p-of-set-rbx-high (implies (x86p x86) (x86p (set-rbx-high ebx x86))) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm x86p-of-set-rcx-high (implies (x86p x86) (x86p (set-rcx-high ecx x86))) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm x86p-of-set-rdx-high (implies (x86p x86) (x86p (set-rdx-high edx x86))) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm x86p-of-set-rsp-high (implies (x86p x86) (x86p (set-rsp-high esp x86))) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm x86p-of-set-rbp-high (implies (x86p x86) (x86p (set-rbp-high ebp x86))) :hints (("Goal" :in-theory (enable set-rbp-high))))

;;;

(defthm eip-of-set-eax (equal (eip (set-eax eax x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm eip-of-set-ebx (equal (eip (set-ebx ebx x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm eip-of-set-ecx (equal (eip (set-ecx ecx x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm eip-of-set-edx (equal (eip (set-edx edx x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm eip-of-set-esp (equal (eip (set-esp esp x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm eip-of-set-ebp (equal (eip (set-ebp ebp x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm eip-of-set-rax-high (equal (eip (set-rax-high val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm eip-of-set-rbx-high (equal (eip (set-rbx-high val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm eip-of-set-rcx-high (equal (eip (set-rcx-high val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm eip-of-set-rdx-high (equal (eip (set-rdx-high val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm eip-of-set-rsp-high (equal (eip (set-rsp-high val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm eip-of-set-rbp-high (equal (eip (set-rbp-high val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

;;;

;(defthm set-rxx-high-of-set-eyx (equal (set-rxx-high val1 (set-eyx val2 x86)) (set-eyx val2 (set-rxx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rxx-high set-eyx ryx-high))))

(defthm set-rax-high-of-set-eax (equal (set-rax-high val1 (set-eax val2 x86)) (set-eax val2 (set-rax-high val1 x86))) :hints (("Goal" :in-theory (enable set-rax-high set-eax rax-high))))
(defthm set-rax-high-of-set-ebx (equal (set-rax-high val1 (set-ebx val2 x86)) (set-ebx val2 (set-rax-high val1 x86))) :hints (("Goal" :in-theory (enable set-rax-high set-ebx rbx-high))))
(defthm set-rax-high-of-set-ecx (equal (set-rax-high val1 (set-ecx val2 x86)) (set-ecx val2 (set-rax-high val1 x86))) :hints (("Goal" :in-theory (enable set-rax-high set-ecx rcx-high))))
(defthm set-rax-high-of-set-edx (equal (set-rax-high val1 (set-edx val2 x86)) (set-edx val2 (set-rax-high val1 x86))) :hints (("Goal" :in-theory (enable set-rax-high set-edx rdx-high))))
(defthm set-rax-high-of-set-esp (equal (set-rax-high val1 (set-esp val2 x86)) (set-esp val2 (set-rax-high val1 x86))) :hints (("Goal" :in-theory (enable set-rax-high set-esp rsp-high))))
(defthm set-rax-high-of-set-ebp (equal (set-rax-high val1 (set-ebp val2 x86)) (set-ebp val2 (set-rax-high val1 x86))) :hints (("Goal" :in-theory (enable set-rax-high set-ebp rbp-high))))

(defthm set-rbx-high-of-set-eax (equal (set-rbx-high val1 (set-eax val2 x86)) (set-eax val2 (set-rbx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbx-high set-eax rax-high))))
(defthm set-rbx-high-of-set-ebx (equal (set-rbx-high val1 (set-ebx val2 x86)) (set-ebx val2 (set-rbx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbx-high set-ebx rbx-high))))
(defthm set-rbx-high-of-set-ecx (equal (set-rbx-high val1 (set-ecx val2 x86)) (set-ecx val2 (set-rbx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbx-high set-ecx rcx-high))))
(defthm set-rbx-high-of-set-edx (equal (set-rbx-high val1 (set-edx val2 x86)) (set-edx val2 (set-rbx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbx-high set-edx rdx-high))))
(defthm set-rbx-high-of-set-esp (equal (set-rbx-high val1 (set-esp val2 x86)) (set-esp val2 (set-rbx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbx-high set-esp rsp-high))))
(defthm set-rbx-high-of-set-ebp (equal (set-rbx-high val1 (set-ebp val2 x86)) (set-ebp val2 (set-rbx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbx-high set-ebp rbp-high))))

(defthm set-rcx-high-of-set-eax (equal (set-rcx-high val1 (set-eax val2 x86)) (set-eax val2 (set-rcx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rcx-high set-eax rax-high))))
(defthm set-rcx-high-of-set-ebx (equal (set-rcx-high val1 (set-ebx val2 x86)) (set-ebx val2 (set-rcx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rcx-high set-ebx rbx-high))))
(defthm set-rcx-high-of-set-ecx (equal (set-rcx-high val1 (set-ecx val2 x86)) (set-ecx val2 (set-rcx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rcx-high set-ecx rcx-high))))
(defthm set-rcx-high-of-set-edx (equal (set-rcx-high val1 (set-edx val2 x86)) (set-edx val2 (set-rcx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rcx-high set-edx rdx-high))))
(defthm set-rcx-high-of-set-esp (equal (set-rcx-high val1 (set-esp val2 x86)) (set-esp val2 (set-rcx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rcx-high set-esp rsp-high))))
(defthm set-rcx-high-of-set-ebp (equal (set-rcx-high val1 (set-ebp val2 x86)) (set-ebp val2 (set-rcx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rcx-high set-ebp rbp-high))))

(defthm set-rdx-high-of-set-eax (equal (set-rdx-high val1 (set-eax val2 x86)) (set-eax val2 (set-rdx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rdx-high set-eax rax-high))))
(defthm set-rdx-high-of-set-ebx (equal (set-rdx-high val1 (set-ebx val2 x86)) (set-ebx val2 (set-rdx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rdx-high set-ebx rbx-high))))
(defthm set-rdx-high-of-set-ecx (equal (set-rdx-high val1 (set-ecx val2 x86)) (set-ecx val2 (set-rdx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rdx-high set-ecx rcx-high))))
(defthm set-rdx-high-of-set-edx (equal (set-rdx-high val1 (set-edx val2 x86)) (set-edx val2 (set-rdx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rdx-high set-edx rdx-high))))
(defthm set-rdx-high-of-set-esp (equal (set-rdx-high val1 (set-esp val2 x86)) (set-esp val2 (set-rdx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rdx-high set-esp rsp-high))))
(defthm set-rdx-high-of-set-ebp (equal (set-rdx-high val1 (set-ebp val2 x86)) (set-ebp val2 (set-rdx-high val1 x86))) :hints (("Goal" :in-theory (enable set-rdx-high set-ebp rbp-high))))

(defthm set-rsp-high-of-set-eax (equal (set-rsp-high val1 (set-eax val2 x86)) (set-eax val2 (set-rsp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rsp-high set-eax rax-high))))
(defthm set-rsp-high-of-set-ebx (equal (set-rsp-high val1 (set-ebx val2 x86)) (set-ebx val2 (set-rsp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rsp-high set-ebx rbx-high))))
(defthm set-rsp-high-of-set-ecx (equal (set-rsp-high val1 (set-ecx val2 x86)) (set-ecx val2 (set-rsp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rsp-high set-ecx rcx-high))))
(defthm set-rsp-high-of-set-edx (equal (set-rsp-high val1 (set-edx val2 x86)) (set-edx val2 (set-rsp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rsp-high set-edx rdx-high))))
(defthm set-rsp-high-of-set-ebp (equal (set-rsp-high val1 (set-esp val2 x86)) (set-esp val2 (set-rsp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rsp-high set-esp rsp-high))))
(defthm set-rsp-high-of-set-esp (equal (set-rsp-high val1 (set-ebp val2 x86)) (set-ebp val2 (set-rsp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rsp-high set-ebp rbp-high))))

(defthm set-rbp-high-of-set-eax (equal (set-rbp-high val1 (set-eax val2 x86)) (set-eax val2 (set-rbp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbp-high set-eax rax-high))))
(defthm set-rbp-high-of-set-ebx (equal (set-rbp-high val1 (set-ebx val2 x86)) (set-ebx val2 (set-rbp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbp-high set-ebx rbx-high))))
(defthm set-rbp-high-of-set-ecx (equal (set-rbp-high val1 (set-ecx val2 x86)) (set-ecx val2 (set-rbp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbp-high set-ecx rcx-high))))
(defthm set-rbp-high-of-set-edx (equal (set-rbp-high val1 (set-edx val2 x86)) (set-edx val2 (set-rbp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbp-high set-edx rdx-high))))
(defthm set-rbp-high-of-set-esp (equal (set-rbp-high val1 (set-esp val2 x86)) (set-esp val2 (set-rbp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbp-high set-esp rsp-high))))
(defthm set-rbp-high-of-set-ebp (equal (set-rbp-high val1 (set-ebp val2 x86)) (set-ebp val2 (set-rbp-high val1 x86))) :hints (("Goal" :in-theory (enable set-rbp-high set-ebp rbp-high))))

(defthm set-rax-high-of-set-eip (equal (set-rax-high val (set-eip eip x86)) (set-eip eip (set-rax-high val x86))) :hints (("Goal" :in-theory (enable set-rax-high set-eip rax-high))))
(defthm set-rbx-high-of-set-eip (equal (set-rbx-high val (set-eip eip x86)) (set-eip eip (set-rbx-high val x86))) :hints (("Goal" :in-theory (enable set-rbx-high set-eip rbx-high))))
(defthm set-rcx-high-of-set-eip (equal (set-rcx-high val (set-eip eip x86)) (set-eip eip (set-rcx-high val x86))) :hints (("Goal" :in-theory (enable set-rcx-high set-eip rcx-high))))
(defthm set-rdx-high-of-set-eip (equal (set-rdx-high val (set-eip eip x86)) (set-eip eip (set-rdx-high val x86))) :hints (("Goal" :in-theory (enable set-rdx-high set-eip rdx-high))))
(defthm set-rsp-high-of-set-eip (equal (set-rsp-high val (set-eip eip x86)) (set-eip eip (set-rsp-high val x86))) :hints (("Goal" :in-theory (enable set-rsp-high set-eip rsp-high))))
(defthm set-rbp-high-of-set-eip (equal (set-rbp-high val (set-eip eip x86)) (set-eip eip (set-rbp-high val x86))) :hints (("Goal" :in-theory (enable set-rbp-high set-eip rbp-high))))
