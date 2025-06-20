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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers for expressing the high bits of the 64-bit registers (in 32-bit mode, these are usually ignored).
;; todo: just make a single one of these?
(defund rax-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rax* x86)))
(defund rbx-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rbx* x86)))
(defund rcx-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rcx* x86)))
(defund rdx-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rdx* x86)))
(defund rsp-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rsp* x86)))
(defund rbp-high (x86) (declare (xargs :stobjs x86)) (slice 63 32 (rgfi *rbp* x86)))

;; Register readers (these take the signed-byte-64 values and chop them down to unsigned-byte-32s):
(defund eax (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rax* x86)))
(defund ebx (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rbx* x86)))
(defund ecx (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rcx* x86)))
(defund edx (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rdx* x86)))
(defund esp (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rsp* x86)))
(defund ebp (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rgfi *rbp* x86)))
;; todo: esi and edi!

;; Introduce the register readers:
;; These rules are disabled since they are not appropriate for 64-bit reasoning:
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

;; Aliases for expressing the high bits of the 48-bit RIP (undefined in 32-bit mode).
(defund rip-high (x86) (declare (xargs :stobjs x86)) (slice 47 32 (rip x86)))

;; Gets the 32-bit instruction pointer:
(defun eip (x86) (declare (xargs :stobjs x86)) (bvchop 32 (rip x86)))

;; These rules are disabled since they are not appropriate for 64-bit reasoning:
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
(defund set-reg-high (reg val x86)
  (declare (xargs :stobjs x86 :guard (and (and (natp reg) (< reg 16))
                                          (unsigned-byte-p 32 val))))
  (!rgfi reg (logext 64 (bvcat 32 val 32 (rgfi reg x86))) x86))

(defthm set-reg-high-of-set-reg-high-same
  (equal (set-reg-high reg val1 (set-reg-high reg val2 x86))
         (set-reg-high reg val1 x86))
  :hints (("Goal" :in-theory (enable set-reg-high
                                     acl2::bvcat-of-bvcat-tighten-arg4))))

(defthm set-reg-high-of-set-reg-high-diff
  (implies (< reg2 reg1)
           (equal (set-reg-high reg1 val1 (set-reg-high reg2 val2 x86))
                  (set-reg-high reg2 val2 (set-reg-high reg1 val1 x86))))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm set-reg-high-of-bvchop (implies (and (<= 32 n) (integerp n)) (equal (set-reg-high reg (bvchop n val) x86) (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high))))
(defthm set-reg-high-does-nothing (implies (equal val (slice 63 32 (rgfi reg x86))) (equal (set-reg-high reg val x86) x86)) :hints (("Goal" :in-theory (enable set-reg-high))))

;; todo: either make separate set-reg-high functions for each register, or don't have separate getters like rax-high
(defthm set-reg-high-of-rax-does-nothing (implies (equal val (rax-high x86)) (equal (set-reg-high *rax* val x86) x86)) :hints (("Goal" :in-theory (enable rax-high set-reg-high))))
(defthm set-reg-high-of-rbx-does-nothing (implies (equal val (rbx-high x86)) (equal (set-reg-high *rbx* val x86) x86)) :hints (("Goal" :in-theory (enable rbx-high set-reg-high))))
(defthm set-reg-high-of-rcx-does-nothing (implies (equal val (rcx-high x86)) (equal (set-reg-high *rcx* val x86) x86)) :hints (("Goal" :in-theory (enable rcx-high set-reg-high))))
(defthm set-reg-high-of-rdx-does-nothing (implies (equal val (rdx-high x86)) (equal (set-reg-high *rdx* val x86) x86)) :hints (("Goal" :in-theory (enable rdx-high set-reg-high))))
(defthm set-reg-high-of-rsp-does-nothing (implies (equal val (rsp-high x86)) (equal (set-reg-high *rsp* val x86) x86)) :hints (("Goal" :in-theory (enable rsp-high set-reg-high))))
(defthm set-reg-high-of-rbp-does-nothing (implies (equal val (rbp-high x86)) (equal (set-reg-high *rbp* val x86) x86)) :hints (("Goal" :in-theory (enable rbp-high set-reg-high))))

(defthm x86p-of-set-reg-high (implies (x86p x86) (x86p (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high))))
(defthm eip-of-set-reg-high (equal (eip (set-reg-high reg val x86)) (eip x86)) :hints (("Goal" :in-theory (enable set-reg-high))))
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

;; Register writers (these only change the low 32 bits):
(defund set-eax (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rax* (logext 64 (bvcat 32 (rax-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-ebx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbx* (logext 64 (bvcat 32 (rbx-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-ecx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rcx* (logext 64 (bvcat 32 (rcx-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-edx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rdx* (logext 64 (bvcat 32 (rdx-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-esp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rsp* (logext 64 (bvcat 32 (rsp-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop
(defund set-ebp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbp* (logext 64 (bvcat 32 (rbp-high x86) 32 (bvchop 32 val))) x86)) ; could drop the bvchop

;; Introduce the register writers
;; The extra calls of set-rax-high, etc. should usually be irrelevant (todo: add rules about that, also reading-the-read rules about those...)
;; These rules are disabled since they are not appropriate for 64-bit reasoning:
(defthmd xw-becomes-set-eax (equal (xw :rgf *rax* val x86) (set-eax (bvchop 32 val) (set-reg-high *rax* (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-eax rax-high set-reg-high))))
(defthmd xw-becomes-set-ebx (equal (xw :rgf *rbx* val x86) (set-ebx (bvchop 32 val) (set-reg-high *rbx* (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-ebx rbx-high set-reg-high))))
(defthmd xw-becomes-set-ecx (equal (xw :rgf *rcx* val x86) (set-ecx (bvchop 32 val) (set-reg-high *rcx* (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-ecx rcx-high set-reg-high))))
(defthmd xw-becomes-set-edx (equal (xw :rgf *rdx* val x86) (set-edx (bvchop 32 val) (set-reg-high *rdx* (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-edx rdx-high set-reg-high))))
(defthmd xw-becomes-set-esp (equal (xw :rgf *rsp* val x86) (set-esp (bvchop 32 val) (set-reg-high *rsp* (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-esp rsp-high set-reg-high))))
(defthmd xw-becomes-set-ebp (equal (xw :rgf *rbp* val x86) (set-ebp (bvchop 32 val) (set-reg-high *rbp* (slice 63 32 val) x86))) :hints (("Goal" :in-theory (enable set-ebp rbp-high set-reg-high))))

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

;;; readers ignore set-reg-high
(defthm eax-of-set-reg-high (equal (eax (set-reg-high reg val x86)) (eax x86)) :hints (("Goal" :in-theory (enable eax set-reg-high))))
(defthm ebx-of-set-reg-high (equal (ebx (set-reg-high reg val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable ebx set-reg-high))))
(defthm ecx-of-set-reg-high (equal (ecx (set-reg-high reg val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable ecx set-reg-high))))
(defthm edx-of-set-reg-high (equal (edx (set-reg-high reg val x86)) (edx x86)) :hints (("Goal" :in-theory (enable edx set-reg-high))))
(defthm esp-of-set-reg-high (equal (esp (set-reg-high reg val x86)) (esp x86)) :hints (("Goal" :in-theory (enable esp set-reg-high))))
(defthm ebp-of-set-reg-high (equal (ebp (set-reg-high reg val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable ebp set-reg-high))))

(defthm xr-of-set-eax
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-eax eax x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm xr-of-set-ebx
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-ebx ebx x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm xr-of-set-ecx
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-ecx ecx x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm xr-of-set-edx
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-edx edx x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm xr-of-set-esp
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-esp esp x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm xr-of-set-ebp
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (xr fld index (set-ebp ebp x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm xr-of-set-eip-irrel
  (implies (not (equal fld :rip))
           (equal (xr fld index (set-eip eip x86))
                  (xr fld index x86))))

;; needed when fld is :seg-hidden-limit
(defthm xr-of-set-reg-high-irrel
  (implies (not (equal fld :rgf))
           (equal (xr fld index (set-reg-high reg val x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-reg-high))))

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

;; Write of write of the same register
(defthm set-eax-of-set-eax (equal (set-eax eax1 (set-eax eax2 x86)) (set-eax eax1 x86)) :hints (("Goal" :in-theory (enable set-eax rax-high))))
(defthm set-ebx-of-set-ebx (equal (set-ebx ebx1 (set-ebx ebx2 x86)) (set-ebx ebx1 x86)) :hints (("Goal" :in-theory (enable set-ebx rbx-high))))
(defthm set-ecx-of-set-ecx (equal (set-ecx ecx1 (set-ecx ecx2 x86)) (set-ecx ecx1 x86)) :hints (("Goal" :in-theory (enable set-ecx rcx-high))))
(defthm set-edx-of-set-edx (equal (set-edx edx1 (set-edx edx2 x86)) (set-edx edx1 x86)) :hints (("Goal" :in-theory (enable set-edx rdx-high))))
(defthm set-esp-of-set-esp (equal (set-esp esp1 (set-esp esp2 x86)) (set-esp esp1 x86)) :hints (("Goal" :in-theory (enable set-esp rsp-high))))
(defthm set-ebp-of-set-ebp (equal (set-ebp ebp1 (set-ebp ebp2 x86)) (set-ebp ebp1 x86)) :hints (("Goal" :in-theory (enable set-ebp rbp-high))))

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

;; used for, for example, when FLD is :UNDEF
(defthm eax-of-xw (implies (not (equal fld :rgf)) (equal (eax (xw fld index value x86)) (eax x86))) :hints (("Goal" :in-theory (enable eax))))
(defthm ebx-of-xw (implies (not (equal fld :rgf)) (equal (ebx (xw fld index value x86)) (ebx x86))) :hints (("Goal" :in-theory (enable ebx))))
(defthm ecx-of-xw (implies (not (equal fld :rgf)) (equal (ecx (xw fld index value x86)) (ecx x86))) :hints (("Goal" :in-theory (enable ecx))))
(defthm edx-of-xw (implies (not (equal fld :rgf)) (equal (edx (xw fld index value x86)) (edx x86))) :hints (("Goal" :in-theory (enable edx))))
(defthm esp-of-xw (implies (not (equal fld :rgf)) (equal (esp (xw fld index value x86)) (esp x86))) :hints (("Goal" :in-theory (enable esp))))
(defthm ebp-of-xw (implies (not (equal fld :rgf)) (equal (ebp (xw fld index value x86)) (ebp x86))) :hints (("Goal" :in-theory (enable ebp))))

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


(defthm x86p-of-set-eax
  (implies (x86p x86)
           (x86p (set-eax eax x86)))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm x86p-of-set-ebx
  (implies (x86p x86)
           (x86p (set-ebx ebx x86)))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm x86p-of-set-ecx
  (implies (x86p x86)
           (x86p (set-ecx ecx x86)))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm x86p-of-set-edx
  (implies (x86p x86)
           (x86p (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm x86p-of-set-esp
  (implies (x86p x86)
           (x86p (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm x86p-of-set-ebp
  (implies (x86p x86)
           (x86p (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm eip-of-set-eax
  (equal (eip (set-eax eax x86))
         (eip x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm eip-of-set-ebx
  (equal (eip (set-ebx ebx x86))
         (eip x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm eip-of-set-ecx
  (equal (eip (set-ecx ecx x86))
         (eip x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm eip-of-set-edx
  (equal (eip (set-edx edx x86))
         (eip x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm eip-of-set-esp
  (equal (eip (set-esp esp x86))
         (eip x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm eip-of-set-ebp
  (equal (eip (set-ebp ebp x86))
         (eip x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;
