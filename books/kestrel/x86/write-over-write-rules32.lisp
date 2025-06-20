; "Write over write" rules for our 32-bit x86 state writers
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "support32")
(include-book "register-readers-and-writers32")
(local (include-book "kestrel/bv/rules" :dir :system)) ; for bvcat-of-logext-arg4
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/rules6" :dir :system))

(defthm write-byte-to-segment-of-set-eip
  (equal (write-byte-to-segment eff-addr seg-reg val (set-eip eip x86))
         (set-eip eip (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm write-to-segment-of-set-eip
  (equal (write-to-segment n eff-addr seg-reg val (set-eip eip x86))
         (set-eip eip  (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm set-undef-of-write-byte-to-segment
  (equal (set-undef undef (write-byte-to-segment eff-addr seg-reg val x86))
         (write-byte-to-segment eff-addr seg-reg val (set-undef undef x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-undef))))

(defthm set-undef-of-write-to-segment
  (equal (set-undef undef (write-to-segment n eff-addr seg-reg val x86))
         (write-to-segment n eff-addr seg-reg val (set-undef undef x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm set-reg-high-of-write-byte-to-segment
  (equal (set-reg-high reg val (write-byte-to-segment eff-addr seg-reg val2 x86))
         (write-byte-to-segment eff-addr seg-reg val2 (set-reg-high reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-reg-high))))

(defthm set-reg-high-of-write-to-segment
  (equal (set-reg-high reg val (write-to-segment n eff-addr seg-reg val2 x86))
         (write-to-segment n eff-addr seg-reg val2 (set-reg-high reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm set-flag-of-write-byte-to-segment
  (equal (set-flag flag fval (write-byte-to-segment eff-addr seg-reg val x86))
         (write-byte-to-segment eff-addr seg-reg val (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-flag))))

(defthm set-flag-of-write-to-segment
  (equal (set-flag flag fval (write-to-segment n eff-addr seg-reg val x86))
         (write-to-segment n eff-addr seg-reg val (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm write-byte-to-segment-of-xw-rgf
  (equal (write-byte-to-segment eff-addr seg-reg val (xw :rgf reg rval x86))
         (xw :rgf reg rval (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm write-to-segment-of-xw-rgf
  (equal (write-to-segment n eff-addr seg-reg val (xw :rgf reg rval x86))
         (xw :rgf reg rval (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;; ;;; write-byte-to-segment of write-<reg>

(defthm write-byte-to-segment-of-set-eax
  (equal (write-byte-to-segment eff-addr seg-reg val (set-eax eax x86))
         (set-eax eax (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-eax))))

(defthm write-byte-to-segment-of-set-ebx
  (equal (write-byte-to-segment eff-addr seg-reg val (set-ebx ebx x86))
         (set-ebx ebx (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-ebx))))

(defthm write-byte-to-segment-of-set-ecx
  (equal (write-byte-to-segment eff-addr seg-reg val (set-ecx ecx x86))
         (set-ecx ecx (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-ecx))))

(defthm write-byte-to-segment-of-set-edx
  (equal (write-byte-to-segment eff-addr seg-reg val (set-edx edx x86))
         (set-edx edx (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-edx))))

(defthm write-byte-to-segment-of-set-esp
  (equal (write-byte-to-segment eff-addr seg-reg val (set-esp esp x86))
         (set-esp esp (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-esp))))

(defthm write-byte-to-segment-of-set-ebp
  (equal (write-byte-to-segment eff-addr seg-reg val (set-ebp ebp x86))
         (set-ebp ebp (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment set-ebp))))

;;; write-to-segment of write-<reg>

(defthm write-to-segment-of-set-eax
  (equal (write-to-segment n eff-addr seg-reg val (set-eax eax x86))
         (set-eax eax (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm write-to-segment-of-set-ebx
  (equal (write-to-segment n eff-addr seg-reg val (set-ebx ebx x86))
         (set-ebx ebx (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm write-to-segment-of-set-ecx
  (equal (write-to-segment n eff-addr seg-reg val (set-ecx ecx x86))
         (set-ecx ecx (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm write-to-segment-of-set-edx
  (equal (write-to-segment n eff-addr seg-reg val (set-edx edx x86))
         (set-edx edx (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm write-to-segment-of-set-esp
  (equal (write-to-segment n eff-addr seg-reg val (set-esp esp x86))
         (set-esp esp (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm write-to-segment-of-set-ebp
  (equal (write-to-segment n eff-addr seg-reg val (set-ebp ebp x86))
         (set-ebp ebp (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;

(defthm set-flag-of-set-eax
  (equal (set-flag flag fval (set-eax eax x86))
         (set-eax eax (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm set-flag-of-set-ebx
  (equal (set-flag flag fval (set-ebx ebx x86))
         (set-ebx ebx (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm set-flag-of-set-ecx
  (equal (set-flag flag fval (set-ecx ecx x86))
         (set-ecx ecx (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm set-flag-of-set-edx
  (equal (set-flag flag fval (set-edx edx x86))
         (set-edx edx (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm set-flag-of-set-esp
  (equal (set-flag flag fval (set-esp esp x86))
         (set-esp esp (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm set-flag-of-set-ebp
  (equal (set-flag flag fval (set-ebp ebp x86))
         (set-ebp ebp (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

;;;

(defthm set-eax-of-set-eip
  (equal (set-eax eax (set-eip eip x86))
         (set-eip eip (set-eax eax x86)))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm set-ebx-of-set-eip
  (equal (set-ebx ebx (set-eip eip x86))
         (set-eip eip (set-ebx ebx x86)))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm set-ecx-of-set-eip
  (equal (set-ecx ecx (set-eip eip x86))
         (set-eip eip (set-ecx ecx x86)))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm set-edx-of-set-eip
  (equal (set-edx edx (set-eip eip x86))
         (set-eip eip (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm set-esp-of-set-eip
  (equal (set-esp esp (set-eip eip x86))
         (set-eip eip (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm set-ebp-of-set-eip
  (equal (set-ebp ebp (set-eip eip x86))
         (set-eip eip (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-eip))))


;; These push set-undef inward:
(defthm set-undef-of-set-eip (equal (set-undef undef (set-eip rip x86)) (set-eip rip (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef))))
(defthm set-undef-of-set-eax (equal (set-undef undef (set-eax rax x86)) (set-eax rax (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-eax))))
(defthm set-undef-of-set-ebx (equal (set-undef undef (set-ebx rbx x86)) (set-ebx rbx (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-ebx))))
(defthm set-undef-of-set-ecx (equal (set-undef undef (set-ecx rcx x86)) (set-ecx rcx (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-ecx))))
(defthm set-undef-of-set-edx (equal (set-undef undef (set-edx rdx x86)) (set-edx rdx (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-edx))))
;; (defthm set-undef-of-set-esi (equal (set-undef undef (set-esi rsi x86)) (set-esi rsi (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-esi))))
;; (defthm set-undef-of-set-edi (equal (set-undef undef (set-edi rdi x86)) (set-edi rdi (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-edi))))
(defthm set-undef-of-set-esp (equal (set-undef undef (set-esp rsp x86)) (set-esp rsp (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-esp))))
(defthm set-undef-of-set-ebp (equal (set-undef undef (set-ebp rbp x86)) (set-ebp rbp (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-ebp))))

(local (in-theory (enable acl2::bvcat-of-bvcat-tighten-arg4)))

;; These push set-reg-high inward:
(defthm set-reg-high-of-set-eip (equal (set-reg-high reg val (set-eip rip x86)) (set-eip rip (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high))))
(defthm set-reg-high-of-set-eax (equal (set-reg-high reg val (set-eax rax x86)) (set-eax rax (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rax-high set-eax))))
(defthm set-reg-high-of-set-ebx (equal (set-reg-high reg val (set-ebx rbx x86)) (set-ebx rbx (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rbx-high set-ebx))))
(defthm set-reg-high-of-set-ecx (equal (set-reg-high reg val (set-ecx rcx x86)) (set-ecx rcx (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rcx-high set-ecx))))
(defthm set-reg-high-of-set-edx (equal (set-reg-high reg val (set-edx rdx x86)) (set-edx rdx (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rdx-high set-edx))))
;; (defthm set-reg-high-of-set-esi (equal (set-reg-high reg val (set-esi rsi x86)) (set-esi rsi (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rbx-high set-esi))))
;; (defthm set-reg-high-of-set-edi (equal (set-reg-high reg val (set-edi rdi x86)) (set-edi rdi (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rbx-high set-edi))))
(defthm set-reg-high-of-set-esp (equal (set-reg-high reg val (set-esp rsp x86)) (set-esp rsp (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rsp-high set-esp))))
(defthm set-reg-high-of-set-ebp (equal (set-reg-high reg val (set-ebp rbp x86)) (set-ebp rbp (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high rbp-high set-ebp))))


;; These push set-mxcsr inward:
(defthm set-mxcsr-of-set-eip (equal (set-mxcsr mxcsr (set-eip rip x86)) (set-eip rip (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm set-mxcsr-of-set-eax (equal (set-mxcsr mxcsr (set-eax rax x86)) (set-eax rax (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-eax))))
(defthm set-mxcsr-of-set-ebx (equal (set-mxcsr mxcsr (set-ebx rbx x86)) (set-ebx rbx (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-ebx))))
(defthm set-mxcsr-of-set-ecx (equal (set-mxcsr mxcsr (set-ecx rcx x86)) (set-ecx rcx (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-ecx))))
(defthm set-mxcsr-of-set-edx (equal (set-mxcsr mxcsr (set-edx rdx x86)) (set-edx rdx (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-edx))))
;; (defthm set-mxcsr-of-set-esi (equal (set-mxcsr mxcsr (set-esi rsi x86)) (set-esi rsi (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-esi))))
;; (defthm set-mxcsr-of-set-edi (equal (set-mxcsr mxcsr (set-edi rdi x86)) (set-edi rdi (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-edi))))
(defthm set-mxcsr-of-set-esp (equal (set-mxcsr mxcsr (set-esp rsp x86)) (set-esp rsp (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-esp))))
(defthm set-mxcsr-of-set-ebp (equal (set-mxcsr mxcsr (set-ebp rbp x86)) (set-ebp rbp (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-ebp))))

(defthm set-reg-high-of-set-flag (equal (set-reg-high reg val (set-flag flag fval x86)) (set-flag flag fval (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-flag set-reg-high))))
(defthm set-reg-high-of-!rflags (equal (set-reg-high reg val (!rflags flags x86)) (!rflags flags (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-reg-high))))
(defthm set-reg-high-of-set-undef (equal (set-reg-high reg val (set-undef undef x86)) (set-undef undef (set-reg-high reg val x86))) :hints (("Goal" :in-theory (enable set-undef set-reg-high))))
